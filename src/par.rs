use crate::*;
use parking_lot::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
};
use std::cell::Cell;
use std::convert::TryInto;

thread_local! {
  static COUNTER: Cell<usize> = const { Cell::new(0) };
}

/// A sharded, thread-safe object pool.
///
/// An external `ObjId` packs the shard index into its highest `SHARD_BITS`
/// bits, where `SHARD_BITS` is the smallest number of bits able to represent
/// all shard indices `0..S`. The remaining low bits hold the object index
/// inside the shard, so each shard can hold up to `2^(32 - SHARD_BITS) - 1`
/// objects.
///
/// In debug builds every `ParObjPool` additionally mixes its own random tag
/// into the external `ObjId`s it issues, so ids of one pool are (with
/// overwhelming probability) rejected by any other pool. See the crate-level
/// documentation for details.
pub struct ParObjPool<T, const S: usize> {
    shards: [RwLock<ObjPool<T>>; S],

    /// Debug-only random tag mixed into every external `ObjId` of this pool.
    tag: PoolTag,
}

impl<T, const S: usize> Default for ParObjPool<T, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const S: usize> ParObjPool<T, S> {
    /// Number of high bits of an external `ObjId` storing the shard index:
    /// the smallest number of bits able to represent all shard indices `0..S`.
    /// For `S == 1` it is zero and ids pass through unchanged.
    const SHARD_BITS: u32 = usize::BITS - (S - 1).leading_zeros();

    /// Number of low bits of an external `ObjId` storing the in-shard object id.
    const INDEX_BITS: u32 = u32::BITS - Self::SHARD_BITS;

    /// Mask selecting the in-shard object id bits of an external `ObjId`.
    const INDEX_MASK: u32 = u32::MAX >> Self::SHARD_BITS;

    pub fn new() -> Self {
        const {
            assert!(S > 0, "ParObjPool requires at least one shard");
            assert!(
                Self::SHARD_BITS < u32::BITS,
                "too many shards: no bits left in ObjId for the object index"
            );
        }
        let mut shards = Vec::with_capacity(S);
        shards.resize_with(S, || RwLock::new(ObjPool::<T>::new()));
        Self {
            shards: shards.try_into().expect("invalid array"),
            tag: PoolTag::random(),
        }
    }

    pub fn insert(&self, object: T) -> ObjId {
        let counter = COUNTER.with(|c| {
            let v = c.get();
            c.set(v.wrapping_add(1));
            v
        });
        let shard_index = counter % S;
        let mut shard = self.shards[shard_index].write();
        let inner = shard.insert(object);
        let index = shard.obj_id_to_index(inner);
        drop(shard);
        self.obj_id_to_external(shard_index, index)
    }

    pub fn remove(&self, obj_id: ObjId) -> Option<T> {
        let (shard_index, index) = self.obj_id_from_external(obj_id)?;
        let mut shard = self.shards[shard_index].write();
        let inner = shard.index_to_obj_id(index);
        shard.remove(inner)
    }

    pub fn get(&self, obj_id: ObjId) -> Option<MappedRwLockReadGuard<'_, T>> {
        let (shard_index, index) = self.obj_id_from_external(obj_id)?;
        RwLockReadGuard::try_map(self.shards[shard_index].read(), |obj_pool| {
            obj_pool.get(obj_pool.index_to_obj_id(index))
        })
        .ok()
    }

    pub fn try_get(&self, obj_id: ObjId) -> Option<MappedRwLockReadGuard<'_, T>> {
        let (shard_index, index) = self.obj_id_from_external(obj_id)?;
        RwLockReadGuard::try_map(self.shards[shard_index].try_read()?, |obj_pool| {
            obj_pool.get(obj_pool.index_to_obj_id(index))
        })
        .ok()
    }

    pub fn get_mut(&self, obj_id: ObjId) -> Option<MappedRwLockWriteGuard<'_, T>> {
        let (shard_index, index) = self.obj_id_from_external(obj_id)?;
        RwLockWriteGuard::try_map(self.shards[shard_index].write(), |obj_pool| {
            obj_pool.get_mut(obj_pool.index_to_obj_id(index))
        })
        .ok()
    }

    pub fn try_get_mut(&self, obj_id: ObjId) -> Option<MappedRwLockWriteGuard<'_, T>> {
        let (shard_index, index) = self.obj_id_from_external(obj_id)?;
        RwLockWriteGuard::try_map(self.shards[shard_index].try_write()?, |obj_pool| {
            obj_pool.get_mut(obj_pool.index_to_obj_id(index))
        })
        .ok()
    }

    pub fn clear(&self) {
        for shard in &self.shards {
            shard.write().clear();
        }
    }

    pub fn shrink_to_fit(&self) {
        for shard in &self.shards {
            let mut shard = shard.write();
            shard.shrink_to_fit();
        }
    }

    pub fn capacity(&self) -> usize {
        self.shards.iter().map(|s| s.read().capacity()).sum()
    }

    fn obj_id_to_external(&self, shard_index: usize, index: u32) -> ObjId {
        debug_assert!(
            index < Self::INDEX_MASK,
            "shard is full: object index does not fit into the index bits"
        );
        let raw = if Self::SHARD_BITS == 0 {
            index
        } else {
            (shard_index as u32) << Self::INDEX_BITS | index
        };
        self.tag.mask_id(ObjId::from_index(raw))
    }

    fn obj_id_from_external(&self, obj_id: ObjId) -> Option<(usize, u32)> {
        let raw = self.tag.unmask_id(obj_id).into_index();
        let (shard_index, index) = if Self::SHARD_BITS == 0 {
            (0, raw)
        } else {
            ((raw >> Self::INDEX_BITS) as usize, raw & Self::INDEX_MASK)
        };
        // A foreign or corrupted id can decode to a nonexistent shard.
        (shard_index < S).then_some((shard_index, index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let o = ParObjPool::<usize, 16>::new();
        let k = o.insert(10);
        assert_eq!(o.get(k).map(|v| *v), Some(10));
        let k = o.insert(20);
        assert_eq!(o.get(k).map(|v| *v), Some(20));
        let k = o.insert(30);
        assert_eq!(o.get(k).map(|v| *v), Some(30));
        assert_eq!(o.try_get(k).map(|v| *v), Some(30));
        assert_eq!(o.try_get_mut(k).map(|v| *v), Some(30));
    }

    #[test]
    fn shard_bits() {
        assert_eq!(ParObjPool::<u8, 1>::SHARD_BITS, 0);
        assert_eq!(ParObjPool::<u8, 1>::INDEX_MASK, u32::MAX);
        assert_eq!(ParObjPool::<u8, 2>::SHARD_BITS, 1);
        assert_eq!(ParObjPool::<u8, 3>::SHARD_BITS, 2);
        assert_eq!(ParObjPool::<u8, 16>::SHARD_BITS, 4);
        assert_eq!(ParObjPool::<u8, 16>::INDEX_MASK, 0x0FFFFFFF);
        assert_eq!(ParObjPool::<u8, 64>::SHARD_BITS, 6);
        assert_eq!(ParObjPool::<u8, 64>::INDEX_MASK, 0x03FFFFFF);
        assert_eq!(ParObjPool::<u8, 65>::SHARD_BITS, 7);
        assert_eq!(ParObjPool::<u8, 100>::SHARD_BITS, 7);
    }

    fn insert_get_remove<const S: usize>() {
        let o = ParObjPool::<usize, S>::new();
        // More inserts than shards, so every shard is exercised.
        let keys: Vec<_> = (0..S * 3 + 1).map(|v| (o.insert(v), v)).collect();
        for (k, v) in &keys {
            let (shard_index, _) = o.obj_id_from_external(*k).expect("id of this pool");
            assert!(shard_index < S);
            assert_eq!(o.get(*k).map(|v| *v), Some(*v));
        }
        for (k, v) in &keys {
            assert_eq!(o.remove(*k), Some(*v));
            assert_eq!(o.get(*k).map(|v| *v), None);
        }
    }

    #[test]
    fn shard_counts() {
        insert_get_remove::<1>();
        insert_get_remove::<2>();
        insert_get_remove::<3>();
        insert_get_remove::<16>();
        insert_get_remove::<64>();
        insert_get_remove::<100>();
    }

    #[cfg(debug_assertions)]
    #[test]
    fn foreign_ids_are_rejected() {
        let a = ParObjPool::<usize, 4>::new();
        let id = a.insert(10);

        let mut b = ParObjPool::<usize, 4>::new();
        // Make sure the pools did not roll the same random tag.
        while b.tag.offset == a.tag.offset {
            b = ParObjPool::new();
        }
        let own = b.insert(20);

        assert!(b.get(id).is_none());
        assert!(b.get_mut(id).is_none());
        assert!(b.remove(id).is_none());
        assert_eq!(b.get(own).map(|v| *v), Some(20));
    }

    #[test]
    fn clear_releases_and_reuses() {
        let o = ParObjPool::<usize, 4>::new();
        let keys: Vec<_> = (0..8).map(|v| o.insert(v)).collect();
        assert!(o.capacity() >= 8);

        o.clear();
        assert_eq!(o.capacity(), 0);
        for k in keys {
            assert!(o.get(k).is_none());
            assert!(o.remove(k).is_none());
        }

        let k = o.insert(42);
        assert_eq!(o.get(k).map(|v| *v), Some(42));
    }

    #[test]
    fn get_mut_mutates_and_remove_twice() {
        let o = ParObjPool::<usize, 4>::new();
        let k = o.insert(1);

        *o.get_mut(k).unwrap() = 2;
        assert_eq!(o.get(k).map(|v| *v), Some(2));

        assert_eq!(o.remove(k), Some(2));
        assert_eq!(o.remove(k), None);
        assert!(o.get(k).is_none());
        assert!(o.get_mut(k).is_none());
    }

    #[test]
    fn try_get_respects_shard_write_lock() {
        let o = ParObjPool::<usize, 2>::new();
        let k = o.insert(7);

        let guard = o.get_mut(k).unwrap();
        // The shard holding `k` is write-locked, so non-blocking reads must fail
        // instead of deadlocking.
        assert!(o.try_get(k).is_none());
        assert!(o.try_get_mut(k).is_none());
        drop(guard);

        assert_eq!(o.try_get(k).map(|v| *v), Some(7));
        assert_eq!(o.try_get_mut(k).map(|v| *v), Some(7));
    }

    #[test]
    fn concurrent_insert_get_remove() {
        let pool = ParObjPool::<usize, 8>::new();
        std::thread::scope(|s| {
            for t in 0..4 {
                let pool = &pool;
                s.spawn(move || {
                    let keys: Vec<_> = (0..100)
                        .map(|i| {
                            let value = t * 1000 + i;
                            (pool.insert(value), value)
                        })
                        .collect();
                    for (k, v) in &keys {
                        assert_eq!(pool.get(*k).map(|g| *g), Some(*v));
                        *pool.get_mut(*k).unwrap() += 1;
                    }
                    for (k, v) in keys {
                        assert_eq!(pool.remove(k), Some(v + 1));
                    }
                });
            }
        });
    }
}
