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
/// all shard indices `0..S`. The remaining low bits hold the object id inside
/// the shard, so each shard can hold up to `2^(32 - SHARD_BITS) - 1` objects.
pub struct ParObjPool<T, const S: usize> {
    shards: [RwLock<ObjPool<T>>; S],
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
        }
    }

    pub fn insert(&self, object: T) -> ObjId {
        let counter = COUNTER.with(|c| {
            let v = c.get();
            c.set(v.wrapping_add(1));
            v
        });
        let shard_index = counter % S;
        self.obj_id_to_external(self.shards[shard_index].write().insert(object), shard_index)
    }

    pub fn remove(&self, obj_id: ObjId) -> Option<T> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        self.shards[shard_index].write().remove(obj_id)
    }

    pub fn get(&self, obj_id: ObjId) -> Option<MappedRwLockReadGuard<'_, T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockReadGuard::try_map(self.shards[shard_index].read(), |obj_pool| {
            obj_pool.get(obj_id)
        })
        .ok()
    }

    pub fn try_get(&self, obj_id: ObjId) -> Option<MappedRwLockReadGuard<'_, T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockReadGuard::try_map(self.shards[shard_index].try_read()?, |obj_pool| {
            obj_pool.get(obj_id)
        })
        .ok()
    }

    pub fn get_mut(&self, obj_id: ObjId) -> Option<MappedRwLockWriteGuard<'_, T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockWriteGuard::try_map(self.shards[shard_index].write(), |obj_pool| {
            obj_pool.get_mut(obj_id)
        })
        .ok()
    }

    pub fn try_get_mut(&self, obj_id: ObjId) -> Option<MappedRwLockWriteGuard<'_, T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockWriteGuard::try_map(self.shards[shard_index].try_write()?, |obj_pool| {
            obj_pool.get_mut(obj_id)
        })
        .ok()
    }

    pub fn clear(&self) {
        for shard in &self.shards {
            let mut shard = shard.write();
            shard.clear();
            shard.shrink_to_fit();
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

    fn obj_id_to_external(&self, obj_id: ObjId, shard_index: usize) -> ObjId {
        debug_assert!(
            obj_id.get() <= Self::INDEX_MASK,
            "shard is full: object id does not fit into the index bits"
        );
        if Self::SHARD_BITS == 0 {
            obj_id
        } else {
            ObjId(
                NonZeroU32::new((shard_index as u32) << Self::INDEX_BITS | obj_id.get())
                    .expect("invalid value"),
            )
        }
    }

    fn obj_id_from_external(&self, obj_id: ObjId) -> (usize, ObjId) {
        if Self::SHARD_BITS == 0 {
            (0, obj_id)
        } else {
            let v = obj_id.get();
            (
                (v >> Self::INDEX_BITS) as usize,
                ObjId(NonZeroU32::new(v & Self::INDEX_MASK).expect("invalid value")),
            )
        }
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
            let (shard_index, _) = o.obj_id_from_external(*k);
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
}
