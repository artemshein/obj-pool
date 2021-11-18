use crate::*;
use parking_lot::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
};
use std::cell::Cell;
use std::convert::TryInto;

thread_local! {
  static COUNTER: Cell<usize> = Cell::new(0);
}

pub struct ParObjPool<T, const S: usize> {
    shards: [RwLock<ObjPool<T>>; S],
}

impl<T, const S: usize> ParObjPool<T, S> {
    pub fn new() -> Self {
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

    pub fn get(&self, obj_id: ObjId) -> Option<MappedRwLockReadGuard<T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockReadGuard::try_map(self.shards[shard_index].read(), |obj_pool| {
            obj_pool.get(obj_id)
        })
        .ok()
    }

    pub fn get_mut(&self, obj_id: ObjId) -> Option<MappedRwLockWriteGuard<T>> {
        let (shard_index, obj_id) = self.obj_id_from_external(obj_id);
        RwLockWriteGuard::try_map(self.shards[shard_index].write(), |obj_pool| {
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
        ObjId(NonZeroU32::new((shard_index << 26) as u32 | obj_id.get()).expect("invalid value"))
    }

    fn obj_id_from_external(&self, obj_id: ObjId) -> (usize, ObjId) {
        let v = obj_id.get();
        (
            (v >> 26) as usize,
            ObjId(NonZeroU32::new(v & 0x03FFFFFF).expect("invalid value")),
        )
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
    }
}
