//! A simple object pool.
//!
//! `ObjPool<T>` is basically just a `Vec<Option<T>>`, which allows you to:
//!
//! * Insert an object (reuse an existing `None` element, or append to the end) and get an `ObjId`
//!   in return.
//! * Remove object with a specified `ObjId`.
//! * Access object with a specified `ObjId`.
//!
//! # Examples
//!
//! Some data structures built using `ObjPool<T>`:
//!
//! * [Doubly linked list](https://github.com/artemshein/obj-pool/blob/master/examples/linked_list.rs)
//! * [Splay tree](https://github.com/artemshein/obj-pool/blob/master/examples/splay_tree.rs)

extern crate unreachable;

use std::fmt;
use std::iter;
use std::mem;
use std::ops::{Index, IndexMut};
use std::ptr;

use unreachable::unreachable;

/// A slot, which is either vacant or occupied.
///
/// Vacant slots in object pool are linked together into a singly linked list. This allows the object pool to
/// efficiently find a vacant slot before inserting a new object, or reclaiming a slot after
/// removing an object.
#[derive(Clone)]
enum Slot<T> {
    /// Vacant slot, containing index to the next slot in the linked list.
    Vacant(u32),

    /// Occupied slot, containing a value.
    Occupied(T),
}

/// An id of the object in an `ObjPool`.
///
/// It is basically just an index in the underlying vector.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ObjId(u32);

/// An object pool.
///
/// `ObjPool<T>` holds an array of slots for storing objects.
/// Every slot is always in one of two states: occupied or vacant.
///
/// Essentially, this is equivalent to `Vec<Option<T>>`.
///
/// # Insert and remove
///
/// When inserting a new object into object pool, a vacant slot is found and then the object is placed
/// into the slot. If there are no vacant slots, the array is reallocated with bigger capacity.
/// The cost of insertion is amortized `O(1)`.
///
/// When removing an object, the slot containing it is marked as vacant and the object is returned.
/// The cost of removal is `O(1)`.
///
/// ```
/// use obj_pool::ObjPool;
///
/// let mut obj_pool = ObjPool::new();
/// let a = obj_pool.insert(10);
/// let b = obj_pool.insert(20);
///
/// assert_ne!(a, b); // ids are not the same
///
/// assert_eq!(obj_pool.remove(a), Some(10));
/// assert_eq!(obj_pool.get(a), None); // there is no object with this `ObjId` anymore
///
/// assert_eq!(obj_pool.insert(30), a); // slot is reused, got the same `ObjId`
/// ```
///
/// # Indexing
///
/// You can also access objects in an object pool by `ObjId`.
/// However, accessing an object with invalid `ObjId` will result in panic.
///
/// ```
/// use obj_pool::ObjPool;
///
/// let mut obj_pool = ObjPool::new();
/// let a = obj_pool.insert(10);
/// let b = obj_pool.insert(20);
///
/// assert_eq!(obj_pool[a], 10);
/// assert_eq!(obj_pool[b], 20);
///
/// obj_pool[a] += obj_pool[b];
/// assert_eq!(obj_pool[a], 30);
/// ```
///
/// To access slots without fear of panicking, use `get` and `get_mut`, which return `Option`s.
pub struct ObjPool<T> {
    /// Slots in which objects are stored.
    slots: Vec<Slot<T>>,

    /// Number of occupied slots in the object pool.
    len: u32,

    /// Index of the first vacant slot in the linked list.
    head: u32,

    /// Offset for index (debug only)
    offset: u32,
}

impl<T> ObjPool<T> {
    /// Constructs a new, empty object pool.
    ///
    /// The object pool will not allocate until objects are inserted into it.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool: ObjPool<i32> = ObjPool::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        ObjPool {
            slots: Vec::new(),
            len: 0,
            head: !0,
            offset: 0,
        }
    }

    #[inline]
    pub fn obj_id_from_index(&self, index: u32) -> ObjId {
        ObjId(index)
    }

    #[inline]
    pub fn index_from_obj_id(&self, obj_id: ObjId) -> u32 {
        obj_id.0
    }

    /// Constructs a new, empty object pool with the specified capacity (number of slots).
    ///
    /// The object pool will be able to hold exactly `capacity` objects without reallocating.
    /// If `capacity` is 0, the object pool will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::with_capacity(10);
    ///
    /// assert_eq!(obj_pool.len(), 0);
    /// assert_eq!(obj_pool.capacity(), 10);
    ///
    /// // These inserts are done without reallocating...
    /// for i in 0..10 {
    ///     obj_pool.insert(i);
    /// }
    /// assert_eq!(obj_pool.capacity(), 10);
    ///
    /// // ... but this one will reallocate.
    /// obj_pool.insert(11);
    /// assert!(obj_pool.capacity() > 10);
    /// ```
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        ObjPool {
            slots: Vec::with_capacity(cap),
            len: 0,
            head: !0,
            offset: 0,
        }
    }

    /// Returns the number of slots in the object pool.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let obj_pool: ObjPool<i32> = ObjPool::with_capacity(10);
    /// assert_eq!(obj_pool.capacity(), 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Returns the number of occupied slots in the object pool.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// assert_eq!(obj_pool.len(), 0);
    ///
    /// for i in 0..10 {
    ///     obj_pool.insert(());
    ///     assert_eq!(obj_pool.len(), i + 1);
    /// }
    /// ```
    #[inline]
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Returns `true` if all slots are vacant.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// assert!(obj_pool.is_empty());
    ///
    /// obj_pool.insert(1);
    /// assert!(!obj_pool.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the `ObjId` of the next inserted object if no other
    /// mutating calls take place in between.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    ///
    /// let a = obj_pool.next_vacant();
    /// let b = obj_pool.insert(1);
    /// assert_eq!(a, b);
    /// let c = obj_pool.next_vacant();
    /// let d = obj_pool.insert(2);
    /// assert_eq!(c, d);
    /// ```
    #[inline]
    pub fn next_vacant(&mut self) -> ObjId {
        if self.head == !0 {
            ObjId(self.len as u32)
        } else {
            ObjId(self.head as u32)
        }
    }

    /// Inserts an object into the object pool and returns the `ObjId` of this object.
    /// The object pool will reallocate if it's full.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    ///
    /// let a = obj_pool.insert(1);
    /// let b = obj_pool.insert(2);
    /// assert!(a != b);
    /// ```
    pub fn insert(&mut self, object: T) -> ObjId {
        self.len += 1;

        if self.head == !0 {
            self.slots.push(Slot::Occupied(object));
            ObjId(self.len - 1)
        } else {
            let index = self.head;
            match self.slots[index as usize] {
                Slot::Vacant(next) => {
                    self.head = next;
                    self.slots[index as usize] = Slot::Occupied(object);
                },
                Slot::Occupied(_) => unreachable!(),
            }
            ObjId(index)
        }
    }

    /// Removes the object stored by `ObjId` from the object pool and returns it.
    ///
    /// `None` is returned in case the there is no object with such an `ObjId`.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let a = obj_pool.insert("hello");
    ///
    /// assert_eq!(obj_pool.len(), 1);
    /// assert_eq!(obj_pool.remove(a), Some("hello"));
    ///
    /// assert_eq!(obj_pool.len(), 0);
    /// assert_eq!(obj_pool.remove(a), None);
    /// ```
    pub fn remove(&mut self, obj_id: ObjId) -> Option<T> {
        match self.slots.get_mut(obj_id.0 as usize) {
            None => None,
            Some(&mut Slot::Vacant(_)) => None,
            Some(slot @ &mut Slot::Occupied(_)) => {
                if let Slot::Occupied(object) = mem::replace(slot, Slot::Vacant(self.head)) {
                    self.head = obj_id.0;
                    self.len -= 1;
                    Some(object)
                } else {
                    unreachable!();
                }
            }
        }
    }

    /// Clears the object pool, removing and dropping all objects it holds. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// for i in 0..10 {
    ///     obj_pool.insert(i);
    /// }
    ///
    /// assert_eq!(obj_pool.len(), 10);
    /// obj_pool.clear();
    /// assert_eq!(obj_pool.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.slots.clear();
        self.len = 0;
        self.head = !0;
    }

    /// Returns a reference to the object by its `ObjId`.
    ///
    /// If object is not found with given `obj_id`, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let obj_id = obj_pool.insert("hello");
    ///
    /// assert_eq!(obj_pool.get(obj_id), Some(&"hello"));
    /// obj_pool.remove(obj_id);
    /// assert_eq!(obj_pool.get(obj_id), None);
    /// ```
    pub fn get(&self, obj_id: ObjId) -> Option<&T> {
        match self.slots.get(obj_id.0 as usize) {
            None => None,
            Some(&Slot::Vacant(_)) => None,
            Some(&Slot::Occupied(ref object)) => Some(object),
        }
    }

    /// Returns a mutable reference to the object by its `ObjId`.
    ///
    /// If object can't be found, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let obj_id = obj_pool.insert(7);
    ///
    /// assert_eq!(obj_pool.get_mut(obj_id), Some(&mut 7));
    /// *obj_pool.get_mut(obj_id).unwrap() *= 10;
    /// assert_eq!(obj_pool.get_mut(obj_id), Some(&mut 70));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, obj_id: ObjId) -> Option<&mut T> {
        match self.slots.get_mut(obj_id.0 as usize) {
            None => None,
            Some(&mut Slot::Vacant(_)) => None,
            Some(&mut Slot::Occupied(ref mut object)) => Some(object),
        }
    }

    /// Returns a reference to the object by its `ObjId`.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if object can't be found.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let obj_id = obj_pool.insert("hello");
    ///
    /// unsafe { assert_eq!(&*obj_pool.get_unchecked(obj_id), &"hello") }
    /// ```
    pub unsafe fn get_unchecked(&self, obj_id: ObjId) -> &T {
        match self.slots.get(obj_id.0 as usize) {
            None => unreachable(),
            Some(&Slot::Vacant(_)) => unreachable(),
            Some(&Slot::Occupied(ref object)) => object,
        }
    }

    /// Returns a mutable reference to the object by its `ObjId`.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if object can't be found.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let obj_id = obj_pool.insert("hello");
    ///
    /// unsafe { assert_eq!(&*obj_pool.get_unchecked_mut(obj_id), &"hello") }
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, obj_id: ObjId) -> &mut T {
        match self.slots.get_mut(obj_id.0 as usize) {
            None => unreachable(),
            Some(&mut Slot::Vacant(_)) => unreachable(),
            Some(&mut Slot::Occupied(ref mut object)) => object,
        }
    }

    /// Swaps two objects in the object pool.
    ///
    /// The two `ObjId`s are `a` and `b`.
    ///
    /// # Panics
    ///
    /// Panics if any of the `ObjId`s is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// let a = obj_pool.insert(7);
    /// let b = obj_pool.insert(8);
    ///
    /// obj_pool.swap(a, b);
    /// assert_eq!(obj_pool.get(a), Some(&8));
    /// assert_eq!(obj_pool.get(b), Some(&7));
    /// ```
    #[inline]
    pub fn swap(&mut self, a: ObjId, b: ObjId) {
        unsafe {
            let fst = self.get_mut(a).unwrap() as *mut _;
            let snd = self.get_mut(b).unwrap() as *mut _;
            if a != b {
                ptr::swap(fst, snd);
            }
        }
    }

    /// Reserves capacity for at least `additional` more objects to be inserted. The object pool may
    /// reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// obj_pool.insert("hello");
    ///
    /// obj_pool.reserve(10);
    /// assert!(obj_pool.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: u32) {
        let vacant = self.slots.len() as u32 - self.len;
        if additional > vacant {
            self.slots.reserve((additional - vacant) as usize);
        }
    }

    /// Reserves the minimum capacity for exactly `additional` more objects to be inserted.
    ///
    /// Note that the allocator may give the object pool more space than it requests.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::new();
    /// obj_pool.insert("hello");
    ///
    /// obj_pool.reserve_exact(10);
    /// assert!(obj_pool.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: u32) {
        let vacant = self.slots.len() as u32 - self.len;
        if additional > vacant {
            self.slots.reserve_exact((additional - vacant) as usize);
        }
    }

    /// Shrinks the capacity of the object pool as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform
    /// the object pool that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use obj_pool::ObjPool;
    ///
    /// let mut obj_pool = ObjPool::with_capacity(10);
    /// obj_pool.insert("first".to_string());
    /// obj_pool.insert("second".to_string());
    /// obj_pool.insert("third".to_string());
    /// assert_eq!(obj_pool.capacity(), 10);
    /// obj_pool.shrink_to_fit();
    /// assert!(obj_pool.capacity() >= 3);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.slots.shrink_to_fit();
    }
}

impl<T> fmt::Debug for ObjPool<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ObjPool {{ ... }}")
    }
}

impl<T> Index<ObjId> for ObjPool<T> {
    type Output = T;

    #[inline]
    fn index(&self, obj_id: ObjId) -> &T {
        self.get(obj_id).expect("object not found")
    }
}

impl<T> IndexMut<ObjId> for ObjPool<T> {
    #[inline]
    fn index_mut(&mut self, obj_id: ObjId) -> &mut T {
        self.get_mut(obj_id).expect("object not found")
    }
}

impl<T> Default for ObjPool<T> {
    fn default() -> Self {
        ObjPool::new()
    }
}

impl<T: Clone> Clone for ObjPool<T> {
    fn clone(&self) -> Self {
        ObjPool {
            slots: self.slots.clone(),
            len: self.len,
            head: self.head,
            offset: self.offset,
        }
    }
}

impl<T> iter::FromIterator<T> for ObjPool<T> {
    fn from_iter<U: IntoIterator<Item=T>>(iter: U) -> ObjPool<T> {
        let iter = iter.into_iter();
        let mut obj_pool = ObjPool::with_capacity(iter.size_hint().0);
        for i in iter {
            obj_pool.insert(i);
        }
        obj_pool
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let obj_pool = ObjPool::<i32>::new();
        assert!(obj_pool.is_empty());
        assert_eq!(obj_pool.len(), 0);
        assert_eq!(obj_pool.capacity(), 0);
    }

    #[test]
    fn insert() {
        let mut obj_pool = ObjPool::new();

        for i in 0..10 {
            let a= obj_pool.insert(i * 10);
            assert_eq!(obj_pool[a], i * 10);
        }
        assert!(!obj_pool.is_empty());
        assert_eq!(obj_pool.len(), 10);
    }

    #[test]
    fn with_capacity() {
        let mut obj_pool = ObjPool::with_capacity(10);
        assert_eq!(obj_pool.capacity(), 10);

        for _ in 0..10 {
            obj_pool.insert(());
        }
        assert_eq!(obj_pool.len(), 10);
        assert_eq!(obj_pool.capacity(), 10);

        obj_pool.insert(());
        assert_eq!(obj_pool.len(), 11);
        assert!(obj_pool.capacity() > 10);
    }

    #[test]
    fn remove() {
        let mut obj_pool = ObjPool::new();

        let a = obj_pool.insert(0);
        let b = obj_pool.insert(10);
        let c = obj_pool.insert(20);
        obj_pool.insert(30);
        assert_eq!(obj_pool.len(), 4);

        assert_eq!(obj_pool.remove(b), Some(10));
        assert_eq!(obj_pool.remove(c), Some(20));
        assert_eq!(obj_pool.len(), 2);

        obj_pool.insert(-1);
        obj_pool.insert(-1);
        assert_eq!(obj_pool.len(), 4);

        assert_eq!(obj_pool.remove(a), Some(0));
        obj_pool.insert(-1);
        assert_eq!(obj_pool.len(), 4);

        obj_pool.insert(400);
        assert_eq!(obj_pool.len(), 5);
    }

    #[test]
    fn clear() {
        let mut obj_pool = ObjPool::new();
        obj_pool.insert(10);
        obj_pool.insert(20);

        assert!(!obj_pool.is_empty());
        assert_eq!(obj_pool.len(), 2);

        let cap = obj_pool.capacity();
        obj_pool.clear();

        assert!(obj_pool.is_empty());
        assert_eq!(obj_pool.len(), 0);
        assert_eq!(obj_pool.capacity(), cap);
    }

    #[test]
    fn indexing() {
        let mut obj_pool = ObjPool::new();

        let a = obj_pool.insert(10);
        let b = obj_pool.insert(20);
        let c = obj_pool.insert(30);

        obj_pool[b] += obj_pool[c];
        assert_eq!(obj_pool[a], 10);
        assert_eq!(obj_pool[b], 50);
        assert_eq!(obj_pool[c], 30);
    }

    #[test]
    #[should_panic]
    fn indexing_vacant() {
        let mut obj_pool = ObjPool::new();

        let _ = obj_pool.insert(10);
        let b = obj_pool.insert(20);
        let _ = obj_pool.insert(30);

        obj_pool.remove(b);
        obj_pool[b];
    }

    #[test]
    #[should_panic]
    fn invalid_indexing() {
        let mut obj_pool = ObjPool::new();

        obj_pool.insert(10);
        obj_pool.insert(20);
        let a = obj_pool.insert(30);
        obj_pool.remove(a);

        obj_pool[a];
    }

    #[test]
    fn get() {
        let mut obj_pool = ObjPool::new();

        let a = obj_pool.insert(10);
        let b = obj_pool.insert(20);
        let c = obj_pool.insert(30);

        *obj_pool.get_mut(b).unwrap() += *obj_pool.get(c).unwrap();
        assert_eq!(obj_pool.get(a), Some(&10));
        assert_eq!(obj_pool.get(b), Some(&50));
        assert_eq!(obj_pool.get(c), Some(&30));

        obj_pool.remove(b);
        assert_eq!(obj_pool.get(b), None);
        assert_eq!(obj_pool.get_mut(b), None);
    }

    #[test]
    fn reserve() {
        let mut obj_pool = ObjPool::new();
        obj_pool.insert(1);
        obj_pool.insert(2);

        obj_pool.reserve(10);
        assert!(obj_pool.capacity() >= 11);
    }

    #[test]
    fn reserve_exact() {
        let mut obj_pool = ObjPool::new();
        obj_pool.insert(1);
        obj_pool.insert(2);
        obj_pool.reserve(10);
        assert!(obj_pool.capacity() >= 11);
    }
}
