extern crate obj_pool;

use obj_pool::{ObjPool, ObjId};

struct Node<T> {
    /// Previous node in the list.
    prev: ObjId,

    /// Next node in the list.
    next: ObjId,

    /// Actual value stored in node.
    value: T,
}

struct List<T> {
    /// This is where nodes are stored.
    obj_pool: ObjPool<Node<T>>,

    /// First node in the list.
    head: ObjId,

    /// Last node in the list.
    tail: ObjId,

    /// The null index, akin to null pointers.
    ///
    /// Just like a null pointer indicates an address no object is ever stored at,
    /// the null index indicates an index no object is ever stored at.
    null: ObjId,
}

impl<T> List<T> {
    /// Constructs a new, empty doubly linked list.
    fn new() -> Self {
        let obj_pool = ObjPool::new();
        let null = obj_pool.obj_id_from_index(u32::max_value());
        List {
            obj_pool,
            head: null,
            tail: null,
            null,
        }
    }

    /// Returns the number of elements in the list.
    fn len(&self) -> usize {
        self.obj_pool.len() as usize
    }

    /// Links nodes `a` and `b` together, so that `a` comes before `b` in the list.
    fn link(&mut self, a: ObjId, b: ObjId) {
        if a != self.null { self.obj_pool[a].next = b; }
        if b != self.null { self.obj_pool[b].prev = a; }
    }

    /// Appends `value` to the back of the list.
    fn push_back(&mut self, value: T) -> usize {
        let node = self.obj_pool.insert(Node {
            prev: self.null,
            next: self.null,
            value,
        });

        let tail = self.tail;
        self.link(tail, node);

        self.tail = node;
        if self.head == self.null {
            self.head = node;
        }
        self.obj_pool.index_from_obj_id(node) as usize
    }

    /// Pops and returns the value at the front of the list.
    fn pop_front(&mut self) -> T {
        let node = self.obj_pool.remove(self.head).unwrap();

        let null = self.null;
        self.link(null, node.next);
        self.head = node.next;
        if node.next == self.null {
            self.tail = self.null;
        }
        node.value
    }

    /// Removes the element specified by `index`.
    fn remove(&mut self, index: usize) -> T {
        let obj_id = self.obj_pool.obj_id_from_index(index as u32);
        let node = self.obj_pool.remove(obj_id).unwrap();

        self.link(node.prev, node.next);
        if self.head == obj_id { self.head = node.next; }
        if self.tail == obj_id { self.tail = node.prev; }

        node.value
    }
}

fn main() {
    let mut list = List::new();

    // The list is now [].

    let one = list.push_back(1);
    list.push_back(2);
    list.push_back(3);

    // The list is now [1, 2, 3].

    list.push_back(10);
    let twenty = list.push_back(20);
    list.push_back(30);

    // The list is now [1, 2, 3, 10, 20, 30].

    assert_eq!(list.len(), 6);

    assert_eq!(list.remove(one), 1);
    assert_eq!(list.remove(twenty), 20);

    // The list is now [2, 3, 10, 30].

    assert_eq!(list.len(), 4);

    assert_eq!(list.pop_front(), 2);
    assert_eq!(list.pop_front(), 3);
    assert_eq!(list.pop_front(), 10);
    assert_eq!(list.pop_front(), 30);

    // The list is now [].

    assert_eq!(list.len(), 0);
}
