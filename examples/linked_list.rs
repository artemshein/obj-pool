extern crate vec_arena;

use vec_arena::VecArena;

struct Node<T> {
    prev: usize,
    next: usize,
    value: T,
}

struct List<T> {
    arena: VecArena<Node<T>>,
    head: usize,
    tail: usize,
}

impl<T> List<T> {
    fn new() -> Self {
        List {
            arena: VecArena::new(),
            head: !0,
            tail: !0,
        }
    }

    fn len(&self) -> usize {
        self.arena.len()
    }

    fn new_node(&mut self, value: T) -> usize {
        self.arena.insert(Node {
            prev: !0,
            next: !0,
            value: value,
        })
    }

    fn link(&mut self, a: usize, b: usize) {
        if a != !0 { self.arena[a].next = b; }
        if b != !0 { self.arena[b].prev = a; }
    }

    fn push_back(&mut self, value: T) -> usize {
        let node = self.new_node(value);

        let tail = self.tail;
        self.link(tail, node);

        self.tail = node;
        if self.head == !0 {
            self.head = node;
        }
        node
    }

    fn pop_front(&mut self) -> T {
        let node = self.arena.remove(self.head);

        self.link(!0, node.next);
        self.head = node.next;
        if node.next == !0 {
            self.tail = !0;
        }
        node.value
    }

    fn remove(&mut self, index: usize) -> T {
        let node = self.arena.remove(index);

        self.link(node.prev, node.next);
        if self.head == index { self.head = node.next; }
        if self.tail == index { self.tail = node.prev; }

        node.value
    }
}

fn main() {
    let mut list = List::new();

    let one = list.push_back(1);
    list.push_back(2);
    list.push_back(3);

    list.push_back(10);
    let twenty = list.push_back(20);
    list.push_back(30);

    assert!(list.len() == 6);

    assert!(list.remove(one) == 1);
    assert!(list.remove(twenty) == 20);

    assert!(list.len() == 4);

    assert!(list.pop_front() == 2);
    assert!(list.pop_front() == 3);
    assert!(list.pop_front() == 10);
    assert!(list.pop_front() == 30);

    assert!(list.len() == 0);
}