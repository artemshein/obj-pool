use obj_pool::{ObjId, ObjPool};

struct Node<T> {
    /// Parent node.
    parent: Option<ObjId>,

    /// Left and right child.
    children: [Option<ObjId>; 2],

    /// Actual value stored in node.
    value: T,
}

impl<T> Node<T> {
    fn new(value: T) -> Node<T> {
        Node {
            parent: None,
            children: [None, None],
            value,
        }
    }
}

struct Splay<T> {
    /// This is where nodes are stored.
    obj_pool: ObjPool<Node<T>>,

    /// The root node.
    root: Option<ObjId>,
}

impl<T> Splay<T>
where
    T: Ord,
{
    /// Constructs a new, empty splay tree.
    fn new() -> Splay<T> {
        Splay {
            obj_pool: ObjPool::new(),
            root: None,
        }
    }

    /// Links nodes `p` and `c` as parent and child with the specified direction.
    #[inline(always)]
    fn link(&mut self, p: ObjId, c: Option<ObjId>, dir: usize) {
        self.obj_pool[p].children[dir] = c;
        if let Some(c) = c {
            self.obj_pool[c].parent = Some(p);
        }
    }

    /// Performs a rotation on node `c`, whose parent is node `p`.
    #[inline(always)]
    fn rotate(&mut self, p: ObjId, c: ObjId) {
        // Variables:
        // - `c` is the child node
        // - `p` is it's parent
        // - `g` is it's grandparent

        // Find the grandparent.
        let g = self.obj_pool[p].parent;

        // The direction of p-c relationship.
        let dir = if self.obj_pool[p].children[0] == Some(c) {
            0
        } else {
            1
        };

        // This is the child of `c` that needs to be reassigned to `p`.
        let t = self.obj_pool[c].children[dir ^ 1];

        self.link(p, t, dir);
        self.link(c, Some(p), dir ^ 1);

        if let Some(g) = g {
            // Link `g` and `c` together.
            let dir = if self.obj_pool[g].children[0] == Some(p) {
                0
            } else {
                1
            };
            self.link(g, Some(c), dir);
        } else {
            // There is no grandparent, so `c` becomes the root.
            self.root = Some(c);
            self.obj_pool[c].parent = None;
        }
    }

    /// Splays a node, rebalancing the tree in process.
    fn splay(&mut self, c: ObjId) {
        loop {
            // Variables:
            // - `c` is the current node
            // - `p` is it's parent
            // - `g` is it's grandparent

            // Find the parent. If there is none, `c` is the root.
            let Some(p) = self.obj_pool[c].parent else {
                break;
            };

            // Find the grandparent.
            let Some(g) = self.obj_pool[p].parent else {
                // There is no grandparent. Just one more rotation is left.
                // Zig step.
                self.rotate(p, c);
                break;
            };

            if (self.obj_pool[g].children[0] == Some(p))
                == (self.obj_pool[p].children[0] == Some(c))
            {
                // Zig-zig step.
                self.rotate(g, p);
                self.rotate(p, c);
            } else {
                // Zig-zag step.
                self.rotate(p, c);
                self.rotate(g, c);
            }
        }
    }

    /// Inserts a new node with specified `value`.
    fn insert(&mut self, value: T) {
        // Variables:
        // - `n` is the new node
        // - `p` will be it's parent
        // - `c` is the present child of `p`

        let n = self.obj_pool.insert(Node::new(value));

        if let Some(root) = self.root {
            let mut p = root;
            loop {
                // Decide whether to go left or right.
                let dir = if self.obj_pool[n].value < self.obj_pool[p].value {
                    0
                } else {
                    1
                };

                match self.obj_pool[p].children[dir] {
                    Some(c) => p = c,
                    None => {
                        self.link(p, Some(n), dir);
                        self.splay(n);
                        break;
                    }
                }
            }
        } else {
            self.root = Some(n);
        }
    }

    /// Pretty-prints the subtree rooted at `node`, indented by `indent` spaces.
    fn print(&self, node: Option<ObjId>, indent: usize)
    where
        T: std::fmt::Display,
    {
        if let Some(node) = node {
            // Print the left subtree.
            self.print(self.obj_pool[node].children[0], indent + 3);

            // Print the current node.
            println!("{:width$}{}", "", self.obj_pool[node].value, width = indent);

            // Print the right subtree.
            self.print(self.obj_pool[node].children[1], indent + 3);
        }
    }
}

fn main() {
    let mut splay = Splay::new();

    // Insert a bunch of pseudorandom numbers.
    let mut num = 1u32;
    for _ in 0..30 {
        num = num.wrapping_mul(17).wrapping_add(255);
        splay.insert(num);
    }

    // Display the whole splay tree.
    splay.print(splay.root, 0);
}
