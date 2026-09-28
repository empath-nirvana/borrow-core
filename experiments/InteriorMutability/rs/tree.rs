// A tree with parent pointers: children own their nodes through `Rc<RefCell<Node>>`, and each
// node points back to its parent through a `Weak`. `depth_and_sum` walks from a node to the
// root. Nodes 0..=5: 0 is the root (value 1); 1 (2) and 2 (3) are its children; 3 (4) is a
// child of 1; 4 (5) of 3; 5 (6) of 4. Prints (4, 18, 4): node 5's depth, the sum of the
// values on its path to the root (6+5+4+2+1), and its parent's id.
use std::cell::RefCell;
use std::rc::{Rc, Weak};

struct Node {
    id: usize,
    value: i32,
    parent: RefCell<Weak<Node>>,
    children: RefCell<Vec<Rc<Node>>>,
}

fn node(id: usize, value: i32) -> Rc<Node> {
    Rc::new(Node { id, value, parent: RefCell::new(Weak::new()), children: RefCell::new(vec![]) })
}

fn add_child(parent: &Rc<Node>, child: Rc<Node>) {
    *child.parent.borrow_mut() = Rc::downgrade(parent);
    parent.children.borrow_mut().push(child);
}

fn depth_and_sum(n: &Rc<Node>) -> (i32, i32) {
    let (mut d, mut s) = (0, n.value);
    let mut cur = n.parent.borrow().upgrade();
    while let Some(p) = cur {
        d += 1;
        s += p.value;
        cur = p.parent.borrow().upgrade();
    }
    (d, s)
}

fn main() {
    let ns: Vec<Rc<Node>> = (0..6).map(|i| node(i, i as i32 + 1)).collect();
    for (p, c) in [(0, 1), (0, 2), (1, 3), (3, 4), (4, 5)] {
        add_child(&ns[p], ns[c].clone());
    }
    let (d, s) = depth_and_sum(&ns[5]);
    let parent = ns[5].parent.borrow().upgrade().unwrap().id;
    println!("({}, {}, {})", d, s, parent);
}
