// AWFY CD's RedBlackTree, index form, the same run as awfy/cd_rbtree.bc: 2000 puts of keys from
// AWFY's Random (seed % 1000) with a Vector3D value; CLRS insertion with parent links and
// rotations; then the in-order walk by successor along parent links. Node 0 is the sentinel nil.
// Answer (count, ok, sum of x).
rs::counting!();

#[derive(Clone, Copy)]
struct Node { key: i32, left: usize, right: usize, parent: usize, red: bool, val: (f64, f64, f64) }

struct Tree { n: Vec<Node>, root: usize }

impl Tree {
    fn left_rotate(&mut self, x: usize) {
        let y = self.n[x].right;
        let yl = self.n[y].left;
        self.n[x].right = yl;
        if yl != 0 { self.n[yl].parent = x }
        let xp = self.n[x].parent;
        self.n[y].parent = xp;
        if xp == 0 { self.root = y } else if x == self.n[xp].left { self.n[xp].left = y } else { self.n[xp].right = y }
        self.n[y].left = x;
        self.n[x].parent = y;
    }
    fn right_rotate(&mut self, x: usize) {
        let y = self.n[x].left;
        let yr = self.n[y].right;
        self.n[x].left = yr;
        if yr != 0 { self.n[yr].parent = x }
        let xp = self.n[x].parent;
        self.n[y].parent = xp;
        if xp == 0 { self.root = y } else if x == self.n[xp].right { self.n[xp].right = y } else { self.n[xp].left = y }
        self.n[y].right = x;
        self.n[x].parent = y;
    }
    fn fixup(&mut self, mut z: usize) {
        while self.n[self.n[z].parent].red {
            let zp = self.n[z].parent;
            let zpp = self.n[zp].parent;
            if zp == self.n[zpp].left {
                let y = self.n[zpp].right;
                if self.n[y].red {
                    self.n[zp].red = false; self.n[y].red = false; self.n[zpp].red = true; z = zpp;
                } else {
                    if z == self.n[zp].right { z = zp; self.left_rotate(z) }
                    let zp2 = self.n[z].parent; let zpp2 = self.n[zp2].parent;
                    self.n[zp2].red = false; self.n[zpp2].red = true; self.right_rotate(zpp2);
                }
            } else {
                let y = self.n[zpp].left;
                if self.n[y].red {
                    self.n[zp].red = false; self.n[y].red = false; self.n[zpp].red = true; z = zpp;
                } else {
                    if z == self.n[zp].left { z = zp; self.right_rotate(z) }
                    let zp2 = self.n[z].parent; let zpp2 = self.n[zp2].parent;
                    self.n[zp2].red = false; self.n[zpp2].red = true; self.left_rotate(zpp2);
                }
            }
        }
        let r = self.root;
        self.n[r].red = false;
    }
    fn put(&mut self, key: i32, val: (f64, f64, f64)) {
        let (mut p, mut cur) = (0, self.root);
        while cur != 0 {
            p = cur;
            let k = self.n[cur].key;
            if key < k { cur = self.n[cur].left } else if k < key { cur = self.n[cur].right } else { self.n[cur].val = val; return }
        }
        let z = self.n.len();
        self.n.push(Node { key, left: 0, right: 0, parent: p, red: true, val });
        if p == 0 { self.root = z } else if key < self.n[p].key { self.n[p].left = z } else { self.n[p].right = z }
        self.fixup(z);
    }
    fn minimum(&self, mut x: usize) -> usize { while self.n[x].left != 0 { x = self.n[x].left } x }
    fn successor(&self, mut x: usize) -> usize {
        if self.n[x].right != 0 { return self.minimum(self.n[x].right) }
        let mut y = self.n[x].parent;
        while y != 0 && x == self.n[y].right { x = y; y = self.n[y].parent }
        y
    }
    fn black_height_to_root(&self, mut x: usize) -> i32 {
        let mut h = 0;
        while x != 0 {
            let p = self.n[x].parent;
            if self.n[x].red && self.n[p].red { h = -1000000 }
            if !self.n[x].red { h += 1 }
            x = p;
        }
        h
    }
}

fn main_tree(n: usize) -> (i32, i32, f64) {
    let mut t = Tree { n: Vec::with_capacity(n + 2), root: 0 };
    t.n.push(Node { key: 0, left: 0, right: 0, parent: 0, red: false, val: (0.0, 0.0, 0.0) });
    let mut seed: i32 = 74755;
    for _ in 0..n {
        seed = (seed.wrapping_mul(1309).wrapping_add(13849)) & 65535;
        t.put(seed % 1000, (seed as f64, 0.0, 1.0));
    }
    let mut x = t.minimum(t.root);
    let (mut count, mut ok, mut prev, mut bh, mut sum) = (0, 1, -1, -1, 0.0);
    while x != 0 {
        count += 1;
        let nd = t.n[x];
        if nd.key <= prev { ok = 0 }
        prev = nd.key;
        sum += nd.val.0;
        if nd.left == 0 || nd.right == 0 {
            let h = t.black_height_to_root(x);
            if bh < 0 { bh = h } else if h != bh { ok = 0 }
        }
        x = t.successor(x);
    }
    (count, ok, sum)
}

fn main() {
    let s0 = rs::snap();
    let r = main_tree(2000);
    rs::report(s0);
    println!("{:?}", r);
}
