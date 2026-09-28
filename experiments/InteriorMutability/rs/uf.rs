// Union-find with path compression behind `&self`: the parent table is `Vec<Cell<usize>>`, so
// `find` and `same` compress while the structure is shared. Same unions and queries as
// `bc/uf-bounded.bc`. Prints (1, 3, 1, 0, 1, 2).
use std::cell::Cell;

struct UnionFind {
    parent: Vec<Cell<usize>>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind { parent: (0..n).map(Cell::new).collect() }
    }
    fn find(&self, x: usize) -> usize {
        let p = self.parent[x].get();
        if p == x {
            return x;
        }
        let r = self.find(p);
        self.parent[x].set(r);
        r
    }
    fn union(&self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        self.parent[ra].set(rb);
    }
    fn same(&self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }
    fn components(&self) -> usize {
        (0..self.parent.len()).filter(|&i| self.parent[i].get() == i).count()
    }
}

fn main() {
    let uf = UnionFind::new(8);
    for (a, b) in [(0, 1), (1, 2), (2, 3), (4, 5), (6, 7), (5, 7)] {
        uf.union(a, b);
    }
    let before = uf.parent[0].get();
    uf.find(0);
    let after = uf.parent[0].get();
    println!(
        "({}, {}, {}, {}, {}, {})",
        before,
        after,
        uf.same(0, 3) as u8,
        uf.same(0, 4) as u8,
        uf.same(4, 6) as u8,
        uf.components()
    );
}
