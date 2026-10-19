// ds/unionfind.bc: parent and rank Vecs, two-pass path compression, union by rank, uf_add.
#[path = "../count.rs"] mod count;
struct UF { p: Vec<usize>, r: Vec<u32> }
impl UF {
    fn new(n: usize) -> Self { UF { p: (0..n).collect(), r: vec![0; n] } }
    fn add(&mut self) -> usize { let i = self.p.len(); self.p.push(i); self.r.push(0); i }
    fn find(&mut self, x: usize) -> usize {
        let mut root = x; while self.p[root] != root { root = self.p[root] }
        let mut y = x; while self.p[y] != root { let q = self.p[y]; self.p[y] = root; y = q }
        root
    }
    fn union(&mut self, x: usize, y: usize) -> bool {
        let (a, b) = (self.find(x), self.find(y));
        if a == b { return false }
        let (ra, rb) = (self.r[a], self.r[b]);
        if ra < rb { self.p[a] = b } else if rb < ra { self.p[b] = a } else { self.p[b] = a; self.r[a] += 1 }
        true
    }
}
fn main() {
    count::warm();
    let s0 = count::snap();
    let n = 1000;
    let mut u = UF::new(n);
    let mut comps = n;
    for i in 0..n { let j = (2 * i + 1) % n; if u.union(i, j) { comps -= 1 } }
    let extra = u.add();
    let r1 = u.find(extra); let r2 = u.find(0); let r3 = u.find(999);
    eprintln!("{} {} {} {}", comps, extra, r1, (r2 == r3) as i32);
    drop(u);
    count::report("unionfind", s0);
}
