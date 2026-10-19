// AWFY Queens, as awfy/queens.bc: eight queens by backtracking, run 10 times.
rs::counting!();
struct Q { free_rows: Vec<bool>, free_maxs: Vec<bool>, free_mins: Vec<bool>, rows: Vec<i32> }
impl Q {
    fn new() -> Q { Q { free_rows: vec![true; 8], free_maxs: vec![true; 16], free_mins: vec![true; 16], rows: vec![-1; 8] } }
    fn get(&self, r: usize, c: usize) -> bool { self.free_rows[r] && self.free_maxs[c + r] && self.free_mins[c + 7 - r] }
    fn set(&mut self, r: usize, c: usize, v: bool) { self.free_rows[r] = v; self.free_maxs[c + r] = v; self.free_mins[c + 7 - r] = v }
    fn place(&mut self, c: usize) -> bool {
        for r in 0..8 {
            if self.get(r, c) {
                self.rows[r] = c as i32;
                self.set(r, c, false);
                if c == 7 { return true }
                if self.place(c + 1) { return true }
                self.set(r, c, true);
            }
        }
        false
    }
}
fn main() {
    let s0 = rs::snap();
    let (mut good, mut code) = (0, 0);
    for _ in 0..10 {
        let mut q = Q::new();
        if q.place(0) { good += 1 }
        let mut s = 0;
        for r in 0..8 { s = s * 8 + q.rows[7 - r] }
        code = s;
    }
    rs::report(s0);
    println!("{} {}", good, code);
}
