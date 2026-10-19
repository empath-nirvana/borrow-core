// AWFY Towers, as awfy/towers.bc: 13 discs; piles are linked lists of disc nodes (AWFY's
// TowersDisk with `next`); a move unlinks the top node and links it onto another pile, checking
// the size order. Answer 8191.
rs::counting!();
struct Disk { size: i32, next: Option<Box<Disk>> }
struct T { piles: [Option<Box<Disk>>; 3], moves: i32 }
impl T {
    fn push(&mut self, mut d: Box<Disk>, p: usize) {
        if let Some(top) = &self.piles[p] { if d.size >= top.size { panic!("cannot put a big disk on a smaller one") } }
        d.next = self.piles[p].take();
        self.piles[p] = Some(d);
    }
    fn pop(&mut self, p: usize) -> Box<Disk> {
        let mut d = self.piles[p].take().expect("empty pile");
        self.piles[p] = d.next.take();
        d
    }
    fn move_top(&mut self, f: usize, t: usize) { let d = self.pop(f); self.push(d, t); self.moves += 1 }
    fn move_disks(&mut self, n: i32, f: usize, t: usize) {
        if n == 1 { self.move_top(f, t) } else {
            let o = 3 - f - t;
            self.move_disks(n - 1, f, o); self.move_top(f, t); self.move_disks(n - 1, o, t)
        }
    }
}
fn main() {
    let s0 = rs::snap();
    let mut t = T { piles: [None, None, None], moves: 0 };
    for k in 0..13 { t.push(Box::new(Disk { size: 13 - k, next: None }), 0) }
    t.move_disks(13, 0, 1);
    rs::report(s0);
    println!("{}", t.moves);
}
