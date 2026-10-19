#[path = "../counting.rs"] mod counting;
// The in-order walk of the balanced search tree over the keys 0..n as an Iterator with an
// explicit stack of pending ranges: the hand-written iterator a Rust programmer writes when a
// recursive generator is wanted.
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(k: i32, r: i32) -> i32 {
    k.wrapping_mul(7919).wrapping_add(r) % 1000
}

struct InOrder {
    // Ranges whose left part is done: (key to yield, right range's end).
    stack: Vec<(i32, i32)>,
    round: i32,
}

impl InOrder {
    fn new(lo: i32, hi: i32, round: i32) -> Self {
        let mut it = InOrder { stack: Vec::new(), round };
        it.descend(lo, hi);
        it
    }
    fn descend(&mut self, lo: i32, hi: i32) {
        let mut hi = hi;
        while lo < hi {
            let m = lo + (hi - lo) / 2;
            self.stack.push((m, hi));
            hi = m;
        }
    }
}

impl Iterator for InOrder {
    type Item = i32;
    fn next(&mut self) -> Option<i32> {
        let (m, hi) = self.stack.pop()?;
        self.descend(m + 1, hi);
        Some(value(m, self.round))
    }
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let mut acc: i64 = 0;
    for r in 0..reps {
        acc = acc.wrapping_add(InOrder::new(0, n, r).map(|x| x as i64).sum::<i64>());
    }
    println!("{acc}");
}

fn main() { real_main(); counting::report(); }
