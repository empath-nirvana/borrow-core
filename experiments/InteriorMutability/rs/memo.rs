// A cache behind `&self`: `Fib::get` memoizes in a `RefCell<HashMap>` and counts misses in a
// `Cell`, so a shared `&Fib` can be queried from anywhere. Prints (6765, 832040, 31):
// fib 20, fib 30, and 31 misses (0..=20 on the first call, 21..=30 on the second).
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

struct Fib {
    memo: RefCell<HashMap<u32, u32>>,
    misses: Cell<u32>,
}

impl Fib {
    fn get(&self, n: u32) -> u32 {
        if let Some(&v) = self.memo.borrow().get(&n) {
            return v;
        }
        self.misses.set(self.misses.get() + 1);
        let v = if n < 2 { n } else { self.get(n - 1) + self.get(n - 2) };
        self.memo.borrow_mut().insert(n, v);
        v
    }
}

fn report(f: &Fib) -> (u32, u32) {
    (f.get(20), f.get(30))
}

fn main() {
    let f = Fib { memo: RefCell::new(HashMap::new()), misses: Cell::new(0) };
    let (a, b) = report(&f);
    println!("({}, {}, {})", a, b, f.misses.get());
}
