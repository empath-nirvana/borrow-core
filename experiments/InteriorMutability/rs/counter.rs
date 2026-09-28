// Counting calls through an `Fn` interface: `apply_twice` takes `&dyn Fn`, so the callback
// cannot take `&mut` state, and the count lives in a `Cell` the closure captures. The same
// shape is `Counted<F>` wrapping a function behind `&self`. Prints (31, 4): 1, 3, 7, 15, 31
// through two `apply_twice`, and 4 calls.
use std::cell::Cell;

fn apply_twice(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    f(f(x))
}

struct Counted<F: Fn(i32) -> i32> {
    f: F,
    calls: Cell<u32>,
}

impl<F: Fn(i32) -> i32> Counted<F> {
    fn call(&self, x: i32) -> i32 {
        self.calls.set(self.calls.get() + 1);
        (self.f)(x)
    }
}

fn main() {
    let c = Counted { f: |x| x * 2 + 1, calls: Cell::new(0) };
    let g = |x| c.call(x);
    let y = apply_twice(&g, apply_twice(&g, 1));
    println!("({}, {})", y, c.calls.get());
}
