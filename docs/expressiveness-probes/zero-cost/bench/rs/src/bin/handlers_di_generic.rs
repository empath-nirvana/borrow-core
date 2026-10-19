#[path = "../counting.rs"] mod counting;
// Dependency injection through generic parameters: `work` is generic in the logger and the
// clock, one copy per logger, the copy chosen at run time by the third argument.
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

trait Logger {
    fn log(&mut self, x: i64);
    fn state(&self) -> i64;
}

trait Clock {
    fn now_ns(&mut self) -> i64;
}

// A logger that adds up its entries.
struct Summing(i64);
impl Logger for Summing {
    fn log(&mut self, x: i64) { self.0 = self.0.wrapping_add(x); }
    fn state(&self) -> i64 { self.0 }
}

// A logger that keeps a checksum of its entries, in order.
struct Hashing(i64);
impl Logger for Hashing {
    fn log(&mut self, x: i64) { self.0 = self.0.wrapping_mul(31).wrapping_add(x); }
    fn state(&self) -> i64 { self.0 }
}

// A clock that advances 3 ns at every reading.
struct FakeClock(i64);
impl Clock for FakeClock {
    fn now_ns(&mut self) -> i64 { self.0 += 3; self.0 }
}

fn value(k: i32) -> i64 {
    (k.wrapping_mul(7919) % 1000) as i64
}

fn work<L: Logger, C: Clock>(n: i32, log: &mut L, clock: &mut C) -> i64 {
    let mut acc = 0i64;
    for i in 0..n {
        let t = clock.now_ns();
        let v = value(i);
        if i & 7 == 0 {
            log.log(t + v);
        }
        acc = acc.wrapping_add(v);
    }
    acc
}

fn run<L: Logger>(n: i32, reps: i32, mut logger: L) -> (i64, i64, i64) {
    let mut clock = FakeClock(0);
    let mut acc = 0i64;
    for _ in 0..reps {
        acc = acc.wrapping_add(work(n, &mut logger, &mut clock));
    }
    (acc, logger.state(), clock.0)
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let mode = arg(&args, 3, 0);
    let (acc, l, c) = if mode == 0 { run(n, reps, Summing(0)) } else { run(n, reps, Hashing(0)) };
    println!("{acc} {l} {c}");
}

fn main() { real_main(); counting::report(); }
