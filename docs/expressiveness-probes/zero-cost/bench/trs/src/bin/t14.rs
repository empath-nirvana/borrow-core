#[path = "../counting.rs"] mod counting;
// T14: a random-number service and a logger passed as `&mut` services, and a buffer filled
// through `&mut` in a call that uses both.
struct Lcg(i32);
impl Lcg { fn next(&mut self) -> i32 { self.0 = self.0.wrapping_mul(1103515245).wrapping_add(12345); ((self.0 as u32) >> 16) as i32 % 100 } }
struct Logger { n: i32, t: i32 }
impl Logger { fn log(&mut self, x: i32) { self.n += 1; self.t += x; } }
fn fill(buf: &mut [i32], rng: &mut Lcg, log: &mut Logger) {
    for p in buf.iter_mut() { let x = rng.next(); *p = x; if x > 50 { log.log(x) } }
}
fn main() {
    let c0 = counting::now();
    let mut rng = Lcg(std::hint::black_box(42));
    let mut lg = Logger { n: 0, t: 0 };
    let mut b = [0; 6];
    fill(&mut b, &mut rng, &mut lg);
    let again = rng.next();
    let used = counting::now() - c0;
    println!("{b:?} ({again}, ({}, {}))", lg.n, lg.t);
    eprintln!("body allocs {used}");
}
