#[path = "../counting.rs"] mod counting;
// T12: (1) a closure writing a captured variable, (2) a closure passed down a recursion that
// accumulates, (3) a stored counter closure.
fn ap(mut f: impl FnMut(i32) -> i32) -> i32 { f(1) }
fn walk(lo: i32, hi: i32, f: &mut impl FnMut(i32)) {
    if lo < hi { let m = (lo + hi) / 2; walk(lo, m, f); f(m); walk(m + 1, hi, f); }
}
fn counter(start: i32, step: i32) -> impl FnMut() -> i32 { let mut n = start; move || { n += step; n } }
fn main() {
    let c0 = counting::now();
    let mut x = 1;
    let a = ap(|u| { x = 5; u + 1 });
    let mut sum = 0;
    let mut seen = Vec::with_capacity(8);
    walk(0, std::hint::black_box(6), &mut |k| { sum += k; seen.push(k); });
    let mut tick = counter(0, 3);
    let (t1, t2) = (tick(), tick());
    let used = counting::now() - c0;
    println!("{:?} ({}, ({}, ({}, {})))", seen, x * 10 + a, sum, t1 + t2, t2);
    eprintln!("body allocs {used}");
}
