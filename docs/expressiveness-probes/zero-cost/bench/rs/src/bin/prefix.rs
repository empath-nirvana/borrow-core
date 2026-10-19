#[path = "../counting.rs"] mod counting;
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(i: i32) -> i64 {
    (i.wrapping_mul(7919) % 1000) as i64
}

/// Each element replaced by the sum of the elements up to it, in place.
fn prefix(v: &mut [i64]) {
    let mut s: i64 = 0;
    for x in v.iter_mut() {
        s = s.wrapping_add(*x);
        *x = s;
    }
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let mut a: Vec<i64> = (0..n).map(value).collect();
    for _ in 0..reps {
        prefix(&mut a);
    }
    println!("{}", a[n as usize - 1]);
}

fn main() { real_main(); counting::report(); }
