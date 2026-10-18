// The in-order walk as internal iteration: a recursive function calling a closure at each key.
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(k: i32, r: i32) -> i32 {
    k.wrapping_mul(7919).wrapping_add(r) % 1000
}

fn walk(lo: i32, hi: i32, r: i32, f: &mut impl FnMut(i32)) {
    if lo < hi {
        let m = lo + (hi - lo) / 2;
        walk(lo, m, r, f);
        f(value(m, r));
        walk(m + 1, hi, r, f);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let mut acc: i64 = 0;
    for r in 0..reps {
        let mut s: i64 = 0;
        walk(0, n, r, &mut |x| s += x as i64);
        acc = acc.wrapping_add(s);
    }
    println!("{acc}");
}
