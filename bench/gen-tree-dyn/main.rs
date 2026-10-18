// The in-order walk as a recursive iterator: each level a `Box<dyn Iterator>` chaining the
// left subtree's walk, the key, and the right subtree's walk.
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(k: i32, r: i32) -> i32 {
    k.wrapping_mul(7919).wrapping_add(r) % 1000
}

fn walk(lo: i32, hi: i32, r: i32) -> Box<dyn Iterator<Item = i32>> {
    if lo < hi {
        let m = lo + (hi - lo) / 2;
        Box::new(walk(lo, m, r).chain(std::iter::once(value(m, r))).chain(walk(m + 1, hi, r)))
    } else {
        Box::new(std::iter::empty())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let mut acc: i64 = 0;
    for r in 0..reps {
        acc = acc.wrapping_add(walk(0, n, r).map(|x| x as i64).sum::<i64>());
    }
    println!("{acc}");
}
