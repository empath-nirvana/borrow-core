#[path = "../counting.rs"] mod counting;
// T08: a memo table (map plus hit count) consulted by the Collatz chain recursion.
use std::collections::HashMap;
struct Memo { m: HashMap<i64, i32>, hits: i32 }
fn collatz(n: i64) -> i64 { if n % 2 == 0 { n / 2 } else { 3 * n + 1 } }
fn chain(n: i64, memo: &mut Memo) -> i32 {
    if n == 1 { return 1; }
    if let Some(&l) = memo.m.get(&n) { memo.hits += 1; return l; }
    let l = 1 + chain(collatz(n), memo);
    memo.m.insert(n, l);
    l
}
fn main() {
    let c0 = counting::now();
    let mut memo = Memo { m: HashMap::with_capacity(64), hits: 0 };
    let mut best = (0, 0);
    for n in 1..std::hint::black_box(30) {
        let l = chain(n, &mut memo);
        if l > best.1 { best = (n, l); }
    }
    let used = counting::now() - c0;
    println!("{best:?} {} {}", memo.hits, memo.m.len());
    eprintln!("body allocs {used}");
}
