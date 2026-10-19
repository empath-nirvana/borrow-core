#[path = "../counting.rs"] mod counting;
// T05: coin change and LCS with two rows swapped.
fn coins(cs: &[i32], amount: usize) -> i64 {
    let mut dp = vec![i64::MAX; amount + 1];
    dp[0] = 0;
    for a in 1..=amount {
        for &c in cs {
            let c = c as usize;
            if c <= a && dp[a - c] != i64::MAX { dp[a] = dp[a].min(dp[a - c] + 1); }
        }
    }
    if dp[amount] == i64::MAX { -1 } else { dp[amount] }
}
fn lcs(x: &[u8], y: &[u8]) -> i32 {
    let mut prev = vec![0; y.len() + 1];
    let mut cur = vec![0; y.len() + 1];
    for i in 1..=x.len() {
        for j in 1..=y.len() {
            cur[j] = if x[i - 1] == y[j - 1] { prev[j - 1] + 1 } else { prev[j].max(cur[j - 1]) };
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[y.len()]
}
fn main() {
    let c0 = counting::now();
    use std::hint::black_box as bb;
    let r1 = coins(&bb([1, 2, 5]), 11);
    let r2 = coins(&bb([2]), 3);
    let l1 = lcs(bb(b"abcde"), bb(b"ace"));
    let l2 = lcs(bb(b"AGGTAB"), bb(b"GXTXAYB"));
    let used = counting::now() - c0;
    println!("({r1}, ({r2}, ({l1}, {l2})))");
    eprintln!("body allocs {used}");
}
