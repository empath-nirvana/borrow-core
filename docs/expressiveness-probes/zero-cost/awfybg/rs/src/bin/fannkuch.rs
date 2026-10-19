// fannkuch-redux, as bg/fannkuch.bc (n = 7 by default, first argument otherwise): every
// permutation by the Game's counting scheme, flips by prefix reversal; checksum and max flips.
rs::counting!();
fn main() {
    let s0 = rs::snap();
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    let s1 = rs::snap();
    let nperm: usize = (1..=n).product();
    let mut perm1: Vec<usize> = (0..n).collect();
    let mut count = vec![0usize; n];
    let mut perm = vec![0usize; n];
    let (mut r, mut maxflips, mut checksum) = (n, 0, 0i64);
    for pc in 0..nperm {
        while r != 1 { count[r - 1] = r; r -= 1 }
        perm.copy_from_slice(&perm1);
        let mut flips = 0;
        let mut k = perm[0];
        while k != 0 { perm[..=k].reverse(); flips += 1; k = perm[0] }
        maxflips = maxflips.max(flips);
        checksum += if pc % 2 == 0 { flips as i64 } else { -(flips as i64) };
        loop {
            if r == n { break }
            let p0 = perm1[0];
            for i in 0..r { perm1[i] = perm1[i + 1] }
            perm1[r] = p0;
            count[r] -= 1;
            if count[r] > 0 { break }
            r += 1;
        }
    }
    let e = rs::snap();
    eprintln!("args: {} allocs", (s1.0 - s0.0) + (s1.1 - s0.1));
    rs::report(s0);
    let _ = e;
    println!("{}\nPfannkuchen({}) = {}", checksum, n, maxflips);
}
