#[path = "../counting.rs"] mod counting;
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

/// The number of primes below `n`: the sieve of Eratosthenes over a flag per number.
fn sieve(n: usize) -> usize {
    let mut a = vec![true; n];
    let mut i = 2;
    while i * i < n {
        if a[i] {
            for j in (i * i..n).step_by(i) {
                a[j] = false;
            }
        }
        i += 1;
    }
    a.iter().filter(|&&f| f).count() - 2
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000) as usize;
    let reps = arg(&args, 2, 1);
    let mut c = 0;
    for _ in 0..reps {
        c = sieve(n);
    }
    println!("{c}");
}

fn main() { real_main(); counting::report(); }
