#[path = "../counting.rs"] mod counting;
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

/// The product of two `n` by `n` matrices, row-major.
fn matmul(a: &[f64], b: &[f64], n: usize) -> Vec<f64> {
    let mut c = vec![0.0; n * n];
    for i in 0..n {
        for j in 0..n {
            c[i * n + j] = (0..n).map(|k| a[i * n + k] * b[k * n + j]).sum();
        }
    }
    c
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 10) as usize;
    let a: Vec<f64> = (0..n * n).map(|k| (k % 7) as f64).collect();
    let b: Vec<f64> = (0..n * n).map(|k| (k % 5) as f64 - 2.0).collect();
    let c = matmul(&a, &b, n);
    let s: f64 = c.iter().sum();
    println!("{}", s as i64);
}

fn main() { real_main(); counting::report(); }
