// Spectral norm (the Benchmarks Game's): ten rounds of the power method on the infinite matrix
// A(i, j) = 1 / ((i + j)(i + j + 1) / 2 + i + 1), cut to n×n. Prints the norm times 10⁹,
// truncated, so that every side prints the same digits.

fn a(i: usize, j: usize) -> f64 {
    let ij = i + j;
    1.0 / (ij * (ij + 1) / 2 + i + 1) as f64
}

fn mul_av(u: &[f64], out: &mut [f64]) {
    for (i, o) in out.iter_mut().enumerate() {
        *o = u.iter().enumerate().map(|(j, &x)| a(i, j) * x).sum();
    }
}

fn mul_atv(u: &[f64], out: &mut [f64]) {
    for (i, o) in out.iter_mut().enumerate() {
        *o = u.iter().enumerate().map(|(j, &x)| a(j, i) * x).sum();
    }
}

fn mul_atav(u: &[f64], out: &mut [f64], tmp: &mut [f64]) {
    mul_av(u, tmp);
    mul_atv(tmp, out);
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut u = vec![1.0; n];
    let mut v = vec![0.0; n];
    let mut tmp = vec![0.0; n];
    for _ in 0..10 {
        mul_atav(&u, &mut v, &mut tmp);
        mul_atav(&v, &mut u, &mut tmp);
    }
    let vbv: f64 = u.iter().zip(&v).map(|(x, y)| x * y).sum();
    let vv: f64 = v.iter().map(|x| x * x).sum();
    let r = (vbv / vv).sqrt();
    println!("{}", (r * 1e9) as i64);
}
