// Mandelbrot (the Benchmarks Game's): the points of an n×n grid over [-1.5, 0.5] × [-1, 1]
// that stay within |z| ≤ 2 for 50 iterations of z ← z² + c. Prints how many do.

fn inside(cr: f64, ci: f64) -> bool {
    let (mut zr, mut zi, mut tr, mut ti) = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
    for _ in 0..50 {
        if tr + ti > 4.0 {
            return false;
        }
        zi = 2.0 * zr * zi + ci;
        zr = tr - ti + cr;
        tr = zr * zr;
        ti = zi * zi;
    }
    tr + ti <= 4.0
}

fn main() {
    let n: i32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(200);
    let fnn = n as f64;
    let mut count = 0;
    for y in 0..n {
        let ci = 2.0 * y as f64 / fnn - 1.0;
        for x in 0..n {
            let cr = 2.0 * x as f64 / fnn - 1.5;
            if inside(cr, ci) {
                count += 1;
            }
        }
    }
    println!("{count}");
}
