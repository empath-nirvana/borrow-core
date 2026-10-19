#[path = "../counting.rs"] mod counting;
// `Result` and `?` four levels deep inside loops, with a small error (an `i32`): the same
// computation as main.bc. The chunk's loop is `try_fold`.
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(k: i32) -> i32 {
    k.wrapping_mul(7919) % 100003
}

type Error = i32;

// Level 4: the key's value, or an error.
fn check(k: i32) -> Result<i64, Error> {
    let x = value(k);
    if x == 0 { Err(k) } else { Ok(x as i64) }
}

// Level 3.
fn scale(k: i32) -> Result<i64, Error> {
    Ok(check(k)?.wrapping_mul(3).wrapping_add(1))
}

// Level 2: one chunk's sum.
fn chunk_sum(c: i32, len: i32) -> Result<i64, Error> {
    (0..len).try_fold(0i64, |s, j| Ok(s.wrapping_add(scale(c.wrapping_mul(len).wrapping_add(j))?)))
}

fn tally(e: &Error) -> i64 {
    *e as i64
}

// Level 1: the sum of the chunks without an error, and the tally of the errors.
fn run_all(chunks: i32, len: i32) -> (i64, i64) {
    let mut sum = 0i64;
    let mut errs = 0i64;
    for c in 0..chunks {
        match chunk_sum(c, len) {
            Ok(s) => sum = sum.wrapping_add(s),
            Err(e) => errs = errs.wrapping_add(tally(&e)),
        }
    }
    (sum, errs)
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let chunks = arg(&args, 1, 10);
    let len = arg(&args, 2, 100);
    let (sum, errs) = run_all(chunks, len);
    println!("{sum} {errs}");
}

fn main() { real_main(); counting::report(); }
