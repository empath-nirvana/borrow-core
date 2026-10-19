// corpus/retry-block.bc (fake clock recording the waits) and ns/retry-backoff2.bc (the platform
// clock): retry a raising block with exponential backoff, the block a generic closure.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
fn retry<A>(times: i32, base: i32, sleep: &mut impl FnMut(i32), mut f: impl FnMut(i32) -> Result<A, i32>) -> Result<A, i32> {
    let (mut pause, mut last) = (base, 0);
    for attempt in 0..times {
        match f(attempt) { Ok(a) => return Ok(a), Err(e) => { last = e; if attempt + 1 < times { sleep(pause); pause *= 2 } } }
    }
    Err(last)
}
fn call(attempt: i32) -> Result<i32, i32> { if attempt < 2 { Err(503) } else { Ok(200) } }
fn with_budget(times: i32) -> (Result<i32, i32>, i32) {
    let mut waited = 0;
    let r = retry(times, 10, &mut |ms| waited += ms, call);
    (r, waited)
}
fn main() {
    let a0 = snapshot();
    report("retry_block (fake clock)", a0);
    println!("{:?} {:?}", with_budget(5), with_budget(2));
    let a0 = snapshot();
    let t0 = std::time::Instant::now();
    let r = retry(5, 10, &mut |ms| std::thread::sleep(std::time::Duration::from_millis(ms as u64)), call);
    report("retry_backoff2 (platform clock)", a0);
    println!("{r:?} {}", t0.elapsed().as_millis() >= 30);
}
