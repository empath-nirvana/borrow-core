// corpus/async-bank-inbox.bc and first-pass/bank-split.bc: two teller tasks, each owning an
// account and holding &mut of it across its awaits; an overdraft is refused (Err) and counted.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
fn apply(b: i32, t: i32) -> Result<i32, i32> { if b + t < 0 { Err(t) } else { Ok(b + t) } }
async fn teller(start: i32, txns: &[i32]) -> (i32, i32) {
    let mut balance = start;
    let acct = &mut balance;            // a borrow held across the awaits
    let mut refused = 0;
    for &t in txns {
        match apply(*acct, t) { Ok(b) => *acct = b, Err(_) => refused += 1 }
        yield_now().await;
    }
    (balance, refused)
}
fn main() {
    let a0 = snapshot();
    let (t1, t2) = ([50, -20], [-30, -40]);
    let r = run(vec![Box::pin(teller(100, &t1)) as Task<(i32, i32)>, Box::pin(teller(50, &t2))]);
    report("bank", a0);
    println!("{r:?}");
}
