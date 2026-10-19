#[path = "../counting.rs"] mod counting;
// T13: two teller tasks, each holding `&mut` to an account owned by `main`, reading its
// transactions across an await, run round robin by a minimal single-threaded executor (std
// only). A task is `Pin<Box<dyn Future>>`: one Box::pin per task, as a hand-rolled executor
// with a homogeneous queue needs.
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
struct YieldNow(bool);
impl Future for YieldNow {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; cx.waker().wake_by_ref(); Poll::Pending }
    }
}
async fn teller(a: &mut i32, txs: &[i32]) -> i32 {
    let mut r = 0;
    for &t in txs {
        if *a + t < 0 { r += 1 } else { *a += t }
        YieldNow(false).await;
    }
    r
}
fn main() {
    let c0 = counting::now();
    let (mut c1, mut c2) = (100, 50);
    let (tx1, tx2) = ([50, -20], [-30, -40]);
    let results = {
        let mut q: VecDeque<(usize, Pin<Box<dyn Future<Output = i32> + '_>>)> = VecDeque::with_capacity(2);
        q.push_back((0, Box::pin(teller(&mut c1, &tx1))));
        q.push_back((1, Box::pin(teller(&mut c2, &tx2))));
        let mut results = [0; 2];
        let mut cx = Context::from_waker(Waker::noop());
        while let Some((i, mut t)) = q.pop_front() {
            match t.as_mut().poll(&mut cx) { Poll::Ready(v) => results[i] = v, Poll::Pending => q.push_back((i, t)) }
        }
        results
    };
    let used = counting::now() - c0;
    println!("{results:?} {c1} {c2}");
    eprintln!("body allocs {used}");
}
