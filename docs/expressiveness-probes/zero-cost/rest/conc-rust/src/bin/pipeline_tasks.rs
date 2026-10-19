// conc/pipeline-tasks.bc: stage1 -> c1 -> stage2 -> c2 -> stage3, three tasks over two channels.
use conc_rust::*;
use std::cell::RefCell;
use std::collections::VecDeque;
#[global_allocator] static A: Counting = Counting;
async fn stage1(c1: &RefCell<VecDeque<i32>>, n: i32) -> i32 { for i in 0..n { c1.borrow_mut().push_back(i); yield_now().await } n }
async fn stage2(c1: &RefCell<VecDeque<i32>>, c2: &RefCell<VecDeque<i32>>, n: i32) -> i32 {
    let mut got = 0;
    while got < n { if let Some(x) = c1.borrow_mut().pop_front() { c2.borrow_mut().push_back(x * x); got += 1 } yield_now().await }
    got
}
async fn stage3(c2: &RefCell<VecDeque<i32>>, n: i32) -> i32 {
    let (mut got, mut s) = (0, 0);
    while got < n { if let Some(x) = c2.borrow_mut().pop_front() { s += x; got += 1 } yield_now().await }
    s
}
fn main() {
    let a0 = snapshot();
    let c1 = RefCell::new(VecDeque::with_capacity(4));
    let c2 = RefCell::new(VecDeque::with_capacity(4));
    let r = run(vec![Box::pin(stage1(&c1, 4)) as Task<i32>, Box::pin(stage2(&c1, &c2, 4)), Box::pin(stage3(&c2, 4))]);
    report("pipeline_tasks", a0);
    println!("{r:?}");
}
