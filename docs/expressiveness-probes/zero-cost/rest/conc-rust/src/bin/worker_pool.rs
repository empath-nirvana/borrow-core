// conc/worker-pool.bc and conc/worker-pool-port.bc: two workers take jobs from one shared queue
// and send results to one shared results channel; five jobs. The shared state is a RefCell
// borrowed by both futures (no Rc needed: the executor runs inside the owner's scope).
use conc_rust::*;
use std::cell::RefCell;
use std::collections::VecDeque;
#[global_allocator] static A: Counting = Counting;
struct Chan { jobs: VecDeque<i32>, results: Vec<i32>, acc: i32 }
async fn worker(ch: &RefCell<Chan>, id: i32) -> i32 {
    let mut done = 0;
    loop {
        let j = ch.borrow_mut().jobs.pop_front();
        match j {
            Some(j) => { let mut c = ch.borrow_mut(); c.acc += j * j; c.results.push(j * 10 + id); drop(c); done += 1; yield_now().await }
            None => break,
        }
    }
    done
}
fn main() {
    let a0 = snapshot();
    let ch = RefCell::new(Chan { jobs: (1..=5).collect(), results: Vec::with_capacity(5), acc: 0 });
    let counts = run(vec![Box::pin(worker(&ch, 1)) as Task<i32>, Box::pin(worker(&ch, 2))]);
    let c = ch.into_inner();
    report("worker_pool", a0);
    println!("{counts:?} {} {:?}", c.acc, c.results);
}
