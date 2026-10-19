// first-pass/op-b.bc: reconcile tasks against a fake API (a RefCell borrowed by every task);
// the first update of deployment 2 is a conflict, retried next round. Ours runs one task
// (reconcile(1, 3)); with three it is refused (B1). Both are run here.
use conc_rust::*;
use std::cell::RefCell;
#[global_allocator] static A: Counting = Counting;
struct Api { cluster: Vec<(i32, i32)>, conflict: bool }
impl Api {
    fn observed(&self, name: i32) -> i32 { self.cluster.iter().find(|o| o.0 == name).map_or(0, |o| o.1) }
    fn update(&mut self, name: i32, r: i32) -> Result<(), i32> {
        if self.conflict && name == 2 { self.conflict = false; return Err(409) }
        match self.cluster.iter_mut().find(|o| o.0 == name) { Some(o) => o.1 = r, None => self.cluster.push((name, r)) }
        Ok(())
    }
}
fn toward(have: i32, want: i32) -> i32 { if have < want { have + 1 } else { have - 1 } }
async fn reconcile(api: &RefCell<Api>, name: i32, want: i32) -> i32 {
    let mut updates = 0;
    for _ in 0..10 {
        let have = api.borrow().observed(name);
        if have == want { break }
        if api.borrow_mut().update(name, toward(have, want)).is_ok() { updates += 1 }
        yield_now().await
    }
    updates
}
fn main() {
    for three in [false, true] {
        let a0 = snapshot();
        let api = RefCell::new(Api { cluster: vec![(2, 4)], conflict: true });
        let mut ts: Vec<Task<i32>> = vec![Box::pin(reconcile(&api, 1, 3))];
        if three { ts.push(Box::pin(reconcile(&api, 2, 0))); ts.push(Box::pin(reconcile(&api, 3, 2))) }
        let counts = run(ts);
        report(if three { "op_b (3 tasks)" } else { "op_b (1 task)" }, a0);
        println!("{counts:?} {:?}", api.borrow().cluster);
    }
}
