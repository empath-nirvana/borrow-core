// corpus/operator-rounds.bc: synchronous level-triggered reconcile rounds against a fake API
// (a struct the reconciler borrows &mut) with an event tally.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
struct Api { cluster: Vec<(i32, i32)>, conflict: bool }
impl Api {
    fn observed(&self, name: i32) -> i32 { self.cluster.iter().find(|o| o.0 == name).map_or(0, |o| o.1) }
    fn update(&mut self, name: i32, r: i32) -> bool {
        if self.conflict && name == 2 { self.conflict = false; return false }
        match self.cluster.iter_mut().find(|o| o.0 == name) { Some(o) => o.1 = r, None => self.cluster.push((name, r)) }
        true
    }
}
#[derive(Debug, Default)] struct Tally { updates: i32, conflicts: i32 }
fn try_update(api: &mut Api, name: i32, r: i32) -> Result<(), i32> { if api.update(name, r) { Ok(()) } else { Err(409) } }
fn reconcile(api: &mut Api, ev: &mut Tally, (name, want): (i32, i32)) -> bool {
    let have = api.observed(name);
    if have == want { return true }
    match try_update(api, name, if have < want { have + 1 } else { have - 1 }) { Ok(()) => ev.updates += 1, Err(_) => ev.conflicts += 1 }
    false
}
fn main() {
    let a0 = snapshot();
    let mut api = Api { cluster: vec![(2, 4)], conflict: true };
    let mut ev = Tally::default();
    let spec = vec![(1, 3), (2, 0), (3, 2)];
    let mut rounds = 0;
    for round in 1..20 {
        let not_done = spec.iter().filter(|&&o| !reconcile(&mut api, &mut ev, o)).count();
        if not_done == 0 { rounds = round; break }
    }
    report("operator_rounds", a0);
    println!("{rounds} {:?} {ev:?}", api.cluster);
}
