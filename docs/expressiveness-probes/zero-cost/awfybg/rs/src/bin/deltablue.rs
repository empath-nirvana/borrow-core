// AWFY DeltaBlue, index form, the same planner subset and run as awfy/deltablue.bc:
// chainTest(100): incrementalAdd/satisfy/chooseMethod/addPropagate/makePlan, plan executed 100x.
// Variables and constraints in Vecs, cross-links are usize indices; each variable's constraint
// list is a Vec<usize>. Answer (good, plan length) = (100, 101).
rs::counting!();

const NONE: u8 = 0;
const FORWARD: u8 = 1;
const BACKWARD: u8 = 2;
#[derive(Clone, Copy, PartialEq)]
enum Kind { Stay, Edit, Equal }

struct Var { value: i32, determined_by: Option<usize>, mark: i32, walk: i32, stay: bool, cons: Vec<usize> }
struct Con { kind: Kind, strength: i32, v1: usize, v2: usize, dir: u8 }

struct P { vars: Vec<Var>, cons: Vec<Con>, mark: i32 }

impl P {
    fn new_mark(&mut self) -> i32 { self.mark += 1; self.mark }
    fn output(&self, c: usize) -> usize {
        let k = &self.cons[c];
        if k.kind == Kind::Equal && k.dir == FORWARD { k.v2 } else { k.v1 }
    }
    fn input(&self, c: usize) -> usize { let k = &self.cons[c]; if k.dir == FORWARD { k.v1 } else { k.v2 } }
    fn choose_method(&mut self, c: usize, mark: i32) {
        let k = &self.cons[c];
        let (st, v1, v2) = (k.strength, k.v1, k.v2);
        let d = if k.kind != Kind::Equal {
            let a = &self.vars[v1];
            if a.mark != mark && st < a.walk { FORWARD } else { NONE }
        } else {
            let (a, b) = (&self.vars[v1], &self.vars[v2]);
            if a.walk > b.walk { if st < a.walk { BACKWARD } else { NONE } }
            else if st < b.walk { FORWARD } else { BACKWARD }
        };
        self.cons[c].dir = d;
    }
    fn add_consuming(&self, v: usize, todo: &mut Vec<usize>) {
        let det = self.vars[v].determined_by;
        for &c in &self.vars[v].cons {
            if Some(c) != det && self.cons[c].dir != NONE { todo.push(c); }
        }
    }
    fn recalculate(&mut self, c: usize) {
        let (kind, st) = (self.cons[c].kind, self.cons[c].strength);
        let out = self.output(c);
        if kind != Kind::Equal {
            self.vars[out].walk = st;
            self.vars[out].stay = kind == Kind::Stay;
        } else {
            let i = self.input(c);
            let (iw, istay, ival) = (self.vars[i].walk, self.vars[i].stay, self.vars[i].value);
            let o = &mut self.vars[out];
            o.walk = st.max(iw);
            o.stay = istay;
            if istay { o.value = ival; }
        }
    }
    fn add_propagate(&mut self, c: usize, mark: i32) -> bool {
        let mut todo = vec![c];
        let mut head = 0;
        while head < todo.len() {
            let d = todo[head];
            head += 1;
            let out = self.output(d);
            if self.vars[out].mark == mark { return false; }
            self.recalculate(d);
            self.add_consuming(out, &mut todo);
        }
        true
    }
    fn satisfy(&mut self, c: usize, mark: i32) -> Option<usize> {
        self.choose_method(c, mark);
        if self.cons[c].dir == NONE { return None; }
        if self.cons[c].kind == Kind::Equal { let i = self.input(c); self.vars[i].mark = mark; }
        let out = self.output(c);
        let ov = self.vars[out].determined_by;
        if let Some(o) = ov { self.cons[o].dir = NONE; }
        self.vars[out].determined_by = Some(c);
        self.add_propagate(c, mark);
        self.vars[out].mark = mark;
        ov
    }
    fn incremental_add(&mut self, c: usize) {
        let mark = self.new_mark();
        let mut ov = self.satisfy(c, mark);
        while let Some(o) = ov { ov = self.satisfy(o, mark); }
    }
    fn constraint(&mut self, kind: Kind, st: i32, v1: usize, v2: usize) -> usize {
        let c = self.cons.len();
        self.cons.push(Con { kind, strength: st, v1, v2, dir: NONE });
        self.vars[v1].cons.push(c);
        if kind == Kind::Equal { self.vars[v2].cons.push(c); }
        self.incremental_add(c);
        c
    }
    fn inputs_known(&self, c: usize, mark: i32) -> bool {
        if self.cons[c].kind != Kind::Equal { return true; }
        let i = &self.vars[self.input(c)];
        i.mark == mark || i.stay || i.determined_by.is_none()
    }
    fn make_plan(&mut self, mut todo: Vec<usize>) -> Vec<usize> {
        let mark = self.new_mark();
        let mut plan = Vec::new();
        let mut head = 0;
        while head < todo.len() {
            let c = todo[head];
            head += 1;
            let out = self.output(c);
            if self.vars[out].mark != mark && self.inputs_known(c, mark) {
                plan.push(c);
                self.vars[out].mark = mark;
                self.add_consuming(out, &mut todo);
            }
        }
        plan
    }
    fn execute(&mut self, plan: &[usize]) {
        for &c in plan {
            if self.cons[c].kind == Kind::Equal {
                let (i, o) = (self.input(c), self.output(c));
                self.vars[o].value = self.vars[i].value;
            }
        }
    }
}

fn chain_test(n: usize) -> (i32, usize) {
    let mut p = P { vars: Vec::with_capacity(n + 1), cons: Vec::with_capacity(n + 2), mark: 0 };
    for _ in 0..n + 1 {
        p.vars.push(Var { value: 0, determined_by: None, mark: 0, walk: 6, stay: false, cons: Vec::new() });
    }
    for i in 0..n { p.constraint(Kind::Equal, 0, i, i + 1); }
    p.constraint(Kind::Stay, 3, n, 0);
    let edit = p.constraint(Kind::Edit, 2, 0, 0);
    let src = if p.cons[edit].dir != NONE { vec![edit] } else { Vec::new() };
    let plan = p.make_plan(src);
    let mut good = 0;
    for i in 0..100 {
        p.vars[0].value = i;
        p.execute(&plan);
        if p.vars[n].value == i { good += 1; }
    }
    (good, plan.len())
}

fn main() {
    let s0 = rs::snap();
    let (g, l) = chain_test(100);
    rs::report(s0);
    println!("{} {}", g, l);
}
