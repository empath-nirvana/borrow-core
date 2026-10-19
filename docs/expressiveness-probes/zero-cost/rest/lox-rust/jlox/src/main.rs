// jlox-shaped tree-walker running tree-arena.bc's Lox program: a boxed AST, environments as
// Rc<RefCell<Environment>> with a HashMap per scope and a parent link, closures holding their
// environment, instances as Rc<RefCell<Instance>>, bound methods binding `this` in a fresh
// environment. Names are interned to u32 as in the probe (i=0 count=1 c1=2 c2=3 c3=4
// makeCounter=5 this=6 n=7 o=8 m=9 inc=10).
#[path = "../../common/counting.rs"]
mod counting;
#[global_allocator]
static A: counting::Counting = counting::Counting;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::fmt::Write;

enum Expr {
    Num(i32), Var(u32), Assign(u32, Box<Expr>), Decl(u32, Box<Expr>), Add(Box<Expr>, Box<Expr>),
    Seq(Box<Expr>, Box<Expr>), Print(Box<Expr>), Fun(usize), Call(Box<Expr>), New(usize),
    Get(Box<Expr>, u32), SetF(Box<Expr>, u32, Box<Expr>),
}
use Expr::*;
fn b(e: Expr) -> Box<Expr> { Box::new(e) }

#[derive(Clone)]
enum Val { Num(i32), Closure(usize, Rc<RefCell<Env>>), Instance(Rc<RefCell<Instance>>), Nil }
struct Env { vars: HashMap<u32, Val>, parent: Option<Rc<RefCell<Env>>> }
struct Instance { class: usize, fields: HashMap<u32, Val> }

struct Interp { funs: Vec<Expr>, methods: Vec<HashMap<u32, usize>>, globals: Rc<RefCell<Env>>, out: String }

fn new_env(parent: Option<Rc<RefCell<Env>>>) -> Rc<RefCell<Env>> { Rc::new(RefCell::new(Env { vars: HashMap::new(), parent })) }

impl Interp {
    fn get(&self, env: &Rc<RefCell<Env>>, n: u32) -> Val {
        let mut e = env.clone();
        loop {
            let next = { let r = e.borrow(); if let Some(v) = r.vars.get(&n) { return v.clone() } r.parent.clone() };
            match next { Some(p) => e = p, None => return Val::Nil }
        }
    }
    fn assign(&self, env: &Rc<RefCell<Env>>, n: u32, v: Val) {
        let mut e = env.clone();
        loop {
            let next = { let mut r = e.borrow_mut(); if let Some(s) = r.vars.get_mut(&n) { *s = v; return } r.parent.clone() };
            match next { Some(p) => e = p, None => return }
        }
    }
    fn eval(&mut self, e: &Expr, env: &Rc<RefCell<Env>>) -> Val {
        match e {
            Num(n) => Val::Num(*n),
            Var(n) => self.get(env, *n),
            Assign(n, x) => { let v = self.eval(x, env); self.assign(env, *n, v.clone()); v }
            Decl(n, x) => { let v = self.eval(x, env); env.borrow_mut().vars.insert(*n, v); Val::Nil }
            Add(a, c) => match (self.eval(a, env), self.eval(c, env)) { (Val::Num(i), Val::Num(j)) => Val::Num(i + j), _ => Val::Nil },
            Seq(a, c) => { self.eval(a, env); self.eval(c, env) }
            Print(a) => { match self.eval(a, env) { Val::Num(i) => { let _ = write!(self.out, "{} ", i); } _ => self.out.push('?') }; Val::Nil }
            Fun(f) => Val::Closure(*f, env.clone()),
            Call(a) => match self.eval(a, env) {
                Val::Closure(f, cenv) => {
                    let ne = new_env(Some(cenv));
                    // The body is shared, not copied: a raw pointer into the immutable table.
                    let body: *const Expr = &self.funs[f];
                    self.eval(unsafe { &*body }, &ne)
                }
                _ => Val::Nil,
            },
            New(c) => Val::Instance(Rc::new(RefCell::new(Instance { class: *c, fields: HashMap::new() }))),
            Get(a, n) => match self.eval(a, env) {
                Val::Instance(i) => {
                    if let Some(v) = i.borrow().fields.get(n) { return v.clone() }
                    let c = i.borrow().class;
                    match self.methods[c].get(n) {
                        Some(&fid) => { let ne = new_env(Some(self.globals.clone())); ne.borrow_mut().vars.insert(6, Val::Instance(i)); Val::Closure(fid, ne) }
                        None => Val::Nil,
                    }
                }
                _ => Val::Nil,
            },
            SetF(a, n, x) => { let o = self.eval(a, env); let v = self.eval(x, env);
                match o { Val::Instance(i) => { i.borrow_mut().fields.insert(*n, v.clone()); v } _ => Val::Nil } }
        }
    }
}

fn main() {
    let s0 = counting::snap();
    let fun0 = Seq(b(Decl(0, b(Num(0)))), b(Seq(b(Decl(1, b(Fun(1)))), b(Var(1)))));
    let fun1 = Seq(b(Assign(0, b(Add(b(Var(0)), b(Num(1)))))), b(Print(b(Var(0)))));
    let fun2 = Seq(b(SetF(b(Var(6)), 7, b(Add(b(Get(b(Var(6)), 7)), b(Num(1)))))), b(Print(b(Get(b(Var(6)), 7)))));
    let sq = |a: Expr, c: Expr| Seq(b(a), b(c));
    let program = sq(Decl(5, b(Fun(0))), sq(Decl(2, b(Call(b(Var(5))))), sq(Decl(3, b(Var(2))),
        sq(Call(b(Var(2))), sq(Call(b(Var(3))), sq(Decl(4, b(Call(b(Var(5))))),
        sq(Call(b(Var(4))), Call(b(Var(2))))))))));
    let program2 = sq(Decl(8, b(New(0))), sq(SetF(b(Var(8)), 7, b(Num(10))), sq(Decl(9, b(Get(b(Var(8)), 10))),
        sq(Call(b(Var(9))), Call(b(Get(b(Var(8)), 10)))))));
    let mut funs = Vec::with_capacity(3); funs.push(fun0); funs.push(fun1); funs.push(fun2);
    let mut m = HashMap::new(); m.insert(10u32, 2usize);
    let s1 = counting::snap();
    let globals = new_env(None);
    let mut it = Interp { funs, methods: vec![m], globals: globals.clone(), out: String::with_capacity(64) };
    let s2 = counting::snap();
    it.eval(&program, &globals);
    it.eval(&program2, &globals);
    let s3 = counting::snap();
    println!("{}", it.out);
    eprintln!("ast+tables allocs {} reallocs {} | interp setup allocs {} | run allocs {} reallocs {} | total allocs {} reallocs {}",
        s1.0 - s0.0, s1.1 - s0.1, s2.0 - s1.0, s3.0 - s2.0, s3.1 - s2.1, s3.0 - s0.0, s3.1 - s0.1);
}
