// clox-shaped VM running clox-vm.bc's bytecode (the same opcodes, operands and one shared chunk
// with function start offsets). Two upvalue representations, selected by argv[1]:
//   rc  : clox's object form in Rust: Rc<Closure> values, upvalues Rc<RefCell<Upvalue>> that are
//         Open(stack slot) until their frame returns, an open-upvalue list for sharing.
//   idx : the index form (closures, upvalue objects and capture lists in Vecs), as the probe.
#[path = "../../common/counting.rs"]
mod counting;
#[global_allocator]
static A: counting::Counting = counting::Counting;

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Write;
use std::rc::Rc;

const SCRIPT: &[u8] = &[11,1,0,3,0,1,0,12,0,3,1, 1,1,3,2,1,1,12,0,10,1,2,12,0,10, 1,4,12,0,10,
    1,0,12,0,3,3,1,3,12,0,10, 1,1,12,0,10,1,4,12,0,10,15];
const MAKE_COUNTER: &[u8] = &[0,0,11,2,1,1,1,11,3,1,1,1,3,4,4,2,13];
const COUNT: &[u8] = &[6,0,0,1,8,7,0,10,6,0,9,0,2,13];
const PEEK: &[u8] = &[6,0,9,0,2,13];

fn chunk() -> (Vec<u8>, Vec<usize>) {
    let mut c = Vec::with_capacity(128);
    let mut fs = Vec::with_capacity(4);
    for f in [SCRIPT, MAKE_COUNTER, COUNT, PEEK] { fs.push(c.len()); c.extend_from_slice(f); }
    (c, fs)
}

mod rc {
    use super::*;
    pub enum Upvalue { Open(usize), Closed(Val) }
    pub struct Closure { pub f: usize, pub up: Vec<Rc<RefCell<Upvalue>>> }
    #[derive(Clone)]
    pub enum Val { Num(i32), Closure(Rc<Closure>), Nil }
    fn num(v: &Val) -> i32 { if let Val::Num(n) = v { *n } else { 0 } }

    pub fn run(out: &mut String) -> usize {
        let (code, fstart) = chunk();
        let consts = vec![Val::Num(0), Val::Num(1), Val::Nil];
        let mut stack: Vec<Val> = Vec::with_capacity(64);
        let mut frames: Vec<(Rc<Closure>, usize, usize)> = Vec::with_capacity(16);
        let mut globals: HashMap<u8, Val> = HashMap::new();
        let mut open: Vec<Rc<RefCell<Upvalue>>> = Vec::new();
        let mut cur = Rc::new(Closure { f: 0, up: Vec::new() });
        stack.push(Val::Closure(cur.clone()));
        let (mut ip, mut base, mut steps) = (0usize, 0usize, 0usize);
        loop {
            steps += 1;
            let op = code[ip];
            let arg = *code.get(ip + 1).unwrap_or(&0);
            match op {
                0 => { stack.push(consts[arg as usize].clone()); ip += 2 }
                1 => { stack.push(globals.get(&arg).cloned().unwrap_or(Val::Nil)); ip += 2 }
                3 => { let v = stack.pop().unwrap(); globals.insert(arg, v); ip += 2 }
                4 => { stack.push(stack[base + arg as usize].clone()); ip += 2 }
                6 => { let v = match &*cur.up[arg as usize].borrow() { Upvalue::Open(s) => stack[*s].clone(), Upvalue::Closed(v) => v.clone() }; stack.push(v); ip += 2 }
                7 => { let v = stack.last().unwrap().clone();
                       let mut u = cur.up[arg as usize].borrow_mut();
                       match &mut *u { Upvalue::Open(s) => stack[*s] = v, Upvalue::Closed(c) => *c = v }; ip += 2 }
                8 => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(Val::Num(num(&a) + num(&b))); ip += 1 }
                9 => { let v = stack.pop().unwrap(); let _ = write!(out, "{} ", num(&v)); ip += 1 }
                10 => { stack.pop(); ip += 1 }
                11 => {
                    let n = code[ip + 2] as usize;
                    let mut up = Vec::with_capacity(n);
                    for j in 0..n {
                        let (is_local, idx) = (code[ip + 3 + 2 * j], code[ip + 4 + 2 * j] as usize);
                        if is_local == 1 {
                            let slot = base + idx;
                            let found = open.iter().find(|u| matches!(&*u.borrow(), Upvalue::Open(s) if *s == slot)).cloned();
                            up.push(found.unwrap_or_else(|| { let u = Rc::new(RefCell::new(Upvalue::Open(slot))); open.push(u.clone()); u }));
                        } else { up.push(cur.up[idx].clone()) }
                    }
                    stack.push(Val::Closure(Rc::new(Closure { f: arg as usize, up })));
                    ip += 3 + 2 * n
                }
                12 => {
                    let callee = match &stack[stack.len() - 1 - arg as usize] { Val::Closure(c) => c.clone(), _ => break };
                    let start = fstart[callee.f];
                    let prev = std::mem::replace(&mut cur, callee);
                    frames.push((prev, ip + 2, base));
                    base = stack.len() - 1 - arg as usize; ip = start
                }
                13 => {
                    let result = stack.pop().unwrap();
                    open.retain(|u| { let mut b = u.borrow_mut();
                        if let Upvalue::Open(s) = *b { if s >= base { *b = Upvalue::Closed(stack[s].clone()); return false } } true });
                    stack.truncate(base); stack.push(result);
                    match frames.pop() { Some((c, rip, rb)) => { cur = c; ip = rip; base = rb } None => break }
                }
                _ => break,
            }
        }
        steps
    }
}

mod idx {
    use super::*;
    #[derive(Clone, Copy)]
    pub enum Val { Num(i32), Closure(usize), Nil }
    fn num(v: Val) -> i32 { if let Val::Num(n) = v { n } else { 0 } }

    pub fn run(out: &mut String) -> usize {
        let (code, fstart) = chunk();
        let consts = vec![Val::Num(0), Val::Num(1), Val::Nil];
        let mut stack: Vec<Val> = Vec::with_capacity(64);
        let mut frames: Vec<(usize, usize, usize)> = Vec::with_capacity(16);
        let mut globals: HashMap<u8, Val> = HashMap::with_capacity(8);
        let mut upv: Vec<(isize, Val)> = Vec::with_capacity(8);
        let mut clo: Vec<(usize, usize, usize)> = Vec::with_capacity(8);
        let mut cupv: Vec<usize> = Vec::with_capacity(8);
        clo.push((0, 0, 0)); stack.push(Val::Closure(0));
        let (mut ip, mut base, mut cur, mut steps) = (0usize, 0usize, 0usize, 0usize);
        loop {
            steps += 1;
            let op = code[ip];
            let arg = *code.get(ip + 1).unwrap_or(&0);
            match op {
                0 => { stack.push(consts[arg as usize]); ip += 2 }
                1 => { stack.push(globals.get(&arg).copied().unwrap_or(Val::Nil)); ip += 2 }
                3 => { let v = stack.pop().unwrap(); globals.insert(arg, v); ip += 2 }
                4 => { stack.push(stack[base + arg as usize]); ip += 2 }
                6 | 7 => {
                    let ui = cupv[clo[cur].1 + arg as usize];
                    let (slot, cv) = upv[ui];
                    if op == 6 { stack.push(if slot >= 0 { stack[slot as usize] } else { cv }) }
                    else { let v = *stack.last().unwrap(); if slot >= 0 { stack[slot as usize] = v } else { upv[ui].1 = v } }
                    ip += 2
                }
                8 => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(Val::Num(num(a) + num(b))); ip += 1 }
                9 => { let v = stack.pop().unwrap(); let _ = write!(out, "{} ", num(v)); ip += 1 }
                10 => { stack.pop(); ip += 1 }
                11 => {
                    let n = code[ip + 2] as usize;
                    let first = cupv.len(); let id = clo.len(); clo.push((arg as usize, first, n));
                    for j in 0..n {
                        let (is_local, ix) = (code[ip + 3 + 2 * j], code[ip + 4 + 2 * j] as usize);
                        if is_local == 1 {
                            let slot = (base + ix) as isize;
                            match upv.iter().position(|u| u.0 == slot) {
                                Some(k) => cupv.push(k),
                                None => { cupv.push(upv.len()); upv.push((slot, Val::Nil)) }
                            }
                        } else { let p = cupv[clo[cur].1 + ix]; cupv.push(p) }
                    }
                    stack.push(Val::Closure(id));
                    ip += 3 + 2 * n
                }
                12 => {
                    let id = match stack[stack.len() - 1 - arg as usize] { Val::Closure(c) => c, _ => break };
                    frames.push((cur, ip + 2, base));
                    cur = id; base = stack.len() - 1 - arg as usize; ip = fstart[clo[id].0]
                }
                13 => {
                    let result = stack.pop().unwrap();
                    for u in upv.iter_mut() { if u.0 >= base as isize { *u = (-1, stack[u.0 as usize]) } }
                    stack.truncate(base); stack.push(result);
                    match frames.pop() { Some((c, rip, rb)) => { cur = c; ip = rip; base = rb } None => break }
                }
                _ => break,
            }
        }
        steps
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "rc".into());
    let mut out = String::with_capacity(64);
    let s0 = counting::snap();
    let steps = if mode == "rc" { rc::run(&mut out) } else { idx::run(&mut out) };
    let s1 = counting::snap();
    println!("{out}\nsteps {steps}");
    eprintln!("{mode}: allocs {} reallocs {}", s1.0 - s0.0, s1.1 - s0.1);
}
