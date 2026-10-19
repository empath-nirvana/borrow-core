// regex-redux, as bg/regex.bc, with a hand-written matcher of the same design (no `regex`
// crate): a Pike VM, leftmost-first, over bytes; literals, `.`, `[...]`/`[^...]`, `*`, top-level
// `|`, `\` escapes. Program = Vec of (op, x, y); classes = 256 bools each. Performance-minded:
// the thread lists, the add-thread stack and the marks are allocated once per pattern and reused
// across steps and start positions (the probe allocates them per call).
use std::io::{Read, Write};
rs::counting!();

#[derive(Clone, Copy)]
enum Op { Byte(u8), Class(usize), Any, Split(usize, usize), Jump(usize), Match }

struct Re { prog: Vec<Op>, classes: Vec<[bool; 256]> }

fn compile(p: &[u8]) -> Re {
    let mut re = Re { prog: Vec::with_capacity(64), classes: Vec::new() };
    let mut jumps = Vec::new();
    let mut i = 0;
    let m = p.len();
    while i < m {
        // the end of this alternative
        let (mut j, mut in_class, mut more) = (i, false, false);
        while j < m {
            let c = p[j];
            if c == b'\\' { j += 2 } else if in_class { if c == b']' { in_class = false } j += 1 }
            else if c == b'[' { in_class = true; j += 1 } else if c == b'|' { more = true; break } else { j += 1 }
        }
        let here = re.prog.len();
        if more { re.prog.push(Op::Split(here + 1, usize::MAX)) }
        while i < j.min(m) {
            let c = p[i];
            let (atom, after) = if c == b'[' {
                let neg = p[i + 1] == b'^';
                let mut k = if neg { i + 2 } else { i + 1 };
                let mut cls = [neg; 256];
                while p[k] != b']' { cls[p[k] as usize] = !neg; k += 1 }
                re.classes.push(cls);
                (Op::Class(re.classes.len() - 1), k + 1)
            } else if c == b'\\' { (Op::Byte(p[i + 1]), i + 2) }
            else if c == b'.' { (Op::Any, i + 1) } else { (Op::Byte(c), i + 1) };
            let star = after < m && p[after] == b'*';
            let l0 = re.prog.len();
            if star { re.prog.push(Op::Split(l0 + 1, usize::MAX)) }
            re.prog.push(atom);
            if star {
                re.prog.push(Op::Jump(l0));
                let out = re.prog.len();
                re.prog[l0] = Op::Split(l0 + 1, out);
                i = after + 1
            } else { i = after }
        }
        if more {
            jumps.push(re.prog.len());
            re.prog.push(Op::Jump(usize::MAX));
            let next = re.prog.len();
            re.prog[here] = Op::Split(here + 1, next);
            i = j + 1
        } else { i = m }
    }
    let end = re.prog.len();
    for jp in jumps { re.prog[jp] = Op::Jump(end) }
    re.prog.push(Op::Match);
    re
}

struct Vm { clist: Vec<usize>, nlist: Vec<usize>, stack: Vec<usize>, mark: Vec<u32>, generation: u32 }

impl Vm {
    fn new(re: &Re) -> Vm { let n = re.prog.len(); Vm { clist: Vec::with_capacity(n), nlist: Vec::with_capacity(n), stack: Vec::with_capacity(2 * n + 2), mark: vec![0; n], generation: 0 } }
    fn add(re: &Re, lst: &mut Vec<usize>, stack: &mut Vec<usize>, mark: &mut [u32], generation: u32, pc: usize) {
        stack.push(pc);
        while let Some(q) = stack.pop() {
            if mark[q] == generation { continue }
            mark[q] = generation;
            match re.prog[q] {
                Op::Jump(x) => stack.push(x),
                Op::Split(x, y) => { stack.push(y); stack.push(x) }
                _ => lst.push(q),
            }
        }
    }
    /// The end of the leftmost-first match starting at `s`.
    fn match_at(&mut self, re: &Re, t: &[u8], s: usize) -> Option<usize> {
        self.generation += 1;
        self.clist.clear();
        Vm::add(re, &mut self.clist, &mut self.stack, &mut self.mark, self.generation, 0);
        let mut found = None;
        let mut i = s;
        while !self.clist.is_empty() && i <= t.len() {
            self.generation += 1;
            self.nlist.clear();
            for k in 0..self.clist.len() {
                let pc = self.clist[k];
                let ok = match re.prog[pc] {
                    Op::Match => { found = Some(i); break }
                    _ if i >= t.len() => false,
                    Op::Byte(x) => t[i] == x,
                    Op::Any => t[i] != b'\n',
                    Op::Class(c) => re.classes[c][t[i] as usize],
                    _ => false,
                };
                if ok { Vm::add(re, &mut self.nlist, &mut self.stack, &mut self.mark, self.generation, pc + 1) }
            }
            std::mem::swap(&mut self.clist, &mut self.nlist);
            i += 1;
        }
        found
    }
}

fn count(p: &str, t: &[u8]) -> usize {
    let re = compile(p.as_bytes());
    let mut vm = Vm::new(&re);
    let (mut c, mut s) = (0, 0);
    while s <= t.len() {
        match vm.match_at(&re, t, s) { Some(e) if e > s => { c += 1; s = e } _ => s += 1 }
    }
    c
}

fn replace_all(p: &str, r: &str, t: &[u8]) -> Vec<u8> {
    let re = compile(p.as_bytes());
    let mut vm = Vm::new(&re);
    let mut out = Vec::with_capacity(t.len());
    let mut s = 0;
    while s < t.len() {
        match vm.match_at(&re, t, s) {
            Some(e) if e > s => { out.extend_from_slice(r.as_bytes()); s = e }
            _ => { out.push(t[s]); s += 1 }
        }
    }
    out
}

fn main() {
    let s0 = rs::snap();
    let mut inp = Vec::new();
    std::io::stdin().read_to_end(&mut inp).unwrap();
    let seq = replace_all(">.*\n|\n", "", &inp);
    let mut o = Vec::new();
    for p in ["agggtaaa|tttaccct", "[cgt]gggtaaa|tttaccc[acg]", "a[act]ggtaaa|tttacc[agt]t", "ag[act]gtaaa|tttac[agt]ct",
              "agg[act]taaa|ttta[agt]cct", "aggg[acg]aaa|ttt[cgt]ccct", "agggt[cgt]aa|tt[acg]accct",
              "agggta[cgt]a|t[acg]taccct", "agggtaa[cgt]|[acg]ttaccct"] {
        let c = count(p, &seq);
        writeln!(o, "{} {}", p, c).unwrap();
    }
    let s1 = replace_all("tHa[Nt]", "<4>", &seq);
    let s2 = replace_all("aND|caN|Ha[DS]|WaS", "<3>", &s1);
    let s3 = replace_all("a[NSt]|BY", "<2>", &s2);
    let s4 = replace_all("<[^>]*>", "|", &s3);
    let s5 = replace_all("\\|[^|][^|]*\\|", "-", &s4);
    writeln!(o, "\n{}\n{}\n{}", inp.len(), seq.len(), s5.len()).unwrap();
    rs::report(s0);
    std::io::stdout().write_all(&o).unwrap();
}
