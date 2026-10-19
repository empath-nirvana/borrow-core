// AWFY Havlak, index form, the same algorithm and CFG as awfy/havlak.bc: buildBaseLoop x25 in an
// outer loop; DFS numbering by an explicit stack, identifyEdges, union-find, the loop forest with
// parent indices. Answer (loops, nested, depth sum) = (75, 74, 122).
rs::counting!();

const UNVISITED: usize = usize::MAX;

struct Cfg { outs: Vec<Vec<usize>>, ins: Vec<Vec<usize>> }

impl Cfg {
    fn connect(&mut self, f: usize, t: usize) {
        let m = f.max(t) + 1;
        if self.outs.len() < m { self.outs.resize_with(m, Vec::new); self.ins.resize_with(m, Vec::new); }
        self.outs[f].push(t);
        self.ins[t].push(f);
    }
    fn straight(&mut self, start: usize, k: usize) -> usize { for i in 0..k { self.connect(start + i, start + i + 1); } start + k }
    fn diamond(&mut self, s: usize) -> usize {
        self.connect(s, s + 1); self.connect(s, s + 2); self.connect(s + 1, s + 3); self.connect(s + 2, s + 3); s + 3
    }
    fn base_loop(&mut self, from: usize) -> usize {
        let header = self.straight(from, 1);
        let d1 = self.diamond(header);
        let d11 = self.straight(d1, 1);
        let d2 = self.diamond(d11);
        let footer = self.straight(d2, 1);
        self.connect(d2, d11);
        self.connect(d1, header);
        self.connect(footer, from);
        self.straight(footer, 1)
    }
}

fn find_set(uf: &mut [usize], w: usize) -> usize {
    let mut r = w;
    while uf[r] != r { r = uf[r]; }
    let mut x = w;
    while uf[x] != x { let p = uf[x]; uf[x] = r; x = p; }
    r
}

fn find_loops(c: &Cfg) -> (usize, usize, usize) {
    let n = c.outs.len();
    let mut number = vec![UNVISITED; n];
    let mut last = vec![0usize; n];
    let mut uf_parent = vec![0usize; n];
    let mut uf_block = vec![0usize; n];
    let mut uf_loop: Vec<Option<usize>> = vec![None; n];
    // DFS by an explicit stack of (block, next edge)
    number[0] = 0; uf_parent[0] = 0; uf_block[0] = 0;
    let mut stack = vec![(0usize, 0usize)];
    let mut cur = 0;
    while let Some((b, e)) = stack.pop() {
        if e < c.outs[b].len() {
            let t = c.outs[b][e];
            stack.push((b, e + 1));
            if number[t] == UNVISITED {
                cur += 1;
                number[t] = cur; uf_parent[cur] = cur; uf_block[cur] = t;
                stack.push((t, 0));
            }
        } else {
            last[number[b]] = cur;
        }
    }
    let size = cur + 1;
    let mut back: Vec<Vec<usize>> = vec![Vec::new(); size];
    let mut nonback: Vec<Vec<usize>> = vec![Vec::new(); size];
    let mut header = vec![0usize; size];
    let mut kind = vec![0u8; size];
    for w in 0..size {
        let nw = uf_block[w];
        for &pv in &c.ins[nw] {
            let v = number[pv];
            if v != UNVISITED {
                if w <= v && v <= last[w] { back[w].push(v) } else { nonback[w].push(v) }
            }
        }
    }
    let mut loop_parent: Vec<Option<usize>> = vec![None];
    let mut loop_header = vec![0usize];
    let mut loop_red = vec![true];
    let mut pool: Vec<usize> = Vec::new();
    for w in (0..size).rev() {
        pool.clear();
        for &v in &back[w] {
            if v != w { let r = find_set(&mut uf_parent, v); pool.push(r) } else { kind[w] = 1 }
        }
        if !pool.is_empty() { kind[w] = 2 }
        let mut head = 0;
        while head < pool.len() {
            let x = pool[head];
            head += 1;
            for j in 0..nonback[x].len() {
                let y = nonback[x][j];
                let yd = find_set(&mut uf_parent, y);
                if w <= yd && yd <= last[w] {
                    if yd != w && !pool.contains(&yd) { pool.push(yd) }
                } else {
                    kind[w] = 3;
                    nonback[w].push(yd)
                }
            }
        }
        if !pool.is_empty() || kind[w] == 1 {
            let l = loop_parent.len();
            loop_parent.push(None);
            loop_header.push(uf_block[w]);
            loop_red.push(kind[w] != 3);
            uf_loop[w] = Some(l);
            for &xm in &pool {
                header[xm] = w;
                uf_parent[xm] = w;
                if let Some(xl) = uf_loop[xm] { loop_parent[xl] = Some(l) }
            }
        }
    }
    let nloops = loop_parent.len();
    let (mut nested, mut depth) = (0, 0);
    for l in 1..nloops {
        if loop_parent[l].is_some() { nested += 1 }
        let mut x = l;
        while let Some(p) = loop_parent[x] { depth += 1; x = p }
    }
    let _ = (&header, &loop_header, &loop_red);
    (nloops - 1, nested, depth)
}

fn build(k: usize) -> Cfg {
    let mut c = Cfg { outs: Vec::new(), ins: Vec::new() };
    c.connect(0, 1);
    let tp = c.straight(1, 1);
    let mut n = tp;
    for _ in 0..k { n = c.base_loop(n) }
    c.straight(n, 1);
    c.connect(n, tp);
    c
}

fn main() {
    let s0 = rs::snap();
    let c = build(25);
    let r = find_loops(&c);
    rs::report(s0);
    println!("{:?}", r);
}
