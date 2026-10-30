#!/usr/bin/env python3
"""The stress generator of docs/async-capabilities.md §6.2 row 15 (U7), for the #743 spike.

Each seed gives one surface program: several tasks, each lending a cell it owns across `await`s
(R1, SPEC §29), with relaxed lends nested inside the body up to depth 3 (an inner cell holding the
outer view, lent again), independent inner relaxed lends, closures and pairs holding a view across
an `await`, `raise` handled inside the lend, and a random schedule of resumptions and
cancellations driven from `main`. The generator simulates the program and writes the answer it
must print to `<name>.expect`; `run.sh` checks it under every mode of `scripts/falsify.sh`.

    gen.py OUTDIR FIRST_SEED COUNT
"""
import os
import random
import sys

M32 = 1 << 32


class Gen:
    def __init__(self, rnd, wide=False):
        self.r = rnd
        self.k = 0
        # the spike's widenings: W-imm (`borrow imm` of a cell) and W-nest (`borrow mut` of an array)
        self.wide = wide

    def fresh(self, base):
        self.k += 1
        return f"{base}{self.k}"

    # A body over a view chain. `view` is the name of the view; `depth` is how many cells hold
    # views between it and the integer (0: `view : mut 'x i32`). Returns (lines, awaits, final
    # name of the view). `st` holds the simulated integer.
    def body(self, view, depth, st, budget, nest):
        lines, awaits = [], 0
        n = self.r.randint(2, 5)
        for _ in range(n):
            if budget[0] <= 0:
                break
            budget[0] -= 1
            c = self.r.random()
            if c < 0.25:
                lines.append("await();")
                awaits += 1
            elif c < 0.45:
                k = self.r.randint(1, 9)
                lines.append(self.update(view, depth, "+", k) + ";")
                st[0] = (st[0] + k) % M32
            elif c < 0.55:
                k = self.r.randint(2, 3)
                lines.append(self.update(view, depth, "*", k) + ";")
                st[0] = (st[0] * k) % M32
            elif c < 0.65:
                # a closure over the view
                # (a closure over a view live across `await` is refused: it has no derived drop,
                # and the cancel path would abandon it; so it is forced before the `await`)
                f = self.fresh("cl")
                v2 = self.fresh("v")
                k = self.r.randint(1, 9)
                lines.append(f"let {f} = {{ {self.update(view, depth, '+', k)}; {view} }};")
                lines.append(f"{v2} <- force {f};")
                lines.append("await();")
                awaits += 1
                st[0] = (st[0] + k) % M32
                view = v2
            elif c < 0.75:
                # a pair holding the view across an await
                p, v2, kk = self.fresh("p"), self.fresh("v"), self.fresh("k")
                k = self.r.randint(1, 9)
                lines.append(f"let {p} = ({view}, {k});")
                lines.append("await();")
                lines.append(f"let ({v2}, {kk}) = {p};")
                lines.append(self.update(v2, depth, "+", kk) + ";")
                awaits += 1
                st[0] = (st[0] + k) % M32
                view = v2
            elif self.wide and c < 0.87 and nest > 0:
                # (W-nest only in a task's own relaxed lend: inside a nested one, the elaborator
                # cannot infer the outer block's result, `ascribe it`; an elaborator gap)
                if nest < 3 or self.r.random() < 0.5:
                    # W-imm: an `imm` relaxed lend of a fresh cell, two copies of the view, one read
                    # before an `await` and one after
                    d, w, n, q = self.fresh("d"), self.fresh("w"), self.fresh("n"), self.fresh("q")
                    n1, n2, e = self.fresh("n"), self.fresh("n"), self.fresh("e")
                    init = self.r.randint(1, 50)
                    lines.append(f"let {d} = alloc({init});")
                    lines.append(f"let {w} = borrow imm {d} {{ '{q}, {n} ->")
                    lines.append(f"  let ({n1}, {n2}) = copy['{q}, i32] {n};")
                    lines.append(f"  let a = *{n1};")
                    lines.append("  await();")
                    lines.append(f"  a + *{n2}")
                    lines.append("};")
                    lines.append(f"let {e} = free({d});")
                    lines.append(self.update(view, depth, "+", f"{w} + {e}") + ";")
                    st[0] = (st[0] + 3 * init) % M32
                    awaits += 1
                else:
                    # W-nest: an owned array lent `mut` as a family across `await`s, a leaf written,
                    # then the slice walked by a `for` that awaits at each element
                    arr, sv, sv2, z = self.fresh("arr"), self.fresh("s"), self.fresh("s"), self.fresh("z")
                    ln = self.r.randint(1, 4)
                    k = self.r.randint(1, 20)
                    lines.append(f"let mut {arr} = array_new[i32]({ln}, ones);")
                    lines.append(f"borrow mut {arr} {{ {sv} ->")
                    lines.append("  await();")
                    lines.append(f"  let {sv2} = set({sv}, 0, {k});")
                    lines.append(f"  walk({sv2}) }};")
                    lines.append(f"let {z} = at(&{arr}, 0, 0);")
                    lines.append(self.update(view, depth, "+", z) + ";")
                    st[0] = (st[0] + 2 * k) % M32
                    awaits += 1 + ln
            elif c < 0.88 and nest > 0:
                # a nested relaxed lend of a cell holding this view
                d, w, v2, inner = self.fresh("d"), self.fresh("w"), self.fresh("v"), self.fresh("n")
                ib, ia, iv = self.body(inner, depth + 1, st, budget, nest - 1)
                lines.append(f"let {d} = alloc({view});")
                lines.append(f"let {w} : i32 = borrow mut {d} {{ {inner} ->")
                lines += ["  " + l for l in ib]
                lines.append("  " + self.read(iv, depth + 1))
                lines.append("};")
                lines.append(f"let {v2} = free({d});")
                # the inner result is the integer it read; fold it in
                lines.append(self.update(v2, depth, "+", w) + ";")
                st[0] = (st[0] + st[0]) % M32
                awaits += ia
                view = v2
            elif nest > 0:
                # an independent nested relaxed lend of a fresh integer cell
                d, w, e, inner = self.fresh("d"), self.fresh("w"), self.fresh("e"), self.fresh("n")
                init = self.r.randint(1, 50)
                sub = [init]
                ib, ia, iv = self.body(inner, 0, sub, budget, nest - 1)
                lines.append(f"let {d} = alloc({init});")
                lines.append(f"let {w} : i32 = borrow mut {d} {{ {inner} ->")
                lines += ["  " + l for l in ib]
                lines.append("  " + self.read(iv, 0))
                lines.append("};")
                lines.append(f"let {e} = free({d});")
                lines.append(self.update(view, depth, "+", f"{w} + {e}") + ";")
                st[0] = (st[0] + 2 * sub[0]) % M32
                awaits += ia
        return lines, awaits, view

    def update(self, view, depth, op, k):
        """A statement adding/multiplying `k` into the integer at the end of the view chain."""
        if depth == 0:
            return f"modify {view} {{ x -> x {op} {k} }}"
        y = self.fresh("y")
        return f"modify {view} {{ {y} -> {self.update(y, depth - 1, op, k)}; {y} }}"

    def read(self, view, depth):
        """The final expression of a body: the integer, the view consumed."""
        if depth == 0:
            return f"modify {view} {{ x -> (x, x) }}"
        y, r = self.fresh("y"), self.fresh("r")
        return f"modify {view} {{ {y} -> let {r} = {self.read(y, depth - 1)}; ({y}, {r}) }}"

    def task(self, i):
        init = self.r.randint(1, 100)
        st = [init]
        budget = [self.r.randint(4, 14)]
        m = self.fresh("m")
        b, a, v = self.body(m, 0, st, budget, 3)
        lines = [f"fn task{i}() -> i32 with Async =", f"  let c = alloc({init});",
                 f"  let r : i32 = borrow mut c {{ {m} ->"]
        lines += ["    " + l for l in b]
        raise_e = None
        if self.r.random() < 0.3:
            # a raise handled inside the lend, as the body's last step
            e = self.r.randint(1, 9)
            fire = self.r.random() < 0.5
            cond = "true" if fire else "false"
            lines.append(f"    let q = with to_result[i32, i32] {{ if {cond} {{ raise({e}) }} else {{ () }}; {self.read(v, 0)} }};")
            lines.append("    match q { inl x -> x | inr e -> 0 - e }")
            raise_e = e if fire else None
        else:
            lines.append("    " + self.read(v, 0))
        lines.append("  };")
        lines.append("  let _ = free(c);")
        lines.append("  r")
        val = ((-raise_e) % M32) if raise_e is not None else st[0]
        return lines, a, val


def program(seed, wide=False):
    r = random.Random(seed)
    g = Gen(r, wide)
    nt = r.randint(2, 5)
    out = ["-- Generated by experiments/Spike743/stress/gen.py, seed %d." % seed,
           "include async", "include fail"] + (["include slice", "",
           "fn ones(i: i32) -> i32 = i + 1",
           "fn walk<'a>(t: array_mut 'a i32) -> 1 with Async = for x in t { modify x { y -> y * 2 }; await() }"]
           if wide else []) + ["",
           "fn done(v: i32) -> Task[i32] = with spawn { v }",
           "fn step(t: Task[i32]) -> Task[i32] = match resume(t) { inl v -> done(v) | inr t2 -> t2 }",
           "fn fin(t: Task[i32]) -> i32 = match resume(t) { inl v -> v | inr t2 -> cancel(t2); 0 - 1 }", ""]
    awaits, vals = [], []
    for i in range(nt):
        ls, a, v = g.task(i)
        out += ls + [""]
        awaits.append(a)
        vals.append(v)
    # The schedule: spawn every task, then random steps and cancellations.
    main = ["main -> i32 ="]
    for i in range(nt):
        main.append(f"  let t{i} = with spawn {{ task{i}() }};")
    pos = [0] * nt          # awaits passed (spawn runs to the first)
    live = [True] * nt
    result = [0] * nt
    for _ in range(r.randint(nt, 6 * nt)):
        i = r.randrange(nt)
        if not live[i]:
            continue
        if r.random() < 0.12:
            main.append(f"  cancel(t{i});")
            live[i] = False
            result[i] = 0
        else:
            main.append(f"  let t{i} = step(t{i});")
            pos[i] += 1
    for i in range(nt):
        if not live[i]:
            continue
        # a task of n awaits answers its value at its (n+1)th resumption
        if r.random() < 0.3:
            main.append(f"  let v{i} = fin(t{i});")
            result[i] = vals[i] if pos[i] >= awaits[i] else (-1) % M32
        else:
            need = max(0, awaits[i] - pos[i])
            for _ in range(need):
                main.append(f"  let t{i} = step(t{i});")
            main.append(f"  let v{i} = fin(t{i});")
            result[i] = vals[i]
        live[i] = None
    terms = []
    total = 0
    for i in range(nt):
        if live[i] is None:
            terms.append(f"v{i} * {i + 1}")
            total = (total + result[i] * (i + 1)) % M32
    main.append("  " + (" + ".join(terms) if terms else "0"))
    out += main
    return "\n".join(out) + "\n", total


# ---------------------------------------------------------------------------------------------
# NURSERY=1 (round 3): W-tick and W-hold sites, in the core text. A task lends its request (`imm`
# with N children holding copies of the view, or `mut` with one writer child) with a nursery
# scope (`withbor1rh` / `withbor2rh`), spawns the children with `spawn_in` at `'r_n`, may tick
# directly, and waits in a `div_iterate` loop: each turn awaits the scheduler (`9.0`), runs one
# round of the children, may cancel the parent (`8.0`, cancelled by its handler) or one child, and
# goes on while a child is pending. `div_fuel_k` closes the wait at a random budget; the close step
# cancels the children still pending. The generator simulates the run.

TICK = "4294967295.0 lin 1 ~> 1 + 1"
ROWN = f"[{TICK}, 9.0 cancel 1 ~> 1, 8.0 cancel 1 ~> 1]"


STATS = {k: 0 for k in ['programs', 'children', 'mut', 'direct_ticks', 'loop_ticks', 'fuel_closed', 'parent_cancelled', 'child_culled', 'children_cancelled', 'turns']}


def nursery_program(seed):
    r = random.Random(seed)
    kv = r.random() < 0.7                    # imm view, N children; else mut, one writer
    n = r.randint(1, 4) if kv else 1
    req = r.randint(1, 20)
    awaits = [r.randint(0, 4) for _ in range(n)]
    mults = [r.randint(1, 9) for _ in range(n)]
    adds = [r.randint(1, 9) for _ in range(n)]
    direct = r.randint(0, 3)                  # ticks performed directly before the spawns
    fuel = r.randint(0, 8)
    cj = r.choice([None, None, r.randint(1, 6)])   # the turn whose `8.0` is cancelled
    cc = r.choice([None, r.randint(1, 5)])         # the turn after which the head child is cancelled
    Q = "QueueIn[i32]<'n /\\ 'r /\\ top>"
    QN = "QueueIn[i32]<'r_n /\\ 'r /\\ top>"
    L = ["-- Stress (round 3, NURSERY=1): W-tick and W-hold, generated; see gen.py.", "include async", ""]
    if kv:
        for i in range(n):
            L.append(f"fn child{i}<'r>(k: imm 'r i32) -> i32 with Async =")
            L.append("  let a = *k;")
            L.append(f"  for _ in 0..{awaits[i]} {{ await() }};")
            L.append(f"  a * {mults[i]}")
            L.append("")
        ks = ", ".join(f"k{i}: imm 'r i32" for i in range(n))
        L.append(f"fn start<'r, 'n < 'r>({ks}) -> {Q} =")
        L.append(f"  let q = queue_in[i32]['n /\\ 'r /\\ top]();")
        for i in range(n):
            L.append(f"  let t{i} = with spawn_in {{ child{i}(k{i}) }};")
            L.append(f"  let q = push_in[i32]['n /\\ 'r /\\ top](q, t{i});")
        L.append("  q")
    else:
        L.append("fn writer<'r>(m: mut 'r i32) -> i32 with Async =")
        L.append(f"  modify m {{ x -> x + {adds[0]} }};")
        L.append(f"  for _ in 0..{awaits[0]} {{ await(); modify m {{ x -> x + 1 }} }};")
        L.append(f"  modify m {{ x -> (x * {mults[0]}, x * {mults[0]}) }}")
        L.append("")
        L.append(f"fn start<'r, 'n < 'r>(m: mut 'r i32) -> {Q} =")
        L.append(f"  let q = queue_in[i32]['n /\\ 'r /\\ top]();")
        L.append("  let t0 = with spawn_in { writer(m) };")
        L.append(f"  push_in[i32]['n /\\ 'r /\\ top](q, t0)")
    L += ["", """fn one_round<'n>(q: QueueIn[i32]<'n>) -> QueueIn[i32]<'n> * (1 + 1) =
  let (n, s) = q;
  let (b, p) = round_in(n, rev_in(n, s));
  ((n, b), p)

fn finish<'n>(q: QueueIn[i32]<'n>) -> i32 =
  let (n, s) = q;
  let (vs, cut) = values_in(n, rev_in(n, s));
  let mut acc = 0;
  let mut cur = vs;
  for _ in 0..n {
    match unroll cur { inl u -> cur = (roll inl () : List[i32]) | inr (x, r) -> acc = acc + x; cur = r }
  };
  match unroll cur { inl u -> () | inr (x, r) -> () };
  if cut { acc - 100 } else { acc }

fn cancel_all<'n>(q: QueueIn[i32]<'n>) -> 1 = let _ = finish(q); ()

fn cull<'n>(q: QueueIn[i32]<'n>) -> QueueIn[i32]<'n> =
  let (n, s) = q;
  match unroll s {
    inl u -> (n, roll inl ())
  | inr (x, r) -> match x {
      inl v -> (n, roll inr (inl v, r))
    | inr t -> cancel_in(t); (n, roll inr (inl (0 - 1), r))
    }
  }

fn rd<'r>(k: imm 'r i32) -> i32 = *k

def plus : i32 * i32 => i32 = unbang host[add32]
def eq : i32 * i32 => 1 + 1 = unbang host[eq32]
""", "main : F i32 =", f"  req <- return (alloc[i32] i32[{req}]);", "  t <- return (thunkv fun (u0 : 1) ->"]
    kw = "withbor1rh" if kv else "withbor2rh"
    L.append(f"    {kw}['r, dom, i32, i32, {ROWN}](req, k) (")
    for j in range(direct):
        L.append(f"      d{j} <- perform[4294967295.0] ();")
        L.append(f"      case d{j} {{ inl a -> return () | inr b -> return () }};")
    if kv:
        names = []
        for i in range(n):
            L.append(f"      kk{i} <- return (copy['r, i32] k);")
            L.append(f"      let (k{i}, k) = kk{i};")
            names.append(f"k{i}")
        arg = "(" + ", ".join(names) + ")" if n > 1 else names[0]
        L.append(f"      sf <- return ((unbang start) ['r] ['r_n]);")
        L.append(f"      a2 <- return {arg};" if n > 1 else f"      a2 <- return {arg};")
        L.append("      q0 <- force sf a2;")
    else:
        L.append(f"      sf <- return ((unbang start) ['r] ['r_n]);")
        L.append("      q0 <- force sf k;")
    fin = "(cf <- return ((unbang cancel_all) ['r_n /\\ 'r /\\ top]); force cf"
    L.append(f"      st <- return ((!thunkv fun (sq : {QN} * i32) ->")
    L.append("        < let (q, j) = sq;")
    L.append(f"          u <- perform[9.0] () unwind ({fin.replace('force cf', 'force cf q')}));")
    L.append("          let () = u;")
    L.append(f"          rf <- return ((unbang one_round) ['r_n /\\ 'r /\\ top]);")
    L.append("          o <- force rf q;")
    L.append("          let (q1, p) = o;")
    L.append(f"          c8 <- return (eq (j, i32[{cj if cj is not None else 0}]));")
    L.append(f"          q2 <- (case c8 {{ inl ne -> return q1 | inr is -> v8 <- perform[8.0] () unwind ({fin.replace('force cf', 'force cf q1')})); let () = v8; return q1 }});")
    L.append(f"          cc <- return (eq (j, i32[{cc if cc is not None else 0}]));")
    L.append(f"          q3 <- (case cc {{ inl ne -> return q2 | inr is -> cu <- return ((unbang cull) ['r_n /\\ 'r /\\ top]); force cu q2 }});")
    L.append("          case p {")
    L.append(f"            inl done -> ff <- return ((unbang finish) ['r_n /\\ 'r /\\ top]); s <- force ff q3; return (inl s)")
    L.append("          | inr more -> let () = more; return (inr (q3, plus (j, i32[1])))")
    L.append("          },")
    L.append(f"          let (q, j) = sq; ff <- return ((unbang finish) ['r_n /\\ 'r /\\ top]); force ff q >) :")
    L.append(f"          !U ({QN} * i32 -o F{ROWN} (i32 + {QN} * i32) & F{ROWN} i32));")
    L.append(f"      f <- return (unbang div_iterate[{ROWN}, {QN} * i32, i32, i32]);")
    L.append("      a0 <- return (st, (q0, i32[1]));")
    L.append("      o <- force f a0;")
    L.append("      s <- (case o { inl b -> return b | inr z -> return z });")
    if kv:
        L.append("      y <- return ((unbang rd) ['r] k);")
        L.append("      x <- return (plus (s, y));")
        L.append("      return (boxed['r] x)));")
    else:
        L.append("      return (boxed['r] s)));")
    K8 = "U ((1 -o F[8.0 cancel 1 ~> 1] i32) & F[8.0 cancel 1 ~> 1] 1)"
    L.append("""  handle_with[8](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (q : 1 * U ((1 -o F i32) & F 1)) ->
        let (x, k) = q; let () = x; w <- (force k).2; let () = w; return i32[5]), ()) :
        !U (1 * U ((1 -o F i32) & F 1) -o F i32) * 1)) (
  handle_with[9](
      ((!thunkv fun (p : ref i32 * i32) ->
        let (c, v) = p; w <- return (free[i32] c); return (plus (v, %s))) : !U (ref i32 * i32 -o F[8.0 cancel 1 ~> 1] i32)),
      (((!thunkv fun (q : 1 * %s) ->
        let (x, k) = q; (force k).1 x), ()) : !U (1 * %s -o F[8.0 cancel 1 ~> 1] i32) * 1)) (
    df <- return (unbang div_fuel_k[[9.0 cancel 1 ~> 1, 8.0 cancel 1 ~> 1], ref i32 * i32]);
    a1 <- return (t, i32[%d]);
    force df a1))""" % ("i32[0]" if kv else "w", K8, K8, fuel))
    # --- simulation ---
    budget = [fuel]
    def tick():
        if budget[0] > 0:
            budget[0] -= 1
            return True
        return False
    for _ in range(direct):
        tick()
    # A task needs one observation per `await` and one more for its value: the observation that
    # runs it to its end answers the finished task, whose next observation answers the value.
    cell = [req]
    tasks = []
    for i in range(n):
        t = ['pend', awaits[i] + 1, i, 0, None]
        if not kv:
            cell[0] = (cell[0] + adds[0]) % M32
            if awaits[0] == 0:
                cell[0] = (cell[0] * mults[0]) % M32
                t[4] = cell[0]
        else:
            t[4] = (req * mults[i]) % M32
        tasks.append(t)
    slots = list(reversed(tasks))
    def resume_child(t):
        t[3] += 1
        if not kv and t[3] <= awaits[0]:
            cell[0] = (cell[0] + 1) % M32
            if t[3] == awaits[0]:
                cell[0] = (cell[0] * mults[0]) % M32
                t[4] = cell[0]
        t[1] -= 1
        if t[1] == 0:
            t[0], t[1] = 'val', t[4]
    def finish_val():
        acc, cut = 0, False
        for t in slots:
            if t[0] == 'val':
                acc = (acc + t[1]) % M32
            else:
                cut = True
                t[0], t[1] = 'cancelled', 0
        return (acc - 100) % M32 if cut else acc
    STATS['programs'] += 1
    STATS['children'] += n
    STATS['mut'] += 0 if kv else 1
    STATS['direct_ticks'] += direct
    j = 1
    answer = None
    while True:
        STATS['turns'] += 1
        # turn j: await (resumed), a round
        pending = False
        for t in reversed(slots):        # processed first-pushed first
            if t[0] == 'pend':
                resume_child(t)
                if t[0] == 'pend':
                    pending = True
        if cj is not None and j == cj:
            answer = 5
            STATS['parent_cancelled'] += 1
            STATS['children_cancelled'] += sum(1 for t in slots if t[0] == 'pend')
            break
        if cc is not None and j == cc:
            h = slots[0]
            if h[0] == 'pend':
                h[0], h[1] = 'val', (-1) % M32
                STATS['child_culled'] += 1
        if not pending:
            s = finish_val()
            break
        if tick():
            STATS['loop_ticks'] += 1
            j += 1
            continue
        STATS['fuel_closed'] += 1
        STATS['children_cancelled'] += sum(1 for t in slots if t[0] == 'pend')
        s = finish_val()
        break
    if answer is None:
        if kv:
            answer = (s + req) % M32
        else:
            answer = (s + cell[0]) % M32
    return "\n".join(L) + "\n", answer


# ---------------------------------------------------------------------------------------------
# TICK=1 (round 3): W-tick sites alone (`withbor2rt` / `withbor1rt`, no nursery). A task lends a
# cell it owns across a `div_iterate` loop: each turn awaits (`9.0`), and either adds to the cell
# through a `mut` view (under `[then]`, its finaliser writing a mark through the view when the turn
# is cancelled), or reads it through an `imm` view; the loop finishes at a random bound, or
# `div_fuel_k` closes it, or the parent is cancelled at a random turn (`8.0`).

def tick_program(seed):
    r = random.Random(seed)
    kv = r.random() < 0.4
    init = r.randint(0, 9)
    inc = r.randint(1, 5)
    bound = r.randint(1, 8)
    fuel = r.randint(0, 8)
    direct = r.randint(0, 2)
    cj = r.choice([None, None, r.randint(1, 6)])
    mark = r.randint(50, 99)
    kw = "withbor1rt" if kv else "withbor2rt"
    V = "imm 'x i32" if kv else "mut 'x i32"
    St = f"{V} * i32"
    L = ["-- Stress (round 3, TICK=1): W-tick, generated; see gen.py.", "include async", "",
         "fn rd<'r>(k: imm 'r i32) -> i32 = *k", "",
         "def plus : i32 * i32 => i32 = unbang host[add32]",
         "def lt : i32 * i32 => 1 + 1 = unbang host[lt_s32]",
         "def eq : i32 * i32 => 1 + 1 = unbang host[eq32]", "",
         "main : F i32 =", f"  c <- return (alloc[i32] i32[{init}]);",
         "  t <- return (thunkv fun (u0 : 1) ->",
         f"    {kw}['x, dom, i32, i32, {ROWN}](c, m) ("]
    for jj in range(direct):
        L.append(f"      d{jj} <- perform[4294967295.0] ();")
        L.append(f"      case d{jj} {{ inl a -> return () | inr b -> return () }};")
    L.append(f"      st <- return ((!thunkv fun (sq : {St}) ->")
    L.append("        < let (v, j) = sq;")
    L.append("          u <- perform[9.0] ();")
    L.append("          let () = u;")
    if kv:
        L.append("          cp <- return (copy['x, i32] v);")
        L.append("          let (v1, v) = cp;")
        L.append("          rv <- return ((unbang rd) ['x] v1);")
        L.append(f"          r <- return (plus (rv, j));")
        L.append(f"          c8 <- return (eq (j, i32[{cj if cj is not None else 0}]));")
        L.append("          w8 <- (case c8 { inl ne -> return () | inr is -> perform[8.0] () });")
        L.append("          let () = w8;")
    else:
        L.append(f"          q <- return (withswap['x, i32, i32] v (thunkv fun (a : i32) -> return (plus (a, i32[{inc}]), plus (a, i32[{inc}]))));")
        L.append("          let (v, r) = q;")
        L.append(f"          c8 <- return (eq (j, i32[{cj if cj is not None else 0}]));")
        L.append("          w8 <- (case c8 { inl ne -> return () | inr is -> perform[8.0] () }) unwind (")
        L.append(f"            q2 <- return (withswap['x, i32, 1] v (thunkv fun (z : i32) -> return (i32[{mark}], ())));")
        L.append("            let (v, z2) = q2; let () = z2; return (forget_mut['x, i32] v));")
        L.append("          let () = w8;")
    L.append(f"          g <- return (lt (j, i32[{bound}]));")
    L.append("          case g {")
    forget = "forget_imm" if kv else "forget_mut"
    L.append(f"            inl ge -> let () = {forget}['x, i32] v; return (inl r)")
    L.append("          | inr lo -> return (inr (v, plus (j, i32[1])))")
    L.append("          },")
    L.append(f"          let (v, j) = sq; let () = {forget}['x, i32] v; return (plus (i32[1000], j)) >) :")
    L.append(f"          !U ({St} -o F{ROWN} (i32 + {St}) & F{ROWN} i32));")
    L.append(f"      f <- return (unbang div_iterate[{ROWN}, {St}, i32, i32]);")
    L.append("      a0 <- return (st, (m, i32[1]));")
    L.append("      o <- force f a0;")
    L.append("      case o { inl b -> return (boxed['x] b) | inr z -> return (boxed['x] z) }));")
    K8 = "U ((1 -o F[8.0 cancel 1 ~> 1] i32) & F[8.0 cancel 1 ~> 1] 1)"
    L.append("""  handle_with[8](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (q : 1 * U ((1 -o F i32) & F 1)) ->
        let (x, k) = q; let () = x; w <- (force k).2; let () = w; return i32[5]), ()) :
        !U (1 * U ((1 -o F i32) & F 1) -o F i32) * 1)) (
  handle_with[9](
      ((!thunkv fun (p : ref i32 * i32) ->
        let (c, v) = p; w <- return (free[i32] c); return (plus (v, w))) : !U (ref i32 * i32 -o F[8.0 cancel 1 ~> 1] i32)),
      (((!thunkv fun (q : 1 * %s) ->
        let (x, k) = q; (force k).1 x), ()) : !U (1 * %s -o F[8.0 cancel 1 ~> 1] i32) * 1)) (
    df <- return (unbang div_fuel_k[[9.0 cancel 1 ~> 1, 8.0 cancel 1 ~> 1], ref i32 * i32]);
    a1 <- return (t, i32[%d]);
    force df a1))""" % (K8, K8, fuel))
    # simulation
    budget = fuel
    for _ in range(direct):
        if budget > 0:
            budget -= 1
    cell = init
    j = 1
    while True:
        if kv:
            res = (cell + j) % M32
        else:
            cell = (cell + inc) % M32
            res = cell
        if cj is not None and j == cj:
            return "\n".join(L) + "\n", 5
        if j >= bound:
            ans = res
            break
        if budget > 0:
            budget -= 1
            j += 1
            continue
        ans = (1000 + j + 1) % M32
        break
    return "\n".join(L) + "\n", (ans + cell) % M32


def main():
    outdir, first, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(outdir, exist_ok=True)
    for s in range(first, first + count):
        if os.environ.get("NURSERY") == "1":
            src, total = nursery_program(s)
        elif os.environ.get("TICK") == "1":
            src, total = tick_program(s)
        else:
            src, total = program(s, os.environ.get("WIDE") == "1")
        with open(os.path.join(outdir, f"s{s:04d}.bc"), "w") as f:
            f.write(src)
        with open(os.path.join(outdir, f"s{s:04d}.expect"), "w") as f:
            f.write(f"i32[{total}]\nlive 0\n")
    if os.environ.get("NURSERY") == "1":
        print("nursery stats:", STATS)


if __name__ == "__main__":
    main()
