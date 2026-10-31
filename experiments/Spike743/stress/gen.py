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


# REIFY=1 (round 4): W-tick lends whose computation `reify_k` makes a first-class loop value
# (`bc/reify/mk.py` builds the pieces). A loop owns a fresh cell lent `mut` (turns add through the
# view; some turns run `inner`, a nested W-tick lend whose tick is a stop of the loop) or `imm`
# (turns read through it); its turns may `await`. The consumer observes it a random number of
# times, directly (some of it inside a lend of another cell, the loop stored in a cell there
# first), through `drive` (a `Div` loop of its own, with fuel), or as a task the handler stores,
# which `main` steps a random number of times and then cancels or runs to the end, a second
# loop observed between steps; the consumer's own `await`s hold the loop, under a finaliser that
# closes it or under none (the loop's derived destructor).

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "bc", "reify"))

RSTATS = {k: 0 for k in ['programs', 'mut', 'imm', 'inner', 'aw', 'direct', 'drive', 'task',
                         'nexts', 'stops', 'closes', 'dones', 'cancels', 'cancel_in_loop',
                         'stored', 'in_lend', 'second', 'cons_awaits', 'derived_drop',
                         'derived_drop_cancelled']}


class LoopSim:
    """The loop's observable behaviour: its first segment, *next* and *close*."""

    def __init__(self, kv, init, inc, lim, aw, inner):
        self.kv, self.inc, self.lim, self.aw, self.inner = kv, inc, lim, aw, inner
        self.cell = init
        self.j = 1
        self.pos = None
        self.awaits = 0
        self.turn()

    def turn(self):
        if self.inner:
            self.pos = 'inner'
            RSTATS['stops'] += 1
            return
        self.finish_turn(self.inc)

    def finish_turn(self, add):
        if self.kv:
            r = (self.cell + self.j) % M32
        else:
            self.cell = (self.cell + add) % M32
            r = self.cell
        if self.aw:
            self.awaits += 1
        if (self.j >= self.lim) if self.kv else (r >= self.lim):
            self.pos = 'done'
            self.r = r
        else:
            self.j += 1
            self.pos = 'back'
            RSTATS['stops'] += 1

    def next(self):
        if self.pos == 'done':
            return True
        RSTATS['nexts'] += 1
        if self.pos == 'inner':
            self.finish_turn(8 + self.inc)
        else:
            self.turn()
        return self.pos == 'done'

    def close(self):
        """The residual's answer."""
        RSTATS['closes'] += 1
        if self.pos == 'inner':
            self.finish_turn(2 + self.inc)
        if self.pos == 'done':
            return self.r
        return (1000 + self.j) % M32 if self.kv else self.cell


def reify_program(seed):
    import mk
    r = random.Random(seed)
    kv = r.random() < 0.35
    inner = (not kv) and r.random() < 0.3
    aw = r.random() < 0.5
    mode = r.choice(['direct', 'direct', 'drive', 'task', 'task'])
    init = r.randint(0, 9)
    inc = 1 if inner else r.randint(1, 4)
    lim = r.randint(1, 6) if kv else init + r.randint(1, 6) * (9 if inner else inc)
    mark = r.randint(50, 99) if (aw and not kv and r.random() < 0.5) else None
    RSTATS['programs'] += 1
    RSTATS['imm' if kv else 'mut'] += 1
    RSTATS['inner'] += inner
    RSTATS['aw'] += aw
    RSTATS[mode] += 1
    lend = mk.lend_imm("x", lim, aw) if kv else mk.lend_mut("x", inc, lim, aw, mark=mark,
                                                             inner="inner" if inner else None)
    L = [f"-- Stress (round 4, REIFY=1, seed {seed}): W-tick under `reify`, generated; see gen.py.",
         mk.PRE]
    if inner:
        L.append(mk.INNER)
    L.append(mk.mk_def("mk", init, lend, aw))
    sim = LoopSim(kv, init, inc, lim, aw, inner)
    LT = mk.loopt(aw)
    fin = mk.fin

    def done_ans(scale):
        return (sim.r * scale + sim.cell) % M32

    if mode == 'drive':
        fuel = r.randint(0, 6)
        L.append(mk.drive_def(aw))
        body = mk.drive_main(aw, fuel)
        # `drive`: next until done, its ticks answered next while fuel lasts, then close.
        while True:
            if sim.next():
                ans = done_ans(1000)
                RSTATS['dones'] += 1
                break
            if fuel > 0:
                fuel -= 1
                continue
            v = sim.close()
            ans = (v * 100 + sim.cell) % M32
            break
        if aw:
            body = body.replace("main : F i32 =\n", "main : F i32 =\n  " + mk.aw_now("", "  ")[:-1] + "\n", 1)
            body = body.rstrip("\n") + ")\n"
        L.append(body)
        return "\n".join(L), ans

    if mode == 'direct':
        n = r.randint(0, 5)
        lend_at = r.randint(0, n) if (not aw and r.random() < 0.4) else None
        out, ind, ans, closed = [], "  ", None, False
        out.append("g <- return (unbang mk); z <- return (); l0 <- force g z;")
        cur, depth, depth_in = "l0", 0, 0
        in_lend = False
        for k in range(n + 1):
            if lend_at == k and not in_lend:
                in_lend = True
                RSTATS['in_lend'] += 1
                stored = r.random() < 0.5
                if stored:
                    RSTATS['stored'] += 1
                    out.append(f"s <- return (alloc[{LT}] {cur});")
                out.append("d <- return (alloc[i32] i32[0]);")
                out.append("r <- return (withbor2['y, top, i32, i32] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->")
                if stored:
                    out.append(f"  ls <- return (free[{LT}] s);")
                    cur = "ls"
                out.append("  " + mk.setm("y", "i32[3]"))
            if k == n:
                break
            if sim.pos == 'done':
                break
            o = f"o{k}"
            out.append(("  " if in_lend else "") + f"{o} <- (nu_out (force {cur})).1;")
            d = sim.next()
            nxt = f"l{k + 1}"
            pre = "  " if in_lend else ""
            if d:
                RSTATS['dones'] += 1
                ans = done_ans(1000)
                res = f"let (c, v) = p; w <- return (free[i32] c); " + (
                    "return (boxed['y] (plus (mul (v, i32[1000]), w)))" if in_lend else
                    "return (plus (mul (v, i32[1000]), w))")
                out.append(pre + f"case {o} {{ inl p -> {res} | inr {nxt} -> q <- (nu_out (force {nxt})).2; let (c, v) = q; w <- return (free[i32] c); return " + ("(boxed['y] i32[0])" if in_lend else "i32[0]") + " }")
                closed = True
                break
            out.append(pre + f"case {o} {{ inl p -> let (c, v) = p; w <- return (free[i32] c); return " + ("(boxed['y] i32[1])" if in_lend else "i32[1]") + f" | inr {nxt} ->")
            if in_lend:
                depth_in += 1
            else:
                depth += 1
            cur = nxt
        if not closed:
            v = sim.close()
            ans = (v * 100 + sim.cell) % M32
            pre = "  " if in_lend else ""
            out.append(pre + f"q <- (nu_out (force {cur})).2; let (c, v) = q; w <- return (free[i32] c); return " +
                       ("(boxed['y] (plus (mul (v, i32[100]), w)))" if in_lend else "(plus (mul (v, i32[100]), w))"))
        if in_lend:
            out.append("  " + "}" * depth_in)
            out.append("  )));")
            out.append("let (d, x) = r; e <- return (free[i32] d); return (plus (x, e))")
            ans = (ans + 3) % M32
        out.append("}" * depth)
        body = "\n  ".join(out)
        main = "main : F i32 =\n  " + (mk.aw_now("  " + body.replace("\n  ", "\n    "), "  ") if aw else body) + "\n"
        L.append(main)
        return "\n".join(L), ans

    # task: the consumer `cons` (at `await`), `main` steps it.
    n = r.randint(0, 4)
    # A loop at `await` cannot be closed by a finaliser (its close performs `await`), and has no
    # derived destructor: the consumer does not hold it across an `await` of its own.
    cons_aw = [(not aw) and r.random() < 0.5 for _ in range(n + 1)]
    # A loop at a row has no derived destructor (its close performs the row): a finaliser then.
    finz = r.random() < 0.6
    if not finz:
        RSTATS['derived_drop'] += 1
    C = ["def cons : !U (1 -o F[" + mk.AW + "] i32) =", "  !thunkv fun (z : 1) ->",
         "    g <- return (unbang mk); z1 <- return (); l0 <- force g z1;"]
    awaits = sim.awaits
    cur, depth, ans, closed = "l0", 0, None, False
    for k in range(n + 1):
        if cons_aw[k] and sim.pos != 'done':
            RSTATS['cons_awaits'] += 1
            awaits += 1
            fz = f" unwind ({mk.CLOSE_UNIT(cur)})" if finz else ""
            C.append(f"    u{k} <- perform[1.0] (){fz}; let () = u{k};")
        if k == n or sim.pos == 'done':
            break
        before = sim.awaits
        d = sim.next()
        awaits += sim.awaits - before
        nxt = f"l{k + 1}"
        C.append(f"    o{k} <- (nu_out (force {cur})).1;")
        if d:
            RSTATS['dones'] += 1
            ans = done_ans(1000)
            C.append(f"    case o{k} {{ inl p -> {fin('p')} | inr {nxt} -> {mk.close_fin(nxt, '7')} }}")
            closed = True
            break
        C.append(f"    case o{k} {{ inl p -> {fin('p', '7')} | inr {nxt} ->")
        depth += 1
        cur = nxt
    if not closed:
        if sim.pos == 'done':
            ans = done_ans(100)
            RSTATS['dones'] += 1
        else:
            before = sim.awaits
            ans = (sim.close() * 100 + sim.cell) % M32
            awaits += sim.awaits - before
        C.append(f"    {mk.close_fin(cur, '100')}")
    C.append("    " + "}" * depth)
    L.append("\n".join(C) + "\n")
    # `main`'s plan: P steps then cancel, or awaits + 1 steps to the end.
    P = r.randint(0, awaits + 1)
    second = r.random() < 0.5
    if second:
        RSTATS['second'] += 1
        L.append(mk.mk_def("mkd", 100, mk.lend_mut("x", 10, 100000, False), False))
    M = ["main : F i32 =", "  tk0 <- " + mk.task_h("    cg <- return (unbang cons); z <- return (); force cg z") + ";"]
    sec = 0
    if second:
        M.append("  g2 <- return (unbang mkd); z2 <- return (); m0 <- force g2 z2;")
        sec_cur = "m0"
    CAN = 9

    def end_second(val):
        if not second:
            return f"return {val}"
        return f"q8 <- (nu_out (force {sec_cur})).2; let (c8, v8) = q8; w8 <- return (free[i32] c8); return (plus ({val}, plus (v8, w8)))"
    steps = P if P <= awaits else awaits + 1
    depth = 0
    for i in range(steps):
        tk, tn = f"tk{i}", f"tk{i + 1}"
        if second and r.random() < 0.6:
            sec += 1
            mo, mn = f"mo{i}", f"m{i + 1}"
            M.append(f"  {mo} <- (nu_out (force {sec_cur})).1;")
            M.append(f"  case {mo} {{ inl p -> c9 <- (nu_out (force {tk})).2; let () = c9; {fin('p')} | inr {mn} ->")
            depth += 1
            sec_cur = mn
        M.append(f"  s{i} <- (nu_out (force {tk})).1;")
        last = (P > awaits and i == steps - 1)
        if last:
            M.append(f"  case s{i} {{ inl v -> {end_second('v')} | inr {tn} -> c9 <- (nu_out (force {tn})).2; let () = c9; {end_second('i32[0]')} }}")
        else:
            M.append(f"  case s{i} {{ inl v -> {end_second('v')} | inr {tn} ->")
            depth += 1
    if P <= awaits:
        RSTATS['cancels'] += 1
        # The consumer does not `await` itself when the loop does: a cancel before its end stops
        # inside a turn of the loop (or of its close), the lend open.
        RSTATS['cancel_in_loop'] += aw and P < awaits
        RSTATS['derived_drop_cancelled'] += (not finz) and (not aw) and P < awaits and any(cons_aw)
        M.append(f"  c9 <- (nu_out (force tk{steps})).2; let () = c9; {end_second(str(CAN))}")
        total = CAN
    else:
        total = ans
    M.append("  " + "}" * depth)
    if second:
        total = (total + 2 * (100 + 10 * (1 + sec))) % M32
    L.append("\n".join(M) + "\n")
    return "\n".join(L), total

# ---------------------------------------------------------------------------------------------
# DEPTH=d (round 5): R1 lends nested to depth d (d = 1..5, or `mix` for a random depth per task),
# each level a cell holding the view of the level above lent again (a view of a view …), awaits,
# writes, pairs and closures across awaits at every level, an independent sibling lend at some
# levels, an error raised at a random level and point, and a random schedule of steps and
# cancellations from `main`. ESCAPE (default): the error's handler is outside the outermost lend,
# so the error crosses every lend between (error escape, `Row.ResumeOCE`). WORK=1: the workaround
# with no new rule: each lend's body is under its own `to_result`, its error returned as data
# (`i32 + i32`) and re-raised after the lend ends, so no abortive operation crosses a lend.

DSTATS = {'programs': 0, 'tasks': 0, 'depth': {}, 'raise_depth': {}, 'raises': 0, 'cancels': 0,
          'cancel_depth': {}, 'unfinished': 0, 'awaits_depth': {}, 'siblings': 0}


def _bump(d, k):
    d[k] = d.get(k, 0) + 1


def depth_program(seed, D, work=False):
    r = random.Random(seed)
    g = Gen(r)
    nt = r.randint(2, 4)
    out = [f"-- Stress (round 5, DEPTH={D}{', WORK=1' if work else ''}, seed {seed}): nested R1 lends "
           "with error escape; see gen.py.", "include async", "include fail", "",
           "fn done(v: i32) -> Task[i32] = with spawn { v }",
           "fn step(t: Task[i32]) -> Task[i32] = match resume(t) { inl v -> done(v) | inr t2 -> t2 }",
           "fn fin(t: Task[i32]) -> i32 = match resume(t) { inl v -> v | inr t2 -> cancel(t2); 0 - 1 }", ""]
    DSTATS['programs'] += 1
    awaits, vals, adepth = [], [], []
    for ti in range(nt):
        d = D if D > 0 else r.randint(1, 5)
        DSTATS['tasks'] += 1
        _bump(DSTATS['depth'], d)
        init = r.randint(1, 100)
        st = [init]
        ev = []                      # execution order: ('a', level) for an await, ('r', e, level)
        dead = [False]
        rl = r.choice([None, None, r.randrange(d)])         # the level that raises
        rpos = r.choice(['pre', 'post'])
        e_val = r.randint(1, 9)

        def ops(view, j):
            """Straight-line operations at level j (awaits, writes, pairs, closures)."""
            budget = [r.randint(1, 4)]
            b, a, v = g.body(view, j, st if not dead[0] else [0], budget, 0)
            if not dead[0]:
                ev.extend([('a', j)] * a)
            return b, v

        def raise_here(j):
            if dead[0]:
                return []
            dead[0] = True
            ev.append(('r', e_val, j))
            return [f"if true {{ raise({e_val}) }} else {{ () }};"]

        def level(view, j):
            L, v = ops(view, j)
            if rl == j and rpos == 'pre':
                L += raise_here(j)
            if j < d - 1:
                dd, w, v2, inner = g.fresh("d"), g.fresh("w"), g.fresh("v"), g.fresh("n")
                saved = st[0]
                IB, iv = level(inner, j + 1)
                if work:
                    IB = IB + [g.read(iv, j + 1)]
                    L.append(f"let {dd} = alloc({v});")
                    L.append(f"let {w} : i32 + i32 = borrow mut {dd} {{ {inner} -> with to_result[i32, i32] {{")
                    L += ["  " + l for l in IB]
                    L.append("} };")
                    L.append(f"let {v2} = free({dd});")
                    w2 = g.fresh("w")
                    L.append(f"let {w2} = match {w} {{ inl x -> x | inr e -> raise(e) }};")
                    L.append(g.update(v2, j, "+", w2) + ";")
                else:
                    L.append(f"let {dd} = alloc({v});")
                    L.append(f"let {w} : i32 = borrow mut {dd} {{ {inner} ->")
                    L += ["  " + l for l in IB]
                    L.append("  " + g.read(iv, j + 1))
                    L.append("};")
                    L.append(f"let {v2} = free({dd});")
                    L.append(g.update(v2, j, "+", w) + ";")
                if not dead[0]:
                    st[0] = (st[0] + st[0]) % M32
                v = v2
            if r.random() < 0.3:
                # an independent sibling lend of a fresh integer cell at this level
                DSTATS['siblings'] += 1
                sd, sw, se, sn = g.fresh("d"), g.fresh("w"), g.fresh("e"), g.fresh("n")
                si = r.randint(1, 50)
                sub = [si]
                sb, sa, sv = g.body(sn, 0, sub if not dead[0] else [0], [r.randint(1, 3)], 0)
                L.append(f"let {sd} = alloc({si});")
                L.append(f"let {sw} : i32 = borrow mut {sd} {{ {sn} ->")
                L += ["  " + l for l in sb]
                L.append("  " + g.read(sv, 0))
                L.append("};")
                L.append(f"let {se} = free({sd});")
                L.append(g.update(v, j, "+", f"{sw} + {se}") + ";")
                if not dead[0]:
                    ev.extend([('a', j + 1)] * sa)
                    st[0] = (st[0] + 2 * sub[0]) % M32
            L2, v = ops(v, j)
            L += L2
            if rl == j and rpos == 'post':
                L += raise_here(j)
            return L, v

        m = g.fresh("m")
        B, v = level(m, 0)
        row = "Async" if work else "Async, Fail[i32]"
        out.append(f"fn body{ti}() -> i32 with {row} =")
        out.append(f"  let c = alloc({init});")
        if work:
            out.append(f"  let r : i32 + i32 = borrow mut c {{ {m} -> with to_result[i32, i32] {{")
            out += ["    " + l for l in B]
            out.append("    " + g.read(v, 0))
            out.append("  } };")
            out.append("  let _ = free(c);")
            out.append("  match r { inl x -> x | inr e -> 0 - e }")
            out.append("")
            out.append(f"fn task{ti}() -> i32 with Async = body{ti}()")
        else:
            out.append(f"  let r : i32 = borrow mut c {{ {m} ->")
            out += ["    " + l for l in B]
            out.append("    " + g.read(v, 0))
            out.append("  };")
            out.append("  let _ = free(c);")
            out.append("  r")
            out.append("")
            out.append(f"fn task{ti}() -> i32 with Async = match with to_result[i32, i32] {{ body{ti}() }} {{ inl v -> v | inr e -> 0 - e }}")
        out.append("")
        na = sum(1 for x in ev if x[0] == 'a')
        rs = [x for x in ev if x[0] == 'r']
        if rs:
            DSTATS['raises'] += 1
            _bump(DSTATS['raise_depth'], rs[0][2] + 1)
            vals.append((-rs[0][1]) % M32)
        else:
            vals.append(st[0])
        awaits.append(na)
        adepth.append([x[1] + 1 for x in ev if x[0] == 'a'])
        for x in ev:
            if x[0] == 'a':
                _bump(DSTATS['awaits_depth'], x[1] + 1)
    main = ["main -> i32 ="]
    for i in range(nt):
        main.append(f"  let t{i} = with spawn {{ task{i}() }};")
    pos = [0] * nt
    live = [True] * nt
    result = [0] * nt
    for _ in range(r.randint(nt, 6 * nt)):
        i = r.randrange(nt)
        if not live[i]:
            continue
        if r.random() < 0.12:
            main.append(f"  cancel(t{i});")
            live[i] = False
            DSTATS['cancels'] += 1
            # the depth the task is stopped at: its pos-th await's level (or done)
            if pos[i] < awaits[i]:
                _bump(DSTATS['cancel_depth'], adepth[i][pos[i]])
            else:
                _bump(DSTATS['cancel_depth'], 0)
        else:
            main.append(f"  let t{i} = step(t{i});")
            pos[i] += 1
    for i in range(nt):
        if not live[i]:
            continue
        if r.random() < 0.3:
            main.append(f"  let v{i} = fin(t{i});")
            if pos[i] >= awaits[i]:
                result[i] = vals[i]
            else:
                result[i] = (-1) % M32
                DSTATS['unfinished'] += 1
                _bump(DSTATS['cancel_depth'], adepth[i][pos[i]])
        else:
            for _ in range(max(0, awaits[i] - pos[i])):
                main.append(f"  let t{i} = step(t{i});")
            main.append(f"  let v{i} = fin(t{i});")
            result[i] = vals[i]
        live[i] = None
    terms, total = [], 0
    for i in range(nt):
        if live[i] is None:
            terms.append(f"v{i} * {i + 1}")
            total = (total + result[i] * (i + 1)) % M32
    main.append("  " + (" + ".join(terms) if terms else "0"))
    out += main
    return "\n".join(out) + "\n", total


def main():
    outdir, first, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(outdir, exist_ok=True)
    for s in range(first, first + count):
        if os.environ.get("NURSERY") == "1":
            src, total = nursery_program(s)
        elif os.environ.get("TICK") == "1":
            src, total = tick_program(s)
        elif os.environ.get("REIFY") == "1":
            src, total = reify_program(s)
        elif os.environ.get("DEPTH"):
            dv = os.environ["DEPTH"]
            src, total = depth_program(s, 0 if dv == "mix" else int(dv), os.environ.get("WORK") == "1")
        else:
            src, total = program(s, os.environ.get("WIDE") == "1")
        with open(os.path.join(outdir, f"s{s:04d}.bc"), "w") as f:
            f.write(src)
        with open(os.path.join(outdir, f"s{s:04d}.expect"), "w") as f:
            f.write(f"i32[{total}]\nlive 0\n")
    if os.environ.get("NURSERY") == "1":
        print("nursery stats:", STATS)
    if os.environ.get("REIFY") == "1":
        print("reify stats:", RSTATS)
    if os.environ.get("DEPTH"):
        print("depth stats:", DSTATS)


if __name__ == "__main__":
    main()
