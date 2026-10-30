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
    def __init__(self, rnd):
        self.r = rnd
        self.k = 0

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
            elif c < 0.88 and nest > 0:
                # a nested relaxed lend of a cell holding this view
                d, w, v2, inner = self.fresh("d"), self.fresh("w"), self.fresh("v"), self.fresh("n")
                ib, ia, iv = self.body(inner, depth + 1, st, budget, nest - 1)
                lines.append(f"let {d} = alloc({view});")
                lines.append(f"let {w} = borrow mut {d} {{ {inner} ->")
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
                lines.append(f"let {w} = borrow mut {d} {{ {inner} ->")
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
                 f"  let r = borrow mut c {{ {m} ->"]
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


def program(seed):
    r = random.Random(seed)
    g = Gen(r)
    nt = r.randint(2, 5)
    out = ["-- Generated by experiments/Spike743/stress/gen.py, seed %d." % seed,
           "include async", "include fail", "",
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


def main():
    outdir, first, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(outdir, exist_ok=True)
    for s in range(first, first + count):
        src, total = program(s)
        with open(os.path.join(outdir, f"s{s:04d}.bc"), "w") as f:
            f.write(src)
        with open(os.path.join(outdir, f"s{s:04d}.expect"), "w") as f:
            f.write(f"i32[{total}]\nlive 0\n")


if __name__ == "__main__":
    main()
