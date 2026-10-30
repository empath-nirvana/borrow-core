#!/usr/bin/env python3
"""The stress generator for R2 (`lend_loop_r`, `CDerivesP.lendLoopR`), for the #743 spike.

Each seed gives one core-text program: one to four R2 loops, each over its own cell, whose state
`(imm 'x i32 + 1) * ((imm 'x i32 + 1) * i32)` keeps up to two views from earlier observations
(the policy `keep`: 0, 1 or 2 slots), reading every kept view and a copy of the fresh one at each
observation. `main` interleaves the loops' observations in a random order, closes each after a
random number of observations, and answers the weighted sum of the close steps' totals. The
generator simulates the program and writes the answer to `<name>.expect`.

With `CANCEL=1`, `main` is handled by `1` (a handler that cancels, or one that resumes, chosen by
the seed), `perform[1.0]` (cancellable) is placed at random points between observations while
loops whose states hold views are live, each with or without a finaliser that closes every live
loop, and a loop may be abandoned instead of closed (left to its derived drop, which closes it).
A cancel answers `inl` the first operation's argument; otherwise `inr` the sum.

    [CANCEL=1] gen_r2.py OUTDIR FIRST_SEED COUNT
"""
import os
import random
import sys

M32 = 1 << 32
READ = ("withload['x, 'z, i32, i32] {} (thunkv Fun 'z < dom. return (thunkv fun (y : i32) -> "
        "return (boxed['z] y)))")
S_TY = "(imm 'x i32 + 1) * ((imm 'x i32 + 1) * i32)"


def forget(e):
    return (f"(case {e} {{ inl o -> u <- return (forget_imm['x, i32] o); let () = u; return () "
            f"| inr u -> let () = u; return () }})")


def next_step(keep):
    if keep == 2:
        new1, new2, drop = "inl v2", "t1", ""
    elif keep == 1:
        new1, new2, drop = "inl v2", "inr ()", f"      z <- {forget('t1')}; let () = z;\n"
    else:
        new1, new2 = "inr ()", "inr ()"
        drop = (f"      z <- {forget('t1')}; let () = z;\n"
                "      z2 <- return (forget_imm['x, i32] v2); let () = z2;\n")
    return f"""(thunkv
      let (v, s) = q;
      let (s1, rest) = s;
      let (s2, acc) = rest;
      w <- return (copy['x, i32] v);
      let (v1, v2) = w;
      a <- return ({READ.format('v1')});
      p1 : (imm 'x i32 + 1) * i32 <- (case s1 {{
        inl o -> w2 <- return (copy['x, i32] o); let (o1, o2) = w2;
          r <- return ({READ.format('o1')}); return (inl o2, r)
      | inr u -> let () = u; return (inr (), i32[0]) }});
      let (t1, b) = p1;
      c <- (case s2 {{ inl o -> return ({READ.format('o')}) | inr u -> let () = u; return i32[0] }});
{drop}      return (inr ({new1}, ({new2}, add (acc, add (a, add (b, c)))))))"""


CLOSE = f"""(thunkv ((
      let (v, s) = q;
      let (s1, rest) = s;
      let (s2, acc) = rest;
      a <- return ({READ.format('v')});
      b <- (case s1 {{ inl o -> return ({READ.format('o')}) | inr u -> let () = u; return i32[0] }});
      c <- (case s2 {{ inl o -> return ({READ.format('o')}) | inr u -> let () = u; return i32[0] }});
      return (add (acc, add (a, add (b, c))))) : F i32))"""


def loop_term(r, keep):
    ll = (f"lend_loop_r['x, top, i32, 1, []]({r}, q) return (\n    {next_step(keep)},\n"
          f"    ({CLOSE},\n     ((inr (), (inr (), i32[0])) : {S_TY})))")
    return f"thunkv nu_in <\n  (nu_out ({ll})).1,\n  (nu_out ({ll})).2 >"


def reads(keep, k):
    """The views read at observation `k` (1-based) of a loop of policy `keep`; `close` reads the
    fresh view and what the state holds after `k - 1` observations."""
    return 1 + (1 if keep >= 1 and k >= 2 else 0) + (1 if keep >= 2 and k >= 3 else 0)


CANCEL = os.environ.get("CANCEL") == "1"
HANDLER_TY = "U ((1 -o F (i32 + i32)) & F 1)"


def handler(cancel):
    clause = ("u <- (force k).2; return (inl x)" if cancel
              else "u <- return (); (force k).1 u")
    return ("  handle_with[1](\n"
            "      ((!thunkv fun (v : i32) -> return (inr v)) : !U (i32 -o F (i32 + i32))),\n"
            f"      (((!thunkv fun (q : i32 * {HANDLER_TY}) ->\n"
            f"        let (x, k) = q; {clause}), ()) : "
            f"!U (i32 * {HANDLER_TY} -o F (i32 + i32)) * 1)) (")


def program(seed):
    r = random.Random(seed)
    nl = r.randint(1, 4)
    vals = [r.randint(1, 50) for _ in range(nl)]
    keeps = [r.randint(0, 2) for _ in range(nl)]
    nobs = [r.randint(0, 6) for _ in range(nl)]
    events = [i for i in range(nl) for _ in range(nobs[i])] + [("c", i) for i in range(nl)]
    # a random interleaving in which each loop's close comes after its observations
    order, left, closed = [], list(nobs), [False] * nl
    pending = list(range(nl))
    while pending:
        i = r.choice(pending)
        if left[i] > 0:
            order.append(("n", i)); left[i] -= 1
        else:
            order.append(("c", i)); pending.remove(i)
    abandon = [CANCEL and r.random() < 0.3 for _ in range(nl)]
    cancel = CANCEL and r.random() < 0.5
    # performs: before event j with probability 0.3, each with or without a finaliser
    perf = {j: (r.randint(1, 99), r.random() < 0.5) for j in range(len(order))
            if CANCEL and r.random() < 0.3}
    totals = []
    for i in range(nl):
        k = nobs[i]
        t = sum(reads(keeps[i], j) for j in range(1, k + 1)) + reads(keeps[i], k + 1)
        totals.append(0 if abandon[i] else t * vals[i] % M32)
    expect = sum(t * (i + 1) for i, t in enumerate(totals)) % M32
    out = [f"-- Generated by experiments/Spike743/stress/gen_r2.py, seed {seed}: loops {nl}, "
           f"cells {vals}, keep {keeps}, observations {nobs}.",
           "def add : i32 * i32 => i32 = unbang host[add32]",
           "def mul : i32 * i32 => i32 = unbang host[mul32]", "",
           "type ULp = U (loop (ref i32 * 1) (ref i32 * i32))", "",
           "main : F (i32 + i32) =" if CANCEL else "main : F i32 ="]
    if CANCEL:
        out[0] += f" cancel {cancel}, abandon {abandon}, performs {perf}."
        out.append(handler(cancel))
    for i in range(nl):
        out.append(f"  r{i} <- return (alloc[i32] i32[{vals[i]}]);")
        out.append(f"  l{i}_0 : ULp <- return ({loop_term(f'r{i}', keeps[i])});")
    cnt = [0] * nl
    live = set(range(nl))
    acc = "i32[0]"
    k = [0]

    def fresh(b):
        k[0] += 1
        return f"{b}{k[0]}"

    def close_others(ind, skip):
        lines = []
        for j in sorted(live):
            if j == skip:
                continue
            q, rr, t, x = fresh("q"), fresh("rr"), fresh("t"), fresh("x")
            lines.append(f"{ind}{q} <- (nu_out (force l{j}_{cnt[j]})).2; let ({rr}, {t}) = {q}; "
                         f"{x} <- return (free[i32] {rr});")
        return lines

    body, ind, closes = [], "  ", 0
    first_perf = None
    for j, (ev, i) in enumerate(order):
        if j in perf:
            arg, fin = perf[j]
            if first_perf is None:
                first_perf = arg
            if fin and live:
                fl = []
                for jj in sorted(live):
                    q, rr, t, x = fresh("q"), fresh("rr"), fresh("t"), fresh("x")
                    fl.append(f"{q} <- (nu_out (force l{jj}_{cnt[jj]})).2; let ({rr}, {t}) = {q}; "
                              f"{x} <- return (free[i32] {rr});")
                body.append(f"{ind}pu{j} <- perform[1.0] i32[{arg}] unwind (" + " ".join(fl)
                            + " return ());")
            else:
                body.append(f"{ind}pu{j} <- perform[1.0] i32[{arg}];")
            body.append(f"{ind}let () = pu{j};")
        if ev == "c" and abandon[i]:
            live.discard(i)
            continue
        if ev == "n":
            o = fresh("o")
            body.append(f"{ind}{o} <- (nu_out (force l{i}_{cnt[i]})).1;")
            body.append(f"{ind}case {o} {{")
            p, rr, u, x = fresh("p"), fresh("rr"), fresh("uw"), fresh("x")
            body.append(f"{ind}  inl {p} -> let ({rr}, {u}) = {p}; let () = {u}; "
                        f"{x} <- return (free[i32] {rr});")
            body += close_others(ind + "    ", i)
            body.append(f"{ind}    return i32[0]")
            cnt[i] += 1
            body.append(f"{ind}| inr l{i}_{cnt[i]} ->")
            ind += "  "
            closes += 1
        else:
            q, rr, t, x, a = fresh("q"), fresh("rr"), fresh("t"), fresh("x"), fresh("a")
            body.append(f"{ind}{q} <- (nu_out (force l{i}_{cnt[i]})).2; let ({rr}, {t}) = {q}; "
                        f"{x} <- return (free[i32] {rr});")
            body.append(f"{ind}{a} <- return (add ({acc}, mul ({t}, i32[{i + 1}])));")
            acc = a
            live.discard(i)
    body.append(f"{ind}return {acc}" + " }" * closes + (")" if CANCEL else ""))
    out += body
    if CANCEL:
        answer = f"inl i32[{first_perf}]" if (cancel and first_perf is not None) else f"inr i32[{expect}]"
    else:
        answer = f"i32[{expect}]"
    return "\n".join(out) + "\n", answer


def main():
    outdir, first, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    os.makedirs(outdir, exist_ok=True)
    for s in range(first, first + count):
        src, total = program(s)
        with open(os.path.join(outdir, f"s{s:04d}.bc"), "w") as f:
            f.write(src)
        with open(os.path.join(outdir, f"s{s:04d}.expect"), "w") as f:
            f.write(f"{total}\nlive 0\n")


if __name__ == "__main__":
    main()
