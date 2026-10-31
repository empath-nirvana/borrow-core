#!/usr/bin/env python3
"""Round 5 (#743 spike), the core text at depth: a nursery (W-hold over `req`, its children
spawned with `spawn_in` holding copies of the `imm` view, its wait a `Div` loop whose turns
`await` cancellably, #750's `9.0 lin 1 ~> 1 + 1` under `[await-c]`) inside D - 1 W-tick lends
(`withbor2rt` `mut` or `withbor1rt` `imm`, each of a cell allocated inside the level above), each
level awaiting the scheduler `8.0` before lending the next and writing (`mut`) or reading (`imm`)
its view after. MODE: `normal` (the waits are answered `inl ()`), `cancel` (the nursery's first
`await` is answered `inr ()`: `cancelled` crosses every lend), `error` (the wait raises `3.0` at
its first turn with a child pending: the error crosses every lend). Every finaliser frees its
place; the answer is simulated.

    gen_r5core.py OUTDIR
"""
import os
import random
import sys

TICK = "4294967295.0 lin 1 ~> 1 + 1"
ROW = f"[{TICK}, 8.0 cancel 1 ~> 1, 9.0 lin 1 ~> 1 + 1, 9.1 cancel 1 ~> 0, 3.0 cancel i32 ~> 0]"
OUTR = "[8.0 cancel 1 ~> 1, 9.0 lin 1 ~> 1 + 1, 9.1 cancel 1 ~> 0, 3.0 cancel i32 ~> 0]"
R83 = "[8.0 cancel 1 ~> 1, 3.0 cancel i32 ~> 0]"
R3 = "[3.0 cancel i32 ~> 0]"
Q = "QueueIn[i32]<'r_n /\\ 'r /\\ top>"

LIB = """include async

fn child<'r>(k: imm 'r i32, n: i32, w: i32) -> i32 with Async =
  let a = *k;
  for _ in 0..w { await() };
  a * n

fn start<'r, 'n < 'r>(k1: imm 'r i32, k2: imm 'r i32) -> QueueIn[i32]<'n /\\ 'r /\\ top> =
  let q = queue_in[i32]['n /\\ 'r /\\ top]();
  let t1 = with spawn_in { child(k1, 2, W1) };
  let q = push_in[i32]['n /\\ 'r /\\ top](q, t1);
  let t2 = with spawn_in { child(k2, 3, W2) };
  push_in[i32]['n /\\ 'r /\\ top](q, t2)

fn one_round<'n>(q: QueueIn[i32]<'n>) -> QueueIn[i32]<'n> * (1 + 1) =
  let (n, s) = q;
  let (b, p) = round_in(n, rev_in(n, s));
  ((n, rev_in(n, b)), p)

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

fn rd<'r>(k: imm 'r i32) -> i32 = *k

def plus : i32 * i32 => i32 = unbang host[add32]
"""


def nursery(mode, ind):
    fin = f"cf <- return ((unbang cancel_all) ['r_n /\\ 'r /\\ top]); force cf"
    err = "" if mode != "error" else f"""
              z <- abort[3.0] i32[13] unwind ({fin} q2);"""
    L = f"""withbor1rh['r, dom, i32, i32, {ROW}](req, k) (
  kk <- return (copy['r, i32] k);
  let (k1, k) = kk;
  kk2 <- return (copy['r, i32] k);
  let (k2, k) = kk2;
  sf <- return ((unbang start) ['r] ['r_n]);
  a2 <- return (k1, k2);
  q0 <- force sf a2;
  st <- return ((!thunkv fun (q : {Q}) ->
    < u <- perform[9.0] () unwind ({fin} q);
      let () = u;
      rf <- return ((unbang one_round) ['r_n /\\ 'r /\\ top]);
      o <- force rf q;
      let (q2, p) = o;
      case p {{
        inl done -> ff <- return ((unbang finish) ['r_n /\\ 'r /\\ top]); s <- force ff q2; return (inl s)
      | inr more -> let () = more;{err}
          return (inr q2)
      }},
      ff <- return ((unbang finish) ['r_n /\\ 'r /\\ top]); force ff q >) :
      !U ({Q} -o F{ROW} (i32 + {Q}) & F{ROW} i32));
  f <- return (unbang div_iterate[{ROW}, {Q}, i32, i32]);
  a0 <- return (st, q0);
  o <- force f a0;
  s <- (case o {{ inl b -> return b | inr z -> return z }});
  y <- return ((unbang rd) ['r] k);
  x <- return (plus (s, y));
  return (boxed['r] x))"""
    return "\n".join(ind + l for l in L.split("\n"))


def program(seed, D, mode):
    r = random.Random(seed)
    w1, w2 = r.randint(1, 3), r.randint(1, 3)
    if mode == "error" and max(w1, w2) == 1:
        w2 = 2                                   # a child pending at the first turn
    kinds = [r.choice(["mut", "imm"]) for _ in range(D - 1)]
    inits = [r.randint(1, 50) for _ in range(D - 1)]
    src = LIB.replace("W1", str(w1)).replace("W2", str(w2))
    # the innermost level: the nursery; its value s + 7, s = 14 + 21 (both finish) when normal
    turns = max(w1, w2)
    val = (14 + 21 + 7)
    hdr = [f"-- Round 5 core-text depth stress (gen_r5core.py, seed {seed}): depth {D}, mode {mode},",
           f"-- levels {' '.join(kinds)} + nursery; children await {w1} and {w2} times."]
    # build from the inside out
    req_init = 7
    body = nursery(mode, "")
    for lv in reversed(range(D - 1)):
        x = f"'x{lv}"
        m = f"m{lv}"
        ref = f"o{lv + 1}" if lv + 1 < D - 1 else "req"
        init = inits[lv + 1] if lv + 1 < D - 1 else req_init
        kw = "withbor2rt" if kinds[lv] == "mut" else "withbor1rt"
        if kinds[lv] == "mut":
            after = f"""q{lv} <- return (withswap[{x}, i32, 1] {m} (thunkv fun (v : i32) -> return (plus (v, i32[1]), ())));
let ({m}, z{lv}) = q{lv};
let () = z{lv};
let () = forget_mut[{x}, i32] {m};
x{lv} <- return (plus (s{lv}, i32[1]));"""
        else:
            after = f"""y{lv} <- return ((unbang rd) [{x}] {m});
x{lv} <- return (plus (s{lv}, y{lv}));"""
        inner = "\n".join("    " + l for l in body.split("\n"))
        body = f"""{kw}[{x}, dom, i32, i32, {ROW}](o{lv}, {m}) (
  u{lv} <- perform[8.0] ();
  let () = u{lv};
  {ref} <- return (alloc[i32] i32[{init}]);
  r{lv} <- (
{inner});
  let ({ref}, s{lv}) = r{lv};
  w{lv} <- return (free[i32] {ref});
""" + "\n".join("  " + l for l in after.split("\n")) + f"""
  return (boxed[{x}] x{lv}))"""
    for lv in reversed(range(D - 1)):
        if kinds[lv] == "mut":
            val = val + 1
        else:
            val = val + inits[lv]
    top_ref = "o0" if D > 1 else "req"
    top_init = inits[0] if D > 1 else req_init
    ans = {"normal": val, "cancel": 5, "error": 1013}[mode]
    hdr.append(f"-- Answer: i32[{ans}]; live 0.")
    ins9 = "inl ()" if mode != "cancel" else "inr ()"
    main = f"""main : F i32 =
  {top_ref} <- return (alloc[i32] i32[{top_init}]);
  t <- return (thunkv fun (u0 : 1) ->
{chr(10).join('    ' + l for l in body.split(chr(10)))});
  handle_with[3](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (e : i32) -> return (plus (e, i32[1000]))) : !U (i32 -o F i32)), ())) (
  handle_with[8](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F{R3} i32)),
      (((!thunkv fun (q : 1 * U ((1 -o F{R3} i32) & F{R3} 1)) ->
        let (x, k) = q; (force k).1 x), ()) :
        !U (1 * U ((1 -o F{R3} i32) & F{R3} 1) -o F{R3} i32) * 1)) (
  handle_with[9](
      ((!thunkv fun (p : ref i32 * i32) ->
        let (c, v) = p; w <- return (free[i32] c); return v) : !U (ref i32 * i32 -o F{R83} i32)),
      (((!thunkv fun (q : 1 * U ((1 + 1 -o F{R83} i32) & top)) ->
          let (x, k) = q; let () = x; w <- return ({ins9} : 1 + 1); (force k).1 w) :
          !U (1 * U ((1 + 1 -o F{R83} i32) & top) -o F{R83} i32)),
       (((!thunkv fun (e : 1) -> let () = e; return i32[5]) : !U (1 -o F{R83} i32)), ()))) (
    df <- return (unbang div_fuel_k[{OUTR}, ref i32 * i32]);
    a1 <- return (t, i32[100]);
    force df a1)))
"""
    return "\n".join(hdr) + "\n" + src + "\n" + main, ans


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    seed = 0
    for D in range(1, 6):
        for mode in ["normal", "cancel", "error"]:
            for rep in range(4):
                seed += 1
                src, ans = program(seed, D, mode)
                with open(os.path.join(out, f"s{seed:04d}.bc"), "w") as f:
                    f.write(src)
                with open(os.path.join(out, f"s{seed:04d}.expect"), "w") as f:
                    f.write(f"i32[{ans}]\nlive 0\n")


if __name__ == "__main__":
    main()
