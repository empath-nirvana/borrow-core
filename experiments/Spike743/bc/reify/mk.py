"""Round 4's hand programs (W-tick under `reify`), written from shared pieces: python3 mk.py."""
import os

TICK = "4294967295.0 lin 1 ~> 1 + 1"
AW = "1.0 cancel 1 ~> 1"
P = "ref i32 * i32"


def ops(aw):
    """The non-tick operations of a row: `aw` is a bool (`await` `1.0` or none) or a list."""
    if isinstance(aw, list):
        return aw
    return [AW] if aw else []


def trow(aw):
    return "[" + ", ".join([TICK] + ops(aw)) + "]"


def srow(aw):
    return "[" + ", ".join(ops(aw)) + "]"


def F(row):
    return "F" if row == "[]" else f"F{row}"


def loopt(aw):
    s = F(srow(aw))
    return f"U (nu X. {s} (({P}) + U X) & {s} ({P}))"


PRE = """fn rd<'r>(k: imm 'r i32) -> i32 = *k

def plus : i32 * i32 => i32 = unbang host[add32]
def mul : i32 * i32 => i32 = unbang host[mul32]
def lt : i32 * i32 => 1 + 1 = unbang host[lt_s32]
def eq : i32 * i32 => 1 + 1 = unbang host[eq32]

"""


def lend_mut(x, inc, lim, aw, mark=None, inner=None, ind="      "):
    """A `mut` W-tick lend of `c` as `m`: each turn adds `inc` through the view, awaits when `aw`
    (its finaliser writing `mark` through the view when given), runs `inner` (a computation of
    `i32`, added too) when given, and finishes once the cell reaches `lim`; its close step reads
    the cell. The lend answers `i32 + i32`: `inl` finished, `inr` closed."""
    T = trow(aw)
    L = [f"withbor2rt['{x}, dom, i32, i32 + i32, {T}](c, m) ("]
    L.append(f"  st <- return ((!thunkv fun (v : mut '{x} i32) ->")
    if inner:
        L.append(f"    < ig <- return (unbang {inner}); z0 <- return (); iv <- force ig z0;")
        L.append(f"      q <- return (withswap['{x}, i32, i32] v (thunkv fun (a : i32) -> return (plus (a, plus (iv, i32[{inc}])), plus (a, plus (iv, i32[{inc}])))));")
    else:
        L.append(f"    < q <- return (withswap['{x}, i32, i32] v (thunkv fun (a : i32) -> return (plus (a, i32[{inc}]), plus (a, i32[{inc}]))));")
    L.append("      let (v, r) = q;")
    if AW in ops(aw):
        if mark is None:
            L.append("      u <- perform[1.0] ();")
        else:
            L.append("      u <- perform[1.0] () unwind (")
            L.append(f"        q9 <- return (withswap['{x}, i32, 1] v (thunkv fun (z : i32) -> return (i32[{mark}], ())));")
            L.append(f"        let (v, z9) = q9; let () = z9; return (forget_mut['{x}, i32] v));")
        L.append("      let () = u;")
    L.append(f"      g <- return (lt (r, i32[{lim}]));")
    L.append(f"      case g {{ inl ge -> let () = forget_mut['{x}, i32] v; return (inl r) | inr lo -> return (inr v) }},")
    L.append(f"      q2 <- return (withswap['{x}, i32, i32] v (thunkv fun (a : i32) -> return (a, a)));")
    L.append(f"      let (v, r2) = q2; let () = forget_mut['{x}, i32] v; return r2 >) :")
    L.append(f"      !U (mut '{x} i32 -o {F(T)} (i32 + mut '{x} i32) & {F(T)} i32));")
    L.append(f"  f <- return (unbang div_iterate[{T}, mut '{x} i32, i32, i32]);")
    L.append("  a0 <- return (st, m);")
    L.append("  o <- force f a0;")
    L.append(f"  case o {{ inl b -> return (boxed['{x}] (inl b)) | inr z -> return (boxed['{x}] (inr z)) }})")
    return ("\n" + ind).join(L)


def lend_imm(x, lim, aw, ind="      "):
    """An `imm` W-tick lend of `c` as `m`: turn `j` reads the cell and answers cell + j; it
    finishes at `j = lim`; its close step answers 1000 + j."""
    T = trow(aw)
    St = f"imm '{x} i32 * i32"
    L = [f"withbor1rt['{x}, dom, i32, i32 + i32, {T}](c, m) ("]
    L.append(f"  st <- return ((!thunkv fun (sq : {St}) ->")
    L.append("    < let (v, j) = sq;")
    L.append(f"      cp <- return (copy['{x}, i32] v); let (v1, v) = cp;")
    L.append(f"      rv <- return ((unbang rd) ['{x}] v1);")
    L.append("      r <- return (plus (rv, j));")
    if AW in ops(aw):
        L.append("      u <- perform[1.0] (); let () = u;")
    L.append(f"      g <- return (lt (j, i32[{lim}]));")
    L.append(f"      case g {{ inl ge -> let () = forget_imm['{x}, i32] v; return (inl r) | inr lo -> return (inr (v, plus (j, i32[1]))) }},")
    L.append(f"      let (v, j) = sq; let () = forget_imm['{x}, i32] v; return (plus (i32[1000], j)) >) :")
    L.append(f"      !U ({St} -o {F(T)} (i32 + {St}) & {F(T)} i32));")
    L.append(f"  f <- return (unbang div_iterate[{T}, {St}, i32, i32]);")
    L.append("  a0 <- return (st, (m, i32[1]));")
    L.append("  o <- force f a0;")
    L.append(f"  case o {{ inl b -> return (boxed['{x}] (inl b)) | inr z -> return (boxed['{x}] (inr z)) }})")
    return ("\n" + ind).join(L)


def mk_def(name, init, lend, aw):
    """`name : !U(1 -o F_Σ Loop)`: a fresh cell `c` holding `init`, lent by `lend` inside a thunk
    that `reify_k` makes a loop value owning `c`."""
    T = trow(aw)
    S = srow(aw)
    return f"""def {name} : !U (1 -o {F(S)} {loopt(aw)}) =
  !thunkv fun (z : 1) ->
    c <- return (alloc[i32] i32[{init}]);
    t <- return ((thunkv fun (u0 : 1) ->
      p <- {lend};
      let (c, o) = p;
      case o {{ inl b -> return (inl (c, b)) | inr z -> return (inr (c, z)) }}) :
      U (1 -o {F(T)} (({P}) + ({P}))));
    rf <- return (unbang reify_k[{S}, {P}]);
    force rf t
"""


# The await handler that resumes at once, answering `i32`.
def aw_now(body, ind="  "):
    return f"""handle_with[1](
{ind}    ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
{ind}    (((!thunkv fun (q : 1 * U ((1 -o F i32) & F 1)) ->
{ind}      let (x, k) = q; (force k).1 x), ()) : !U (1 * U ((1 -o F i32) & F 1) -o F i32) * 1)) (
{body})"""


def fin(p, scale="1000"):
    """Free the cell of the pair `p = (c, v)` and answer v * scale + cell."""
    return f"let (c, v) = {p}; w <- return (free[i32] c); return (plus (mul (v, i32[{scale}]), w))"


FILES = {}

# ---------------------------------------------------------------------------------------------
FILES["r1b-imm-await-to-done"] = ("""-- R1 (round 4): an `imm` W-tick lend reified, its turns awaiting (the loop's row is `await`), the
-- consumer under an await handler that resumes at once, observing it to its end. Turn `j` reads
-- the cell (3) and answers 3 + j; the first segment (at `reify`) runs turn 1, each *next* one
-- more; turn 4 finishes, so the third *next* answers `inl (c, 7)`.
--
-- Answer: i32[7003]: 7 * 1000 + the cell's 3.
""", PRE + mk_def("mk", 3, lend_imm("x", 4, True), True) + """
main : F i32 =
  """ + aw_now("""    g <- return (unbang mk); z <- return (); l0 <- force g z;
    o1 <- (nu_out (force l0)).1;
    case o1 {
      inl p -> return i32[1]
    | inr l1 ->
        o2 <- (nu_out (force l1)).1;
        case o2 {
          inl p -> return i32[2]
        | inr l2 ->
            o3 <- (nu_out (force l2)).1;
            case o3 { inl p -> """ + fin("p") + """ | inr l3 -> q <- (nu_out (force l3)).2; let (c, v) = q; w <- return (free[i32] c); return i32[4] }
        }
    }""") + "\n")


LT0 = loopt(False)
LT1 = loopt(True)
TASK = "U (nu X. F (i32 + U X) & F 1)"
KT = "U ((1 -o F " + TASK + ") & F 1)"


def task_h(body, ind="  "):
    """The handler of `await` (`1.0`) that stores the continuation: it answers a task, the
    consumer suspended there, which `main` steps (*next*) or cancels (*close*)."""
    return f"""handle_with[1](
{ind}    ((!thunkv fun (v : i32) -> return (thunkv nu_in < return (inl v), return () >)) : !U (i32 -o F {TASK})),
{ind}    (((!thunkv fun (q : 1 * {KT}) ->
{ind}      let (x, k) = q; let () = x;
{ind}      return (thunkv nu_in < u <- return (); t <- (force k).1 u; return (inr t), (force k).2 >)), ()) :
{ind}      !U (1 * {KT} -o F {TASK}) * 1)) (
{body})"""


def close_fin(l, scale="1"):
    return f"q <- (nu_out (force {l})).2; let (c, v) = q; w <- return (free[i32] c); return (plus (mul (v, i32[{scale}]), w))"


CLOSE_UNIT = lambda l: f"q <- (nu_out (force {l})).2; let (c, v) = q; w <- return (free[i32] c); return ()"


def setm(y, val):
    return (f"q7 <- return (withswap['{y}, i32, 1] m (thunkv fun (a : i32) -> return ({val}, ()))); "
            f"let (m, u7) = q7; let () = u7; let () = forget_mut['{y}, i32] m;")


FILES["r1c-close-first-and-done"] = ("""-- R1 (round 4): closing a reified W-tick loop with no *next*, and closing one that finished in its
-- first segment. `mka`'s first segment runs turn 1 (cell 1) and stops at the tick: *close* answers
-- the tick *close*, `iterate` runs its close step (reading 1), the lend ends, and the residual is
-- `(c, 1)`. `mkb`'s first turn finishes (6 >= 3): the loop is `done (c, 6)` and *close* hands back
-- `res (c, 6)`.
--
-- Answer: i32[707]: (1 * 100 + 1) + (6 * 100 + 6).
""", PRE + mk_def("mka", 0, lend_mut("x", 1, 10, False), False)
  + mk_def("mkb", 5, lend_mut("x", 1, 3, False), False) + """
main : F i32 =
  ga <- return (unbang mka); z <- return (); la <- force ga z;
  qa <- (nu_out (force la)).2;
  let (ca, va) = qa; wa <- return (free[i32] ca);
  gb <- return (unbang mkb); z2 <- return (); lb <- force gb z2;
  qb <- (nu_out (force lb)).2;
  let (cb, vb) = qb; wb <- return (free[i32] cb);
  return (plus (plus (mul (va, i32[100]), wa), plus (mul (vb, i32[100]), wb)))
""")

FILES["r2a-stored-in-cell-observed-in-lend"] = ("""-- R2 (round 4): the reified loop is stored in a cell, the consumer lends another cell `d` (`'y`,
-- after the loop's lend opened), takes the loop out of its cell inside that lend and observes it
-- there to its end: the loop's lend ends inside `'y`'s. Turn n leaves the cell at n; the loop
-- finishes at 3 on the second *next*, and the consumer writes 3 * 10 through its view of `d`.
--
-- Answer: i32[330]: the cell's 3 (freed inside `'y`) * 100, plus `d`'s 30.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 3, False), False) + f"""
main : F i32 =
  g <- return (unbang mk); z <- return (); l0 <- force g z;
  s <- return (alloc[{LT0}] l0);
  d <- return (alloc[i32] i32[0]);
  r <- return (withbor2['y, top, i32, i32] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->
    l <- return (free[{LT0}] s);
    o1 <- (nu_out (force l)).1;
    case o1 {{
      inl p -> let (c, v) = p; w <- return (free[i32] c); {setm("y", "v")} return (boxed['y] w)
    | inr l1 ->
        o2 <- (nu_out (force l1)).1;
        case o2 {{
          inl p -> let (c, v) = p; w <- return (free[i32] c); {setm("y", "mul (v, i32[10])")} return (boxed['y] w)
        | inr l2 -> q <- (nu_out (force l2)).2; let (c, v) = q; w <- return (free[i32] c); {setm("y", "v")} return (boxed['y] (plus (w, i32[1000])))
        }}
    }})));
  let (d, x) = r;
  e <- return (free[i32] d);
  return (plus (mul (x, i32[100]), e))
""")

FILES["r2b-returned-after-owner-scope"] = ("""-- R2 (round 4): `mk2` makes the loop (its cell allocated in `mk`, whose scope has ended),
-- observes it once and returns it, with a count, through `pass`; `main` observes it twice more
-- and closes it. Turns add 2: after turns 1-4 the cell is 8 (< 9), so the close step reads 8.
--
-- Answer: i32[808]: 8 * 100 + 8, plus the count 0.
""", PRE + mk_def("mk", 0, lend_mut("x", 2, 9, False), False) + f"""
def mk2 : !U (1 -o F ({LT0} * i32)) =
  !thunkv fun (z : 1) ->
    g <- return (unbang mk); z1 <- return (); l0 <- force g z1;
    o <- (nu_out (force l0)).1;
    case o {{
      inl p -> let (c, v) = p; w <- return (free[i32] c); g2 <- return (unbang mk); z2 <- return ();
               l1 <- force g2 z2; return (l1, plus (mul (v, i32[1000]), w))
    | inr l1 -> return (l1, i32[0])
    }}

def pass : !U ({LT0} * i32 -o F ({LT0} * i32)) = !thunkv fun (p : {LT0} * i32) -> return p

main : F i32 =
  g <- return (unbang mk2); z <- return (); p0 <- force g z;
  pf <- return (unbang pass); p <- force pf p0;
  let (l, a) = p;
  o1 <- (nu_out (force l)).1;
  case o1 {{
    inl p -> {fin("p")}
  | inr l1 ->
      o2 <- (nu_out (force l1)).1;
      case o2 {{
        inl p -> {fin("p")}
      | inr l2 -> q <- (nu_out (force l2)).2; let (c, v) = q; w <- return (free[i32] c); return (plus (a, plus (mul (v, i32[100]), w)))
      }}
  }}
""")

CONS = f"""def cons : !U (1 -o F[{AW}] i32) =
  !thunkv fun (z : 1) ->
    g <- return (unbang mk); z1 <- return (); l0 <- force g z1;
    u1 <- perform[1.0] () unwind ({CLOSE_UNIT("l0")});
    let () = u1;
    o1 <- (nu_out (force l0)).1;
    case o1 {{
      inl p -> let (c, v) = p; w <- return (free[i32] c); return (plus (v, w))
    | inr l1 ->
        u2 <- perform[1.0] () unwind ({CLOSE_UNIT("l1")});
        let () = u2;
        o2 <- (nu_out (force l1)).1;
        case o2 {{
          inl p -> let (c, v) = p; w <- return (free[i32] c); return (plus (v, w))
        | inr l2 -> {close_fin("l2", "100")}
        }}
    }}
"""

FILES["r2c-task-holds-loop"] = ("""-- R2 (round 4): a consumer task holds the reified loop across its own `await`s; the handler stores
-- the consumer's continuation (a task), and `main` steps it between observations of a second
-- reified loop over another cell. The consumer observes once between its awaits and closes after
-- the second: turns 1-3 leave its cell at 3, so it answers 3 * 100 + 3 (a step answers the task
-- at its next stop; the task that has finished answers `inl` at the step after). The second loop
-- (from 100, adding 10) is observed once and closed at 120.
--
-- Answer: i32[543]: 303 + 120 + 120.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False)
  + mk_def("mkd", 100, lend_mut("x", 10, 1000, False), False) + CONS + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons); z <- return (); force cg z")};
  g2 <- return (unbang mkd); z2 <- return (); m0 <- force g2 z2;
  s1 <- (nu_out (force tk)).1;
  case s1 {{
    inl v -> {close_fin("m0")}
  | inr tk2 ->
      mo <- (nu_out (force m0)).1;
      case mo {{
        inl p -> c9 <- (nu_out (force tk2)).2; let () = c9; {fin("p")}
      | inr m1 ->
          s2 <- (nu_out (force tk2)).1;
          case s2 {{
            inl v -> q <- (nu_out (force m1)).2; let (c, vd) = q; wd <- return (free[i32] c); return (plus (v, plus (vd, wd)))
          | inr tk3 ->
              s3 <- (nu_out (force tk3)).1;
              case s3 {{
                inl v -> q <- (nu_out (force m1)).2; let (c, vd) = q; wd <- return (free[i32] c); return (plus (v, plus (vd, wd)))
              | inr tk4 -> c9 <- (nu_out (force tk4)).2; let () = c9; {close_fin("m1")}
              }}
          }}
      }}
  }}
""")

CONS2 = f"""def cons2 : !U (1 -o F[{AW}] i32) =
  !thunkv fun (z : 1) ->
    g <- return (unbang mk); z1 <- return (); l0 <- force g z1;
    o1 <- (nu_out (force l0)).1;
    case o1 {{
      inl p -> {fin("p", "100")}
    | inr l1 ->
        o2 <- (nu_out (force l1)).1;
        case o2 {{ inl p -> {fin("p", "100")} | inr l2 -> {close_fin("l2")} }}
    }}
"""

FILES["r2d-task-suspended-inside-loop"] = ("""-- R2 (round 4): the reified loop's turns `await` (its row is `await`), and the consumer runs as a
-- task whose continuation the handler stores: each step of the task stops inside a turn of the
-- loop, inside its lend (the stored continuation holds the loop's stored continuation, which holds
-- the open lend). `main` steps the task inside its own lend of `d`. Turns 1-3 leave the cell at 3,
-- the third finishing: the consumer answers 3 * 100 + 3 at the fourth step (a step answers the task
-- at its next stop; the finished task answers `inl` at the step after).
--
-- Answer: i32[3333]: 303 * 10, plus `d`'s 303.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 3, True, mark=77), True) + CONS2 + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons2); z <- return (); force cg z")};
  d <- return (alloc[i32] i32[0]);
  r <- return (withbor2['y, top, i32, i32] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->
    s1 <- (nu_out (force tk)).1;
    case s1 {{
      inl v -> {setm("y", "v")} return (boxed['y] v)
    | inr tk1 ->
        s2 <- (nu_out (force tk1)).1;
        case s2 {{
          inl v -> {setm("y", "v")} return (boxed['y] v)
        | inr tk2 ->
            s3 <- (nu_out (force tk2)).1;
            case s3 {{
              inl v -> {setm("y", "v")} return (boxed['y] v)
            | inr tk3 ->
                s4 <- (nu_out (force tk3)).1;
                case s4 {{
                  inl v -> {setm("y", "v")} return (boxed['y] v)
                | inr tk4 -> c9 <- (nu_out (force tk4)).2; let () = c9; {setm("y", "i32[0]")} return (boxed['y] i32[0])
                }}
            }}
        }}
    }})));
  let (d, x) = r;
  e <- return (free[i32] d);
  return (plus (mul (x, i32[10]), e))
""")

FILES["r3a-cancel-consumer-holding-loop"] = ("""-- R3 (round 4): the consumer task holds the reified loop across its `await`s, each under `[then]`
-- whose finaliser closes the loop and frees its cell. `main` steps the task once (past the first
-- await, one *next*: the cell at 2) and then cancels it at the second await: the finaliser closes
-- the loop there (the tick answered *close*, the close step, the lend's end), once.
--
-- Answer: i32[9]; `live 0`.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False) + CONS + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons); z <- return (); force cg z")};
  s1 <- (nu_out (force tk)).1;
  case s1 {{
    inl v -> return v
  | inr tk2 -> c9 <- (nu_out (force tk2)).2; let () = c9; return i32[9]
  }}
""")

FILES["r3b-abort-caught-outside"] = ("""-- R3 (round 4): the consumer holds the reified loop (after one *next*: the cell at 2) across an
-- abortive operation (`3.0`, caught by a handler outside), under `[then]` whose finaliser closes
-- the loop: the abort runs the finaliser, which ends the lend once and frees the cell; the
-- handler answers 1000 + 5. (The code after the abort is `absurd x`, `x : 0`.)
--
-- Answer: i32[1005]; `live 0`.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False) + f"""
main : F i32 =
  handle_with[3](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (e : i32) -> return (plus (e, i32[1000]))), ()) : !U (i32 -o F i32) * 1)) (
    g <- return (unbang mk); z <- return (); l0 <- force g z;
    o1 <- (nu_out (force l0)).1;
    case o1 {{
      inl p -> {fin("p")}
    | inr l1 ->
        x <- abort[3.0] i32[5] unwind ({CLOSE_UNIT("l1")});
        absurd x
    }})
""")

FILES["r3c-cancel-inside-loop-turn"] = ("""-- R3 (round 4): r2d's task (the loop's turns `await`) cancelled after two steps, while it is
-- suspended in turn 3's `await`, inside the loop's lend: the turn's finaliser writes 77 through
-- the view, then the lend's unwinding ends it and the owner's destructor frees the cell, once.
--
-- Answer: i32[75]: 7 * 10, plus `d`'s 5; `live 0`.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 3, True, mark=77), True) + CONS2 + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons2); z <- return (); force cg z")};
  d <- return (alloc[i32] i32[0]);
  r <- return (withbor2['y, top, i32, i32] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->
    s1 <- (nu_out (force tk)).1;
    case s1 {{
      inl v -> {setm("y", "v")} return (boxed['y] v)
    | inr tk1 ->
        s2 <- (nu_out (force tk1)).1;
        case s2 {{
          inl v -> {setm("y", "v")} return (boxed['y] v)
        | inr tk2 -> c9 <- (nu_out (force tk2)).2; let () = c9; {setm("y", "i32[5]")} return (boxed['y] i32[7])
        }}
    }})));
  let (d, x) = r;
  e <- return (free[i32] d);
  return (plus (mul (x, i32[10]), e))
""")

FILES["r3d-cancel-in-first-segment"] = ("""-- R3 (round 4): the task is cancelled at its first stop, which is inside the loop's first segment
-- (turn 1's `await`, under `reify`'s handler, before `reify` has answered a loop): the turn's
-- finaliser writes through the view, the lend ends, the cell is freed.
--
-- Answer: i32[11]; `live 0`.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 3, True, mark=77), True) + CONS2 + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons2); z <- return (); force cg z")};
  c9 <- (nu_out (force tk)).2; let () = c9;
  return i32[11]
""")


def iter_imm(x, kv, mult, lim):
    """`k` read across the ticks of a `Div` loop (no lend of its own): turn `j` answers
    `*k * mult + j`, finishing at `j = lim`; its close step answers 1000 + j."""
    St = f"imm '{x} i32 * i32"
    T = trow(False)
    return f"""st <- return ((!thunkv fun (sq : {St}) ->
          < let (v, j) = sq;
            cp <- return (copy['{x}, i32] v); let (v1, v) = cp;
            rv <- return ((unbang rd) ['{x}] v1);
            r <- return (plus (mul (rv, i32[{mult}]), j));
            g <- return (lt (j, i32[{lim}]));
            case g {{ inl ge -> let () = forget_imm['{x}, i32] v; return (inl r) | inr lo -> return (inr (v, plus (j, i32[1]))) }},
            let (v, j) = sq; let () = forget_imm['{x}, i32] v; return (plus (i32[1000], j)) >) :
            !U ({St} -o {F(T)} (i32 + {St}) & {F(T)} i32));
          f <- return (unbang div_iterate[{T}, {St}, i32, i32]);
          a0 <- return (st, ({kv}, i32[1]));
          force f a0"""


LTI = "U (nu X. F (i32 + U X) & F i32)"
DTICK = "d0 <- perform[4294967295.0] (); case d0 { inl a -> return () | inr b -> return () }"

FILES["r4a-two-loops-imm-views-one-place"] = ("""-- R4 (round 4): two reified loops over `imm` views of one place, interleaved, held across the
-- `tick`s of a W-tick `imm` lend. `c` (7) is lent `imm` as `k` across direct `tick`s
-- (`withbor1rt`, its ticks answered by `div_fuel_k` outside); inside, two computations each read
-- a copy of `k` at every turn of a `Div` loop of their own and are reified; the lend's body
-- observes them in turn, a direct tick between observations, and both finish inside the lend.
-- Loop 1 answers 7 * 2 + j and finishes at j = 3 (17); loop 2 answers 7 * 3 + j and finishes at
-- j = 2 (23).
--
-- Answer: i32[54]: 17 + 23 + the view's 7, plus the cell's 7 after the lend.
""", PRE + f"""
main : F i32 =
  c <- return (alloc[i32] i32[7]);
  t <- return (thunkv fun (u0 : 1) ->
    withbor1rt['x, dom, i32, i32, [{TICK}]](c, k) (
      kk <- return (copy['x, i32] k); let (k1, k) = kk;
      kk2 <- return (copy['x, i32] k); let (k2, k) = kk2;
      t1 <- return ((thunkv fun (u1 : 1) ->
          {iter_imm("x", "k1", 2, 3)}) : U (1 -o F[{TICK}] (i32 + i32)));
      t2 <- return ((thunkv fun (u2 : 1) ->
          {iter_imm("x", "k2", 3, 2)}) : U (1 -o F[{TICK}] (i32 + i32)));
      rf <- return (unbang reify_k[[], i32]);
      l1 <- force rf t1;
      rf2 <- return (unbang reify_k[[], i32]);
      l2 <- force rf2 t2;
      {DTICK};
      o1 <- (nu_out (force l1)).1;
      {DTICK};
      o2 <- (nu_out (force l2)).1;
      {DTICK};
      a <- (case o1 {{ inl b -> return b | inr m1 -> o3 <- (nu_out (force m1)).1;
                        case o3 {{ inl b -> return b | inr m2 -> (nu_out (force m2)).2 }} }});
      b <- (case o2 {{ inl b -> return b | inr n1 -> (nu_out (force n1)).2 }});
      y <- return ((unbang rd) ['x] k);
      return (boxed['x] (plus (plus (a, b), y)))));
  df <- return (unbang div_fuel_k[[], ref i32 * i32]);
  a1 <- return (t, i32[100]);
  p <- force df a1;
  let (c, v) = p; w <- return (free[i32] c); return (plus (v, w))
""")

FILES["r4b-owner-used-while-loop-holds-it"] = ("""-- R4 (round 4, refused): the reified loop owns `c` (its thunk captured it); `main` then reads `c`
-- directly. Refused: `c` is consumed by the thunk.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False).replace(
    "    rf <- return (unbang reify_k[[], ref i32 * i32]);",
    "    w <- return (free[i32] c);\n    rf <- return (unbang reify_k[[], ref i32 * i32]);") + """
main : F i32 =
  g <- return (unbang mk); z <- return (); l0 <- force g z;
  q <- (nu_out (force l0)).2; let (c, v) = q; w <- return (free[i32] c); return (plus (v, w))
""")

FILES["r4c-two-loops-one-owner"] = ("""-- R4 (round 4, refused): two thunks each lending `c` `mut` across ticks, to make two reified loops
-- over one place. Refused: `c` is consumed by the first.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False).replace(
    "    rf <- return (unbang reify_k[[], ref i32 * i32]);\n    force rf t\n",
    "    t2 <- return ((thunkv fun (u0 : 1) ->\n      p <- " + lend_mut("x", 1, 50, False) + ";\n      let (c, o) = p;\n      case o { inl b -> return (inl (c, b)) | inr z -> return (inr (c, z)) }) :\n      U (1 -o F[" + TICK + "] ((ref i32 * i32) + (ref i32 * i32))));\n    rf <- return (unbang reify_k[[], ref i32 * i32]);\n    l1 <- force rf t;\n    rf2 <- return (unbang reify_k[[], ref i32 * i32]);\n    l2 <- force rf2 t2;\n    return (l1, l2)\n").replace("def mk : !U (1 -o F " + LT0 + ")", "def mk : !U (1 -o F (" + LT0 + " * " + LT0 + "))") + """
main : F i32 =
  g <- return (unbang mk); z <- return (); ll <- force g z;
  let (l0, l1) = ll;
  q <- (nu_out (force l0)).2; let (c, v) = q; w <- return (free[i32] c);
  q1 <- (nu_out (force l1)).2; let (c1, v1) = q1; w1 <- return (free[i32] c1); return (plus (v, w))
""")

FILES["r3e-no-finaliser-await"] = ("""-- R3 (round 4, refused): r3a's consumer with no finaliser at its `await`: the loop (which owns a
-- cell and an open lend) would be abandoned if the task were cancelled there. Refused.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False) + CONS.replace(
    'u1 <- perform[1.0] () unwind (' + CLOSE_UNIT("l0") + ');', 'u1 <- perform[1.0] ();') + f"""
main : F i32 =
  tk <- {task_h("    cg <- return (unbang cons); z <- return (); force cg z")};
  s1 <- (nu_out (force tk)).1;
  case s1 {{
    inl v -> return v
  | inr tk2 -> c9 <- (nu_out (force tk2)).2; let () = c9; return i32[9]
  }}
""")

FILES["r3f-no-finaliser-abort"] = ("""-- R3 (round 4, refused): r3b with no finaliser at the abort: the loop would be abandoned. Refused.
""", PRE + mk_def("mk", 0, lend_mut("x", 1, 50, False), False) + f"""
main : F i32 =
  handle_with[3](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (e : i32) -> return (plus (e, i32[1000]))), ()) : !U (i32 -o F i32) * 1)) (
    g <- return (unbang mk); z <- return (); l0 <- force g z;
    o1 <- (nu_out (force l0)).1;
    case o1 {{
      inl p -> {fin("p")}
    | inr l1 ->
        x <- abort[3.0] i32[5];
        absurd x
    }})
""")

ESC_THUNK = lambda tail: f"""      t <- return ((thunkv fun (u0 : 1) ->
        p <- {lend_mut("x", 1, 50, False, ind="        ")};
        let (c, o) = p;
        {setm("y", "i32[1]")}
        case o {{ inl b -> return (inl (c, b)) | inr z -> return (inr (c, z)) }}) :
        U (1 -o F[{TICK}] ((ref i32 * i32) + (ref i32 * i32))));
      rf <- return (unbang reify_k[[], ref i32 * i32]);
      l0 <- force rf t;
{tail}"""

FILES["r2e-leak-loop-out-of-lend"] = ("""-- R2 leak (round 4, refused): inside a lend of `d` (`'y`), a reified loop whose computation also
-- writes through `d`'s view after its own lend; the loop is returned out of `'y`'s callback.
-- Refused: `U` outlives no lifetime.
""", PRE + f"""
main : F i32 =
  c <- return (alloc[i32] i32[0]);
  d <- return (alloc[i32] i32[0]);
  r <- return (withbor2['y, top, i32, {LT0}] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->
{ESC_THUNK("      return (boxed['y] l0)")})));
  let (d, l) = r;
  e <- return (free[i32] d);
  q <- (nu_out (force l)).2; let (c, v) = q; w <- return (free[i32] c); return (plus (v, plus (w, e)))
""")

FILES["r2f-leak-loop-into-outer-cell"] = ("""-- R2 leak (round 4, refused): r2e's loop put in a cell owned outside `'y`'s lend (captured by the
-- callback, refilled with the loop, handed back as the callback's answer). Refused: `ref U(..)`
-- outlives no lifetime.
""", PRE + f"""

main : F i32 =
  c <- return (alloc[i32] i32[0]);
  d <- return (alloc[i32] i32[0]);
  s <- return (alloc[1] ());
  r <- return (withbor2['y, top, i32, ref {LT0}] d (thunkv Fun 'y < dom. return (thunkv fun (m : mut 'y i32) ->
{ESC_THUNK("      u <- return (free[1] s); let () = u; s2 <- return (alloc[" + LT0 + "] l0); return (boxed['y] s2)")})));
  let (d, s2) = r;
  e <- return (free[i32] d);
  e2 <- return (alloc[i32] i32[0]);
  r2 <- return (withbor2['z, top, i32, i32] e2 (thunkv Fun 'z < dom. return (thunkv fun (m2 : mut 'z i32) ->
    let () = forget_mut['z, i32] m2;
    l <- return (free[{LT0}] s2);
    q <- (nu_out (force l)).2; let (c, v) = q; w <- return (free[i32] c); return (boxed['z] (plus (v, w))))));
  let (e2, v) = r2;
  e3 <- return (free[i32] e2);
  return (plus (v, e))
""")

INNER = f"""def inner : !U (1 -o F[{TICK}] i32) =
  !thunkv fun (z : 1) ->
    c <- return (alloc[i32] i32[0]);
    p <- {lend_mut("y", 2, 4, False, ind="    ")};
    let (c, o) = p;
    w <- return (free[i32] c);
    case o {{ inl b -> return (plus (b, w)) | inr z -> return (plus (i32[0], w)) }}
"""
INNER3 = f"""def inner3 : !U (1 -o F[{TICK}] i32) =
  !thunkv fun (z : 1) ->
    c <- return (alloc[i32] i32[0]);
    p <- {lend_mut("w", 1, 9, False, inner="inner", ind="    ")};
    let (c, o) = p;
    w <- return (free[i32] c);
    case o {{ inl b -> return (plus (b, w)) | inr z -> return (plus (i32[0], w)) }}
"""


def drive_def(sig):
    """`drive : !U(Loop ⊸ F_{{tick, Σ}}(P ⊕ P))`: a `Div` loop of the consumer whose turns observe the
    reified loop with *next*, its close step closing it."""
    T = trow(sig)
    LT = loopt(sig)
    return f"""def drive : !U ({LT} -o {F(T)} (({P}) + ({P}))) =
  !thunkv fun (l0 : {LT}) ->
    st <- return ((!thunkv fun (l : {LT}) ->
      < o <- (nu_out (force l)).1;
        case o {{ inl p -> return (inl p) | inr l2 -> return (inr l2) }},
        (nu_out (force l)).2 >) :
      !U ({LT} -o {F(T)} (({P}) + {LT}) & {F(T)} ({P})));
    f <- return (unbang div_iterate[{T}, {LT}, {P}, {P}]);
    a0 <- return (st, l0);
    force f a0
"""


def drive_main(sig, fuel, mkname="mk"):
    S = srow(sig)
    return f"""
main : F i32 =
  g <- return (unbang {mkname}); z <- return (); l0 <- force g z;
  t <- return ((thunkv fun (u : 1) -> dg <- return (unbang drive); force dg l0) : U (1 -o {F(trow(sig))} (({P}) + ({P}))));
  df <- return (unbang div_fuel_k[{S}, ({P}) + ({P})]);
  a1 <- return (t, i32[{fuel}]);
  o <- force df a1;
  case o {{ inl p -> {fin("p")} | inr p -> {fin("p", "100")} }}
"""


FILES["r5a-depth2-to-done"] = ("""-- R5 (round 4): depth 2. The reified loop's turns run `inner`, which lends a cell of its own
-- `mut` across a `Div` loop (W-tick): `inner`'s tick is not handled inside the outer lend, so it is
-- an observation boundary of the reified loop, with both lends open in the stored continuation.
-- `inner` answers 8; each outer turn adds 9; the loop finishes at 27 after 3 turns (6 stops).
-- The consumer drives it with a `Div` loop of its own (`drive`, its ticks answered by
-- `div_fuel_k`), observing with *next* to the end.
--
-- Answer: i32[27027]: 27 * 1000 + 27.
""", PRE + INNER + mk_def("mk", 0, lend_mut("x", 1, 27, False, inner="inner"), False) + drive_def(False)
  + drive_main(False, 100))

FILES["r5b-depth2-close-at-inner-stop"] = ("""-- R5 (round 4): r5a's loop closed at its third stop, inside `inner`'s lend (turn 2, `inner`'s
-- cell at 2): the inner tick is answered *close*, `inner`'s close step answers 0 and its lend
-- ends (`inner` answers its cell's 2); the outer turn adds 3 (cell 12), reaches its back edge,
-- whose tick is answered *close* in turn: the outer close step reads 12, the outer lend ends.
-- The consumer's fuel is 1: `drive`'s second tick is answered *close*, and its close step closes the loop.
--
-- Answer: i32[1212]: 12 * 100 + 12.
""", PRE + INNER + mk_def("mk", 0, lend_mut("x", 1, 27, False, inner="inner"), False) + drive_def(False)
  + drive_main(False, 1))

FILES["r5c-depth3-to-done"] = ("""-- R5 (round 4): depth 3. The reified loop's turns run `inner3`, whose W-tick lend's turn runs
-- `inner` (r5a's): a stop of the reified loop is inside three open lends. `inner3` answers 18
-- (one turn: 8 + 1 = 9, plus its cell's 9); each outer turn adds 19; the loop finishes at 38.
--
-- Answer: i32[38038]: 38 * 1000 + 38.
""", PRE + INNER + INNER3 + mk_def("mk", 0, lend_mut("x", 1, 38, False, inner="inner3"), False)
  + drive_def(False) + drive_main(False, 100))

def r5d():
    here = os.path.dirname(os.path.abspath(__file__))
    src = open(os.path.join(here, "..", "nursery", "t2a-nursery.bc")).read()
    head = src[src.index("include async"):src.index("main : F i32 =")]
    body = src[src.index("    withbor1rh['r"):src.index("      return (boxed['r] x)));") + len("      return (boxed['r] x))")]
    N = "9.0 cancel 1 ~> 1"
    sig = [N]
    T = trow(sig)
    return ("""-- R5 (round 4): W-hold under `reify`. The nursery of `bc/nursery/t2a` (a task lends its request
-- `imm` across `await`s, W-hold, spawns two children holding copies of the view, and waits for
-- them in a `Div` loop, W-tick) is made a first-class loop value by `reify_k`, which owns the
-- request; the consumer drives it with `drive` under the `9.0` scheduler that resumes at once.
--
-- Answer: i32[42007]: t2a's 42 * 1000, plus the request's 7.
""" + head.replace("def plus : i32 * i32 => i32 = unbang host[add32]\n",
        "def plus : i32 * i32 => i32 = unbang host[add32]\ndef mul : i32 * i32 => i32 = unbang host[mul32]\n")
        + drive_def(sig) + f"""
main : F i32 =
  req <- return (alloc[i32] i32[7]);
  t <- return ((thunkv fun (u0 : 1) ->
    p <- {body.strip()};
    return (inl p)) : U (1 -o F{T} (({P}) + ({P}))));
  handle_with[9](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (q : 1 * U ((1 -o F i32) & F 1)) ->
        let (x, k) = q; (force k).1 x), ()) : !U (1 * U ((1 -o F i32) & F 1) -o F i32) * 1)) (
    rf <- return (unbang reify_k[[{N}], {P}]);
    l0 <- force rf t;
    tt <- return ((thunkv fun (u : 1) -> dg <- return (unbang drive); force dg l0) : U (1 -o F{T} (({P}) + ({P}))));
    df <- return (unbang div_fuel_k[[{N}], ({P}) + ({P})]);
    a1 <- return (tt, i32[100]);
    o <- force df a1;
    case o {{ inl p -> {fin("p")} | inr p -> {fin("p", "100")} }})
""")


FILES["r5d-whold-nursery-reified"] = r5d()

INNERT = f"""def innert : !U (1 -o F[{TICK}] i32) =
  !thunkv fun (z : 1) ->
    d <- return (alloc[i32] i32[1]);
    p <- withbor2rt['y, dom, i32, i32, [{TICK}]](d, n) (
      th <- return ((thunkv fun (u : 1) ->
          q <- return (withswap['y, i32, i32] n (thunkv fun (a : i32) -> return (plus (a, i32[5]), plus (a, i32[5]))));
          return q) : U (1 -o F (mut 'y i32 * i32)));
      t0 <- perform[4294967295.0] ();
      case t0 {{ inl a -> return () | inr b -> return () }};
      u1 <- return ();
      q <- force th u1;
      let (n, r) = q;
      let () = forget_mut['y, i32] n;
      return (boxed['y] r));
    let (d, v) = p;
    w <- return (free[i32] d);
    return (plus (v, w))
"""

FILES["r5e-thunk-below-lend-across-tick"] = ("""-- R5 (round 4): the shape of `thunkF_RL_fails_below_at` under `reify`. Each turn of the reified
-- loop runs `innert`, whose W-tick lend of its own cell (`'y`, below the loop's `'x`) builds a
-- thunk capturing the view `mut 'y`, ticks directly with the thunk held (a stop of the reified
-- loop, inside both lends, the stored continuation holding a `U` over a view below `'x`), then
-- forces it (cell 1 + 5). `innert` answers 12 (6, plus its cell's 6); each outer turn adds 13;
-- the loop finishes at 39 after three turns.
--
-- Answer: i32[39039]: 39 * 1000 + 39.
""", PRE + INNERT + mk_def("mk", 0, lend_mut("x", 1, 39, False, inner="innert"), False)
  + drive_def(False) + drive_main(False, 100))

FILES["p2-shape-iterator-over-view"] = ("""-- P2's kernel shape (round 4): `echo<'a>(t)` reads its borrowed `t : imm 'a i32` at every step of
-- a `Div` loop made a first-class loop value by `reify_k`, which the caller observes step by step
-- (`drive`-like, three *next*s) and closes. The loop holds the view `t`, not a lend: no relaxed
-- rule is used (the assurance is `unconditional`).
--
-- Answer: i32[39]: step j answers 7 + j and the loop finishes at j = 4 (11) on the third *next*;
-- 11 + 7 * 3 read through the view, plus the cell's 7.
""", PRE + f"""
def echo : !U (forall 'a < top. imm 'a i32 -o F {LTI}) =
  !thunkv Fun 'a < top. fun (t : imm 'a i32) ->
    th <- return ((thunkv fun (u0 : 1) ->
        {iter_imm("a", "t", 1, 4)}) : U (1 -o F[{TICK}] (i32 + i32)));
    rf <- return (unbang reify_k[[], i32]);
    force rf th

main : F i32 =
  c <- return (alloc[i32] i32[7]);
  r <- return (withbor1['y, i32, i32] c (thunkv Fun 'y < dom. return (thunkv fun (k : imm 'y i32) ->
    kk <- return (copy['y, i32] k); let (k1, k) = kk;
    e <- return (unbang echo);
    l0 <- ((force e) ['y]) k1;
    o1 <- (nu_out (force l0)).1;
    a <- (case o1 {{ inl b -> return b | inr l1 ->
           o2 <- (nu_out (force l1)).1;
           case o2 {{ inl b -> return b | inr l2 ->
             o3 <- (nu_out (force l2)).1;
             case o3 {{ inl b -> return b | inr l3 -> (nu_out (force l3)).2 }} }} }});
    y <- return ((unbang rd) ['y] k);
    return (boxed['y] (plus (a, mul (y, i32[3])))))));
  let (c, v) = r;
  w <- return (free[i32] c);
  return (plus (v, w))
""")

YROW = ["2.0 cancel i32 ~> 1"]


def lend_gen(x, ind="      "):
    """P6's generator body: a `mut` W-tick lend of its own cell across an endless `Div` loop whose
    turns add 1 through the view and `yield` (`2.0`) the cell; its close step reads the cell."""
    T = trow(YROW)
    L = [f"withbor2rt['{x}, dom, i32, i32 + i32, {T}](c, m) ("]
    L.append(f"  st <- return ((!thunkv fun (v : mut '{x} i32) ->")
    L.append(f"    < q <- return (withswap['{x}, i32, i32] v (thunkv fun (a : i32) -> return (plus (a, i32[1]), plus (a, i32[1]))));")
    L.append("      let (v, r) = q;")
    L.append("      u <- perform[2.0] r; let () = u;")
    L.append("      return (inr v),")
    L.append(f"      q2 <- return (withswap['{x}, i32, i32] v (thunkv fun (a : i32) -> return (a, a)));")
    L.append(f"      let (v, r2) = q2; let () = forget_mut['{x}, i32] v; return r2 >) :")
    L.append(f"      !U (mut '{x} i32 -o {F(T)} (i32 + mut '{x} i32) & {F(T)} i32));")
    L.append(f"  f <- return (unbang div_iterate[{T}, mut '{x} i32, i32, i32]);")
    L.append("  a0 <- return (st, m);")
    L.append("  o <- force f a0;")
    L.append(f"  case o {{ inl b -> return (boxed['{x}] (inl b)) | inr z -> return (boxed['{x}] (inr z)) }})")
    return ("\n" + ind).join(L)


FILES["p6-shape-endless-generator"] = ("""-- P6's kernel shape (round 4): an endless generator borrowing its own local `mut` across every
-- `yield` (`2.0`) and every step: a W-tick lend of its cell across a `Div` loop that never
-- finishes, made a first-class loop value by `reify_k` at the row `yield`. The consumer observes
-- it three times under a handler of `yield` that sums what is yielded, then closes it.
--
-- Answer: i32[414]: the close's residual 4 * 100 + the cell's 4, plus the yields 1 + 2 + 3 + 4
-- (turn 1 at `reify`, one per *next*), which the deep handler of `yield` adds to the answer.
""", PRE + mk_def("mk", 0, lend_gen("x"), YROW) + f"""
main : F i32 =
  handle_with[2](
      ((!thunkv fun (v : i32) -> return v) : !U (i32 -o F i32)),
      (((!thunkv fun (q : i32 * U ((1 -o F i32) & F 1)) ->
        let (y, k) = q; u <- return (); r <- (force k).1 u; return (plus (y, r))), ()) :
        !U (i32 * U ((1 -o F i32) & F 1) -o F i32) * 1)) (
    g <- return (unbang mk); z <- return (); l0 <- force g z;
    o1 <- (nu_out (force l0)).1;
    case o1 {{ inl p -> {fin("p")} | inr l1 ->
      o2 <- (nu_out (force l1)).1;
      case o2 {{ inl p -> {fin("p")} | inr l2 ->
        o3 <- (nu_out (force l2)).1;
        case o3 {{ inl p -> {fin("p")} | inr l3 -> {close_fin("l3", "100")} }} }} }})
""")

def r3g():
    T = trow(True)
    lend = lend_mut("x", 1, 50, True, mark=77).replace(
        "      u <- perform[1.0] () unwind (",
        "      g1 <- return (lt (r, i32[2]));\n"
        "      u <- (case g1 { inl ge -> perform[1.0] () | inr lo -> return () }) unwind (")
    K = f"U ((1 -o F[{TICK}] (({P}) + ({P}))) & F[{TICK}] 1)"
    return ("""-- R3 (round 4, refused): a handler of `await` between the lend and `reify` (inside the reified
-- computation) that cancels its continuation at turn 2's `await`, after turn 1 stopped at the tick.
-- Refused: a handler around a computation that may tick is typed only at clauses that resume `κ`
-- in tail (`effHandleT`), so the reified computation's ticks never cross a handler that drops or
-- cancels; the cancel paths reach the lend only from outside the loop (r3c, r3d).
""", PRE + f"""
def mk : !U (1 -o F {loopt(False)}) =
  !thunkv fun (z : 1) ->
    c <- return (alloc[i32] i32[0]);
    t <- return ((thunkv fun (u0 : 1) ->
      handle_with[1](
          ((!thunkv fun (x : ({P}) + ({P})) -> return x) : !U ((({P}) + ({P})) -o F[{TICK}] (({P}) + ({P})))),
          (((!thunkv fun (q : 1 * {K}) ->
            let (x, k) = q; let () = x; c9 <- (force k).2; let () = c9;
            n <- return (alloc[i32] i32[42]); return (inr (n, i32[5]))), ()) :
            !U (1 * {K} -o F[{TICK}] (({P}) + ({P}))) * 1)) (
        p <- {lend};
        let (c, o) = p;
        case o {{ inl b -> return (inl (c, b)) | inr z -> return (inr (c, z)) }})) :
      U (1 -o F[{TICK}] (({P}) + ({P}))));
    rf <- return (unbang reify_k[[], {P}]);
    force rf t

main : F i32 =
  g <- return (unbang mk); z <- return (); l0 <- force g z;
  o1 <- (nu_out (force l0)).1;
  case o1 {{ inl p -> {fin("p")} | inr l1 ->
    o2 <- (nu_out (force l1)).1;
    case o2 {{ inl p -> {fin("p")} | inr l2 -> {close_fin("l2", "100")} }} }}
""")


FILES["r3g-cancel-by-handler-inside-reify"] = r3g()

def r5f():
    src = r5d()
    a = src.index("    tt <- return ((thunkv fun (u : 1)")
    b = src.index("    case o {", a)
    src = src[:a] + "    o <- (nu_out (force l0)).2;\n" + src[b:]
    src = src.replace("case o { inl p -> let (c, v) = p; w <- return (free[i32] c); return (plus (mul (v, i32[1000]), w)) | inr p -> let (c, v) = p; w <- return (free[i32] c); return (plus (mul (v, i32[100]), w)) })",
                      "let (c, v) = o; w <- return (free[i32] c); return (plus (mul (v, i32[1000]), w)))")
    head = """-- R5 (round 4): r5d's reified nursery closed at its first stop (the back edge after the first
-- round, both children pending, each holding a copy of the view): the tick is answered *close*,
-- the nursery's close step (`finish`) cancels the pending children (the cut counts -100), the
-- request is read through the view (7), and the W-hold lend ends: the residual is (req, -93).
--
-- Answer: i32[4294874303]: -93 * 1000 + the request's 7, modulo 2^32.
"""
    return head + src[src.index("include async"):]


FILES["r5f-whold-nursery-closed-mid-wait"] = r5f()

def emit():
    here = os.path.dirname(os.path.abspath(__file__))
    for name, src in FILES.items():
        with open(os.path.join(here, name + ".bc"), "w") as f:
            f.write("".join(src) if isinstance(src, tuple) else src)


if __name__ == "__main__":
    emit()
