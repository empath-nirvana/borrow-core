"""Bug injection for H1 and H3: each bug is a patch of one of the typed terms, written to
`<case>/bugs/<id>.bc` and run through `bcc check` (and, when the kernel accepts it, the LIR
interpreter and Wasm, for the answer and `live`). MEMORY bugs (use after free, double free, a leak,
an affine value duplicated, a borrow outliving its lend, an alias of a lent owner) must be refused;
SEMANTIC controls (a wrong value, a skipped computation that releases its resources) are expected to
be accepted; LEAK-CHECK variants drop suspended machines mid-walk and must end at `live 0`.

    python3 experiments/core-hard-cases/h3/bugs.py     (from the repository root)
"""
import os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
CASES = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(CASES))
BCC = os.path.join(ROOT, ".lake", "build", "bin", "bcc")

EARLY = ("  let mut more = true;\n  while more {\n    more = false;",
         "  let mut more = true;\n  for round in 0..5 {\n    more = false;")

BUGS = [
  # H1 (ii): the stored recursive generator.
  ("h1", "g2-gen-zip-stored", "B1", "MEMORY", "a stored generator (linear `U`) observed twice: next and close",
   "      o <- (nu_out force it).1;\n      case o {",
   "      o <- (nu_out force it).1;\n      e <- (nu_out force it).2;\n      case o {"),
  ("h1", "g2-gen-zip-stored", "B2", "MEMORY", "one machine's code (linear) used for two stored generators",
   "      return (thunkv nu_in < (nu_out force f s0).1, (nu_out force f s0).2 >)",
   "      g1 <- return (thunkv nu_in < (nu_out force f s0).1, (nu_out force f s0).2 >);\n      g2 <- return (thunkv nu_in < (nu_out force f s0).1, (nu_out force f s0).2 >);\n      return g1"),
  ("h1", "g2-gen-zip-stored", "B3", "LEAK-CHECK", "both stored walks dropped mid-walk (after 10 steps) with no close: the checker's destructor must close them, live 0",
   "  while go {", "  for it in 0..10 {"),
  ("h1", "g2-gen-zip-stored", "S1", "SEMANTIC", "the wrong round's value yielded at a popped frame",
   "return (inl ((unbang value) (m, r2),", "return (inl ((unbang value) (m, i32[0]),"),
  # H1 (iii): the recursive task, frames in an owned array.
  ("h1", "a1b-async-tree-array", "B4", "MEMORY", "the frames array used after it was moved into `array_replace` (use after move/free)",
   "      return (a3, (unbang host[add32]) (sp, i32[1]))", "      return (a1, (unbang host[add32]) (sp, i32[1]))"),
  ("h1", "a1b-async-tree-array", "B5", "MEMORY", "a task's frames (owned) duplicated at its resume",
   "      stk2 <- return (unbang push) (stk, fr);\n      dv : D", "      stk2 <- return (unbang push) (stk, fr);\n      stk3 <- return (unbang push) (stk, fr);\n      dv : D"),
  ("h1", "a1b-async-tree-array", "B6", "MEMORY", "a `linear` frames array never released (a leak the kernel cannot repair)",
   "      fr : Frame <- return inr (a, (m, r));", "      linear junk <- return (unbang array_new[Frame]) (i32[4], zf);\n      fr : Frame <- return inr (a, (m, r));"),
  ("h1", "a1b-async-tree-array", "B7", "LEAK-CHECK", "the scheduler stops after 5 rounds and drops the suspended tasks (their frames arrays): live 0",
   EARLY[0], EARLY[1]),
  ("h1", "a1b-async-tree-array", "S2", "SEMANTIC", "the wrong round's value added at `K_right`",
   "((unbang value) (m, r))), v);", "((unbang value) (m, i32[0]))), v);"),
  # H3: re-borrow per step.
  ("h3", "r3-owned-tree-reborrow", "B8", "MEMORY", "the step's walk captured with the lend's borrow and run after the lend has closed (a borrow outliving its lend)",
   "      return withbor1['x, Tree, R + 1] c (thunkv Fun 'x < dom.\n          return (thunkv fun (b : imm 'x Tree) ->\n              nv <- return unbang nav;\n              bw <- return (b, w);\n              force nv ['x] bw))",
   "      r0 <- return withbor1['x, Tree, U (F (R + 1))] c (thunkv Fun 'x < dom.\n          return (thunkv fun (b : imm 'x Tree) ->\n              return boxed['x] (thunk (nv <- return unbang nav;\n                bw <- return (b, w);\n                o <- force nv ['x] bw;\n                return unbox o))));\n      let (c2, t) = r0;\n      o <- force t;\n      return (c2, o)"),
  ("h3", "r3-owned-tree-reborrow", "B9", "MEMORY", "the tree's cell freed at the resume, then lent (use after free)",
   "      cr <- return (unbang advance) (c, w);\n      return (unbang settle) (cr, (r, s2))",
   "      t0 <- return free[Tree] c;\n      cr <- return (unbang advance) (c, w);\n      return (unbang settle) (cr, (r, s2))"),
  ("h3", "r3-owned-tree-reborrow", "B10", "MEMORY", "the owner freed inside its own lend (the lent cell aliased by its owner)",
   "              nv <- return unbang nav;\n              bw <- return (b, w);", "              t0 <- return free[Tree] c;\n              nv <- return unbang nav;\n              bw <- return (b, w);"),
  ("h3", "r3-owned-tree-reborrow", "B11", "MEMORY", "the owned path array kept in the state and also handed to the walk (affine duplicated)",
   "      cr <- return (unbang advance) (c, w);\n      return (unbang settle) (cr, (r, s2))",
   "      cr <- return (unbang advance) (c, w);\n      t0 <- return (unbang array_size[i32]) path;\n      return (unbang settle) (cr, (r, s2))"),
  ("h3", "r3-owned-tree-reborrow", "B12", "LEAK-CHECK", "the scheduler stops after 5 rounds and drops the suspended tasks (each owning its tree): live 0",
   EARLY[0], EARLY[1]),
  ("h3", "r3-owned-tree-reborrow", "S3", "SEMANTIC", "the wrong round's value added",
   "((unbang value) (key, r)));", "((unbang value) (key, i32[0])));"),
  # H3: the consuming form, frames holding owned subtrees.
  ("h3", "z3-owned-tree-consume", "B13", "MEMORY", "a frame's owned subtree also freed at once (one cell freed twice / used after free)",
   "                    lt <- return free[Tree] l;", "                    lt <- return free[Tree] l;\n                    xx <- return free[Tree] rr;"),
  ("h3", "z3-owned-tree-consume", "B14", "MEMORY", "a node's left cell freed twice (double free)",
   "                    lt <- return free[Tree] l;", "                    lt <- return free[Tree] l;\n                    l2 <- return free[Tree] l;"),
  ("h3", "z3-owned-tree-consume", "B15", "MEMORY", "a frame holding an owned subtree pushed twice (affine duplicated)",
   "                    stk2 <- return (unbang push) (stk, fr);\n                    lt <- return free[Tree] l;",
   "                    stk1 <- return (unbang push) (stk, fr);\n                    stk2 <- return (unbang push) (stk1, fr);\n                    lt <- return free[Tree] l;"),
  ("h3", "z3-owned-tree-consume", "B16", "LEAK-CHECK", "the scheduler stops after 5 rounds and drops the suspended tasks (frames owning subtrees): live 0",
   EARLY[0], EARLY[1]),
  ("h3", "z3-owned-tree-consume", "S4", "SEMANTIC", "the right subtree skipped (its cell freed, not walked): a wrong sum, nothing leaked",
   "      t <- return free[Tree] rr;\n      dv : D <- return inl (t, (r, stk2));",
   "      t <- return free[Tree] rr;\n      dv : D <- return inl ((roll inl () : Tree), (r, stk2));"),
]

def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    return (r.stdout + r.stderr).strip()

for case, base, bid, kind, desc, old, new in BUGS:
    src = open(os.path.join(CASES, case, base + ".bc")).read()
    assert src.count(old) == 1, (bid, src.count(old))
    d = os.path.join(CASES, case, "bugs"); os.makedirs(d, exist_ok=True)
    f = os.path.join(d, f"{bid}-{base}.bc")
    open(f, "w").write(f"-- {bid} ({kind}): {desc}. A patch of `{base}.bc` (`h3/bugs.py`).\n" + src.replace(old, new))
    chk = run([BCC, "check", f])
    acc = [l for l in chk.splitlines() if l.startswith("assurance:")]
    if acc:
        lir = run([BCC, "interp", "--stage", "lir", f]).replace("\n", " ")
        wasm = run([BCC, "run", "--backend", "new", f]).replace("\n", " ")
        verdict = f"ACCEPTED ({acc[0]}) | lir: {lir} | wasm: {wasm}"
    else:
        err = [l for l in chk.splitlines() if not l.startswith("loop ")][:1]
        verdict = "REFUSED: " + (err[0].replace(CASES + "/", "") if err else chk[:200])
    print(f"{bid} {kind} {case}/{base}: {desc}\n    {verdict}")
