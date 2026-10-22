# The injected bugs of H8: each a variant of an accepted term, one textual change.
# kind: MEMORY (the kernel must reject) or SEMANTIC (expected to be accepted).
import os
here = os.path.dirname(os.path.abspath(__file__))
base = os.path.dirname(here)
bugs = [
  ("m1-read-after-free", "MEMORY", "h8b-for-lend-index.bc",
   "        r <- return (unbang read) (a, i);",
   "        z <- return (unbang array_free[i32]) ((!thunkv fun (x : i32) -> return ()), a);\n        r <- return (unbang read) (a, i);"),
  ("m2-view-family-used-after-move", "MEMORY", "h8a2-for-lend-view-external.bc",
   "                  case (unbang array_get['l, i32]) (w2, i) {",
   "                  case (unbang array_get['l, i32]) (w, i) {"),
  ("m3-double-free-cell", "MEMORY", "h8c-list-cursor-refold.bc",
   "        let (c, k) = s; return () >",
   "        let (c, k) = s; d <- return free[L] c; d2 <- return free[L] c; return () >"),
  ("m4-owned-list-duplicated", "MEMORY", "h8d-list-ownership-walk.bc",
   "return (inl (x, (rest, ((roll inr (x, back) : L), (unbang host[add32]) (k, i32[1])))) : i32 * (L * (L * i32)) + (1 + L * (L * i32)))",
   "return (inl (x, (rest, ((roll inr (x, rest) : L), (unbang host[add32]) (k, i32[1])))) : i32 * (L * (L * i32)) + (1 + L * (L * i32)))"),
  ("m5-close-drops-lists", "MEMORY", "h8d-list-ownership-walk.bc",
   "        let (front, q) = s; let (back, k) = q; return () >",
   "        return () >"),
  ("s1-skips-elements", "SEMANTIC", "h8b-for-lend-index.bc",
   "inl x -> return (inl (x, (a, (unbang host[add32]) (i, i32[1]))) : i32 * S + (1 + S))",
   "inl x -> return (inl (x, (a, (unbang host[add32]) (i, i32[2]))) : i32 * S + (1 + S))"),
]
# m6-view-stored-in-state.bc is written by hand.
for name, kind, src, old, new in bugs:
    s = open(os.path.join(base, src)).read()
    assert s.count(old) == 1, (name, s.count(old))
    s = s.replace(old, new)
    s = f"-- H8 injected bug {name} ({kind}), a variant of `{src}`.\n" + s
    open(os.path.join(here, name + ".bc"), "w").write(s)
    print(name, kind)
