# The injected bugs of H2: each a variant of an accepted term, one textual change.
# kind: MEMORY (the kernel must reject) or SEMANTIC (expected to be accepted).
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
base = os.path.dirname(here)
bugs = [
  ("m1-double-free", "MEMORY", "h2c-cancel.bc",
   "inl v -> let (extra, q) = v; let (buf, r) = q; d <- return free[i32] buf; e <- return free[i32] extra; return ()",
   "inl v -> let (extra, q) = v; let (buf, r) = q; d <- return free[i32] buf; d2 <- return free[i32] buf; e <- return free[i32] extra; return ()"),
  ("m2-use-after-free", "MEMORY", "h2c-cancel.bc",
   "  let _ = free(buf);\n  let e = free(extra);\n  v + e",
   "  let _ = free(buf);\n  let w = borrow mut buf { m -> modify m { x -> (x, x) } };\n  let e = free(extra);\n  v + e"),
  ("m3-borrow-stored-in-state", "MEMORY", "h2c-cancel.bc",
   "let r = borrow mut buf { m -> let p = (m, 5); let (m0, k) = p; ((), k) };\n  (extra, (buf, r))",
   "let r = borrow mut buf { m -> let p = (m, 5); let (m0, k) = p; (m0, k) };\n  (extra, (buf, r))"),
  ("m4-task-duplicated", "MEMORY", "h2c-cancel.bc",
   "< c <- return cancel[i32](t); return (inl i32[2] : i32 + box top Task[i32]),",
   "< c <- return cancel[i32](t); c2 <- return cancel[i32](t); return (inl i32[2] : i32 + box top Task[i32]),"),
  ("m5-mutable-alias", "MEMORY", "h2c-cancel.bc",
   "let v = borrow mut buf { m -> let p = (m, k); let (m2, k2) = p; modify m2 { x -> (x, x + k2) } };",
   "let v = borrow mut buf { m -> let w = borrow mut buf { n -> modify n { x -> (x, x) } }; let p = (m, k); let (m2, k2) = p; modify m2 { x -> (x, x + k2) } };"),
  ("m6-close-leaks-extra", "MEMORY", "h2c-cancel.bc",
   "inl v -> let (extra, q) = v; let (buf, r) = q; d <- return free[i32] buf; e <- return free[i32] extra; return ()",
   "inl v -> let (extra, q) = v; let (buf, r) = q; d <- return free[i32] buf; return ()"),
  ("m7-resume-after-cancel", "MEMORY", "h2c-cancel.bc",
   "< c <- return cancel[i32](t); return (inl i32[2] : i32 + box top Task[i32]),",
   "< c <- return cancel[i32](t); o <- return resume[i32](t); return (inl i32[2] : i32 + box top Task[i32]),"),
  ("m8-free-lender-inside-lend", "MEMORY", "h2b-local-borrows-resupply.bc",
   "          s0 : 1 + 1 <- return inl ();",
   "          z <- return free[i32] c1;\n          s0 : 1 + 1 <- return inl ();"),
  ("s1-wrong-summand-resumed", "SEMANTIC", "h2c-local-borrows.bc",
   "| inr c -> return (inr (inl (counter_seg1 c) : i32 + SC) : i32 * SC + (i32 + SC))",
   "| inr c -> return (inl (i32[1], (inr c : SC)) : i32 * SC + (i32 + SC))"),
  ("s2-wrong-log-value", "SEMANTIC", "h2c-logged.bc",
   "return (inr (inr a, boxed[top] (inr (inl c) : S)) : R)",
   "return (inr (inr (a + 100), boxed[top] (inr (inl c) : S)) : R)"),
]
# m9-stored-borrow-escapes-lend.bc is written by hand (a multi-line change of h2a-pair-view-external-field.bc).
for name, kind, src, old, new in bugs:
    s = open(os.path.join(base, src)).read()
    assert s.count(old) == 1, (name, s.count(old))
    s = s.replace(old, new)
    s = f"-- H2 injected bug {name} ({kind}), a variant of `{src}`.\n" + s
    open(os.path.join(here, name + ".bc"), "w").write(s)
    print(name, kind)
