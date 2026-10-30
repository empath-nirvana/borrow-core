import Paper.S2_Statics.Definitions
import Backend.Falsify

/-!
# Backend — the falsifier's negative tests

Untyped closed terms, each of which breaks one rule the falsifier checks
(`Backend/Falsify.lean`, docs/async-capabilities.md §6.1). No typed program builds any of them:
each is the shape of a bug the type system rules out. Each names the mode that must report it
and a part of the report; `scripts/falsify.sh` runs them (`bcc kernel negatives`), and checks
that the mode fails with that report and that `Support`'s interpreter gives the answer listed
(the fault is invisible to it, or it is stuck).
-/

namespace Backend.FalsifyTests
open BoCa

def lit (n : UInt32) : Expr := .prim (.lit (.i32 n))
def allocE (e : Expr) : Expr := .app (.prim .alloc) e
def freeE (e : Expr) : Expr := .app (.prim .free) e
def loadE (e : Expr) : Expr := .app (.prim .load) e
def storeE (a b : Expr) : Expr := .app (.app (.prim .store) a) b
/-- `let x = e; body`, `x` the variable `0` of `body`. -/
def letE (e body : Expr) : Expr := .app (.lam body) e
/-- `withbor x (Λ. λm. body)`: `m` is `0` in `body`, and every outer variable is shifted by 2. -/
def borrowE (x body : Expr) : Expr := .app (.app BoCa.withbor x) (.lam (.lam body))
/-- `withload x (Λ. λc. body)`. -/
def loadWithE (x body : Expr) : Expr := .app (.app BoCa.withload x) (.lam (.lam body))
/-- `let (o, v) = e; free o; v`: the owner back from a lend, freed, and the answer. -/
def finishE (e : Expr) : Expr := .letpair e (.seq (letE (freeE (.var 1)) .unit) (.var 0))

/-- `let r = alloc 5; free r; let s = alloc 7; let v = load r; free s; v`: a use after free.
The least-free allocator gives `s` the location `r` had, so the run reads `7`, silently. -/
def uafReuse : Expr :=
  letE (allocE (lit 5)) <|
  letE (freeE (.var 0)) <|
  letE (allocE (lit 7)) <|
  letE (loadE (.var 2)) <|
  .seq (letE (freeE (.var 1)) .unit) (.var 0)

/-- `let r = alloc 5; let (r, m) = withbor r (Λ. λm. m); load m; free r`: the view returned out
of its lend and read after the lend ended. -/
def staleView : Expr :=
  letE (allocE (lit 5)) <|
  .letpair (borrowE (.var 0) (.var 0)) <|
  letE (loadE (.var 0)) <|
  .seq (letE (freeE (.var 2)) .unit) (.var 0)

/-- `withbor r (Λ. λm. r := 9; *m)`: the callback writes through the owner while it is lent. -/
def ownerWhileLent : Expr :=
  letE (allocE (lit 5)) <|
  finishE (borrowE (.var 0) (.seq (storeE (.var 2) (lit 9)) (loadE (.var 0))))

/-- `withbor r (Λ. λm. withbor m (Λ. λm₂. m := 1; m₂ := 2; *m₂))`: a write through the outer
view while the reborrow above it is live: two `mut` views of one cell in use. -/
def aliasedWrite : Expr :=
  letE (allocE (lit 5)) <|
  .letpair
    (borrowE (.var 0)
      (borrowE (.var 0) (.seq (storeE (.var 2) (lit 1)) (.seq (storeE (.var 0) (lit 2))
        (loadE (.var 0)))))) <|
  .letpair (.var 0) <|
  .seq (letE (freeE (.var 3)) .unit) (.var 0)

/-- The handler of name `5` whose one clause receives `(w, κ)`, reads `w`, and resumes `κ` with
`()` (`resume = true`), or answers `0` and drops `κ`. -/
def hnd5 (resume : Bool) : Val :=
  let clause : Expr :=
    if resume then
      .lam (.letpair (.var 0) (letE (loadE (.var 1))
        (.seq (letE (.var 0) .unit) (.app (.app (.var 1) (.inj₁ .unit)) .unit))))
    else .lam (.letpair (.var 0) (.pair (lit 0) (lit 0)))
  BoLo.hndVal 5 .unit (.lam (.var 0)) ⟨.pair clause .unit, by simp only [clause]; split <;> exact .pair .lam .unit⟩

/-- A lend whose callback performs `5` with the view as its argument: the handler, outside the
lend, reads the view while the lend is suspended at the stop. -/
def suspendedView : Expr :=
  letE (allocE (lit 5)) <|
  finishE (BoLo.hndE (hnd5 true)
    (borrowE (.var 0)
      (.seq (BoLo.performE (.pair (lit 5) (.pair (lit 0) (.var 0)))) (loadE (.var 0)))))

/-- `withbor outer (Λ. λm. withload m (Λ. λc. c := 9))`, `outer` holding the owner of `inner`:
`withload` hands the contents as an `imm` view, and the callback writes through it. -/
def immWrite : Expr :=
  letE (allocE (lit 5)) <|
  letE (allocE (.var 0)) <|
  .letpair (borrowE (.var 0) (loadWithE (.var 0) (storeE (.var 0) (lit 9)))) <|
  letE (freeE (.var 1)) <|
  freeE (.var 0)

/-- A lend whose callback performs `5`, whose handler drops the continuation: the lend never
ends, and the owner is lost with the continuation (`live 1`). -/
def droppedLend : Expr :=
  letE (allocE (lit 5)) <|
  BoLo.hndE (hnd5 false)
    (borrowE (.var 0)
      (.seq (BoLo.performE (.pair (lit 5) (.pair (lit 0) (.var 0)))) (loadE (.var 0))))

/-- A loop whose first observation begins a lend and answers the rest of the loop with the lend
neither ended nor held by a suspended continuation: `let r = alloc 5; λ_. let (t, v) = LEND r;
inr (λ_. inl 0)`. The marker is called with no frame around the callback, the shape of a lend
that leaves its scope while active. It is driven as a `main` that returns a loop
(`loopNegatives`); at the boundary after the first observation the lend is active. -/
def activeAtBoundary : Expr :=
  letE (allocE (lit 5)) <|
  .lam (.letpair (.app (Falsify.mk Falsify.markLend) (.var 1)) (.inj₂ (.lam (.inj₁ (lit 0)))))

/-- R2's term (`lendLoopApp`) at `r`, the variable `0`, with the steps `N`, `K` and the first
state `s₀`, each untyped. -/
def r2Loop (N K s0 : Expr) : Expr :=
  BoCa.Fig16.LogRel.Core.lendLoopApp (.int .w32) .unit (.int .w32) N K s0

/-- R2's loop over `r = alloc 5` whose close step hands the view out (`K = let (v, s) = q; v`),
which no typed close step can (`R` is free of the lend's lifetime): after the close, the owner is
written and the view read. Under R2's rule the tag ended at the close. -/
def r2AfterClose : Expr :=
  letE (allocE (lit 5)) <|
  letE (r2Loop (.inj₂ .unit) (.letpair (.var 0) (.var 1)) .unit) <|
  .letpair (.app (.var 0) (.inj₂ .unit)) <|
  .seq (storeE (.var 1) (lit 9)) <|
  letE (loadE (.var 0)) <|
  .seq (letE (freeE (.var 2)) .unit) (.var 0)

/-- R2's loop over `r = alloc 5` whose next step finishes the loop and hands the view out with
the owner (`N = let (v, s) = q; inl v`), which no typed step can (`B` is free of the lend's
lifetime): the owner is written, then the view read. Under R2's rule the tag ended when
the step answered `inl`. -/
def r2AfterFinish : Expr :=
  letE (allocE (lit 5)) <|
  letE (r2Loop (.letpair (.var 0) (.inj₁ (.var 1))) (.letpair (.var 0) (.var 0)) .unit) <|
  .case (.app (.var 0) (.inj₁ .unit))
    (.letpair (.var 0) (.seq (storeE (.var 1) (lit 9))
      (letE (loadE (.var 0)) (.seq (letE (freeE (.var 2)) .unit) (.var 0)))))
    (lit 0)

/-- R2's loop over `r = alloc 5` whose next step stores the view in an outer cell `c` and goes
on (`N = let (v, s) = q; c := v; inr s`), which no typed step can (`N` is closed but for `q`):
between the two observations the view is read out of `c`. Under R2's rule the tag is parked
there, live and suspended. -/
def r2Between : Expr :=
  letE (allocE (lit 0)) <|
  letE (allocE (lit 5)) <|
  letE (r2Loop (.letpair (.var 0) (.seq (storeE (.var 5) (.var 1)) (.inj₂ (.var 0)))) (lit 0)
    .unit) <|
  .case (.app (.var 0) (.inj₁ .unit))
    (lit 0)
    (letE (loadE (loadE (.var 3))) <|
      .letpair (.app (.var 1) (.inj₂ .unit)) <|
      .seq (letE (freeE (.var 1)) .unit) (.seq (letE (freeE (.var 6)) .unit) (.var 2)))

/-- `reify` (`Core/DivReify.lean`) of a computation that lends `r` (`withbor`), stores the view in
an outer cell `c`, and ticks, which no typed computation can (a lend's callback is closed but for
its view): the tick is answered by `reify`'s handler, which answers the loop holding the
continuation, the lend open inside it. The consumer then reads through the view out of `c`, and
closes the loop (the tick answered *close*, the lend ends, the residual `λb. b` hands back the
owner and the answer). Under R1's rule the tag is suspended while `reify`'s loop holds it. -/
def reifyBetween : Expr :=
  letE (allocE (lit 0)) <|
  letE (allocE (lit 5)) <|
  letE (.app (.val (BoCa.Fig16.LogRel.Core.reifyV ⟨.lam (.var 0), .lam⟩)) (.lam (.inj₁
      (borrowE (.var 1) (.seq (storeE (.var 4) (.var 0))
        (letE (BoLo.performE (.pair (.prim (.lit (.i32 4294967295))) (.pair (lit 0) .unit)))
          (lit 0))))))) <|
  letE (loadE (loadE (.var 2))) <|
  .letpair (.app (.var 1) (.val closeV)) <|
  .seq (letE (freeE (.var 1)) .unit) (.seq (letE (freeE (.var 5)) .unit) (.var 2))

/-- Each negative test: its name, its term, the mode that must report it, a part of the report,
and what `Support`'s interpreter answers. -/
def negatives : List (String × Expr × String × String × String) :=
  [("neg-uaf-reuse", uafReuse, "fresh", "use after free of location 0",
      "source interpreter: stuck (BoCa.Stuck.useAfterFree)"),
   ("neg-stale-view", staleView, "tags", "after its lend ended", "i32[5]"),
   ("neg-owner-while-lent", ownerWhileLent, "tags", "through the owner while tag 1", "i32[9]"),
   ("neg-aliased-write", aliasedWrite, "tags", "write of location 0 through tag 1 (lend) while tag 2",
      "i32[2]"),
   ("neg-suspended-view", suspendedView, "tags", "while its lend is suspended", "i32[5]"),
   ("neg-imm-write", immWrite, "tags", "write of location 0 through an imm tag", "i32[9]"),
   ("neg-dropped-lend", droppedLend, "tags", "never ended", "live 1"),
   ("neg-active-at-boundary", activeAtBoundary, "tags", "active at an observation boundary",
      "source interpreter: stuck"),
   ("neg-r2-after-close", r2AfterClose, "tags", "after its lend ended", "i32[9]"),
   ("neg-r2-after-finish", r2AfterFinish, "tags", "after its lend ended", "i32[9]"),
   ("neg-r2-between", r2Between, "tags", "while its lend is suspended", "i32[5]"),
   ("neg-reify-between", reifyBetween, "tags", "while its lend is suspended", "i32[5]")]

/-- The negative tests that are loops: each is driven as a `main` that returns a loop is, one
observation at a time (`Falsify.interpLoop`, `Source.interpLoop`). -/
def loopNegatives : List String := ["neg-active-at-boundary"]

end Backend.FalsifyTests
