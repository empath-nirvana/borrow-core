import Core.EffPrograms
import Core.EffCancel
import Core.EffExamples

/-!
# Backend — kernel programs

The programs of `Core/` that the surface cannot spell, compiled by `bcc kernel`. The backend
lowers their operations in `Backend/Clos/Capture.lean` and `Backend/Clos/Unwind.lean`.

- Spec §19's acceptance programs, each a closed term with a `CDerives` derivation in
  `Core/EffPrograms.lean`.
- The two handled programs of `Core/EffExamples.lean`, typed there: a clause that resumes `κ` in
  tail position (`prog`), and one that cancels it (`progC`).
- The cancels of `Core/EffCancel.lean`, a finaliser that raises during a cancel: `prog`, its error
  suppressed (`prog_run`); and `prog₃` with an answer clause that tags the value, its error
  re-raised at the canceller and caught outside the region (`prog₃_run`).
- Terms that exercise the lowering's other shapes (*Shapes*, below). They are not typed: each
  stage is compared with `Support`'s interpreter on them.
-/

namespace Backend
open BoCa.Fig16.LogRel.Core.EffPrograms

open BoCa.Fig16.LogRel.Core.CancelIntercept in
/-- `prog₃` (`Core/EffCancel.lean`) with `H₃`'s answer clause `λx. inj₁ x`: `inl ()` when the cancel
ends cleanly, `inr ()` when the finaliser's error reaches `H₃`. -/
def cancelKept : BoCa.Expr :=
  BoCa.BoLo.hndE (BoCa.BoLo.hndVal 3 (BoCa.Val.lam (.inj₁ (.var 0))) (BoCa.Val.pair c₃ BoCa.Val.unit))
    (body 3)

/-! ### Shapes

Each is a closed term the lowering takes a path of its own on: a loop of tail calls through a
suspension, recursion through a suspension point, a call that may reach two codes that suspend, a
handler inside a handler that forwards the outer one's operations (and a cancel through it), and
a continuation resumed twice. -/

namespace Shapes
open BoCa

/-- `let x = M in N`. -/
def letE (M N : Expr) : Expr := .app (.lam N) M

def i32E (n : UInt32) : Expr := .prim (.lit (.i32 n))

def hostE (op : HostOp) (a : Expr) : Expr := .app (.prim (.host op)) a

/-- `perform (n, (0, v))`. -/
def performU (n : UInt32) (v : Expr := .unit) : Expr :=
  .app (.prim .perform) (.pair (i32E n) (.pair (i32E 0) v))

/-- `handle_n e with (hr, (cl, ()))`. -/
def hndE (n : UInt32) (hr cl : Expr) (e : Expr) : Expr :=
  .app (.app (.prim .hnd) (.pair (i32E n) (.pair hr (.pair cl .unit)))) e

/-- `λx. x`. -/
def idE : Expr := .lam (.var 0)

/-- The clause that resumes `κ` in tail position with the argument: `λ(x, k). k.resume x`. -/
def resumeCl : Expr := .lam (.letpair (.var 0) (.app (.app (.var 0) (.inj₁ .unit)) (.var 1)))

/-- The clause that cancels `κ`: `λ(x, k). x; k.cancel`. -/
def cancelCl : Expr := .lam (.letpair (.var 0) (.seq (.var 1) (.app (.var 0) (.inj₂ .unit))))

/-- `x == 0`, a test (`inr ()` when it holds), and `x - 1`, at the variable `x`. -/
def isZero (x : Nat) : Expr := hostE (.rel .w32 .eq) (.pair (.var x) (i32E 0))
def pred (x : Nat) : Expr := hostE (.bin .w32 .sub) (.pair (.var x) (i32E 1))

/-- `loop x = if x == 0 then () else (yield (); loop (x - 1))`, the recursive call in tail
position, handled by a clause that resumes in tail position, `n` times. Constant stack. -/
def loopTail (n : UInt32) : Expr :=
  -- In the `case`'s arms, `x` is index 1 and `self` index 2.
  let B : Expr := .case (isZero 0) (.seq (performU 5) (.app (.var 2) (pred 1))) .unit
  hndE 5 idE resumeCl (.app (.val (Fig16.LogRel.Core.selfV B)) (i32E n))

/-- `rec x = if x == 0 then () else (rec (x - 1); yield ())`: the recursive call is a
resumption point, so each level's state holds the next level's suspended computation. -/
def recYield (n : UInt32) : Expr :=
  let B : Expr := .case (isZero 0) (.seq (.app (.var 2) (pred 1)) (performU 6)) .unit
  hndE 6 idE resumeCl (.app (.val (Fig16.LogRel.Core.selfV B)) (i32E n))

/-- `f () = yield ()` and `g () = yield (); yield ()`; `h` is one of them, chosen by a test the
analysis does not decide, and `h ()` is called under the handler. -/
def twoCallees : Expr :=
  let f : Expr := .lam (performU 7)
  let g : Expr := .lam (.seq (performU 7) (performU 7))
  hndE 7 idE resumeCl
    (letE (.case (hostE (.rel .w32 .eq) (.pair (i32E 1) (i32E 1))) f g) (.app (.var 0) .unit))

/-- `handle_9 (handle_10 (yield₉ (); yield₁₀ (); yield₉ ())) …`: the inner handler forwards the
outer one's operations. -/
def forward : Expr :=
  hndE 9 idE resumeCl (hndE 10 idE resumeCl
    (.seq (performU 9) (.seq (performU 10) (performU 9))))

/-- The outer handler cancels a continuation that holds the inner handler, a cell and its
finaliser: `handle_9 (handle_10 (r ← alloc (); yield₉ () then x. free r; x unwind free r))`, the
clause of `9` cancelling. The cell is freed by the cancel. -/
def forwardCancel : Expr :=
  -- `thenE N D M` binds `x` in `N` and `_` in `D`; `r` is index 1 under either.
  let freeR : Expr := .case (.app (.prim .free) (.var 1)) (.var 0) (.var 0)
  let body : Expr := letE (.app (.prim .alloc) (.inj₁ .unit))
    (Fig16.LogRel.Core.thenE (.seq freeR (.var 0)) freeR (performU 9))
  hndE 9 idE cancelCl (hndE 10 idE resumeCl body)

/-- `choose ()`, resumed twice: `handle (case choose () {inl _ ⇒ 1 | inr _ ⇒ 10})` with the clause
`λ(x, k). k.resume (inl ()) + k.resume (inr ())`, which answers `11`. -/
def multiShot : Expr :=
  let cl : Expr := .lam (.letpair (.var 0) (hostE (.bin .w32 .add)
    (.pair (.app (.app (.var 0) (.inj₁ .unit)) (.inj₁ .unit))
      (.app (.app (.var 0) (.inj₁ .unit)) (.inj₂ .unit)))))
  hndE 8 idE cl (.case (performU 8) (i32E 1) (i32E 10))

end Shapes

/-- The kernel programs `bcc kernel` compiles, by name. -/
def kernelPrograms : List (String × BoCa.Expr) :=
  [ ("log-outside", logOutside),
    ("fail-outside", failOutside),
    ("reborrow-raise", reborrowRaise),
    ("log-in-borrow", logInBorrow),
    ("tick-answering", tickAnsProg 3),
    ("log-outside-native", nLogOutside),
    ("fail-outside-native", nFailOutside),
    ("tick-native", tickProg 3),
    ("take", takeProg 1),
    ("take-all", takeProg 5),
    ("store-cancel", storeCancel),
    ("resume-tail", BoCa.Fig16.LogRel.Core.EffExamples.prog),
    ("cancel-now", BoCa.Fig16.LogRel.Core.EffExamples.progC),
    ("cancel-suppressed", BoCa.Fig16.LogRel.Core.CancelIntercept.prog),
    ("cancel-reraised", cancelKept),
    ("loop-tail", Shapes.loopTail 100000),
    ("recursive-yield", Shapes.recYield 20),
    ("two-callees", Shapes.twoCallees),
    ("forward", Shapes.forward),
    ("forward-cancel", Shapes.forwardCancel),
    ("multi-shot", Shapes.multiShot) ]

end Backend
