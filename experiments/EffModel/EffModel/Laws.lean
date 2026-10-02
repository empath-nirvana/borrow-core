import EffModel.Prelude

/-!
# EffModel — laws, checked observationally

A law `M ≡ N` is checked as: in every context of a suite in which both sides type, both sides
produce the same observable (outcome, world trace, leaks).

**The suite.** A law names the instances its two sides leave free, and for each one a list of
implementations (handlers into `F A` or into a function type, or runners over an owned
capability). A context is

- an **order** of the instances (every permutation): which binder is outermost;
- an **implementation** for each (every combination);
- an **inner frame** around the hole, inside every binder: nothing; a `using` frame whose
  destructor is observable; a `to` that emits the answer; a handler of an unrelated fresh
  `Fail` instance (which must not handle anything).

So a law with two free instances, of three and two implementations, is checked in
`2 × 6 × 4 = 48` contexts, less those in which a side does not type. Some laws hold only in some
contexts (sum versus tensor); for those the law states the contexts in which it should hold, and
the check is that it holds in exactly those.
-/

namespace EffModel

/-- A context: the instances innermost first, each with its implementation, and the frame. -/
structure CtxDesc where
  order : List (String × String)
  frame : String
  deriving Repr

def CtxDesc.show (d : CtxDesc) : String :=
  String.intercalate " < " (d.order.map (fun (x, i) => s!"{x}:{i}")) ++ s!" [{d.frame}]"

/-- Is `x` bound outside `y`? -/
def CtxDesc.outside (d : CtxDesc) (x y : String) : Bool :=
  (d.order.map (·.1)).idxOf x > (d.order.map (·.1)).idxOf y

def CtxDesc.impl (d : CtxDesc) (x : String) : String := (d.order.lookup x).getD ""

def insertAll (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

def choices : List (String × List Impl) → List (List (String × Impl))
  | [] => [[]]
  | (x, is) :: rest => is.flatMap (fun i => (choices rest).map ((x, i) :: ·))

/-- Inner frames around a hole of type `int`. -/
def frames : List (String × (Tm → Tm)) := [
  ("none", id),
  ("using", fun M => .using "r9" 9 (.bind M "v9" (seq (.use (v "r9")) (.ret (v "v9"))))),
  ("emit", fun M => .bind M "v7" (emitThen (v "v7") (.ret (v "v7")))),
  ("fresh-handler", fun M => .handle "q9" "Fail" (hDefault (n 0)) [] (.F .int) M)]

/-- Close a term under the layers, innermost first. -/
def closeUnder : List (String × Impl) → VTy → Tm → Option Tm
  | [], _, M => some M
  | (x, i) :: rest, A, M => do
      let (M', A') ← i.wrap x A (rest.map (fun (y, _) => .i y)) M
      closeUnder rest A' M'

/-- Every context of the suite, as a description and a closing function. -/
def suite (layers : List (String × List Impl)) : List (CtxDesc × (Tm → Option Tm)) :=
  (perms layers).flatMap fun ord =>
    (choices ord).flatMap fun ch =>
      frames.map fun (fn, fr) =>
        (⟨ch.map (fun (x, i) => (x, i.name)), fn⟩, fun M => closeUnder ch .int (fr M))

structure Law where
  name : String
  lhs : Tm
  rhs : Tm
  layers : List (String × List Impl)
  /-- The contexts in which the law should hold. -/
  expect : CtxDesc → Bool := fun _ => true

instance : Inhabited Law := ⟨{ name := "", lhs := .unit, rhs := .unit, layers := [] }⟩

structure LawResult where
  name : String
  contexts : Nat
  typed : Nat
  holds : Nat
  /-- Contexts where the outcome differs from `expect`, or one side types and the other not. -/
  surprises : List String
  deriving Repr

def LawResult.ok (r : LawResult) : Bool := r.surprises.isEmpty && r.typed > 0

def checkLaw (L : Law) : LawResult :=
  let rows := (suite L.layers).filterMap fun (d, close) => do
    let l ← close L.lhs
    let r ← close L.rhs
    pure (d, accepts sigs l, accepts sigs r, run sigs l == run sigs r)
  let typed := rows.filter (fun (_, a, b, _) => a && b)
  let holds := typed.filter (fun (_, _, _, e) => e)
  let surprises :=
    (rows.filter (fun (_, a, b, _) => a != b)).map (fun (d, a, _, _) =>
      s!"typing differs ({if a then "rhs" else "lhs"} rejected) at {d.show}") ++
    (typed.filter (fun (d, _, _, e) => e != L.expect d)).map (fun (d, _, _, e) =>
      s!"{if e then "holds" else "fails"} at {d.show}")
  ⟨L.name, rows.length, typed.length, holds.length, surprises⟩

/-! ## The laws -/

/-- `Log` printed with a tag added: distinguishes two handlers. -/
def hTag (t : Int) : Hnd :=
  .cl "log" "p" "k" (letAdd "pt" (v "p") (n t) (emitThen (v "pt") (call (v "k") .unit)))
    (.ret "a" (.ret (v "a")))

/-- `Log` printed, with a return clause that is observable and not the identity. -/
def hRE : Hnd :=
  .cl "log" "p" "k" (emitThen (v "p") (call (v "k") .unit))
    (.ret "a" (emitThen (v "a") (add (v "a") (n 1))))

def LF : List (String × List Impl) := [("l", logImpls), ("f", failImpls)]

/-- L1a, algebraicity, at each kind of frame and at arity 0. -/
def algebraicity : List Law := [
  { name := "L1a at `to`: (op; y.M) to z. N ≡ op; y.(M to z. N)"
    lhs := .bind (log "l" (n 1) (.ret (n 5))) "z" (log "l" (v "z") (.ret (v "z")))
    rhs := log "l" (n 1) (.bind (.ret (n 5)) "z" (log "l" (v "z") (.ret (v "z"))))
    layers := LF },
  { name := "L1a at a function type: (op; y.M) w ≡ op; y.(M w)"
    lhs := .app (log "l" (n 1) (.lam "w" .int (log "l" (v "w") (add (v "w") (n 1))))) (n 4)
    rhs := log "l" (n 1) (.app (.lam "w" .int (log "l" (v "w") (add (v "w") (n 1)))) (n 4))
    layers := LF },
  { name := "L1a at a record type: π₁ (op; y.M) ≡ op; y.(π₁ M)"
    lhs := .prj true (log "l" (n 1) (.rcd (log "l" (n 2) (.ret (n 1))) (raise "f")))
    rhs := log "l" (n 1) (.prj true (.rcd (log "l" (n 2) (.ret (n 1))) (raise "f")))
    layers := LF },
  { name := "L1a with an affine operation (a consumer may cancel κ)"
    lhs := .bind (yld "y" (n 1) (.ret (n 5))) "z" (yld "y" (v "z") (.ret (v "z")))
    rhs := yld "y" (n 1) (.bind (.ret (n 5)) "z" (yld "y" (v "z") (.ret (v "z"))))
    layers := [("y", yieldImpls), ("f", failImpls)] },
  { name := "L1a with a multi-shot operation (κ resumed twice)"
    lhs := .bind (.op "ch" "choose" .unit "b" (.ite (v "b") (.ret (n 1)) (.ret (n 2)))) "z"
      (log "l" (v "z") (add (v "z") (n 10)))
    rhs := .op "ch" "choose" .unit "b"
      (.bind (.ite (v "b") (.ret (n 1)) (.ret (n 2))) "z" (log "l" (v "z") (add (v "z") (n 10))))
    layers := [("ch", chooseImpls), ("l", logImpls)] },
  { name := "L1a at arity 0: raise to z. N ≡ raise"
    lhs := .bind (raise "f") "q" (log "l" (v "q") (.ret (v "q")))
    rhs := raise "f"
    layers := LF },
  { name := "L1a at arity 0, function type: (raise) w ≡ raise"
    lhs := .app (raise "f" (.arr "w" .int [] (.F .int))) (n 4)
    rhs := raise "f"
    layers := LF },
  { name := "L1a at arity 0, destructor form: K[raise] ≡ D_K; raise"
    lhs := .using "r" 1 (.bind (raise "f") "q" (seq (.use (v "r")) (.ret (v "q"))))
    rhs := seq (.using "r" 1 (.ret .unit)) (raise "f")
    layers := LF }]

/-- L2, the handler laws, with `ν` and `handleAt` so that `κ` can name the instance. -/
def handlerLaws : List Law :=
  let M := log "h" (n 3) (log "l" (n 4) (.ret (n 10)))
  let H (M : Tm) : Tm := .handleAt "h" hRE [] (.F .int) M
  let nuH (M : Tm) : Tm := .nu "h" "Log" (bnd "Log") M
  [{ name := "H-ret: handle (return v) ≡ h_ret v"
     lhs := .handle "h" "Log" hRE [] (.F .int) (.ret (n 3))
     rhs := emitThen (n 3) (add (n 3) (n 1))
     layers := LF },
   { name := "H-op: handle (op_h v; y.M) ≡ h_op(v, λy. handle M)"
     lhs := nuH (H (.op "h" "log" (n 2) "y" M))
     rhs := nuH (emitThen (n 2) (call (.thunk Mode.lin (.lam "y" .unit (H M))) .unit))
     layers := LF },
   { name := "H-fwd: handle_h (op_l v; y.M) ≡ op_l v; y. handle_h M"
     lhs := nuH (H (log "l" (n 1) (log "h" (n 2) (.ret (n 0)))))
     rhs := nuH (log "l" (n 1) (H (log "h" (n 2) (.ret (n 0)))))
     layers := LF },
   { name := "H-fwd at arity 0: handle_h (raise_f) ≡ raise_f"
     lhs := nuH (H (raise "f"))
     rhs := raise "f"
     layers := LF }]

/-- L4: `Log` and `Fail` in both orders. The absorption law holds exactly where `Fail` is handled
outside a `Log` that is a pure model (the writer); where `Log` is outside, or prints to the
world, the log survives (the sum). The runner, a comodel over an owned capability, cannot be
placed inside `Fail` at all: the capability has no destructor. -/
def logFail : List Law := [
  { name := "L4 absorption: log m; raise ≡ raise (only with Fail outside a writer Log)"
    lhs := log "l" (n 7) (raise "f")
    rhs := raise "f"
    layers := LF
    expect := fun d => d.outside "f" "l" && d.impl "l" == "writer" }]

/-- Tensor: operations on disjoint capabilities commute; two printing handlers do not. -/
def commuting : List Law := [
  { name := "tensor: disjoint capabilities commute"
    lhs := inc "c1" (inc "c2" (get "c1" "g" (.ret (v "g"))))
    rhs := inc "c2" (inc "c1" (get "c1" "g" (.ret (v "g"))))
    layers := [("c1", ctrImpls), ("c2", ctrImpls)] },
  { name := "sum: two Log instances commute unless both print to the world"
    lhs := log "l1" (n 1) (log "l2" (n 2) (.ret (n 0)))
    rhs := log "l2" (n 2) (log "l1" (n 1) (.ret (n 0)))
    layers := [("l1", logImpls), ("l2", logImpls)]
    expect := fun d => !(d.impl "l1" == "print" && d.impl "l2" == "print") },
  { name := "sum for lent state: inc c; raise ≢ raise (the lend survives the abort)"
    lhs := inc "c" (raise "f")
    rhs := raise "f"
    layers := [("c", ctrImpls), ("f", failImpls)]
    expect := fun _ => false }]

/-- L6, Staton's instance laws, and abstraction safety as handler transparency. -/
def instanceLaws : List Law :=
  let LA := [("a", logImpls), ("f", failImpls)]
  let H (b : String) (t : Int) (M : Tm) : Tm := .handleAt b (hTag t) [] (.F .int) M
  let nu (b : String) (M : Tm) : Tm := .nu b "Log" (bnd "Log") M
  [{ name := "idem-ν: ν b. M ≡ M (b ∉ M)"
     lhs := nu "b" (log "a" (n 1) (.ret (n 0)))
     rhs := log "a" (n 1) (.ret (n 0))
     layers := LA },
   { name := "ν/ν: ν b₁. ν b₂. M(b₁,b₂) ≡ ν b₁. ν b₂. M(b₂,b₁)"
     lhs := nu "b1" (nu "b2" (H "b1" 100 (H "b2" 200
       (log "b1" (n 1) (log "b2" (n 2) (log "a" (n 3) (.ret (n 0))))))))
     rhs := nu "b1" (nu "b2" (H "b2" 100 (H "b1" 200
       (log "b2" (n 1) (log "b1" (n 2) (log "a" (n 3) (.ret (n 0))))))))
     layers := LA },
   { name := "ν/op: ν b. op_a(v; y.M b) ≡ op_a(v; y. ν b. M b)"
     lhs := nu "b" (log "a" (n 1) (H "b" 100 (log "b" (n 2) (.ret (n 0)))))
     rhs := log "a" (n 1) (nu "b" (H "b" 100 (log "b" (n 2) (.ret (n 0)))))
     layers := LA },
   { name := "new-ν: ν b. (if a = b then M else N) ≡ ν b. N"
     lhs := nu "b" (.bind (.ieq "a" "b") "e" (.ite (v "e") (.ret (n 1)) (.ret (n 2))))
     rhs := nu "b" (.ret (n 2))
     layers := LA },
   { name := "no accidental handling: ν h. handle_h M ≡ M (h ∉ M, return clause the identity)"
     lhs := .nu "h" "Fail" (bnd "Fail")
       (.handleAt "h" (hDefault (n 0)) [] (.F .int) (log "l" (n 1) (raise "f")))
     rhs := log "l" (n 1) (raise "f")
     layers := LF }]

def allLaws : List Law := algebraicity ++ handlerLaws ++ logFail ++ commuting ++ instanceLaws

def lawResults : List LawResult := allLaws.map checkLaw

end EffModel
