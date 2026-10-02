import EffModel.Typing
import EffModel.Eval

/-!
# EffModel — effects, handlers and runners used by the tests

One signature per effect; an instance of it is implemented either by a handler (a model, which
receives `κ`) or, when every operation is tail-resumptive, by a runner over an owned capability
(a comodel, which answers in place).
-/

namespace EffModel

/-- The effects. `Log` and `Ctr` are tail-resumptive (`κ` linear); `Fail` is abortive; `Yield`
and `Tick` affine (a consumer or a timeout may stop); `Choose` multi-shot; `Again` relevant
(resumed at least once). -/
def sigs : Sigs := [
  ("Log", [⟨"log", .int, .unit, Mode.lin⟩]),
  ("Fail", [⟨"raise", .unit, .void, Mode.aff⟩]),
  ("Yield", [⟨"yield", .int, .unit, Mode.aff⟩]),
  ("Choose", [⟨"choose", .unit, .bool, Mode.unr⟩]),
  ("Tick", [⟨"tick", .unit, .unit, Mode.aff⟩]),
  ("Ctr", [⟨"inc", .unit, .unit, Mode.lin⟩, ⟨"get", .unit, .int, Mode.lin⟩]),
  ("Again", [⟨"again", .unit, .unit, Mode.rel⟩])]

def bnd (e : String) : Bound := boundOf ((sigs.lookup e).getD [])

/-! ## Term sugar -/

def v (x : String) : Tm := .var x
def n (k : Int) : Tm := .int k
def log (l : String) (a : Tm) (M : Tm) : Tm := .op l "log" a "_" M
def raise (f : String) (c : CTy := .F .int) : Tm := .op f "raise" .unit "z_" (.absurd (v "z_") c)
def yld (y : String) (a : Tm) (M : Tm) : Tm := .op y "yield" a "_" M
def inc (c : String) (M : Tm) : Tm := .op c "inc" .unit "_" M
def get (c x : String) (M : Tm) : Tm := .op c "get" .unit x M
def tick (t : String) (M : Tm) : Tm := .op t "tick" .unit "_" M
def add (a b : Tm) : Tm := .prim .add a b
def sub (a b : Tm) : Tm := .prim .sub a b
/-- `let x = a + b in M`. -/
def letAdd (x : String) (a b : Tm) (M : Tm) : Tm := .bind (add a b) x M
def emitThen (a : Tm) (M : Tm) : Tm := seq (.emit a) M

/-! ## Handlers -/

/-- `Log` printed to the world, `κ` resumed in place. -/
def hPrint : Hnd :=
  .cl "log" "p" "k" (emitThen (v "p") (call (v "k") .unit)) (.ret "a" (.ret (v "a")))

/-- `Log` as a writer: the handler is a function of the running total (a handler into a
function type), and the total is emitted once, at the end. -/
def hWriter : Hnd :=
  .cl "log" "p" "k"
    (.lam "s" .int (letAdd "s1" (v "s") (v "p") (.app (call (v "k") .unit) (v "s1"))))
    (.ret "a" (.lam "s" .int (.ret (.pair (v "a") (v "s")))))

def writerC (A : VTy) (ρ : Row) : CTy := .arr "s" .int ρ (.F (.prod A .int))

/-- `Fail` to an option. -/
def hOpt (A : VTy) : Hnd :=
  .cl "raise" "p" "k" (.ret (.inr A .unit)) (.ret "a" (.ret (.inl (v "a") .unit)))

/-- `Fail` to a default. -/
def hDefault (d : Tm) : Hnd :=
  .cl "raise" "p" "k" (.ret d) (.ret "a" (.ret (v "a")))

/-- `Yield` printed, `κ` resumed. -/
def hYieldPrint : Hnd :=
  .cl "yield" "p" "k" (emitThen (v "p") (call (v "k") .unit)) (.ret "a" (.ret (v "a")))

/-- `Yield` consumed `n` at a time: after the budget, `κ` is dropped (cancelled). -/
def hTake : Hnd :=
  .cl "yield" "p" "k"
    (.lam "m" .int (.bind (.prim .eq (v "m") (n 0)) "z0"
      (.ite (v "z0") (.ret (.inr .int .unit))
        (emitThen (v "p") (.bind (sub (v "m") (n 1)) "m1" (.app (call (v "k") .unit) (v "m1")))))))
    (.ret "a" (.lam "m" .int (.ret (.inl (v "a") .unit))))

def takeC (ρ : Row) : CTy := .arr "m" .int ρ (.F (.sum .int .unit))

/-- `Yield` summed into a running total. -/
def hYieldSum : Hnd :=
  .cl "yield" "p" "k"
    (.lam "s" .int (letAdd "s1" (v "s") (v "p") (.app (call (v "k") .unit) (v "s1"))))
    (.ret "a" (.lam "s" .int (.ret (.pair (v "a") (v "s")))))

/-- `Choose`, both ways, summed: `κ` resumed twice. -/
def hAllSum : Hnd :=
  .cl "choose" "p" "k"
    (.bind (.app (.force (v "k")) (.bool true)) "a1"
      (.bind (.app (.force (v "k")) (.bool false)) "a2" (add (v "a1") (v "a2"))))
    (.ret "a" (.ret (v "a")))

/-- `Choose`, the first way only. -/
def hFirst : Hnd :=
  .cl "choose" "p" "k" (.app (.force (v "k")) (.bool true)) (.ret "a" (.ret (v "a")))

/-- `Tick` counted against a budget: a timeout, into `budget → F (int + 1)`. When the budget is
spent the continuation is dropped, which cancels it. -/
def hTimeout : Hnd :=
  .cl "tick" "p" "k"
    (.lam "b" .int (.bind (.prim .eq (v "b") (n 0)) "z0"
      (.ite (v "z0") (.ret (.inr .int .unit))
        (.bind (sub (v "b") (n 1)) "b1" (.app (call (v "k") .unit) (v "b1"))))))
    (.ret "a" (.lam "b" .int (.ret (v "a"))))

/-- `Tick` ignored. -/
def hTickIgnore : Hnd :=
  .cl "tick" "p" "k" (call (v "k") .unit) (.ret "a" (.ret (v "a")))

/-- `Yield` to a stored generator: the clause returns the continuation, so the handler keeps it
(it is not tail-resumptive) and its instance's bound says it may suspend. -/
def hStream : Hnd :=
  .cl "yield" "p" "k" (.ret (.inr .int (.pair (v "p") (.thunk Mode.lin (call (v "k") .unit)))))
    (.ret "a" (.ret (.inl (v "a") (.prod .int (.stream [] .int)))))

def streamC : CTy := .F (.sum .int (.prod .int (.stream [] .int)))

/-! ## Comodels -/

/-- A counter's co-operations: state access `A × S → F (B × S)`. -/
def coCtr : Hnd :=
  .cl "inc" "q" "_" (.split (v "q") "u" "s" (letAdd "s1" (v "s") (n 1) (.ret (.pair .unit (v "s1")))))
  (.cl "get" "q" "_" (.split (v "q") "u" "s" (.ret (.pair (v "s") (v "s"))))
  (.ret "_" (.ret .unit)))

/-- `Log` answered by a comodel that totals what is logged. -/
def coLog : Hnd :=
  .cl "log" "q" "_" (.split (v "q") "w" "s" (letAdd "s1" (v "s") (v "w") (.ret (.pair .unit (v "s1")))))
  (.ret "_" (.ret .unit))

/-! ## Implementations of an instance, as layers around a term

A layer binds instance `x` around `M`, given `M`'s answer type `A` and the row `ρ` that the
outer layers handle, and answers the wrapped term's answer type, or `none` when it does not
apply at `A`. -/

structure Impl where
  name : String
  wrap : (x : String) → (A : VTy) → (ρ : Row) → Tm → Option (Tm × VTy)

def isInt : VTy → Bool | .int => true | _ => false

def logPrint : Impl := ⟨"print", fun x A _ M => some (.handle x "Log" hPrint [] (.F A) M, A)⟩
def logWriter : Impl := ⟨"writer", fun x A ρ M =>
  some (.bind (.app (.handle x "Log" hWriter [] (writerC A ρ) M) (n 0)) (x ++ "p")
    (.split (v (x ++ "p")) (x ++ "a") (x ++ "s")
      (emitThen (v (x ++ "s")) (.ret (v (x ++ "a"))))), A)⟩
/-- `Log` run against an owned capability lent for the scope; its total is emitted after. -/
def logRunner : Impl := ⟨"runner", fun x A _ M =>
  let c := x ++ "c"
  some (.bind (.newcap "Log" .int coLog (n 0)) c
    (.bind (.lend c x M) (x ++ "a")
      (.bind (.getcap (v c)) (x ++ "s") (emitThen (v (x ++ "s")) (.ret (v (x ++ "a")))))), A)⟩

def failOpt : Impl := ⟨"option", fun x A _ M =>
  some (.handle x "Fail" (hOpt A) [] (.F (.sum A .unit)) M, .sum A .unit)⟩
def failDefault : Impl := ⟨"default", fun x A _ M =>
  if isInt A then some (.handle x "Fail" (hDefault (n 99)) [] (.F A) M, A) else none⟩

def yieldPrint : Impl := ⟨"print", fun x A _ M => some (.handle x "Yield" hYieldPrint [] (.F A) M, A)⟩
def yieldSum : Impl := ⟨"sum", fun x A ρ M =>
  some (.bind (.app (.handle x "Yield" hYieldSum [] (writerC A ρ) M) (n 0)) (x ++ "p")
    (.split (v (x ++ "p")) (x ++ "a") (x ++ "s")
      (emitThen (v (x ++ "s")) (.ret (v (x ++ "a"))))), A)⟩
def yieldTake1 : Impl := ⟨"take1", fun x A ρ M =>
  if isInt A then some (.app (.handle x "Yield" hTake [] (takeC ρ) M) (n 1), .sum .int .unit)
  else none⟩

def chooseAll : Impl := ⟨"all", fun x A _ M =>
  if isInt A then some (.handle x "Choose" hAllSum [] (.F .int) M, .int) else none⟩
def chooseFirst : Impl := ⟨"first", fun x A _ M => some (.handle x "Choose" hFirst [] (.F A) M, A)⟩

/-- A counter run against an owned capability; the final count is emitted after. -/
def ctrRunner : Impl := ⟨"runner", fun x A _ M =>
  let c := x ++ "c"
  some (.bind (.newcap "Ctr" .int coCtr (n 0)) c
    (.bind (.lend c x M) (x ++ "a")
      (.bind (.getcap (v c)) (x ++ "s") (emitThen (v (x ++ "s")) (.ret (v (x ++ "a")))))), A)⟩

def logImpls : List Impl := [logPrint, logWriter, logRunner]
def failImpls : List Impl := [failOpt, failDefault]
def yieldImpls : List Impl := [yieldPrint, yieldSum, yieldTake1]
def chooseImpls : List Impl := [chooseAll, chooseFirst]
def ctrImpls : List Impl := [ctrRunner]

end EffModel
