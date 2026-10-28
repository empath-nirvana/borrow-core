import Lowering.Print
import Lowering.Own

/-!
# Lowering — the print to the LIR  `[spec §56]`

The print turns a low term (`Lowering/Low.lean`) into a program of Backend2's LIR
(`Backend2/Syntax.lean`). It reads no type.

- **Closure conversion.** A `λb` becomes a closure `clos c env` of a code `c` of its own: `env`
  the slots the body captures (`capt b`), the code's function taking them, then the argument
  (`lamEnv b`). A function's variables are numbered from `0` in its own frame.
- **Named form.** Each subterm's value is bound to a fresh variable (`letv`), in the machine's
  order: a pair left first, an application its argument first.
- **Calls are dispatched** (`app`): no call is made direct, so no flow analysis is read.
- **Copies and drops.** A slot read where the rest of the term reads it again is read through a
  `copy`, and a binder its scope does not read is dropped where it is bound (a `case` arm also
  drops the slots only the other arm reads). This is how the kernel's constants are printed: their
  bodies are the kernel's closed terms (atoms of the low subset, `LowConst`), which duplicate
  their arguments. On `own`'s output (SPEC §54) every slot is consumed exactly once on every path
  that returns, which leaves the print none of its own on such a path outside the constants (an
  argument from `Explicit`, not machine-checked); a path that ends at `absurd` is reached by no
  run.
- **The source's memory** is kept as it is (`Op.cellNew`, …): a location is the LIR's address,
  a cell an object of one address, a family `(ℓ, n)` the pair of its base and its length. The
  machine's primitives are the closures of fixed codes, the program's first (`rtCode`,
  `preludePS`); a host operation's is written where it is used (`hostFn`).
- **The LIR is untyped here**: every variable is at `unit` (`tyTable`). The interpreter reads a
  variable's type only at its `copy`, `drop` and `load` checks and in printing `main`'s value;
  the print writes no `load`.

`Pr` is the print as a relation over the final program, with `lirOf_pr` saying the print's output
is in it; the simulation is proved over `Pr` (`Lowering/PrintFwd.lean`).
-/

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-! ### Slots -/

/-- The slots the rest of a term still reads, which a subterm must leave in the frame. -/
abbrev Out := Nat → Bool

/-- Either. -/
def unionO (o q : Out) : Out := fun k => o k || q k

/-- The slots `e` mentions past `d` binders. -/
def fvAt (d : Nat) (e : Expr) : Out := fun k => mentions e (k + d)

/-- `o` under `d` binders, which it does not hold. -/
def liftO (d : Nat) (o : Out) : Out := fun k => decide (d ≤ k) && o (k - d)

/-- No slot. -/
def noOut : Out := fun _ => false

/-! ### Closure conversion -/

/-- The slots `λb` captures, in order: the `k` with `b` mentioning `k + 1`. -/
def capt (b : Expr) : List Nat := (List.range (fvBound b)).filter fun k => mentions b (k + 1)

/-- The variables of `λb`'s code's function: the argument at `(capt b).length`, the `i`-th
captured slot at `i`. -/
def lamEnv (b : Expr) (i : Nat) : Nat :=
  if i = 0 then (capt b).length else (capt b).idxOf (i - 1)

/-- `ρ` under one binder at `x`. -/
def cons1 (x : Nat) (ρ : Nat → Nat) (i : Nat) : Nat := if i = 0 then x else ρ (i - 1)

/-- `ρ` under `let (x, y)`: `y` at `0`, `x` at `1`. -/
def cons2 (y x : Nat) (ρ : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then y else if i = 1 then x else ρ (i - 2)

/-- The environment of a closure capturing the slots `cs`: a slot the rest still reads (`out`)
through its copy at a fresh variable from `m`, any other its own variable. -/
def envVars (ρ : Nat → Nat) (out : Out) : List Nat → Nat → List Nat
  | [], _ => []
  | k :: ks, m => (if out k then m else ρ k) :: envVars ρ out ks (m + 1)

/-- The copies `envVars` reads. -/
def envCopies (ρ : Nat → Nat) (out : Out) : List Nat → Nat → Tm → Tm
  | [], _, t => t
  | k :: ks, m, t => if out k then .copy (ρ k) m (envCopies ρ out ks (m + 1) t)
      else envCopies ρ out ks (m + 1) t

/-! ### Drops -/

/-- `x` dropped before `t` when `c`. -/
def dropIf (c : Bool) (x : Nat) (t : Tm) : Tm := if c then .drop x t else t

/-- The variables `xs` dropped before `t`, in order. -/
def dropsT (xs : List Nat) (t : Tm) : Tm := xs.foldr .drop t

/-- The slots below `B` that `f` holds, in order. -/
def slotsOf (B : Nat) (f : Nat → Bool) : List Nat := (List.range B).filter f

/-- The outer slots a `case` arm drops when it starts: those only the other arm reads (`b`'s
past its binder and not `a`'s), which the rest does not read. -/
def armDrops (out : Out) (a b : Expr) : List Nat :=
  slotsOf (fvBound a + fvBound b) fun k => mentions b (k + 1) && !mentions a (k + 1) && !out k

/-! ### The program being written -/

/-- What the print has written so far: one code per function, at the same index, and a bound on
every variable. -/
structure PS where
  fns : Array Fn := #[]
  codes : Array Code := #[]
  bound : Nat := 2

/-- A `λ` code's function: its parameters `0, …, k`, its body. -/
def lamFn (k : Nat) (t : Tm) : Fn where
  name := "lam"
  params := List.range (k + 1)
  body := t
  ret := LTy.unit

/-- The `λ` code whose function is at `c`. -/
def lamCode (c : Nat) : Code where
  kind := CodeKind.lam
  fns := [c]
  ty := LCTy.ret LTy.unit

/-- Write a code of `k + 1` parameters and the body `body`, every variable below `m`. -/
def emit (k : Nat) (body : Tm) (m : Nat) : StateM PS Nat := fun s =>
  (s.fns.size, PS.mk (s.fns.push (lamFn k body)) (s.codes.push (lamCode s.fns.size)) (max s.bound m))

/-- A host operation's code. -/
def hostFn (op : HostOp) : Tm := .prim (.host op) [0]

/-! ### The machine's primitives -/

/-- The code of each of the machine's primitives that is not an effect, a literal or a host
operation: the program's first codes (`preludePS`). -/
def rtCode : Prim → Option Nat
  | .alloc => some 0
  | .free => some 1
  | .load => some 2
  | .store => some 3
  | .idx => some 5
  | .split => some 6
  | .tab => some 7
  | .drop => some 9
  | .count => some 11
  | .countTry => some 12
  | .boundedFix => some 13
  | _ => none

/-- `store`'s second code, `store ℓ`'s: the location captured, the value its argument. -/
def store1Code : Nat := 4
/-- `tab`'s loop. -/
def tabLoopCode : Nat := 8
/-- `drop`'s loop. -/
def dropLoopCode : Nat := 10
/-- The self-reference `bounded_fix` hands its step (`fixSelf`): `fixBody`'s code. -/
def fixSelfCode : Nat := 14

/-- `alloc v`. -/
def allocB : Tm := .prim .cellNew [0]
/-- `free ℓ`. -/
def freeB : Tm := .prim .cellFree [0]
/-- `load ℓ`. -/
def loadB : Tm := .prim .cellLoad [0]
/-- `store ℓ`: the closure of `store1Code` on `ℓ`. -/
def store0B : Tm := .clos store1Code [0]
/-- `store ℓ v`, `ℓ` at `0`, `v` at `1`. -/
def store1B : Tm := .prim .cellStore [0, 1]
/-- `idx ((ℓ, n), i)`. -/
def idxB : Tm := .letpair 1 2 0 (.prim .famIdx [1, 2])
/-- `split ((ℓ, n), i)`. -/
def splitB : Tm := .letpair 1 2 0 (.prim .famSplit [1, 2])

/-- `tab (c, f)`: `len(c)` cells, then `tabLoop (f, ℓ, len(c), 0, len(c))`. -/
def tabB : Tm :=
  .letpair 1 2 0 (.copy 1 3 (.letv 4 (.prim .cellsNew [1]) (.letv 5 (.prim .clampLen [3])
    (.copy 5 6 (.letv 7 (.lit (.i32 0)) (.call tabLoopCode [2, 4, 5, 7, 6]))))))

/-- `tabLoop (f, ℓ, n, i, k)`: at `k = 0` the family `(ℓ, n)`; else `ℓ + i` stored with `f i`, and
the loop from `i + 1` at `k − 1` (`tabFill`). -/
def tabLoopB : Tm :=
  .letv 5 (.lit (.i32 0)) (.copy 4 6 (.letv 7 (.prim .cntLt [5, 6])
    (.case 7 8 (.drop 8 (.drop 0 (.drop 3 (.drop 4 (.pair 1 2)))))
      9 (.drop 9 (.copy 0 10 (.copy 3 11 (.letv 12 (.app 10 11)
        (.copy 1 13 (.copy 3 14 (.letv 15 (.prim .locAdd [13, 14])
          (.letv 16 (.prim .cellStore [15, 12]) (.drop 16
            (.letv 17 (.prim .cntSucc [3]) (.letv 18 (.prim .cntPred [4])
              (.call tabLoopCode [0, 1, 2, 17, 18])))))))))))))))

/-- `drop (f, (ℓ, n))`: `dropLoop (f, ℓ, 0, n)`. -/
def dropB : Tm :=
  .letpair 1 2 0 (.letpair 3 4 2 (.letv 5 (.lit (.i32 0)) (.call dropLoopCode [1, 3, 5, 4])))

/-- `dropLoop (f, ℓ, i, k)`: at `k = 0` `()`; else `f` of the cell `ℓ + i` freed, and the loop from
`i + 1` at `k − 1` (`dropFill`). -/
def dropLoopB : Tm :=
  .letv 4 (.lit (.i32 0)) (.copy 3 5 (.letv 6 (.prim .cntLt [4, 5])
    (.case 6 7 (.drop 7 (.drop 0 (.drop 1 (.drop 2 (.drop 3 .unit)))))
      8 (.drop 8 (.copy 0 9 (.copy 1 10 (.copy 2 11 (.letv 12 (.prim .locAdd [10, 11])
        (.letv 13 (.prim .cellFree [12]) (.letv 14 (.app 9 13) (.drop 14
          (.letv 15 (.prim .cntSucc [2]) (.letv 16 (.prim .cntPred [3])
            (.call dropLoopCode [0, 1, 15, 16]))))))))))))))

/-- `count (f, (n, (i, s)))` (`countNext`): while `i < len(n)`, `count (f, (n, (i + 1, f (i, s))))`;
then `s`. -/
def countB : Tm :=
  .letpair 1 2 0 (.letpair 3 4 2 (.letpair 5 6 4 (.copy 3 7 (.letv 8 (.prim .clampLen [7])
    (.copy 5 9 (.letv 10 (.prim .cntLt [9, 8])
      (.case 10 11 (.drop 11 (.drop 1 (.drop 3 (.drop 5 (.var 6)))))
        12 (.drop 12 (.copy 1 13 (.copy 5 14 (.letv 15 (.pair 14 6) (.letv 16 (.app 13 15)
          (.letv 17 (.prim .cntSucc [5]) (.letv 18 (.pair 17 16) (.letv 19 (.pair 3 18)
            (.letv 20 (.pair 1 19) (.letv 21 (.clos 11 []) (.app 21 20))))))))))))))))))

/-- `count_try (f, (n, (i, s)))` (`countTryNext`): while `i < len(n)`, `f (i, s)`, and on its
`inl s′` `count_try (f, (n, (i + 1, s′)))`, on its `inr e` `inr e`; then `inl s`. -/
def countTryB : Tm :=
  .letpair 1 2 0 (.letpair 3 4 2 (.letpair 5 6 4 (.copy 3 7 (.letv 8 (.prim .clampLen [7])
    (.copy 5 9 (.letv 10 (.prim .cntLt [9, 8])
      (.case 10 11 (.drop 11 (.drop 1 (.drop 3 (.drop 5 (.inj false 6)))))
        12 (.drop 12 (.copy 1 13 (.copy 5 14 (.letv 15 (.pair 14 6) (.letv 16 (.app 13 15)
          (.case 16 17 (.letv 18 (.prim .cntSucc [5]) (.letv 19 (.pair 18 17)
              (.letv 20 (.pair 3 19) (.letv 21 (.pair 1 20) (.letv 22 (.clos 12 []) (.app 22 21))))))
            23 (.drop 1 (.drop 3 (.drop 5 (.inj true 23)))))))))))))))))

/-- `bounded_fix (s, (k, a))` (`boundedFixNext`): `s (self, a)`, `self` `inl ()` at `k = 0` and else
`inr` of the closure of `fixSelfCode` on `s` and `k − 1`. -/
def boundedFixB : Tm :=
  .letpair 1 2 0 (.letpair 3 4 2 (.letv 5 (.lit (.i32 0)) (.copy 3 6 (.letv 7 (.prim .cntLt [5, 6])
    (.case 7 8 (.drop 8 (.drop 3 (.letv 9 .unit (.letv 10 (.inj false 9)
        (.letv 11 (.pair 10 4) (.app 1 11))))))
      12 (.drop 12 (.copy 1 13 (.letv 14 (.prim .cntPred [3]) (.letv 15 (.clos fixSelfCode [13, 14])
        (.letv 16 (.inj true 15) (.letv 17 (.pair 16 4) (.app 1 17))))))))))))

/-- The body of `bounded_fix`'s self-reference at the budget `k`: `λx. bounded_fix (s, (k − 1, x))`
is `λ` of this, `s` and `k − 1` at its slots `1` and `2` (`fixSelf`). -/
def fixBody : Expr := .app (.prim .boundedFix) (.pair (.var 1) (.pair (.var 2) (.var 0)))

/-- The primitives' codes, in order: each its number of parameters less one, and its body. -/
def rtBodies : List (Nat × Tm) :=
  [(0, allocB), (0, freeB), (0, loadB), (0, store0B), (1, store1B), (0, idxB), (0, splitB),
    (0, tabB), (4, tabLoopB), (0, dropB), (3, dropLoopB), (0, countB), (0, countTryB),
    (0, boundedFixB)]

/-- A bound on the variables of the primitives' codes. -/
def rtBound : Nat := 24

/-! ### The print -/

/-- `e` mentions slot `k` or the rest reads it: the slots the frame must hold when `e` starts. -/
def need (e : Expr) (out : Out) (k : Nat) : Bool := mentions e k || out k

/-- A primitive as a value: a literal, a host operation's code's closure, or a primitive's. An
effect primitive has no code: it is in no term the print is proved on. -/
def primT (n : Nat) : Prim → StateM PS (Tm × Nat)
  | .lit c => pure (.lit c, n)
  | .host op => do
      let c ← emit 0 (hostFn op) 1
      pure (.clos c [], n)
  | q => pure (match rtCode q with
      | some c => (.clos c [], n)
      | none => (.prim .unreachable [], n))

/-- **The print** of `e` at the variables `ρ` of its slots, the slots `out` read after it, its
own variables from `n`: the LIR term and the next free variable. -/
def prG (ρ : Nat → Nat) (n : Nat) (out : Out) : Expr → StateM PS (Tm × Nat)
  | .var k => pure (if out k then (.copy (ρ k) n (.var n), n + 1) else (.var (ρ k), n))
  | .unit => pure (.unit, n)
  | .loc ℓ => pure (.prim (.locAt ℓ) [], n)
  | .prim q => primT n q
  | .pair a b => do
      let (ta, n₁) ← prG ρ (n + 2) (unionO out (fvAt 0 b)) a
      let (tb, n₂) ← prG ρ n₁ out b
      pure (.letv n ta (.letv (n + 1) tb (.pair n (n + 1))), n₂)
  | .inj₁ a => do
      let (ta, n₁) ← prG ρ (n + 1) out a
      pure (.letv n ta (.inj false n), n₁)
  | .inj₂ a => do
      let (ta, n₁) ← prG ρ (n + 1) out a
      pure (.letv n ta (.inj true n), n₁)
  | .seq a b => do
      let (ta, n₁) ← prG ρ (n + 1) (unionO out (fvAt 0 b)) a
      let (tb, n₂) ← prG ρ n₁ out b
      pure (.letv n ta (.drop n tb), n₂)
  | .app f a => do
      let (ta, n₁) ← prG ρ (n + 2) (unionO out (fvAt 0 f)) a
      let (tf, n₂) ← prG ρ n₁ out f
      pure (.letv n ta (.letv (n + 1) tf (.app (n + 1) n)), n₂)
  | .letpair a b => do
      let (ta, n₁) ← prG ρ (n + 3) (unionO out (fvAt 2 b)) a
      let (tb, n₂) ← prG (cons2 (n + 2) (n + 1) ρ) n₁ (liftO 2 out) b
      pure (.letv n ta (.letpair (n + 1) (n + 2) n
        (dropIf (!mentions b 1) (n + 1) (dropIf (!mentions b 0) (n + 2) tb))), n₂)
  | .case s a b => do
      let (ts, n₁) ← prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) s
      let (ta, n₂) ← prG (cons1 (n + 1) ρ) n₁ (liftO 1 out) a
      let (tb, n₃) ← prG (cons1 (n + 2) ρ) n₂ (liftO 1 out) b
      pure (.letv n ts (.case n
        (n + 1) (dropIf (!mentions a 0) (n + 1) (dropsT ((armDrops out a b).map ρ) ta))
        (n + 2) (dropIf (!mentions b 0) (n + 2) (dropsT ((armDrops out b a).map ρ) tb))), n₃)
  | .lam b => do
      let (tb, m) ← prG (lamEnv b) ((capt b).length + 1) noOut b
      let c ← emit (capt b).length (dropIf (!mentions b 0) (capt b).length tb) m
      pure (envCopies ρ out (capt b) n (.clos c (envVars ρ out (capt b) n)), n + (capt b).length)


/-- The primitives' codes, written: the first fourteen hand-written (`rtBodies`), then
`fixBody`'s, at `fixSelfCode`. -/
def preludePS : PS :=
  let s₀ : PS := rtBodies.foldl (fun s kt => (emit kt.1 kt.2 rtBound s).2) {}
  ((prG (fun _ => 0) 0 noOut (.lam fixBody)) s₀).2

/-- Every variable below `N` at `unit`. -/
def tyTable (N : Nat) : Std.HashMap Var LTy :=
  (List.range N).foldl (fun m x => m.insert x .unit) {}

/-- **The program** of a closed term: the primitives' codes, the term's codes, and `main` its
print. -/
def lirOf (e : Expr) : Prog :=
  let ((t, n), s) := (prG (fun _ => 0) 0 noOut e).run preludePS
  { fns := s.fns, codes := s.codes, main := t, mainTy := .unit, ty := tyTable (max s.bound n) }

/-- **The print of a checked program**: its explicit-ownership lowering `own` (SPEC §54), printed. -/
def printOwn (c : Frontend.Check.Checked) : Prog := lirOf (own c.t)

end Lowering
