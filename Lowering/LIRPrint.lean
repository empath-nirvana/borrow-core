import Lowering.Print
import Lowering.Own

/-!
# Lowering — the print to the LIR, on the core fragment  `[spec §56]`

The print turns a low term (`Lowering/Low.lean`) into a program of Backend2's LIR
(`Backend2/Syntax.lean`). It decides no ownership: every `copy` and `drop` of the LIR is the
image of a `copy` or a `forget` of the term (`own` wrote them, SPEC §54), and every other variable
is consumed by the operation that takes it.

- **Closure conversion.** A `λb` becomes a closure `clos c env` of a code `c` of its own: `env`
  the slots the body captures (`capt b`, each consumed by the closure, `Explicit.lam`), the code's
  function taking them, then the argument (`lamEnv b`). A function's variables are numbered from
  `0` in its own frame.
- **Named form.** Each subterm's value is bound to a fresh variable (`letv`), in the machine's
  order: a pair left first, an application its argument first.
- **Calls are dispatched** (`app`): no call is made direct, so no flow analysis is read.
- **The kernel's constants**: `copy` applied is the LIR's `copy`, `forget` applied its `drop`, a
  host operation applied its `prim (host op)`; each, as a value, the closure of a code that does
  the same (`copyFn`, `forgetFn`, `hostFn`). An integer literal is the LIR's `lit`.
- **The core fragment** (`coreB`): no location and no primitive but literals and host
  operations. Outside it the print writes `unreachable`; the simulation is proved on it
  (`Lowering/PrintFwd.lean`).
- **The LIR is untyped here**: every variable is at `unit` (`tyTable`). The interpreter reads a
  variable's type only at its `copy`, `drop` and `load` checks and in printing `main`'s value;
  `load` is outside the fragment.

`Pr` is the print as a relation over the final program, with `lirOf_pr` saying the print's output
is in it; the simulation is proved over `Pr`.
-/

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-! ### The core fragment -/

/-- **The core fragment**: no location, and no primitive but integer literals and host
operations. -/
def coreB : Expr → Bool
  | .var _ | .unit => true
  | .loc _ => false
  | .prim (.lit _) | .prim (.host _) => true
  | .prim _ => false
  | .pair a b | .seq a b | .app a b | .letpair a b => coreB a && coreB b
  | .inj₁ a | .inj₂ a | .lam a => coreB a
  | .case s a b => coreB s && coreB a && coreB b

/-- The kernel's constants the print maps itself: `copy` and `forget`. -/
def isCF (e : Expr) : Bool := e == copy || e == forget

/-! ### Closure conversion -/

/-- The slots `λb` captures, in order: the `k` with `b` mentioning `k + 1`. -/
def capt (b : Expr) : List Nat := (List.range (fvBound b)).filter fun k => mentions b (k + 1)

/-- The variables of `λb`'s code's function: the argument at `(capt b).length`, the `i`-th
captured slot at `i`. -/
def lamEnv (b : Expr) (i : Nat) : Var :=
  if i = 0 then (capt b).length else (capt b).idxOf (i - 1)

/-- `ρ` under one binder at `x`. -/
def cons1 (x : Var) (ρ : Nat → Var) (i : Nat) : Var := if i = 0 then x else ρ (i - 1)

/-- `ρ` under `let (x, y)`: `y` at `0`, `x` at `1`. -/
def cons2 (y x : Var) (ρ : Nat → Var) (i : Nat) : Var :=
  if i = 0 then y else if i = 1 then x else ρ (i - 2)

/-! ### The print -/

/-- What the print has written so far: one code per function, at the same index, and a bound on
every variable. -/
structure PS where
  fns : Array Fn := #[]
  codes : Array Code := #[]
  bound : Nat := 2

/-- A `λ` code's function: its parameters `0, …, k`, its body, every variable below `m`. -/
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

def emit (k : Nat) (body : Tm) (m : Nat) : StateM PS Nat := fun s =>
  (s.fns.size, PS.mk (s.fns.push (lamFn k body)) (s.codes.push (lamCode s.fns.size)) (max s.bound m))

/-- `copy`'s code: `copy x₀ x₁; (x₀, x₁)`. -/
def copyFn : Tm := .copy 0 1 (.pair 0 1)

/-- `forget`'s code: `drop x₀; ()`. -/
def forgetFn : Tm := .drop 0 .unit

/-- A host operation's code. -/
def hostFn (op : HostOp) : Tm := .prim (.host op) [0]

/-- **The print** of `e` at the variables `ρ` of its free slots, its own variables from `n`: the
LIR term and the next free variable. -/
def prT (ρ : Nat → Var) (n : Nat) : Expr → StateM PS (Tm × Nat)
  | .var k => pure (.var (ρ k), n)
  | .unit => pure (.unit, n)
  | .prim (.lit c) => pure (.lit c, n)
  | .prim (.host op) => do
      let c ← emit 0 (hostFn op) 1
      pure (.clos c [], n)
  | .pair a b => do
      let (ta, n₁) ← prT ρ (n + 2) a
      let (tb, n₂) ← prT ρ n₁ b
      pure (.letv n ta (.letv (n + 1) tb (.pair n (n + 1))), n₂)
  | .inj₁ a => do
      let (ta, n₁) ← prT ρ (n + 1) a
      pure (.letv n ta (.inj false n), n₁)
  | .inj₂ a => do
      let (ta, n₁) ← prT ρ (n + 1) a
      pure (.letv n ta (.inj true n), n₁)
  | .seq a b => do
      let (ta, n₁) ← prT ρ (n + 1) a
      let (tb, n₂) ← prT ρ n₁ b
      pure (.letv n ta (.drop n tb), n₂)
  | .letpair a b => do
      let (ta, n₁) ← prT ρ (n + 3) a
      let (tb, n₂) ← prT (cons2 (n + 2) (n + 1) ρ) n₁ b
      pure (.letv n ta (.letpair (n + 1) (n + 2) n tb), n₂)
  | .case s a b =>
      if a = BoLo.stuckE ∧ b = BoLo.stuckE then do
        let (ts, n₁) ← prT ρ (n + 1) s
        pure (.letv n ts (.absurd n), n₁)
      else do
        let (ts, n₁) ← prT ρ (n + 3) s
        let (ta, n₂) ← prT (cons1 (n + 1) ρ) n₁ a
        let (tb, n₃) ← prT (cons1 (n + 2) ρ) n₂ b
        pure (.letv n ts (.case n (n + 1) ta (n + 2) tb), n₃)
  | .lam b =>
      if Expr.lam b = copy then do
        let c ← emit 0 copyFn 2
        pure (.clos c [], n)
      else if Expr.lam b = forget then do
        let c ← emit 0 forgetFn 1
        pure (.clos c [], n)
      else do
        let (tb, m) ← prT (lamEnv b) ((capt b).length + 1) b
        let c ← emit (capt b).length tb m
        pure (.clos c ((capt b).map ρ), n)
  | .app f a =>
      if f = copy then do
        let (ta, n₁) ← prT ρ (n + 2) a
        pure (.letv n ta (.copy n (n + 1) (.pair n (n + 1))), n₁)
      else if f = forget then do
        let (ta, n₁) ← prT ρ (n + 1) a
        pure (.letv n ta (.drop n .unit), n₁)
      else match f with
        | .prim (.host op) => do
            let (ta, n₁) ← prT ρ (n + 1) a
            pure (.letv n ta (.prim (.host op) [n]), n₁)
        | f => do
            let (ta, n₁) ← prT ρ (n + 2) a
            let (tf, n₂) ← prT ρ n₁ f
            pure (.letv n ta (.letv (n + 1) tf (.app (n + 1) n)), n₂)
  | .loc _ | .prim _ => pure (.prim .unreachable [], n)

/-- Every variable below `N` at `unit`. -/
def tyTable (N : Nat) : Std.HashMap Var LTy :=
  (List.range N).foldl (fun m x => m.insert x .unit) {}

/-- **The program** of a closed term: its codes, and `main` its print. -/
def lirOf (e : Expr) : Prog :=
  let ((t, n), s) := (prT (fun _ => 0) 0 e).run {}
  { fns := s.fns, codes := s.codes, main := t, mainTy := .unit, ty := tyTable (max s.bound n) }

/-- **The print of a checked program**: its explicit-ownership lowering `own` (SPEC §54), printed. -/
def printOwn (c : Frontend.Check.Checked) : Prog := lirOf (own c.t)

/-! ### The print as a relation over the final program -/

/-- The code `c` of `p` is a `λ` code whose function, at `c`, has the parameters `0, …, k` and the
body `t`. -/
def CodeAt (p : Prog) (c k : Nat) (t : Tm) : Prop :=
  p.codes[c]? = some (lamCode c) ∧
    ∃ fn : Fn, p.fns[c]? = some fn ∧ fn.params = List.range (k + 1) ∧ fn.body = t

/-- **The print, as a relation**: `Pr p N ρ n e t n'` when `t` is a print of `e` at `ρ`, its own
variables from `n` below `n'`, its codes those of `p`, each function's variables below `N`. -/
inductive Pr (p : Prog) (N : Nat) : (Nat → Var) → Nat → Expr → Tm → Nat → Prop where
  | var (ρ : Nat → Var) (n k : Nat) : Pr p N ρ n (.var k) (.var (ρ k)) n
  | unit (ρ : Nat → Var) (n : Nat) : Pr p N ρ n .unit .unit n
  | lit (ρ : Nat → Var) (n : Nat) (c : IntLit) : Pr p N ρ n (.prim (.lit c)) (.lit c) n
  | hostV (ρ : Nat → Var) (n : Nat) (op : HostOp) (c : Nat) (h : CodeAt p c 0 (hostFn op)) :
      Pr p N ρ n (.prim (.host op)) (.clos c []) n
  | copyV (ρ : Nat → Var) (n c : Nat) (h : CodeAt p c 0 copyFn) : Pr p N ρ n copy (.clos c []) n
  | forgetV (ρ : Nat → Var) (n c : Nat) (h : CodeAt p c 0 forgetFn) :
      Pr p N ρ n forget (.clos c []) n
  | pair {ρ : Nat → Var} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 2) a ta n₁) (hb : Pr p N ρ n₁ b tb n₂) :
      Pr p N ρ n (.pair a b) (.letv n ta (.letv (n + 1) tb (.pair n (n + 1)))) n₂
  | inj₁ {ρ : Nat → Var} {n n₁ : Nat} {a : Expr} {ta : Tm} (ha : Pr p N ρ (n + 1) a ta n₁) :
      Pr p N ρ n (.inj₁ a) (.letv n ta (.inj false n)) n₁
  | inj₂ {ρ : Nat → Var} {n n₁ : Nat} {a : Expr} {ta : Tm} (ha : Pr p N ρ (n + 1) a ta n₁) :
      Pr p N ρ n (.inj₂ a) (.letv n ta (.inj true n)) n₁
  | seq {ρ : Nat → Var} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 1) a ta n₁) (hb : Pr p N ρ n₁ b tb n₂) :
      Pr p N ρ n (.seq a b) (.letv n ta (.drop n tb)) n₂
  | letpair {ρ : Nat → Var} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 3) a ta n₁) (hb : Pr p N (cons2 (n + 2) (n + 1) ρ) n₁ b tb n₂) :
      Pr p N ρ n (.letpair a b) (.letv n ta (.letpair (n + 1) (n + 2) n tb)) n₂
  | case {ρ : Nat → Var} {n n₁ n₂ n₃ : Nat} {s a b : Expr} {ts ta tb : Tm}
      (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE))
      (hs : Pr p N ρ (n + 3) s ts n₁) (ha : Pr p N (cons1 (n + 1) ρ) n₁ a ta n₂)
      (hb : Pr p N (cons1 (n + 2) ρ) n₂ b tb n₃) :
      Pr p N ρ n (.case s a b) (.letv n ts (.case n (n + 1) ta (n + 2) tb)) n₃
  | absurd {ρ : Nat → Var} {n n₁ : Nat} {s : Expr} {ts : Tm} (hs : Pr p N ρ (n + 1) s ts n₁) :
      Pr p N ρ n (absurdL s) (.letv n ts (.absurd n)) n₁
  | lam {ρ : Nat → Var} {n m : Nat} {b : Expr} {tb : Tm} (c : Nat)
      (hcp : Expr.lam b ≠ copy) (hfg : Expr.lam b ≠ forget)
      (hb : Pr p N (lamEnv b) ((capt b).length + 1) b tb m) (hm : m ≤ N)
      (hc : CodeAt p c (capt b).length tb) :
      Pr p N ρ n (.lam b) (.clos c ((capt b).map ρ)) n
  | appCopy {ρ : Nat → Var} {n n₁ : Nat} {a : Expr} {ta : Tm} (ha : Pr p N ρ (n + 2) a ta n₁) :
      Pr p N ρ n (.app copy a) (.letv n ta (.copy n (n + 1) (.pair n (n + 1)))) n₁
  | appForget {ρ : Nat → Var} {n n₁ : Nat} {a : Expr} {ta : Tm} (ha : Pr p N ρ (n + 1) a ta n₁) :
      Pr p N ρ n (.app forget a) (.letv n ta (.drop n .unit)) n₁
  | appHost {ρ : Nat → Var} {n n₁ : Nat} {a : Expr} {ta : Tm} (op : HostOp)
      (ha : Pr p N ρ (n + 1) a ta n₁) :
      Pr p N ρ n (.app (.prim (.host op)) a) (.letv n ta (.prim (.host op) [n])) n₁
  | app {ρ : Nat → Var} {n n₁ n₂ : Nat} {f a : Expr} {ta tf : Tm}
      (hcp : f ≠ copy) (hfg : f ≠ forget) (hh : ∀ op, f ≠ .prim (.host op))
      (ha : Pr p N ρ (n + 2) a ta n₁) (hf : Pr p N ρ n₁ f tf n₂) :
      Pr p N ρ n (.app f a) (.letv n ta (.letv (n + 1) tf (.app (n + 1) n))) n₂

end Lowering

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-! ### The print is in the relation -/

/-- `s'` extends `s`: its tables have `s`'s as a prefix, and its bound is at least `s`'s. -/
def Grows (s s' : PS) : Prop :=
  s.fns.size ≤ s'.fns.size ∧ (∀ i, i < s.fns.size → s'.fns[i]? = s.fns[i]? ∧ s'.codes[i]? = s.codes[i]?) ∧
    s.bound ≤ s'.bound

/-- The program `p` holds the tables of `s`. -/
def Ext (p : Prog) (s : PS) : Prop :=
  ∀ i, i < s.fns.size → p.fns[i]? = s.fns[i]? ∧ p.codes[i]? = s.codes[i]?

theorem Grows.refl (s : PS) : Grows s s := ⟨le_refl _, fun _ _ => ⟨rfl, rfl⟩, le_refl _⟩

theorem Grows.trans {s₁ s₂ s₃ : PS} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun i hi => ⟨(h₂.2.1 i (by have := h₁.1; omega)).1.trans (h₁.2.1 i hi).1,
    (h₂.2.1 i (by have := h₁.1; omega)).2.trans (h₁.2.1 i hi).2⟩, h₁.2.2.trans h₂.2.2⟩

theorem Ext.mono {p : Prog} {s s' : PS} (h : Ext p s') (hg : Grows s s') : Ext p s :=
  fun i hi => ⟨(h i (by have := hg.1; omega)).1.trans (hg.2.1 i hi).1,
    (h i (by have := hg.1; omega)).2.trans (hg.2.1 i hi).2⟩

theorem emit_spec (k : Nat) (body : Tm) (m : Nat) (s : PS) (hs : s.fns.size = s.codes.size) :
    let r := emit k body m s
    r.2.fns.size = r.2.codes.size ∧ Grows s r.2 ∧ m ≤ r.2.bound ∧
      ∀ p, Ext p r.2 → CodeAt p r.1 k body := by
  simp only [emit]
  refine ⟨by simp [hs], ⟨by simp, fun i hi => ?_, by simp⟩, by simp, fun p hp => ?_⟩
  · simp [Array.getElem?_push, hi.ne, hs ▸ hi.ne]
  · have h := hp s.fns.size (by simp)
    exact ⟨by rw [h.2]; simp [hs], lamFn k body, by rw [h.1]; simp, rfl, rfl⟩

end Lowering

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

theorem prT_bind {α β : Type} (x : StateM PS α) (f : α → StateM PS β) (s : PS) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

theorem prT_pure {α : Type} (a : α) (s : PS) : (pure a : StateM PS α) s = (a, s) := rfl

/-- **The print is in the relation**: on the core fragment its tables grow, keeping one code per
function, and over any program holding its final tables, with every function's variables below
`N`, its output is a print of the term. -/
theorem prT_pr : ∀ (e : Expr) (ρ : Nat → Var) (n : Nat) (s : PS), coreB e = true →
    s.fns.size = s.codes.size →
    (prT ρ n e s).2.fns.size = (prT ρ n e s).2.codes.size ∧ Grows s (prT ρ n e s).2 ∧
      ∀ p N, Ext p (prT ρ n e s).2 → (prT ρ n e s).2.bound ≤ N →
        Pr p N ρ n e (prT ρ n e s).1.1 (prT ρ n e s).1.2 := by
  intro e
  induction e with
  | var k => intro ρ n s _ hs; exact ⟨hs, Grows.refl s, fun p N _ _ => .var ρ n k⟩
  | unit => intro ρ n s _ hs; exact ⟨hs, Grows.refl s, fun p N _ _ => .unit ρ n⟩
  | loc _ => intro ρ n s hc; simp [coreB] at hc
  | prim q =>
      intro ρ n s hc hs
      cases q with
      | lit c => exact ⟨hs, Grows.refl s, fun p N _ _ => .lit ρ n c⟩
      | host op =>
          obtain ⟨h1, g1, -, c1⟩ := emit_spec 0 (hostFn op) 1 s hs
          exact ⟨h1, g1, fun p N hp _ => .hostV ρ n op _ (c1 p hp)⟩
      | _ => simp [coreB] at hc
  | pair a b iha ihb | seq a b iha ihb =>
      intro ρ n s hc hs
      simp only [coreB, Bool.and_eq_true] at hc
      first
      | (obtain ⟨h1, g1, p1⟩ := iha ρ (n + 2) s hc.1 hs
         obtain ⟨h2, g2, p2⟩ := ihb ρ (prT ρ (n + 2) a s).1.2 _ hc.2 h1
         exact ⟨h2, g1.trans g2, fun p N hp hN =>
           .pair (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩)
      | (obtain ⟨h1, g1, p1⟩ := iha ρ (n + 1) s hc.1 hs
         obtain ⟨h2, g2, p2⟩ := ihb ρ (prT ρ (n + 1) a s).1.2 _ hc.2 h1
         exact ⟨h2, g1.trans g2, fun p N hp hN =>
           .seq (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩)
  | inj₁ a ih | inj₂ a ih =>
      intro ρ n s hc hs
      obtain ⟨h1, g1, p1⟩ := ih ρ (n + 1) s hc hs
      first
      | exact ⟨h1, g1, fun p N hp hN => .inj₁ (p1 p N hp hN)⟩
      | exact ⟨h1, g1, fun p N hp hN => .inj₂ (p1 p N hp hN)⟩
  | letpair a b iha ihb =>
      intro ρ n s hc hs
      simp only [coreB, Bool.and_eq_true] at hc
      obtain ⟨h1, g1, p1⟩ := iha ρ (n + 3) s hc.1 hs
      obtain ⟨h2, g2, p2⟩ := ihb (cons2 (n + 2) (n + 1) ρ) (prT ρ (n + 3) a s).1.2 _ hc.2 h1
      exact ⟨h2, g1.trans g2, fun p N hp hN =>
        .letpair (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩
  | case v a b ihv iha ihb =>
      intro ρ n s hc hs
      simp only [coreB, Bool.and_eq_true] at hc
      by_cases hab : a = BoLo.stuckE ∧ b = BoLo.stuckE
      · obtain ⟨rfl, rfl⟩ := hab
        obtain ⟨h1, g1, p1⟩ := ihv ρ (n + 1) s hc.1.1 hs
        have e : prT ρ n (.case v BoLo.stuckE BoLo.stuckE) s =
            ((.letv n (prT ρ (n + 1) v s).1.1 (.absurd n), (prT ρ (n + 1) v s).1.2),
              (prT ρ (n + 1) v s).2) := by
          simp only [prT, and_self, if_true]; rfl
        rw [e]
        exact ⟨h1, g1, fun p N hp hN => .absurd (p1 p N hp hN)⟩
      · obtain ⟨h1, g1, p1⟩ := ihv ρ (n + 3) s hc.1.1 hs
        obtain ⟨h2, g2, p2⟩ := iha (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 _ hc.1.2 h1
        obtain ⟨h3, g3, p3⟩ := ihb (cons1 (n + 2) ρ) (prT (cons1 (n + 1) ρ)
          (prT ρ (n + 3) v s).1.2 a (prT ρ (n + 3) v s).2).1.2 _ hc.2 h2
        have e : prT ρ n (.case v a b) s =
            ((.letv n (prT ρ (n + 3) v s).1.1 (.case n (n + 1)
              (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a (prT ρ (n + 3) v s).2).1.1 (n + 2)
              (prT (cons1 (n + 2) ρ) (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).1.2 b (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).2).1.1),
              (prT (cons1 (n + 2) ρ) (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).1.2 b (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).2).1.2),
              (prT (cons1 (n + 2) ρ) (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).1.2 b (prT (cons1 (n + 1) ρ) (prT ρ (n + 3) v s).1.2 a
                (prT ρ (n + 3) v s).2).2).2) := by
          simp only [prT, if_neg hab]; rfl
        rw [e]
        exact ⟨h3, g1.trans (g2.trans g3), fun p N hp hN =>
          .case hab (p1 p N ((hp.mono g3).mono g2) (g2.2.2.trans (g3.2.2.trans hN)))
            (p2 p N (hp.mono g3) (g3.2.2.trans hN)) (p3 p N hp hN)⟩
  | lam b ih =>
      intro ρ n s hc hs
      simp only [coreB] at hc
      by_cases hcp : Expr.lam b = copy
      · have e : prT ρ n (.lam b) s = ((.clos s.fns.size [], n), (emit 0 copyFn 2 s).2) := by
          simp only [prT, if_pos hcp]; rfl
        rw [e]
        obtain ⟨h1, g1, -, c1⟩ := emit_spec 0 copyFn 2 s hs
        exact ⟨h1, g1, fun p N hp _ => hcp ▸ .copyV ρ n _ (c1 p hp)⟩
      by_cases hfg : Expr.lam b = forget
      · have e : prT ρ n (.lam b) s = ((.clos s.fns.size [], n), (emit 0 forgetFn 1 s).2) := by
          simp only [prT, if_neg hcp, if_pos hfg]; rfl
        rw [e]
        obtain ⟨h1, g1, -, c1⟩ := emit_spec 0 forgetFn 1 s hs
        exact ⟨h1, g1, fun p N hp _ => hfg ▸ .forgetV ρ n _ (c1 p hp)⟩
      obtain ⟨h1, g1, p1⟩ := ih (lamEnv b) ((capt b).length + 1) s hc hs
      have e : prT ρ n (.lam b) s =
          ((.clos (prT (lamEnv b) ((capt b).length + 1) b s).2.fns.size ((capt b).map ρ), n),
            (emit (capt b).length (prT (lamEnv b) ((capt b).length + 1) b s).1.1
              (prT (lamEnv b) ((capt b).length + 1) b s).1.2
              (prT (lamEnv b) ((capt b).length + 1) b s).2).2) := by
        simp only [prT, if_neg hcp, if_neg hfg]; rfl
      rw [e]
      obtain ⟨h2, g2, hm, c2⟩ := emit_spec (capt b).length
        (prT (lamEnv b) ((capt b).length + 1) b s).1.1
        (prT (lamEnv b) ((capt b).length + 1) b s).1.2 _ h1
      exact ⟨h2, g1.trans g2, fun p N hp hN =>
        .lam _ hcp hfg (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (hm.trans hN) (c2 p hp)⟩
  | app f a ihf iha =>
      intro ρ n s hc hs
      simp only [coreB, Bool.and_eq_true] at hc
      by_cases hcp : f = copy
      · subst hcp
        obtain ⟨h1, g1, p1⟩ := iha ρ (n + 2) s hc.2 hs
        exact ⟨h1, g1, fun p N hp hN => .appCopy (p1 p N hp hN)⟩
      by_cases hfg : f = forget
      · subst hfg
        obtain ⟨h1, g1, p1⟩ := iha ρ (n + 1) s hc.2 hs
        exact ⟨h1, g1, fun p N hp hN => .appForget (p1 p N hp hN)⟩
      by_cases hh : ∃ op, f = .prim (.host op)
      · obtain ⟨op, rfl⟩ := hh
        have e : prT ρ n (.app (.prim (.host op)) a) s =
            ((.letv n (prT ρ (n + 1) a s).1.1 (.prim (.host op) [n]), (prT ρ (n + 1) a s).1.2),
              (prT ρ (n + 1) a s).2) := by
          simp only [prT]
          rw [if_neg hcp, if_neg hfg]; rfl
        rw [e]
        obtain ⟨h1, g1, p1⟩ := iha ρ (n + 1) s hc.2 hs
        exact ⟨h1, g1, fun p N hp hN => .appHost op (p1 p N hp hN)⟩
      simp only [not_exists] at hh
      obtain ⟨h1, g1, p1⟩ := iha ρ (n + 2) s hc.2 hs
      obtain ⟨h2, g2, p2⟩ := ihf ρ (prT ρ (n + 2) a s).1.2 _ hc.1 h1
      have e : prT ρ n (.app f a) s =
          ((.letv n (prT ρ (n + 2) a s).1.1 (.letv (n + 1)
            (prT ρ (prT ρ (n + 2) a s).1.2 f (prT ρ (n + 2) a s).2).1.1 (.app (n + 1) n)),
            (prT ρ (prT ρ (n + 2) a s).1.2 f (prT ρ (n + 2) a s).2).1.2),
            (prT ρ (prT ρ (n + 2) a s).1.2 f (prT ρ (n + 2) a s).2).2) := by
        simp only [prT]
        rw [if_neg hcp, if_neg hfg]
        rfl
      rw [e]
      exact ⟨h2, g1.trans g2, fun p N hp hN =>
        .app hcp hfg hh (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩

end Lowering

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

theorem tyTable_get (N : Nat) : ∀ x, x < N → (tyTable N)[x]? = some LTy.unit := by
  have key : ∀ (l : List Nat) (m : Std.HashMap Var LTy) x,
      (l.foldl (fun m x => m.insert x LTy.unit) m)[x]? = if x ∈ l then some LTy.unit else m[x]? := by
    intro l
    induction l with
    | nil => intro m x; simp
    | cons a l ih =>
        intro m x
        simp only [List.foldl_cons, ih, List.mem_cons, Std.HashMap.getElem?_insert]
        by_cases h : x ∈ l
        · simp [h]
        · by_cases ha : a = x
          · subst ha; simp
          · simp [h, ha, Ne.symm ha]
  intro x hx
  simp only [tyTable, key]
  simp [hx]

/-- **The program of a closed core term is its print**: `main` is a print of the term over the
program's codes, every variable below `N` at `unit`, and `N ≥ 2`. -/
theorem lirOf_pr (e : Expr) (hc : coreB e = true) :
    ∃ N n', Pr (lirOf e) N (fun _ => 0) 0 e (lirOf e).main n' ∧ n' ≤ N ∧ 2 ≤ N ∧
      ∀ x, x < N → (lirOf e).ty[x]? = some LTy.unit := by
  obtain ⟨-, g, hp⟩ := prT_pr e (fun _ => 0) 0 {} hc rfl
  refine ⟨max (prT (fun _ => 0) 0 e {}).2.bound (prT (fun _ => 0) 0 e {}).1.2,
    (prT (fun _ => 0) 0 e {}).1.2, ?_, le_max_right _ _, ?_, tyTable_get _⟩
  · exact hp _ _ (fun i _ => ⟨rfl, rfl⟩) (le_max_left _ _)
  · exact le_trans g.2.2 (le_max_left _ _)

end Lowering
