import HandlersAsBorrows.Weaken

/-!
# The source fragment: answering handlers of System Ξ, with state

System Ξ (Brachthäuser, Schuster & Ostermann, *Effects as Capabilities*, OOPSLA 2020, TR §4,
Fig. 3–4) restricted as `README.md` §1 states:

* value types are first-order data, `1`, `A ⊗ B`, `A ⊕ B`, and value variables are used
  **linearly** (Ξ's value context is unrestricted);
* a block `{x ⇒ s}` takes one value argument and no block argument, and captures no value
  variable; it may use every capability and block in scope (Ξ's `[Block]`, `[Def]`);
* an operation `F(e)` and a block call `f(e)` are Ξ's `[Call]`;
* `handle` is Ξ's `[Handle]` at an **answering** clause: the clause resumes exactly once, in
  tail position, with a value it computes from the argument and the handler's state `S`
  (a parameterized handler; at `S = 1` it is Ξ's own `handle`).  The clause is pure: it uses no
  capability and no value variable of the context.

Capabilities and blocks live in one lexically scoped environment `K : List Entry`, innermost
first; `op j` and `call j` name its `j`-th entry (Ξ's block variables, de Bruijn).

**Padding.**  Source contexts carry consumed slots where the translation binds a variable the
source does not see (the threaded environment, the `Λ` of a borrow callback).  They are never
live, so they do not change which programs are typed; they make source and target indices
coincide.  Their types are irrelevant (`DWk`).  `[encoding]`
-/

noncomputable section

namespace HandlersAsBorrows.Xi
open BoCa

/-- Value types: first-order data. -/
inductive VTy where
  | unit
  | pair (A B : VTy)
  | sum (A B : VTy)
  deriving DecidableEq, Repr

/-- The data type a value type denotes in BoLo. -/
def VTy.tr : VTy → Ty
  | .unit => .unit
  | .pair A B => .tensor A.tr B.tr
  | .sum A B => .sum A.tr B.tr

/-- Ξ's expressions `e ::= x | v`, at data. -/
inductive VExp where
  | var (i : Nat)
  | unit
  | pair (e₁ e₂ : VExp)
  | inj₁ (e : VExp)
  | inj₂ (e : VExp)
  deriving Repr

/-- An entry of the lexical environment: a capability (handler with state `S`, operation
`A → B`), or a block `A → B`. -/
inductive Entry where
  | cap (S A B : VTy)
  | blk (A B : VTy)
  deriving DecidableEq, Repr

/-- Statements. -/
inductive Stmt where
  /-- `e`: return a value (Ξ `[Expr]`). -/
  | ret (e : VExp)
  /-- `val x = s₀; s₁` (Ξ `[Val]`). -/
  | val (s₀ s₁ : Stmt)
  /-- `let (x, y) = e; s`: data elimination. -/
  | split (e : VExp) (s : Stmt)
  /-- `case e {x ⇒ s₁ | y ⇒ s₂}`: data elimination. -/
  | case (e : VExp) (s₁ s₂ : Stmt)
  /-- `F(e)`, `F` the capability at environment index `j` (Ξ `[Call]` at a capability). -/
  | op (j : Nat) (e : VExp)
  /-- `f(e)`, `f` the block at environment index `j` (Ξ `[Call]` at a block). -/
  | call (j : Nat) (e : VExp)
  /-- `def f = {x ⇒ body}; s` (Ξ `[Def]` at a `[Block]` literal). -/
  | defn (body s : Stmt)
  /-- `handle {F ⇒ s} with state e₀ : S, clause cl` (Ξ `[Handle]`, answering). -/
  | handle (S : VTy) (e₀ : VExp) (cl s : Stmt)
  deriving Repr

/-- A padding slot. -/
abbrev pad : Slot VTy := ⟨.unit, false⟩

/-- Value typing, linear. -/
inductive VDerives : Ctx VTy → VExp → VTy → Prop where
  | var {Γ i A} : Ctx.Solo Γ i A → VDerives Γ (.var i) A
  | unit {Γ} : Ctx.Dead Γ → VDerives Γ .unit .unit
  | pair {Γ Γ₁ Γ₂ e₁ e₂ A B} : Ctx.Split Γ Γ₁ Γ₂ → VDerives Γ₁ e₁ A → VDerives Γ₂ e₂ B →
      VDerives Γ (.pair e₁ e₂) (.pair A B)
  | inj₁ {Γ e A B} : VDerives Γ e A → VDerives Γ (.inj₁ e) (.sum A B)
  | inj₂ {Γ e A B} : VDerives Γ e B → VDerives Γ (.inj₂ e) (.sum A B)

/-- Statement typing `K; Γ ⊢ s : C` (Ξ's `Γ Δ ⊢ s : τ`, with `Δ` the environment `K`). -/
inductive XDerives : List Entry → Ctx VTy → Stmt → VTy → Prop where
  | ret {K Γ e A} : VDerives Γ e A → XDerives K Γ (.ret e) A
  | val {K Γ Γ₁ Γ₂ s₀ s₁ A B} : Ctx.Split Γ Γ₁ Γ₂ → XDerives K Γ₁ s₀ A →
      XDerives K (⟨A, true⟩ :: pad :: Γ₂) s₁ B → XDerives K Γ (.val s₀ s₁) B
  | split {K Γ Γ₁ Γ₂ e s A₁ A₂ B} : Ctx.Split Γ Γ₁ Γ₂ → VDerives Γ₁ e (.pair A₁ A₂) →
      XDerives K (⟨A₂, true⟩ :: ⟨A₁, true⟩ :: pad :: Γ₂) s B → XDerives K Γ (.split e s) B
  | case {K Γ Γ₁ Γ₂ e s₁ s₂ A₁ A₂ B} : Ctx.Split Γ Γ₁ Γ₂ → VDerives Γ₁ e (.sum A₁ A₂) →
      XDerives K (⟨A₁, true⟩ :: pad :: Γ₂) s₁ B → XDerives K (⟨A₂, true⟩ :: pad :: Γ₂) s₂ B →
      XDerives K Γ (.case e s₁ s₂) B
  | op {K Γ j e S A B} : K[j]? = some (.cap S A B) → VDerives Γ e A → XDerives K Γ (.op j e) B
  | call {K Γ j e A B} : K[j]? = some (.blk A B) → VDerives Γ e A → XDerives K Γ (.call j e) B
  /-- The block body sees the environment of its definition and its own argument only. -/
  | defn {K Γ body s A B C} : XDerives K [⟨A, true⟩, pad] body B →
      XDerives (.blk A B :: K) (pad :: Γ) s C → XDerives K Γ (.defn body s) C
  /-- The handled statement sees the new capability at index `0`; the clause is closed. -/
  | handle {K Γ Γ₁ Γ₂ e₀ cl s S A B C} : Ctx.Split Γ Γ₁ Γ₂ → VDerives Γ₁ e₀ S →
      XDerives [] [⟨.pair S A, true⟩] cl (.pair S B) →
      XDerives (.cap S A B :: K) (pad :: pad :: pad :: Γ₂) s C →
      XDerives K Γ (.handle S e₀ cl s) C

end HandlersAsBorrows.Xi
