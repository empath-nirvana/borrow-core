import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.Statics.Contexts
import Support.Syntax.Terms

/-!
# [TR] §2 Statics  (physical pp. 2–3)

The typing judgment `Δ; Γ ⊢ e : T` (rules id, 1I, 1E, ⊗I, ⊗E, ⊕I, ⊕E, ⊸I, ⊸E, ∀I,
∀E, [l]I, [l]E, alloc, free, ⊑Imm, ⊑Mut), type well-formedness `Δ ⊢ T`
("Presumes ⊨ Δ"), the outlives judgment `Δ ⊢ T ⊐ @a` ("Presumes ⊨ Δ and
Δ ⊨ @a"), the axiom table (p. 3)

    Δ ⊢ swap     : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁
    Δ ⊢ copy     : Imm @a T ⊸ Imm @a T ⊗ Imm @a T
    Δ ⊢ forget   : Imm @a T ⊸ 1   ∣   Mut @a T ⊸ 1   ∣   Unk ⊸ 1
    Δ ⊢ withbor  : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂
                   Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂      (Δ ⊢ T₁ ⊐ @b)
                   Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂
    Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂
    Δ ⊢ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂

the metafunction `Imm̲ 'b T`, lifetime substitutions `LSub ∋ δ : LifeVar ⇀ Life`,

    ⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀ 'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}      ⊨ Δ ≜ ⟦Δ⟧ ≠ ∅
    Δ ⊨ @a ≜ ∀ δ ∈ ⟦Δ⟧. @aδ defined        Δ ⊨ @a ⊏ @b ≜ ∀ δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ

and the interpretation `@aδ`.  The axiom table names the terms `[TR]` defines on
p. 4, so this file imports §3's.  Each row gives its number (`Paper/INDEX.md`,
*Definitions*), the printed form, the page and a tag; `§N` citations are to
`docs/adjudications.md`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa
open BoCa.Lifetime

/-!
### 2.38 · the axiom table's left column: `Δ ⊢ <term> : <type>`, with no Γ and no premise column · [TR] p. 3 · `[encoding]`

The unwritten Γ is read as `●` (§12.19).
-/
/-- `•` — every slot already consumed. -/
inductive Ctx.Dead {τ : Type} : Ctx τ → Prop where
  | nil                                   : Ctx.Dead []
  | cons {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Dead (⟨T, false⟩ :: Γ)

/-! `[about ours]` -/
/-- `Γ = x : T`, with `x` at de Bruijn index `i` — `ID`'s context. -/
inductive Ctx.Solo {τ : Type} : Ctx τ → Nat → τ → Prop where
  | here  {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Solo (⟨T, true⟩ :: Γ) 0 T
  | there {S T : τ} {Γ : Ctx τ} {i : Nat} : Ctx.Solo Γ i T →
      Ctx.Solo (⟨S, false⟩ :: Γ) (i + 1) T

end BoCa

namespace BoCa

/-!
### 2.39 · `Δ ⊢ swap : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` · [TR] p. 3 (type), p. 4 (term) · `[repair]`

The type is as printed; the term is row 3.24's.

### 3.24 · `swap ≜ λx.λy.let z = load x; store x y; (x, y)` · [TR] p. 4 · `[repair]`

The Lean is [CONF] Fig. 3b's body, which returns the old payload as the type on
[TR] p. 3 requires (§12.20).
-/
/-- `swap ≜ λx.λy₂. let y₁ = load x; store x y₂; (x, y₁)` — [CONF] Fig. 3b
    (p. 415:4). -/
def swap : Expr :=
  lam2 (elet (.app load' v1)
             (.seq (.app (.app store' v2) v1)
                   (.pair v2 v0)))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
Row 2.39, continued.
-/
/-- `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁`. -/
def axSwapTy (T₁ T₂ : Ty) : Ty := .lolli (.ref T₁) (.lolli T₂ (.tensor (.ref T₂) T₁))

/-!
### 2.40 · `Δ ⊢ copy : Imm @a T ⊸ Imm @a T ⊗ Imm @a T` · [TR] p. 3 · `[encoding]`

[CONF] calls the same axiom `dupl` (§12.21).
-/
def axCopyTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) (.tensor (.imm a T) (.imm a T))

/-!
### 2.41 · `Δ ⊢ forget : Imm @a T ⊸ 1` · [TR] p. 3 · `[encoding]`
-/
def axForgetImmTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) .unit

/-!
### 2.42 · `Δ ⊢ forget : Mut @a T ⊸ 1` · [TR] p. 3 · `[encoding]`
-/
def axForgetMutTy (a : Life) (T : Ty) : Ty := .lolli (.mut a T) .unit

/-!
### 2.43 · `Δ ⊢ forget : Unk ⊸ 1` · [TR] p. 3 · `[encoding]`
-/
def axForgetUnkTy : Ty := .lolli .unk .unit

end BoCa

namespace BoCa

/-!
### 2.44 · `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂` · [TR] p. 3 (type), p. 4 (term) · `[as printed]`

The ∀ binder is schematic: the constructor takes `x : LifeVar` with the freshness
premise `Δ.find? x = none` (§12.44, §12.45), as do `withbor2Ax`, `withbor3Ax` and
`withloadAx`.  `⊓Δ` is §12.15; the term is row 3.27's.

### 3.27 · `withbor ≜ λx.λf.(x, f x)` · [TR] p. 4 · `[repair]`

The Lean is [CONF] Fig. 15's `λx.λf.(x, f () x)`, which forces the thunked callback
that [TR] p. 4's `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` requires (§12.20).
-/
/-- `withbor ≜ λx.λf. (x, f () x)` — [CONF] Fig. 15 (p. 415:17). -/
def withbor : Expr := lam2 (.pair v1 (.app (.app v0 unit') v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
Row 2.44, continued.
-/
/-- `(1) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
def axWithbor1Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-!
### 2.45 · `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂`, side condition `Δ ⊢ T₁ ⊐ @b` on this line · [TR] p. 3 · `[repair]`

The free `@b` of the side condition is quantified existentially, with `Δ ⊨ @b`
(§12.9).
-/
/-- `(2) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
def axWithbor2Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-!
### 2.46 · `Δ ⊢ withbor : Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂` · [TR] p. 3 · `[repair]`

The type is as printed, with no side condition; the term is row 3.27's.  [TR]
Lemma 6.174 reads `Δ ⊢ T₁ ⊐ @a` off "well-formedness of the type `Mut @a T₁`",
which row 2.28 does not supply (§12.32).
-/
/-- `(3) Mut @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b]T₂) ⊸ Mut @a T₁ ⊗ T₂` -/
def axWithbor3Ty (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.mut a T₁) T₂))

end BoCa

namespace BoCa

/-!
### 2.47 · `Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂` (leading `Imm` UNDERLINED) · [TR] p. 3 (type), p. 4 (term) · `[repair]`

The underlined `Imm̲` is the metafunction `BoCa.Ty.immReborrow` (§12.28); the term
is row 3.28's.

### 3.28 · `withload ≜ λx.λf.(x, f (load x))` · [TR] p. 4 · `[repair]`

The Lean is [CONF] Fig. 14's `λx.λf. f () (load x)`, which returns the bare `T₂`
of the printed type and forces the thunked callback (§12.20).
-/
/-- `withload ≜ λx λf. f () (load x)` — [CONF] Fig. 14 (p. 415:16). -/
def withload : Expr := lam2 (.app (.app v0 unit') (.app load' v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-!
### 2.48 · `Δ ⊢ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂` · [TR] p. 3 · `[encoding]`
-/
def axWithswapTy (a : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁) (.lolli (.lolli T₁ (.tensor T₁ T₂)) (.tensor (.mut a T₁) T₂))

/-!
### 2.49 · `Imm̲ 'b 1 ≜ 1`; `Imm̲ 'b (T₁⊕T₂)`; `Imm̲ 'b (T₁⊗T₂)`; `Imm̲ 'b (T₁⊸T₂) ≜ Unk`; `Imm̲ 'b (Ref T) ≜ Imm 'b T`; `Imm̲ 'b (Imm @a T) ≜ Imm @a T`; `Imm̲ 'b ([@a]T) ≜ Imm̲ 'b T`; `Imm̲ 'b (∀ '.a ⊏ @a. T) ≜ Unk` · [TR] p. 3 · `[as printed]`

The underline is on the right-hand sides of the ⊕, ⊗ and `[@a]` clauses and not
on the `Ref` and `Imm` clauses, which send to the constructor.

### 2.50 · — no printed clause — · [TR] p. 3 · `[repair]`

Two clauses are added: `Imm̲ 'b (Mut @a T) ≜ Imm 'b T` from [CONF] Fig. 9 (§12.10),
and `Imm̲ 'b Unk ≜ Unk` (§12.11).
-/
/-- `Imm̲ 'b T`, the reborrow metafunction. -/
def Ty.immReborrow (b : Life) : Ty → Ty
  | .unit          => .unit                                          -- (1)
  | .sum    T₁ T₂  => .sum    (T₁.immReborrow b) (T₂.immReborrow b)   -- (2)
  | .tensor T₁ T₂  => .tensor (T₁.immReborrow b) (T₂.immReborrow b)   -- (3)
  | .lolli  _  _   => .unk                                           -- (4)
  | .ref T         => .imm b T                                 -- (5) constructor
  | .bang T        => .bang T                                  -- `!T` holds no resource  `[spec §2]`
  | .imm a T       => .imm a T                                 -- (6) constructor
  | .box _ T       => T.immReborrow b                          -- (7) recursive
  | .all _ _ _     => .unk                                           -- (8)
  -- (9) [CONF] Fig. 9 (§12.10).  The index is the load's fresh `'b`, not the
  -- mutable borrow's `@a` ([CONF] p. 415:11).
  | .mut _ T       => .imm b T                                 -- (9) constructor
  | .unk           => .unk                                     -- §12.11

/-!
Row 2.47, continued.
-/
/-- `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂`. -/
def axWithloadTy (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.imm a T₁)
    (.lolli (.all x bnd (.lolli (Ty.immReborrow (.var x) T₁) (.box (.var x) T₂)))
            T₂)

end BoCa

namespace BoCa.Lifetime

/-!
### 2.51 · `LSub ∋ δ : LifeVar ⇀ Life` · [TR] p. 3 · `[encoding]`

The codomain is p. 4's semantic `Life`, carried as `Nat`; the partial map is an
association list.
-/
structure LSub where
  entries : List (LifeVar × Nat)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa.Lifetime.LSub

/-! `[about ours]` -/
def find? (δ : LSub) (x : LifeVar) : Option Nat := assocFind x δ.entries

end BoCa.Lifetime.LSub

namespace BoCa.Lifetime

/-!
### 2.54 · `@aδ ≜ δ('a)`, `⊤`, `@b₁δ ⊓ @b₂δ` at `@a = @b₁ ⊔ @b₂`, `@b₁δ ⊔ @b₂δ` at `@a = @b₁ ⊔ @b₂` · [TR] p. 3 · `[repair]`

The third clause's guard is read as `@a = @b₁ ⊓ @b₂`, [CONF] Fig. 11's
homomorphic interpretation (§12.7).  `@aδ` is undefined (`none`) when a variable
is outside `dom(δ)`.
-/
def Life.interp (δ : LSub) : Life → Option Nat
  | .var x    => δ.find? x
  | .top      => some SLife.top
  -- §12.7
  | .join a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.join m n)
  | .meet a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.meet m n)

/-! `[about ours]` -/
@[simp] theorem Life.interp_var (δ : LSub) (x : LifeVar) :
    (Life.var x).interp δ = δ.find? x := rfl

@[simp] theorem Life.interp_top (δ : LSub) :
    (Life.top).interp δ = some SLife.top := rfl

/-!
### 2.52 · `⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}` · [TR] p. 3 · `[encoding]`

The first conjunct is implied by the second and is not stated.

### 4.12 · `𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝` · [TR] p. 4, with ⟦Δ⟧ from p. 3 · `[encoding]`
-/
def LifeCtx.Models (Δ : LifeCtx) (δ : LSub) : Prop :=
  ∀ x u, Δ.find? x = some u →
    ∃ m n, δ.find? x = some m ∧ u.interp δ = some n ∧ SLife.Lt m n

/-!
### 2.53 · `⊨ Δ ≜ ⟦Δ⟧ ≠ ∅` · [TR] p. 3 · `[as printed]`
-/
/-- `⊨ Δ`.  `LifeCtx.Ok` is a decidable sufficient condition. -/
def LifeCtx.Sat (Δ : LifeCtx) : Prop := ∃ δ, Δ.Models δ

/-!
### 2.55 · `Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined` · [TR] p. 3 · `[as printed]`
-/
def LifeCtx.Defines (Δ : LifeCtx) (a : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ n, a.interp δ = some n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.19 · `Δ ⊢ T` — "Presumes ⊨ Δ" (boxed judgment form) · [TR] p. 2 · `[encoding]`

The presupposition `⊨ Δ` is carried by no constructor, and no `BoCa.Derives`
constructor has a `WfTy` premise.  `BoCa.DerivesWf` consults `Δ ⊢ T` at binders
and eliminated types through the decidable `BoCa.Ty.scopedB` (§C.26).

### 2.20 · `Δ ⊢ 1` · [TR] p. 2 · `[as printed]`

### 2.21 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊗ T₂` · [TR] p. 2 · `[as printed]`

### 2.22 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊕ T₂` · [TR] p. 2 · `[as printed]`

### 2.23 · `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊸ T₂` · [TR] p. 2 · `[as printed]`

### 2.24 · `Δ ⊢ T` / `Δ ⊢ Ref T` · [TR] p. 2 · `[as printed]`

### 2.25 · `Δ, ('a ⊏ @b) ⊢ T`, `Δ ⊨ @b` / `Δ ⊢ ∀ ('a ⊏ @b).T` · [TR] p. 2 · `[as printed]`

### 2.26 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ [@a] T` · [TR] p. 2 · `[as printed]`

### 2.27 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Imm @a T` · [TR] p. 2 · `[as printed]`

### 2.28 · `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Mut @a T` · [TR] p. 2 · `[as printed]`

### 2.29 · no rule for `Unk` anywhere in `Δ ⊢ T` · [TR] p. 2 · `[as printed]`
-/
/-- `Δ ⊢ T`. -/
inductive WfTy : LifeCtx → Ty → Prop where
  | unit   {Δ}                                              : WfTy Δ .unit
  | tensor {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.tensor T₁ T₂)
  | sum    {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.sum T₁ T₂)
  | lolli  {Δ T₁ T₂} : WfTy Δ T₁ → WfTy Δ T₂                → WfTy Δ (.lolli T₁ T₂)
  | ref    {Δ T}     : WfTy Δ T                             → WfTy Δ (.ref T)
  | bang    {Δ T}     : WfTy Δ T                             → WfTy Δ (.bang T)
  | all    {Δ x b T} : Δ.Defines b → WfTy (Δ.extend x b) T  → WfTy Δ (.all x b T)
  | box    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.box a T)
  | imm    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.imm a T)
  /-- The two printed premises (§12.32). -/
  | mut    {Δ a T}   : WfTy Δ T → Δ.Defines a               → WfTy Δ (.mut a T)

end BoCa

namespace BoCa.Lifetime

/-!
### 2.56 · `Δ ⊨ @a ⊏ @b ≜ ∀δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ` · [TR] p. 3 · `[as printed]`

Definedness of both sides, which `@aδ ⊏ @bδ` presupposes, is part of the Lean
statement.
-/
def LifeCtx.EntailsLt (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Lt m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.30 · `Δ ⊢ T ⊐ @a` — "Presumes ⊨ Δ and Δ ⊨ @a" (boxed judgment form) · [TR] p. 2 · `[encoding]`

Neither presupposition is a hypothesis of the judgment (§C.25).

### 2.31 · `Δ ⊢ 1 ⊐ @a` · [TR] p. 2 · `[as printed]`

### 2.32 · `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊗ T₂ ⊐ @a` · [TR] p. 2 · `[as printed]`

### 2.33 · `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊕ T₂ ⊐ @a` · [TR] p. 2 · `[as printed]`

### 2.34 · `Δ ⊢ T ⊐ @a` / `Δ ⊢ Ref T ⊐ @a` · [TR] p. 2 · `[as printed]`

### 2.35 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ [@b] T ⊐ @a` · [TR] p. 2 · `[as printed]`

[TR]'s premise, not [CONF] Fig. 7's disjunction (§12.17).

### 2.36 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Imm @b T ⊐ @a` · [TR] p. 2 · `[as printed]`

### 2.37 · `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Mut @b T ⊐ @a` · [TR] p. 2 · `[as printed]`
-/
/-- The seven rules of `Δ ⊢ T ⊐ @a`.  There is no rule for `⊸`, `∀` or `Unk`. -/
inductive OutlivesRules (Δ : LifeCtx) (a : Life) : Ty → Prop where
  | unit                                                       : OutlivesRules Δ a .unit
  | tensor {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.tensor T₁ T₂)
  | sum    {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.sum T₁ T₂)
  | ref    {T}     : OutlivesRules Δ a T                       → OutlivesRules Δ a (.ref T)
  | bang    {T}     :                                             OutlivesRules Δ a (.bang T)
  | box    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.box b T)
  | imm    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.imm b T)
  | mut    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.mut b T)

/-!
Row 2.30, continued.
-/
/-- `Δ ⊢ T ⊐ @a`, at an unrestricted index (§C.25). -/
def Outlives (Δ : LifeCtx) (T : Ty) (a : Life) : Prop :=
  OutlivesRules Δ a T

end BoCa

namespace BoCa.Lifetime

/-!
### 2.57 · `Δ ⊨ @a ⊑ @b` — premise of ⊑Imm and ⊑Mut, NEVER DEFINED · [TR] p. 2 (used); nowhere (defined) · `[encoding]`

Read as the non-strict companion of p. 3's `Δ ⊨ @a ⊏ @b`, at [CONF] Fig. 11's
"(and similarly for `⊑̇`)" (§12.3).
-/
def LifeCtx.EntailsLe (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Le m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 2.58 · `Δ ⊨ Γ ⊐ @a` — premise of [l]I, NEVER DEFINED · [TR] p. 2 (used); nowhere (defined) · `[repair]`

Read as [CONF] Fig. 7's pointwise lift `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a`, with
`dom(Γ)` the live slots (§12.6, §C.25).
-/
def Ctx.Outlives (Δ : LifeCtx) (Γ : Ctx Ty) (a : Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → OutlivesRules Δ a s.ty

end BoCa

namespace BoCa.Lifetime

/-!
### 2.59 · `⊓Δ` — the ∀ bound in all three `withbor` forms and in `withload`, never defined as an operation · [TR] p. 3 · `[encoding]`

The meet over `dom(Δ)`, as a right fold of p. 1's binary ⊓, with `⊓∅ = ⊤`
(§12.15).
-/
def meetOfDomL : List (LifeVar × Life) → Life
  | []          => .top
  | (x, _) :: t => .meet (.var x) (meetOfDomL t)

/-!
Row 2.59, continued.
-/
def LifeCtx.meetOfDom (Δ : LifeCtx) : Life := meetOfDomL Δ.entries

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
Rows 2.38–2.48, continued.

### 2.1 · `Δ; Γ ⊢ e : T` (boxed judgment form) · [TR] p. 2 · `[encoding]`

De Bruijn `Expr` and a positional `BoCa.Ctx` of ⟨type, live⟩ slots: `●` is
`BoCa.Ctx.Dead`, `x : T` is `BoCa.Ctx.Solo` and `Γ₁,Γ₂` is the `BoCa.Ctx.Split`
partition.

### 2.2 · ID: `Δ; x : T ⊢ x : T` · [TR] p. 2 · `[encoding]`

### 2.3 · 1I: `Δ; ● ⊢ () : 1` · [TR] p. 2 · `[encoding]`

### 2.4 · 1E: `Δ; Γ₁ ⊢ e₁ : 1`, `Δ; Γ₂ ⊢ e₂ : T` / `Δ; Γ₁,Γ₂ ⊢ e₁; e₂ : T` · [TR] p. 2 · `[as printed]`

### 2.5 · ⊗I: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₂` / `Δ; Γ₁,Γ₂ ⊢ (e₁,e₂) : T₁ ⊗ T₂` · [TR] p. 2 · `[as printed]`

### 2.6 · ⊗E: `Δ; Γp ⊢ ep : T₁ ⊗ T₂`, `Δ; Γ, x₁:T₁, x₂:T₂ ⊢ e : T` / `Δ; Γp,Γ ⊢ let (x₁,x₂) = ep; e : T` · [TR] p. 2 · `[encoding]`

### 2.7 · ⊕I: `Δ; Γ ⊢ e : Tᵢ`, `i ∈ {1,2}` / `Δ; Γ ⊢ i e : T₁ ⊕ T₂` · [TR] p. 2 · `[encoding]`

One constructor for each `i`; `i e` is p. 1's `injᵢ e` (§12.16).

### 2.8 · ⊕E: `Δ; Γs ⊢ es : T₁ ⊕ T₂`, `Δ; Γ, x_b : T_b ⊢ e_b : T` for `b ∈ {1,2}` / `Δ; Γs,Γ ⊢ match es {x₁ ⇒ e₁, x₂ ⇒ e₂} : T` · [TR] p. 2 · `[as printed]`

§2's `match` is §1's `case` (§12.21).

### 2.9 · ⊸I: `Δ; Γ, x : T₁ ⊢ e : T₂` / `Δ; Γ ⊢ λx.e : T₁ ⊸ T₂` · [TR] p. 2 · `[as printed]`

### 2.10 · ⊸E: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₁ ⊸ T₂` / `Δ; Γ₁,Γ₂ ⊢ e₁ e₂ : T₂` · [TR] p. 2 · `[repair]`

The conclusion is read as `e₂ e₁`, function on the left, as in p. 1's production
and the β-rule (§12.2, §12.1).

### 2.11 · ∀I: `Δ, ('a ⊏ @b); Γ ⊢ e : T` / `Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T` · [TR] p. 2 · `[repair]`

`Λ.e ≜ λ_.e` (row 1.8, §12.14), and the freshness premise `Δ.find? x = none` is
added (§12.44).

### 2.12 · ∀E: `Δ; Γ ⊢ e : ∀ 'a ⊏ @b. T`, `Δ ⊨ @a ⊏ @b` / `Δ; Γ ⊢ e[] : T[@a/'a]` · [TR] p. 2 · `[repair]`

`e[] ≜ e ()`, as in [CONF] Fig. 7 and [TR] p. 4's `𝒱⟦∀⟧` (§12.14).

### 2.13 · [l]I: `Δ; Γ ⊢ e : T`, `Δ ⊨ Γ ⊐ @a` / `Δ; Γ ⊢ □e : [@a] T` · [TR] p. 2 · `[repair]`

The premise is row 2.58's reading (§12.6); the index is unrestricted (§C.25).

### 2.14 · [l]E: `Δ; Γ ⊢ □e : [@a] T` / `Δ; Γ ⊢ □e : T` · [TR] p. 2 · `[encoding]`

`□` is a typesetting marker and is erased (§12.5).

### 2.15 · alloc: `Δ; ● ⊢ alloc : T ⊸ Ref T` · [TR] p. 2 · `[encoding]`

### 2.16 · free: `Δ; ● ⊢ free : Ref T ⊸ T` · [TR] p. 2 · `[encoding]`

### 2.17 · ⊑Imm: `Δ; Γ ⊢ e : Imm @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Imm @b T` · [TR] p. 2 · `[repair]`

The conclusion is at `Imm @a T`, as in [CONF] Figs. 7/9 and [TR] Lemma 6.167
(§12.4).

### 2.18 · ⊑Mut: `Δ; Γ ⊢ e : Mut @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Mut @b T` · [TR] p. 2 · `[repair]`

The conclusion is at `Mut @a T`, as in [CONF] Fig. 9 and [TR] Lemma 6.168
(§12.4).
-/
/-- `Δ; Γ ⊢ e : T`: `e` consumes exactly the live slots of `Γ`. -/
inductive Derives : LifeCtx → Ctx Ty → Expr → Ty → Prop where
  ---------------------------------------------------------------- core
  /-- `ID`:  `Δ; x : T ⊢ x : T`. -/
  | var {Δ Γ i T} (h : Ctx.Solo Γ i T) : Derives Δ Γ (.var i) T
  /-- `1I`:  `Δ; • ⊢ () : 1`. -/
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : Derives Δ Γ (.val .unit) .unit
  /-- `1E`:  `Δ; Γ₁ ⊢ e₁ : 1`, `Δ; Γ₂ ⊢ e₂ : T`  ⟹  `Δ; Γ₁,Γ₂ ⊢ e₁;e₂ : T`. -/
  | unitE {Δ Γ Γ₁ Γ₂ e₁ e₂ T} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : Derives Δ Γ₁ e₁ .unit) (h₂ : Derives Δ Γ₂ e₂ T) :
      Derives Δ Γ (.seq e₁ e₂) T
  /-- `⊗I`. -/
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : Derives Δ Γ₁ e₁ T₁) (h₂ : Derives Δ Γ₂ e₂ T₂) :
      Derives Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂)
  /-- `⊗E`.  De Bruijn: `x₂` is index 0, `x₁` is index 1. -/
  | tensorE {Δ Γ Γp Γb ep eb T₁ T₂ T} (hs : Ctx.Split Γ Γp Γb)
      (hp : Derives Δ Γp ep (.tensor T₁ T₂))
      (hb : Derives Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
      Derives Δ Γ (.letpair ep eb) T
  /-- `⊕I` at `i = 1`. -/
  | sumI₁ {Δ Γ e T₁ T₂} (h : Derives Δ Γ e T₁) :
      Derives Δ Γ (.inj₁ e) (.sum T₁ T₂)
  /-- `⊕I` at `i = 2`. -/
  | sumI₂ {Δ Γ e T₁ T₂} (h : Derives Δ Γ e T₂) :
      Derives Δ Γ (.inj₂ e) (.sum T₁ T₂)
  /-- `⊕E`. -/
  | sumE {Δ Γ Γs Γb es e₁ e₂ T₁ T₂ T} (hs : Ctx.Split Γ Γs Γb)
      (h₀ : Derives Δ Γs es (.sum T₁ T₂))
      (h₁ : Derives Δ (⟨T₁, true⟩ :: Γb) e₁ T)
      (h₂ : Derives Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
      Derives Δ Γ (.case es e₁ e₂) T
  /-- `⊸I`.  The binder's slot is live in the premise, so the body must consume
      it. -/
  | lolliI {Δ Γ b T₁ T₂}
      (h : Derives Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      Derives Δ Γ (.val (.lam b)) (.lolli T₁ T₂)
  /-- `⊸E` (§12.2): `a` is the printed `e₁ : T₁`, `f` the printed
      `e₂ : T₁ ⊸ T₂`. -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : Derives Δ Γ₁ a T₁) (hf : Derives Δ Γ₂ f (.lolli T₁ T₂)) :
      Derives Δ Γ (.app f a) T₂
  ------------------------------------------------------- lifetimes, §12.14
  /-- `∀I`.  `Λ.e ≜ λ_.e`, so the premise's context gains a slot that is already
      dead; its type is schematic. -/
  | allI {Δ Γ x b S e T} (hx : Δ.find? x = none)
      (h : Derives (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
      Derives Δ Γ (.val (.lam e)) (.all x b T)
  /-- `∀E`.  `e[] ≜ e ()` (§12.14). -/
  | allE {Δ Γ e x b T a} (h : Derives Δ Γ e (.all x b T))
      (hlt : Δ.EntailsLt a b) :
      Derives Δ Γ (.app e (.val .unit)) (Ty.instLife x a T)
  /-- `[]I` (§12.5, §12.6). -/
  | boxIctx {Δ Γ e T a} (h : Derives Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
      Derives Δ Γ e (.box a T)
  /-- `[]E`. -/
  | boxE {Δ Γ e T a} (h : Derives Δ Γ e (.box a T)) : Derives Δ Γ e T
  /-- `⊑Imm`, concluding at `@a` (§12.4). -/
  | immSub {Δ Γ e a b T} (h : Derives Δ Γ e (.imm b T))
      (hle : Δ.EntailsLe a b) :
      Derives Δ Γ e (.imm a T)
  /-- `⊑Mut`, concluding at `@a` (§12.4). -/
  | mutSub {Δ Γ e a b T} (h : Derives Δ Γ e (.mut b T))
      (hle : Δ.EntailsLe a b) :
      Derives Δ Γ e (.mut a T)
  ---------------------------------------------------------- memory
  /-- `Δ; • ⊢ alloc : T ⊸ Ref T`. -/
  | allocAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T))
  /-- `Δ; • ⊢ free : Ref T ⊸ T`. -/
  | freeAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ (.val (.prim .free)) (.lolli (.ref T) T)
  ------------------------------------------------- the axiom table, [TR] p. 3
  /-  The axioms have no premise; the one side condition is `Δ ⊢ T₁ ⊐ @b` beside
      `withbor`'s second form.                                                  -/
  | swapAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ swap (axSwapTy T₁ T₂)
  | copyAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ copy (axCopyTy a T)
  | forgetImmAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ forget (axForgetImmTy a T)
  | forgetMutAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ forget (axForgetMutTy a T)
  | forgetUnkAx {Δ Γ} (hΓ : Ctx.Dead Γ) : Derives Δ Γ forget axForgetUnkTy
  /-- Form (1).  The ∀ binder is a parameter, fresh for `Δ` (§12.44, §12.45). -/
  | withbor1Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (2), with the side condition `Δ ⊢ T₁ ⊐ @b` read existentially
      (§12.9). -/
  | withbor2Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b) :
      Derives Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (3), with no side condition, as printed (§12.32). -/
  | withbor3Ax {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)
  | withloadAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none) :
      Derives Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂)
  | withswapAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) :
      Derives Δ Γ withswap (axWithswapTy a T₁ T₂)

end BoCa

namespace BoCa.Lifetime

/-!
Row 2.59, continued.
-/
def LifeCtx.freshVar (Δ : LifeCtx) : LifeVar := freshOfL Δ.entries

end BoCa.Lifetime

end
