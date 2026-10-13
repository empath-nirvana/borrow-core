import ProbeD1.Binder

/-!
# ProbeD1 — the block push (`GROUND.md` §4.2, `NEXT.md` item 1b)

[TR] 6.150's reborrow puts every reborrowed cell at one lifetime `β`. A cell at an internal
lifetime and at an unlent place can be neither a view nor above the cut, so the stack lends every
reborrowed place at `β`: a **block** of entries sharing variable, lifetime and lender's row.
GhostEnd's `LEnt` lends one place and stays as it is.

The single own push (`OwnPushM`) is kept. A block of two or more entries is pushed beside it, at a
callback-shaped type whose argument fits the block one entry per leaf (`BlockFits`), read at both
callback shapes (`CbArg`). A single-leaf callback has no block push (`BlockFitsLeafLe`,
`GroundBlock.lean`).

* `blockL`, `StackOKB`: a stack in shape with blocks admitted. Two entries share a variable
  exactly when they share a lifetime, and a block's entries share their lender's row.
* `BlockFits`, `CbArg`: the block against the callback's argument.
* `OwnOKB`, `OwnPushB`: a block's own lend. `OwnOKB.placeFree` admits `own` cells at a block place
  frozen under an `imm` ancestor.
* `StackJBase`, `StackJB`: `StackJ` and `StackJM` with blocks. Their distinct variables are dropped
  (`StackOKB`'s variable condition replaces them), and their third kind is read at the innermost
  block.

Definitions only; the gate lemmas are in `GroundBlock.lean`.
-/

noncomputable section

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS)

/-- `τ`'s entries all at `a`. -/
abbrev blockL (τ : LStack) (a : Life) : List Life := τ.map fun _ => a

/-- **A stack in shape, blocks admitted**: one lifetime per entry, non-decreasing outward; two
entries share a variable exactly when they share a lifetime; a block's entries share their lender's
row. `StackOK` is the case with no block (`stackOKB_of_ok`, `GroundBlock.lean`). -/
def StackOKB (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· ≤ ·) αs ∧
    (∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.1.x = q.1.x ↔ p.2 = q.2) ∧
    ∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.2 = q.2 → p.1.cross = q.1.cross

/-- **A block fits an argument type at `'x`, one entry per leaf.** Each entry is assigned to one
borrow leaf of `A` at `'x` (`Mut 'x S`, `Imm 'x S`) whose kind and payload it has, and no leaf takes
two entries, except that a family's element and a `μ` unrolling repeat their leaves. A sum takes one
side, as its value does. No entry fits under `!`, whose value holds no cell. -/
inductive BlockFits (x : LifeVar) : LStack → VTy → Prop
  | nil (A : VTy) : BlockFits x [] A
  | mut {e : LEnt} {S : VTy} : e.k = .mut → e.T = S → BlockFits x [e] (.mut (.var x) S)
  | imm {e : LEnt} {S : VTy} : (∃ u, e.k = .imm u) → e.T = S → BlockFits x [e] (.imm (.var x) S)
  | tensor {τ τ₁ τ₂ : LStack} {A B : VTy} : BlockFits x τ₁ A → BlockFits x τ₂ B →
      τ.Perm (τ₁ ++ τ₂) → BlockFits x τ (.tensor A B)
  | sumL {τ : LStack} {A B : VTy} : BlockFits x τ A → BlockFits x τ (.sum A B)
  | sumR {τ : LStack} {A B : VTy} : BlockFits x τ B → BlockFits x τ (.sum A B)
  | box {τ : LStack} {a : Lifetime.Life} {A : VTy} : BlockFits x τ A → BlockFits x τ (.box a A)
  | fam {τ τ₁ τ₂ : LStack} {L : VTy} : BlockFits x τ₁ L → BlockFits x τ₂ (.fam L) →
      τ.Perm (τ₁ ++ τ₂) → BlockFits x τ (.fam L)
  | mu {τ : LStack} {A : VTy} : (VTy.mu A).Cl 0 → BlockFits x τ (VTy.inst (.mu A) A) →
      BlockFits x τ (.mu A)

/-- **The argument a callback-shaped computation type takes**: `A` at `A ⊸ D` (the `.arr` shape,
the unwinding constants' `cbUTy`) and at `F (U (A ⊸ D))` (the `.ret` shape: the non-unwinding
constants' callbacks and `foldImm`'s algebra). -/
def CbArg (C' : CTy) (A : VTy) : Prop :=
  (∃ D, C' = .arr A D) ∨ ∃ D, C' = .ret (.thunk (.arr A D))

/-- **A block's own lend.** `placeFree` admits `own` cells at a block place frozen under an `imm`
ancestor (a copy of the lend's view held by the callback, `NEXT.md` §1.6). -/
structure OwnOKB (δ : LSub) (σ : LStack) (αs : List Life) (x : LifeVar) (τ : LStack) (a : Life)
    (ρ : WRes) : Prop where
  ne : τ ≠ []
  named : ∀ e ∈ τ, e.x = x
  sameRow : ∀ e ∈ τ, ∀ e' ∈ τ, e.cross = e'.cross
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : x ∉ σ.map LEnt.x
  placesNodup : (τ.map LEnt.l).Nodup
  places : ∀ e ∈ τ, e.l ∉ σ.map LEnt.l
  placeFree : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ
  pay : ∀ e ∈ τ, ∀ y, VFree y e.T → (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y ≠ none
  selfFree : ∀ e ∈ τ, ¬ VFree x e.T

/-- **The own lend at the type `C`, a block of two or more entries**: at a callback-shaped type,
the block fitting its argument (`BlockFits`), `OwnPushM`'s `payLocal` kept. A single push stays
`OwnPushM`'s. -/
def OwnPushB (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (τ : LStack) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy) (A : VTy), C = .all x c C' ∧ CbArg C' A ∧
    x ∉ CTy.binders C' ∧ 2 ≤ τ.length ∧ OwnOKB δ s.1 s.2 x τ a ρ ∧
    LtLife (extS δ s.1 s.2) c a ∧ (∀ e ∈ τ, ∀ y, VFree y e.T → CFree y C) ∧ BlockFits x τ A

/-- **`StackJ` with blocks**: its distinct variables dropped (`StackOKB`'s variable condition
replaces them), its third kind read at the innermost block. `SemIdxM` and `SemSMC` read it. -/
def StackJBase (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (∀ e ∈ σ, ∀ y, VFree y e.T → (∃ u, Δ.find? y = some u) ∨ y ∈ σ.map LEnt.x) ∧
  ∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head?.map LEnt.x = some e.x ∧ CtxFresh e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧ ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)

/-- **`StackJM` with blocks**: `StackJBase` and `StackJM`'s extra conjunct at the innermost block.
`SemSM` reads it. -/
def StackJB (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  StackJBase σ αs δ Δ Γ C ∧
  ∀ e ∈ σ, Δ.find? e.x = none → σ.head?.map LEnt.x = some e.x → (∃ c C', C = .all e.x c C') →
    (∀ a ∈ αs.head?, SubFresh δ a) ∧ ∀ e' ∈ σ, ¬ VFree e.x e'.T

end ProbeD1

end
