import DenseCarrier.Carrier

/-!
# DenseCarrier — Core's relation over the lifetime order `L`, at the fragment `GapWitness` reads

The clauses are `Core/Relation.lean`'s, at the formers `GapWitness.lean` and `SegShift.lean`
use (`1`, `Mut`, `F`, `∀`) and the ones the `∀` rules of the fundamental property meet beside
them (`[@a]`, `⊸`, `⊤`). Each clause is Core's with these changes, and no other:

* `δ` is `LSubD L` and `@aδ` is `interpD` (values in `L`, not `ℕ`);
* the `∀` clause ranges over `α : L`;
* where a clause compares an `L`-lifetime with a cell's lifetime (a slot), it reads the slot
  through `ι : Slots L`: `ptoMutD`'s `α ⊑ ι b` for `ptoMutS`'s `α ⊑ b`, and `OutlivesD`'s
  `α ⊏ ι(@ψ)` for `Outlives`'s `α ⊏ @ψ` in `[α]`.

Everything else is Core's own definition, not a copy: the cells and resources, `wpTS` with its
typed world `TW` and tagged record lists, `↭`, `⋆`, `─⋆`, `⌜−⌝`. Outside the fragment the clauses
are `False`; `FragV`/`FragC` name the fragment.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-- `ψ ∈ Cell_α` with the slot read in `L` (`CellU.InStratum` through `ι`). -/
def InStratumD (ι : Slots L) (α : L) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => α < ι i.ls.meet
  | .mut m => α < ι m.β

/-- `@ρ ⊐ α` with the slots read in `L` (`Outlives` through `ι`). -/
def OutlivesD (ι : Slots L) (ρ : WRes) (α : L) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → InStratumD ι α ψ

/-- `[α] P` (`box` through `ι`). -/
def boxD (ι : Slots L) (α : L) (P : WProp) : WProp := fun ρ => P ρ ∧ OutlivesD ι ρ α

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ` (`ptoMutS` with `α ⊑ ι b` for `α ⊑ b`). -/
def ptoMutD (ι : Slots L) (l : Loc) (α : L) (ls : List SRec) (P : List SRec → Val → WProp) :
    WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ≤ ι b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

/-- `𝒱⟦A⟧(ls)δ(v)` at the fragment's value types (`vCE none true`'s clauses). -/
def vD (ι : Slots L) : VTy → List SRec → LSubD L → Val → WProp
  | .unit, _, _, v => ⌜v = .unit⌝
  | .box a A, ls, δ, v => atLifeD δ a fun α => boxD ι α (vD ι A ls δ v)
  | .mut a A, ls, δ, v =>
      atLifeD δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutD ι ℓ α ls (fun ls₀ => vD ι A ls₀ δ)
  | _, _, _, _ => fun _ => False

/-- `𝒞⟦C⟧(ls)δ(e)` at the fragment's computation types (`cC`'s clauses). -/
def cD (ι : Slots L) : CTy → List SRec → LSubD L → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vD ι A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ => ∀ v, (vD ι A ls δ v ─⋆ cD ι C ls δ (.app e (.val v))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α : L, (⌜LtLifeD δ c α⌝ ─⋆ cD ι C ls (δ.extend x α) (.app e (.val .unit))) ρ
  | _, _, _, _ => fun _ => False

/-- The fragment's value types. -/
def FragV : VTy → Prop
  | .unit => True
  | .box _ A => FragV A
  | .mut _ A => FragV A
  | _ => False

/-- The fragment's computation types. -/
def FragC : CTy → Prop
  | .ret A => FragV A
  | .arr A C => FragV A ∧ FragC C
  | .top => True
  | .all _ _ C => FragC C
  | _ => False

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧(ls)δ(γ(x))` (`gSepC`). -/
def gSepD (ι : Slots L) (ls : List SRec) (δ : LSubD L) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ => if s.live then vD ι s.ty ls δ v ⋆ gSepD ι ls δ Γ γ else gSepD ι ls δ Γ γ

/-- `𝒢⟦Γ⟧(ls)δ(γ)` (`gDenC`). -/
def gDenD (ι : Slots L) (ls : List SRec) (δ : LSubD L) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepD ι ls δ Γ γ

/-- `Δ; Γ ⊨ e : C` over `L` (`SemC`). -/
def SemD (ι : Slots L) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ (δ : LSubD L) γ (ls : List SRec) ρ, ModelsD Δ δ → gDenD ι ls δ Γ γ ρ →
    cD (ℍ := ℍ) ι C ls δ (substAll γ e) ρ

end DenseCarrier

end
