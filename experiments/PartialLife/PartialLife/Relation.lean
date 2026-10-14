import PartialLife.Reading
import DenseCarrier.Relation

/-!
# PartialLife — Core's relation over a partial order of lifetimes, at the fragment

The clauses are `Core/Relation.lean`'s at the formers `DenseCarrier/Relation.lean` rebuilt (`1`,
`⊗`, `U`, `Ref`, `[@a]`, `Mut`, `F`, `⊸`, `⊤`, `∀`), with the lifetimes the relation reads in a
partial order `L` with a top. Each clause is Core's with these changes, and no other:

* `δ` is `LSubD L` and `@aδ` is `interpP`: values in `L`; `@a ⊔ @b` and `@a ⊓ @b` read as the least
  upper and greatest lower bound, undefined where `L` has none (Core: always defined, `min`/`max`
  on `ℕ`);
* the `∀` clause ranges over `α : L`;
* where a clause compares an `L`-lifetime with a cell's lifetime (a slot), it reads the slot through
  `ι : Reading L`: `ptoMutP`'s `α ⊑ ι b` for `ptoMutS`'s `α ⊑ b`, and `OutlivesP`'s `α ⊏ ι(@ψ)` for
  `Outlives`'s `α ⊏ @ψ` in `[α]`.

No clause compares two lifetimes of `L` except through `≤` and `<`, and no clause asks two of them to
be comparable. Everything else is Core's own definition, not a copy: the cells and resources, `wpTS`
with its typed world `TW` and tagged record lists, `↭`, `⋆`, `─⋆`, `⌜−⌝`. The comparisons Core's
model makes between two cells, or a cell and a record, stay on the slots. Outside the fragment the
clauses are `False`; the fragment is `DenseCarrier.FragV`/`FragC`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open DenseCarrier (LSubD FragV FragC)

variable {L : Type} [PartialOrder L] [OrderTop L]

/-- `ψ ∈ Cell_α` with the slot read in `L` (`CellU.InStratum` through `ι`). -/
def InStratumP (ι : Reading L) (α : L) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => α < ι i.ls.meet
  | .mut m => α < ι m.β

/-- `@ρ ⊐ α` with the slots read in `L` (`Outlives` through `ι`). -/
def OutlivesP (ι : Reading L) (ρ : WRes) (α : L) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → InStratumP ι α ψ

/-- `[α] P` (`box` through `ι`). -/
def boxP (ι : Reading L) (α : L) (P : WProp) : WProp := fun ρ => P ρ ∧ OutlivesP ι ρ α

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ` (`ptoMutS` with `α ⊑ ι b` for `α ⊑ b`). -/
def ptoMutP (ι : Reading L) (l : Loc) (α : L) (ls : List SRec) (P : List SRec → Val → WProp) :
    WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ≤ ι b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

mutual
/-- `𝒱⟦A⟧(ls)δ(v)` at the fragment's value types, lifetimes read in a partial order. -/
def vP (ι : Reading L) : VTy → List SRec → LSubD L → Val → WProp
  | .unit, _, _, v => ⌜v = .unit⌝
  | .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vP ι A ls δ v₁ ⋆ vP ι B ls δ v₂
  | .thunk C, ls, δ, v => fun ρ => ∀ ls', Ext ls ls' ρ → cP ι C ls' δ (forceE C (.val v)) ρ
  | .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP ι A ls δ v'
  | .box a A, ls, δ, v => atLifeP δ a fun α => boxP ι α (vP ι A ls δ v)
  | .mut a A, ls, δ, v =>
      atLifeP δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutP ι ℓ α ls (fun ls₀ => vP ι A ls₀ δ)
  | _, _, _, _ => fun _ => False

/-- `𝒞⟦C⟧(ls)δ(e)` at the fragment's computation types, lifetimes read in a partial order. -/
def cP (ι : Reading L) : CTy → List SRec → LSubD L → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vP ι A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ => ∀ v, (vP ι A ls δ v ─⋆ cP ι C ls δ (.app e (.val v))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α : L, (⌜LtLifeP δ c α⌝ ─⋆ cP ι C ls (δ.extend x α) (.app e (.val .unit))) ρ
  | _, _, _, _ => fun _ => False
end

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧(ls)δ(γ(x))` (`gSepC`). -/
def gSepP (ι : Reading L) (ls : List SRec) (δ : LSubD L) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ => if s.live then vP ι s.ty ls δ v ⋆ gSepP ι ls δ Γ γ else gSepP ι ls δ Γ γ

/-- `𝒢⟦Γ⟧(ls)δ(γ)` (`gDenC`). -/
def gDenP (ι : Reading L) (ls : List SRec) (δ : LSubD L) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepP ι ls δ Γ γ

/-- `Δ; Γ ⊨ e : C` over a partial order (`SemC`). -/
def SemP (ι : Reading L) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ (δ : LSubD L) γ (ls : List SRec) ρ, ModelsP Δ δ → gDenP ι ls δ Γ γ ρ →
    cP (ℍ := ℍ) ι C ls δ (substAll γ e) ρ

end PartialLife

end
