import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Statics.Contexts
import CBPVWorld.Types
import CBPVWorld.Records
import CBPVWorld.World

/-!
# CBPVWorld — Relation

The mode-indexed CBPV relation over the typed world whose records are typed at `VTy`.

`vC b A` interprets value types and `cC C` computation types, over the tagged `wpTS`: the
Kripke quantifier over `Ext` sits at `U` only, `wpTS` at `F` only.  `b = false` is the observable
view an `Imm` payload is held at, with `U` relaxed to `True`.  The resource clauses are the
typed world's (`ptoOwn`, `ptoImmS`, `ptoMutS`, `atLife`/`box`, `ρ = ∅` at `!`, `emp` at `Unk`),
and the `Imm` clause reads the coherence `CohE` at the payload type itself.

A thunk of `F A` is `λ_. M`, forced by applying it to `()`; a thunk of any other computation
type is the λ-value that computation is, forced by using it as it stands (`forceE`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ`: a `mut` cell at `b ⊒ α` whose stored predicate is `P ls₀`, `ls₀`
having the members of `ls` strictly longer-lived than `b`; and `P` lies in `Res_b` at every
list. -/
def ptoMutS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ`: an `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload holds
at `ls₀`, the members of `ls` strictly longer-lived than the cell. -/
def ptoImmS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P ls₀ u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ s.meet)

/-- `Coh` up to `TyEq`. -/
def CohE (rs : List FrameRec) (m : Loc) (S : VTy) (δ : LSub) : Prop :=
  ∃ S₀ δ₀, TyEq S δ S₀ δ₀ ∧ Coh rs m S₀ δ₀

/-- `force`, at the computation type forced.  A thunk of `F A` is `λ_. M` and is forced by
applying it to `()`; a thunk of any other computation type is the λ-value that computation
already is, and is forced by using it as it stands. -/
def forceE : CTy → Expr → Expr
  | .ret _, e => .app e (.val .unit)
  | _, e => e

mutual
/-- `𝒱⟦A⟧(ls)δ(v)`.  `full = true`: the program's relation.  `full = false`: the observable
view an `Imm` payload is held at, with `U` positions relaxed to `True`. -/
def vC : Bool → VTy → List SRec → LSub → Val → WProp
  | _, .unit, _, _, v => ⌜v = .unit⌝
  | b, .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vC b A ls δ v₁ ⋆ vC b B ls δ v₂
  | _, .zero, _, _, _ => fun _ => False
  | b, .sum A B, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vC b A ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vC b B ls δ v₂)
  | true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → cC C ls' δ (forceE C (.val v)) ρ
  | false, .thunk _, _, _, _ => fun _ => True
  | _, .bang A, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vC true A ls δ v ρ
  | b, .box a A, ls, δ, v => atLife δ a fun α => box α (vC b A ls δ v)
  | b, .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vC b A ls δ v'
  | _, .imm a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ A δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vC false A ls₀ δ)
  | _, .mut a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vC true A ls₀ δ)
  | _, .unk, _, _, _ => emp
/-- `𝒞⟦C⟧(ls)δ(e)`, curried on the connective. -/
def cC : CTy → List SRec → LSub → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vC true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v, (vC true A ls δ v ─⋆ cC C ls δ (.app e (.val v))) ρ
  | .amp C D, ls, δ, e => fun ρ =>
      cC C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cC D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cC C ls (δ.extend x α) (.app e (.val .unit))) ρ
end

/-- The program's relation. -/
abbrev vP : VTy → List SRec → LSub → Val → WProp := vC true

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧(ls)δ(γ(x))`. -/
def gSepC (ls : List SRec) (δ : LSub) : Ctx VTy → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vC true s.ty ls δ v ⋆ gSepC ls δ Γ γ else gSepC ls δ Γ γ

/-- `𝒢⟦Γ⟧(ls)δ(γ)`. -/
def gDenC (ls : List SRec) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepC ls δ Γ γ

/-- `Δ; Γ ⊨ e : C`, at every record list. -/
def SemC (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenC ls δ Γ γ ρ → cC C ls δ (substAll γ e) ρ

/-- `Δ; Γ ⊨ V : A` for a value: `return V` at `F A`. -/
abbrev SemV (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy) : Prop := SemC Δ Γ e (.ret A)

/-- `!Γ`: every live slot is at a `!` type. -/
def Persistent (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → ∃ A, s.ty = .bang A

end BoCa.Fig16.LogRel.CBPVWorld

end
