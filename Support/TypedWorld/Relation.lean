import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Statics.Contexts
import Support.TypedWorld.Records
import Support.TypedWorld.World

/-!
# Support — TypedWorld — Relation

`[about ours]`.  The repaired logical relation of `[TR]` §4: `vX`, the `Imm`/`Mut` points-to at a record list, the context relation `gDenX` and the judgment `SemX`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-!
Row 4.9 · `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.
-/
/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ`: a `mut` cell at `b ⊒ α` whose stored predicate is
`P ls₀`, `ls₀` having the members of `ls` strictly longer-lived than `b`; and `P̂ : Val →
SProp_b` — the family `P` lies in `Res_b` at every list.  The last conjunct is `[TR]` p. 4's
`Mut_α ≜ {(β ⊐ α, v, ρ : Res_β, P̂ : Val → SProp_β) | …}`, the type of `P̂`, read of the
family: the paper's `𝒱⟦S⟧δ` is one predicate, ours one per list.
`[about ours: [TR] p. 4's Mut clause, the list stratified at the cell's lifetime]` -/
def ptoMutS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

/-!
Row 4.8 · `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.
-/
/-- `ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ`: an `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload
holds at `ls₀`, the members of `ls` strictly longer-lived than the cell (`@ψ = ⊓β̄`).  The
cell stores no predicate; `ls₀` is fixed by the cell's lifetime, which `Ext` keeps.
`[about ours: [TR] p. 4's Imm clause, the list stratified at the cell's lifetime]` -/
def ptoImmS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P ls₀ u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ s.meet)

/-- `Coh` up to `TyEq`.  `[about ours]` -/
def CohE (rs : List FrameRec) (m : Loc) (S : Ty) (δ : LSub) : Prop :=
  ∃ S₀ δ₀, TyEq S δ S₀ δ₀ ∧ Coh rs m S₀ δ₀

/-!
Row 4.4 · `𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.

Row 4.5 · `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.

Rows 4.8 and 4.9, continued.
-/
/-- `𝒱X full ⟦T⟧(ls)δ(v)`.  `full = true`: the program's relation.  `full = false`: the
observable view an `imm` cell's payload is held at — `⊸`/`∀` positions relaxed to `True`.
`[about ours: [TR] p. 4's Imm clause with its payload read at the observable view, per
[CONF] 415:10 and 415:15; docs/adjudications.md §12.69–§12.72]` -/
def vX (wpX : WpOp) : Bool → Ty → List SRec → LSub → Val → WProp
  | _, .unit, _, _, v => ⌜v = .unit⌝
  | b, .tensor T₁ T₂, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vX wpX b T₁ ls δ v₁ ⋆ vX wpX b T₂ ls δ v₂
  | b, .sum T₁ T₂, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vX wpX b T₁ ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vX wpX b T₂ ls δ v₂)
  | true, .lolli T₁ T₂, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → ∀ v',
        (vX wpX true T₁ ls' δ v' ─⋆
          wpX ls' (.app (.val v) (.val v')) (fun ls'' => vX wpX true T₂ ls'' δ)) ρ
  | false, .lolli _ _, _, _, _ => fun _ => True
  -- `!T`: resource `∅` and `T`'s full relation, in both modes.  `[spec §2]`
  | _, .bang T, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vX wpX true T ls δ v ρ
  | true, .all x c T, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → ∀ α,
        (⌜LtLife δ c α⌝ ─⋆ wpX ls' (.app (.val v) (.val .unit))
          (fun ls'' => vX wpX true T ls'' (δ.extend x α))) ρ
  | false, .all _ _ _, _, _, _ => fun _ => True
  | b, .box a T, ls, δ, v => atLife δ a fun α => box α (vX wpX b T ls δ v)
  | b, .ref T, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vX wpX b T ls δ v'
  | _, .imm a T, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ T δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vX wpX false T ls₀ δ)
  | _, .mut a T, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vX wpX true T ls₀ δ)
  | _, .unk, _, _, _ => emp

/-- The program's relation at the tagged `wp`. -/
abbrev vP : Ty → List SRec → LSub → Val → WProp := vX wpTS true

/-!
Row 4.13 · `𝒢⟦Γ⟧(γ) ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.
-/
/-- `⊛_{x ∈ dom(Γ)} 𝒱X⟦Γ(x)⟧(ls)δ(γ(x))`.  `[about ours]` -/
def gSepX (ls : List SRec) (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vP s.ty ls δ v ⋆ gSepX ls δ Γ γ else gSepX ls δ Γ γ

/-- `𝒢X⟦Γ⟧(ls)δ(γ)`.  `[about ours]` -/
def gDenX (ls : List SRec) (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepX ls δ Γ γ

/-!
Row 4.14 · `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.
-/
/-- `Δ; Γ ⊨ e : T` at the typed world: `[TR]` p. 4's judgment, `∀δ ∈ 𝒟⟦Δ⟧, γ.
𝒢⟦Γ⟧δ(γ) ⊨ ℰ⟦T⟧δ(γ(e))`, read at `𝒱X` and the tagged `wpTS`, at every record list.
`[about ours: [TR] p. 4's judgment at the definitions docs/adjudications.md §12.69–§12.72 repair]` -/
def SemX (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenX ls δ Γ γ ρ →
    wpTS ls (substAll γ e) (fun ls' => vP T ls' δ) ρ

end BoCa.Fig16.LogRel.Typed

end
