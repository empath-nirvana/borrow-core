import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Statics.Contexts

/-!
# [TR] §4 Logical Relation  (physical p. 4)

    𝒱⟦1⟧δ(v)             ≜ ⌜v = ()⌝
    𝒱⟦T₁ ⊗ T₂⟧δ(v)       ≜ ∃ v₁, v₂. ⌜v = (v₁, v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)
    𝒱⟦T₁ ⊕ T₂⟧δ(v)       ≜ (∃ v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃ v₂. ⌜v = inj₂ v₂⌝ ⋆ 𝒱⟦T₂⟧δ(v₂))
    𝒱⟦T₁ ⊸ T₂⟧δ(v)       ≜ ∀ v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)
    𝒱⟦∀ 'a ⊏ @b. T⟧δ(v)  ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())
    𝒱⟦[@a] T⟧δ(v)        ≜ [@aδ] 𝒱⟦T⟧δ(v)
    𝒱⟦Ref T⟧δ(v)         ≜ ∃ ℓ, v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)
    𝒱⟦Imm @a T⟧δ(v)      ≜ ∃ ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ
    𝒱⟦Mut @a T⟧δ(v)      ≜ ∃ ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ
    𝒱⟦Unk⟧δ(v)           ≜ emp
    ℰ⟦T⟧δ(e)             ≜ wp (e) {𝒱⟦T⟧δ}
    𝒟⟦Δ⟧(δ)              ≜ ⌜δ ∈ ⟦Δ⟧⌝
    𝒢⟦Γ⟧(γ)              ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))
    Δ; Γ ⊨ e : T         ≜ !∀ δ, γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))

The literal reading is this file (`vDen`, `eDen`, `gDen`, `SemTy`, over `[TR]`
p. 6's `wp`).  The repaired reading is the typed world in `Support/TypedWorld/`
(`Fig16.LogRel.Typed.vX`, `wpTS`, `gDenX`, `SemX`; `docs/adjudications.md`
§12.69–§12.72).  Rows are numbered as in `Paper/INDEX.md` (*Definitions*); tags
as in `CLAUDE.md`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.6 · `𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)` · [TR] p. 4 · `[encoding]`

`@aδ` is partial; in argument position it is wrapped as `∃α. @aδ = α ∧ …` (`atLife`, row 4.15).

### 4.15 · — no printed counterpart — · [TR] p. 4 · `[repair]`

`atLife` (argument position) and `LtLife` (bound position): the meaning of a clause at an undefined `@aδ` (`docs/adjudications.md` L3, C14).
-/
/-- `@aδ` as a connective's ARGUMENT. -/
def atLife (δ : LSub) (a : Lifetime.Life) (F : Life → SPropU BoCa.Loc BoCa.Val) :
    WProp :=
  fun ρ => ∃ α, a.interp δ = some α ∧ F α ρ

/-!
### 4.12 · `𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝` · [TR] p. 4, with ⟦Δ⟧ from p. 3 · `[encoding]`

Inherits row 2.52's encoding.
-/
def dDen (Δ : LifeCtx) (δ : LSub) : WProp := ⌜Δ.Models δ⌝

end BoCa.Fig16.LogRel

namespace BoCa
open BoCa.Lifetime

/-!
### 4.13 · `𝒢⟦Γ⟧(γ) ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` · [TR] p. 4 · `[repair]`

`dom(γ)` for the printed `dom(δ)`, and `δ` taken as a parameter as in row 4.14.
-/
/-- `dom(Γ) ⊆ dom(γ)` with `dom(Γ)` the live slots (L4): slots of `Γ` past the
    end of `γ` must be consumed. -/
def Ctx.LiveWithin {τ σ : Type} : Ctx τ → List σ → Prop
  | [],     _      => True
  | s :: Γ, []     => ¬ s.live ∧ Ctx.LiveWithin Γ ([] : List σ)
  | _ :: Γ, _ :: γ => Ctx.LiveWithin Γ γ

@[simp] theorem Ctx.liveWithin_nil {τ σ : Type} (γ : List σ) :
    Ctx.LiveWithin ([] : Ctx τ) γ := by cases γ <;> trivial

@[simp] theorem Ctx.liveWithin_cons {τ σ : Type} (s : Slot τ) (Γ : Ctx τ)
    (v : σ) (γ : List σ) : Ctx.LiveWithin (s :: Γ) (v :: γ) ↔ Ctx.LiveWithin Γ γ :=
  Iff.rfl

@[simp] theorem Ctx.liveWithin_cons_nil {τ σ : Type} (s : Slot τ) (Γ : Ctx τ) :
    Ctx.LiveWithin (s :: Γ) ([] : List σ) ↔ (¬ s.live ∧ Ctx.LiveWithin Γ ([] : List σ)) :=
  Iff.rfl

end BoCa

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `α ⊏ @bδ` as a proposition about the partial `@bδ`. -/
def LtLife (δ : LSub) (b : Lifetime.Life) (α : Life) : Prop :=
  ∃ β, b.interp δ = some β ∧ α ⊏ β

/-!
### 4.1 · `𝒱⟦1⟧δ(v) ≜ ⌜v = ()⌝` · [TR] p. 4 · `[as printed]`
-/
/-- `𝒱⟦T⟧δ(v)` (`[TR]` p. 4). -/
noncomputable def vDen : Ty → LSub → Val → WProp
  -- 𝒱⟦1⟧δ(v) ≜ ⌜v = ()⌝
  | .unit, _, v => ⌜v = .unit⌝
  -- 𝒱⟦T₁ ⊗ T₂⟧δ(v) ≜ ∃v₁,v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)
  | .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ =>
        ⌜v = .pair v₁ v₂⌝ ⋆ vDen T₁ δ v₁ ⋆ vDen T₂ δ v₂
  -- 𝒱⟦T₁ ⊕ T₂⟧δ(v) ≜ (∃v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃v₂. …)
  | .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vDen T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vDen T₂ δ v₂)
  -- 𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)
  | .lolli T₁ T₂, δ, v =>
      all fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)
  | .fn T₁ T₂, δ, v =>
      BoLo.and (all fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ))
        (fun ρ => ρ = PMap.empty)
  -- 𝒱⟦∀'x ⊏ @b. T⟧δ(v) ≜ ∀α. ⌜α ⊏ @bδ⌝ ─⋆ ℰ⟦T⟧_{δ['x↦α]}(v ())
  | .all x b T, δ, v =>
      all fun α =>
        ⌜LtLife δ b α⌝ ─⋆ wp (.app (.val v) (.val .unit)) (vDen T (δ.extend x α))
  -- 𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)
  | .box a T, δ, v => atLife δ a fun α => box α (vDen T δ v)
  -- 𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)
  | .ref T, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vDen T δ v'
  -- 𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ
  | .imm a T, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vDen T δ)
  -- 𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ
  | .mut a T, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoMut ℓ α (vDen T δ)
  -- 𝒱⟦Unk⟧δ(v) ≜ emp
  | .unk, _, _ => emp

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
variable (δ : LSub) (v : Val)

@[simp] theorem vDen_unit : vDen .unit δ v = ⌜v = .unit⌝ := rfl

/-!
### 4.10 · `𝒱⟦Unk⟧δ(v) ≜ emp` · [TR] p. 4 · `[as printed]`
-/
@[simp] theorem vDen_unk : vDen .unk δ v = emp := rfl

/-!
### 4.2 · `𝒱⟦T₁ ⊗ T₂⟧δ(v) ≜ ∃v₁,v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)` · [TR] p. 4 · `[as printed]`
-/
theorem vDen_tensor (T₁ T₂ : Ty) :
    vDen (.tensor T₁ T₂) δ v =
      ex (fun v₁ => ex fun v₂ =>
        ⌜v = .pair v₁ v₂⌝ ⋆ vDen T₁ δ v₁ ⋆ vDen T₂ δ v₂) := rfl

/-!
### 4.3 · `𝒱⟦T₁ ⊕ T₂⟧δ(v) ≜ (∃v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃v₂. ⌜v = inj₂ v₂⌝ ⋆ 𝒱⟦T₂⟧δ(v₂))` · [TR] p. 4 · `[as printed]`
-/
theorem vDen_sum (T₁ T₂ : Ty) :
    vDen (.sum T₁ T₂) δ v =
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vDen T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vDen T₂ δ v₂) := rfl

/-!
### 4.4 · `𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)` · [TR] p. 4 · `[repair]`

`ℰ⟦T₂⟧δ` inlined as its `wp`.  At the typed world the clause is Kripke over the record list (`Typed.vX`, `docs/adjudications.md` §12.72).
-/
theorem vDen_lolli (T₁ T₂ : Ty) :
    vDen (.lolli T₁ T₂) δ v =
      all (fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)) := rfl

/-- `𝒱⟦fn T₁ T₂⟧δ(v) ≜ 𝒱⟦T₁ ⊸ T₂⟧δ(v) ∧ ρ = ∅`: closed code holds no resource.  `[spec §2]` -/
theorem vDen_fn (T₁ T₂ : Ty) :
    vDen (.fn T₁ T₂) δ v =
      BoLo.and (all (fun v' => vDen T₁ δ v' ─⋆ wp (.app (.val v) (.val v')) (vDen T₂ δ)))
        (fun ρ => ρ = PMap.empty) := rfl

/-!
### 4.5 · `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` · [TR] p. 4 · `[repair]`

`ℰ⟦T⟧` at `δ['a ↦ α]`, as [CONF] p. 415:12 prints it; the bounded `∀` is an unbounded one guarded by `⌜LtLife δ b α⌝`.  At the typed world, Kripke as row 4.4 (§12.72).
-/
theorem vDen_all (x : LifeVar) (b : Lifetime.Life) (T : Ty) :
    vDen (.all x b T) δ v =
      all (fun α =>
        ⌜LtLife δ b α⌝ ─⋆
          wp (.app (.val v) (.val .unit)) (vDen T (δ.extend x α))) := rfl

theorem vDen_box (a : Lifetime.Life) (T : Ty) :
    vDen (.box a T) δ v = atLife δ a (fun α => box α (vDen T δ v)) := rfl

/-!
### 4.7 · `𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)` · [TR] p. 4 · `[as printed]`
-/
theorem vDen_ref (T : Ty) :
    vDen (.ref T) δ v =
      ex (fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vDen T δ v') := rfl

/-!
### 4.8 · `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

The `∃α` of `atLife` is hoisted outside `∃ℓ`.  At the typed world: the payload at its observable view (§12.69), stratified by the record list (§12.70), with the coherence conjunct `CohE` (§12.71).
-/
theorem vDen_imm (a : Lifetime.Life) (T : Ty) :
    vDen (.imm a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vDen T δ)) := rfl

/-!
### 4.9 · `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` · [TR] p. 4 · `[repair]`

The cell stores the predicate (Fig. 16 row 5); row 4.17 shows the clause empty at `Mut @a (Imm @b 1)`.  At the typed world the payload is stratified by the record list (§12.70).
-/
theorem vDen_mut (a : Lifetime.Life) (T : Ty) :
    vDen (.mut a T) δ v =
      atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoMut ℓ α (vDen T δ)) := rfl

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.11 · `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` · [TR] p. 4 · `[repair]`

`wp` runs `BoLo.Steps`, which adds the frames `K; e` and `injᵢ K` (`docs/adjudications.md` §12.42, D6).  At the typed world `ℰ` is `Typed.wpTS` (row 5.33, §12.72).
-/
/-- `ℰ⟦T⟧δ(e)` (`[TR]` p. 4). -/
noncomputable def eDen (δ : LSub) (T : Ty) (e : Expr) : WProp := wp e (vDen T δ)

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`, over the live slots (L4). -/
noncomputable def gSep (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vDen s.ty δ v ⋆ gSep δ Γ γ else gSep δ Γ γ

/-- `𝒢⟦Γ⟧δ(γ)` (`[TR]` p. 4, row 4.13). -/
noncomputable def gDen (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSep δ Γ γ

/-!
### 4.14 · `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` · [TR] p. 4 · `[repair]`

`γ(e)` is the parallel substitution `substAll` (L5).  At the typed world: `Typed.SemX` (§12.69–§12.72).
-/
/-- `Δ; Γ ⊨ e : T` (`[TR]` p. 4). -/
noncomputable def SemTy (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : WProp :=
  !ₛ(all fun δ => all fun γ =>
      dDen Δ δ ─⋆ (gDen δ Γ γ ─⋆ eDen δ T (substAll γ e)))

/-!
### 4.16 · — no printed counterpart — · [TR] p. 4 · `[repair]`

Fig. 16 row 5's `P̂ : Val → SProp_β` as a predicate, since `SProp_β` is a subset of `SProp` on this carrier.
-/
/-- `P̂ : Val → SProp_β`. -/
def Supported (β : Life) (P : Val → WProp) : Prop := ∀ v ρ, P v ρ → ρ.InStratum β

/-- `Supported` is membership in the image of `SPropS.toU` at each value. -/
theorem supported_iff (β : Life) (P : Val → WProp) :
    Supported β P ↔ ∀ v, ∃ Q : SPropS BoCa.Loc BoCa.Val β, SPropS.toU Q = P v := by
  constructor
  · exact fun h v => (SPropS.toU_range β (P v)).mpr (fun ρ => h v ρ)
  · exact fun h v ρ hρ => (SPropS.toU_range β (P v)).mp (h v) ρ hρ

end BoCa.Fig16.LogRel

end
