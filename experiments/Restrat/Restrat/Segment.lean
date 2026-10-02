import Restrat.Fixed
import Core.Relation

/-!
# Restrat — the re-stratification corollary for a frozen stack segment

L14.4 (`docs/effects-tr/14-stored-continuations.md`) splits, following the coordinator's
framing, into the parts below.

1. **The extent enters only through `∀'a ⊏ @b`.**  `vDen_all_iff`: `𝒱⟦∀'x ⊏ @b. T⟧_δ` reads the
   extent `α` only as `α ⊏ @bδ` and as `δ['x ↦ α]`.  No definition of `Paper/`, `Support/` or
   `Core/` computes a lifetime (`Restrat.Audit`), so nothing reads `'h = ↓o`.
2. **Instantiation.**  A segment proved under `∀δ ∈ ⟦Δ⟧` (`Core`'s `SemC`) holds at the shifted
   assignment `e∘δ`, which is in `⟦Δ⟧` (`models_mapN_iff`), fixes every outer variable, and puts
   every inner variable below any given point (`restrat_segment`).
3. **The frozen value is fixed.**  A re-stratification is the identity on `Res_c`
   (`Restrat.Fixed`): the external footprint of a frozen segment, and every `own` cell, are
   unchanged, invariants included.

What is not here.  The running state of a segment is not transported: `𝒱⟦Mut @a T⟧` is not
invariant under the move of a cell whose payload type mentions a moved lifetime
(`Restrat.MutCounterexample`), so an internal `mut` cell has to be ghost-ended at the freeze and
re-lent at the resume (D14.4's `Freeze` and `Relend`).  The ghost end itself (L14.4 ingredient
2) is not proved here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Restrat.Segment
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `𝒱⟦∀'x ⊏ @b. T⟧_δ(v)(ρ)` reads the extent `α` only through `α ⊏ @bδ` and `δ['x ↦ α]`. -/
theorem vDen_all_iff (x : LifeVar) (b : BoCa.Lifetime.Life) (T : Ty) (δ : LSub) (v : Val)
    (ρ : WRes) :
    vDen (.all x b T) δ v ρ ↔
      ∀ α : Life, LtLife δ b α → wp (.app (.val v) (.val .unit)) (vDen T (δ.extend x α)) ρ := by
  constructor
  · intro h α hα
    exact h α PMap.empty ρ ⟨rfl, hα⟩ (ResU.comp_empty_right ρ)
  · intro h α ρ₁ ρ₂ ⟨hρ₁, hα⟩ hc
    subst hρ₁
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)]
    exact h α hα

/-- A shift fixes every variable at or above the cut. -/
theorem shift_outer {c : Life} {k : ℕ} {δ : LSub} {x : LifeVar} {n : ℕ}
    (h : δ.find? x = some n) (hout : c ≤ OrderDual.toDual n) :
    (Restrat.LSub.mapN (Restrat.Emb.shift c k).toNat δ).find? x = some n := by
  rw [Restrat.LSub.find?_mapN, h]
  exact congrArg some (congrArg OrderDual.ofDual ((Restrat.Emb.shift c k).fix _ hout))

/-- A shift by `p` moves every variable below the cut to below `p`. -/
theorem shift_inner {c p : Life} {δ : LSub} {x : LifeVar} {n : ℕ}
    (h : δ.find? x = some n) (hin : OrderDual.toDual n < c) :
    ∃ n', (Restrat.LSub.mapN (Restrat.Emb.shift c (OrderDual.ofDual p)).toNat δ).find? x
        = some n' ∧ OrderDual.toDual n' < p := by
  refine ⟨_, by rw [Restrat.LSub.find?_mapN, h]; rfl, ?_⟩
  exact Restrat.Emb.shift_fresh p le_rfl hin

/-- **The re-stratification of a segment proved under `∀δ ∈ ⟦Δ⟧`.**  At the cut `c` and the
current point `p`, the shift `e = shift c p` gives an assignment `e∘δ` that

* is in `⟦Δ⟧`;
* agrees with `δ` at every outer variable;
* puts every inner variable strictly below `p`;
* fixes every resource in `Res_c`;

and the segment's relation holds there, at every typed world, closing substitution and
resource. -/
theorem restrat_segment {Δ : LifeCtx} {Γ : Ctx Core.VTy} {M : Expr} {C : Core.CTy}
    (hS : Core.SemC Δ Γ M C) (c p : Life) {δ : LSub} (hδ : Δ.Models δ) :
    let e := Restrat.Emb.shift c (OrderDual.ofDual p)
    let δ' := Restrat.LSub.mapN e.toNat δ
    Δ.Models δ' ∧
    (∀ x n, δ.find? x = some n → c ≤ OrderDual.toDual n → δ'.find? x = some n) ∧
    (∀ x n, δ.find? x = some n → OrderDual.toDual n < c →
      ∃ n', δ'.find? x = some n' ∧ OrderDual.toDual n' < p) ∧
    (∀ r : WRes, r.InStratum c → e.relRU r = r) ∧
    (∀ γ ls ρ, Core.gDenC ls δ' Γ γ ρ → Core.cC C ls δ' (substAll γ M) ρ) := by
  intro e δ'
  have hδ' : Δ.Models δ' := (e.models_mapN_iff Δ δ).mpr hδ
  exact ⟨hδ', fun x n h hout => shift_outer h hout, fun x n h hin => shift_inner h hin,
    fun r hr => e.relRU_of_inStratum hr, fun γ ls ρ hg => hS δ' γ ls ρ hδ' hg⟩

end Restrat.Segment
