import Core.Chain.Goal791N
import Core.Chain.LendExit835N

/-!
# RQ1 chain tests: locality of a payload, and configuration (a) under a bound-relative freeze

* `vN_above_iff`: a value of a type outliving `@bnd δ = b` reads the world only strictly above
  `b`. It is `vN_outlives` plus `vN_extR` along `LocTy.extR_above`; nothing new is needed.
* `famL_bound`: hence the stored family of a lend at `a ≤ b` whose payload outlives `b` depends on
  the world only above `b`: the snapshot is already bound-relative, extensionally.
* `ExtRB`: `ExtR` with the freeze read at a per-key bound `bd l a` instead of at `a`.
* `extRB_foldTransfer_below`: configuration (a) (`not_extRFoldTransfer`'s, a key `(1, β)` added
  while the island `(0, A)` is folded) passes when `β ≤ bd 0 A`.
* `not_extRB_foldTransfer_above`: it fails when `β` lands above the bound.
-/

noncomputable section

namespace RQ1Chain
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeCtx)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem above_above (Θ : LocTy) {a b : Life} (hab : a ≤ b) : (Θ.above a).above b = Θ.above b := by
  refine LocTy.ext' (fun x y => ?_) ?_
  · simp only [LocTy.above_apply]
    by_cases hby : b < y
    · simp [hby, lt_of_le_of_lt hab hby]
    · simp [hby]
  · simp only [LocTy.above_imm, List.filter_filter]
    congr 1
    funext x
    by_cases hbx : b < x.2
    · simp [hbx, lt_of_le_of_lt hab hbx]
    · simp [hbx]

/-- **Locality**: a value of a type outliving `b` reads the world only above `b`. -/
theorem vN_above_iff {Δ : LifeCtx} {δ : LSub} {bnd : Lifetime.Life} {b : Life}
    (hδ : Δ.Models δ) (hb : bnd.interp δ = some b) {T : VTy} (hO : VOutlives Δ bnd T)
    (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) :
    vN (ℍ := ℍ) T δ Θ n v ρ ↔ vN (ℍ := ℍ) T δ (Θ.above b) n v ρ := by
  constructor
  · intro h
    have hρ := vN_outlives (ℍ := ℍ) hδ hb hO Θ n v ρ h
    exact vN_extR T δ n v ρ (LocTy.extR_above Θ hρ).2 h
  · intro h
    have hρ := vN_outlives (ℍ := ℍ) hδ hb hO _ n v ρ h
    exact vN_extR T δ n v ρ (LocTy.extR_above Θ hρ).1 h

theorem vN_congr_above {Δ : LifeCtx} {δ : LSub} {bnd : Lifetime.Life} {b : Life}
    (hδ : Δ.Models δ) (hb : bnd.interp δ = some b) {T : VTy} (hO : VOutlives Δ bnd T)
    {Θ₁ Θ₂ : LocTy} (h : Θ₁.above b = Θ₂.above b) (n : Nat) (v : Val) (ρ : WRes) :
    vN (ℍ := ℍ) T δ Θ₁ n v ρ ↔ vN (ℍ := ℍ) T δ Θ₂ n v ρ := by
  rw [vN_above_iff hδ hb hO Θ₁, vN_above_iff hδ hb hO Θ₂, h]

/-- **The snapshot is bound-relative already**: a lend at `a ≤ b` of a payload outliving `b`
stores a family that depends on the world only above `b`. -/
theorem famL_bound {Δ : LifeCtx} {δ : LSub} {bnd : Lifetime.Life} {b a : Life}
    (hδ : Δ.Models δ) (hb : bnd.interp δ = some b) {T : VTy} (hO : VOutlives Δ bnd T)
    (hab : a ≤ b) {Θ₁ Θ₂ : LocTy} (h : Θ₁.above b = Θ₂.above b) :
    famL a (fun Θ j u r => vN (ℍ := ℍ) T δ Θ j u r) Θ₁ =
      famL a (fun Θ j u r => vN (ℍ := ℍ) T δ Θ j u r) Θ₂ := by
  funext j u r
  simp only [famL]
  apply propext
  apply vN_congr_above hδ hb hO
  rw [above_above Θ₁ hab, above_above Θ₂ hab, h]

/-! ### Configuration (a) under a bound-relative freeze -/

/-- `ExtR` with the freeze read at the key's bound `bd l a ≥ a`. -/
def ExtRB (bd : Loc → Life → Life) (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  (∀ l a F, Θ l a = some F → CellIn ρ a → Θ' l a = some F ∧ Θ'.above (bd l a) = Θ.above (bd l a)) ∧
    Θ.Keeps Θ' ρ

/-- The borrowed share of configuration (a): `ℓ = 0` lent `mut` at `A`. -/
abbrev shareA (A : Life) : WRes :=
  ResU.single 0 (CellU.mutOf A Val.unit PMap.empty (ResU.inStratum_empty A) (fun _ _ => True) trivial)

theorem cellIn_shareA (A : Life) : CellIn (shareA A) A :=
  ⟨0, _, ResU.single_get_self _ _, by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c,
    by rw [CellU.at_mutOf]⟩

/-- Configuration (a): the lender's world empty, `(1, β)` added while the island `(0, A)` is
folded. At the borrowed share, with the island restored on both sides, the bound-relative freeze
holds when `β` is not above the island's bound. -/
theorem extRB_foldTransfer_below {A β : Life} (bd : Loc → Life → Life) (hβ : β ≤ bd 0 A)
    (hbd : A ≤ bd 0 A) (G : Nat → Val → SPropS Loc Val β) (F : Nat → Val → SPropS Loc Val A) :
    ExtRB bd (LocTy.empty.add 0 A F) ((LocTy.empty.add 1 β G).add 0 A F) (shareA A) := by
  refine ⟨fun l a H hH _ => ?_, fun x hx _ => by simp at hx⟩
  have ha : a = A := by
    by_contra ha; rw [LocTy.add_keep _ _ _ _ ha] at hH; simp at hH
  subst ha
  have hl : l = 0 := by
    by_contra hl; rw [LocTy.add_other _ hl] at hH; simp at hH
  subst hl
  refine ⟨by rw [LocTy.add_self] at hH ⊢; exact hH, ?_⟩
  refine LocTy.ext' (fun x y => ?_) (by simp)
  simp only [LocTy.above_apply]
  by_cases hy : bd 0 a < y
  · have hyA : y ≠ a := ne_of_gt (lt_of_le_of_lt hbd hy)
    have hyβ : y ≠ β := ne_of_gt (lt_of_le_of_lt hβ hy)
    simp [hy, LocTy.add_keep _ _ _ _ hyA, LocTy.add_keep _ _ _ _ hyβ]
  · simp [hy]

/-- **The first break of (a) under the bound-relative freeze**: `β` above the island's bound. -/
theorem not_extRB_foldTransfer_above {A β : Life} (bd : Loc → Life → Life) (hβ : bd 0 A < β)
    (hbd : A ≤ bd 0 A) (G : Nat → Val → SPropS Loc Val β) (F : Nat → Val → SPropS Loc Val A) :
    ¬ ExtRB bd (LocTy.empty.add 0 A F) ((LocTy.empty.add 1 β G).add 0 A F) (shareA A) := by
  intro h
  have hβA : β ≠ A := ne_of_gt (lt_of_le_of_lt hbd hβ)
  have h' := (h.1 0 A F (LocTy.add_self _ _ _ _) (cellIn_shareA A)).2
  have h₁ := congrArg (fun Θ : LocTy => Θ 1 β) h'
  simp only [LocTy.above_apply, if_pos hβ, LocTy.add_keep _ _ _ _ hβA] at h₁
  rw [LocTy.add_self] at h₁
  simp at h₁

end RQ1Chain
