import Core.Chain.Kappa835N

/-!
# The public order on the per-lend world, at a lifetime floor  `[spec §19, §27]`

`docs/new-core/scope-835-public.md`. Dreyer, Neis & Birkedal (JFP 2012 §7.1, Fig. 5/6) relate
continuations only at public future worlds (`K⟦τ⟧` along `⊒pub`), and §7.2 (Lemma 10) shows that
once continuations are values, the order a continuation is owed along must be the order values are
monotone along. Here `κ` is a value of `U(…)`, so the stop must owe the handled continuation along
`U`'s order. This file states that order and checks the two things the mapping asks of it.

`LocTy.ExtP lo Θ Θ′ ρ` is `ExtR` at `ρ` together with two clauses read at the floor `lo`, the
lifetime below which every lend taken from here on lies:

* every key strictly longer-lived than `lo` is the same in `Θ′` (nothing added above `lo`, nothing
  removed above it);
* the `imm` records lent strictly above `lo` are the same list.

Moves below the floor are public: a lend at `α ≤ lo` (`LocTy.extP_add`), an `imm` record at
`α ≤ lo` (`LocTy.extP_addImm`).

**The fold.** Under a live `mut` lend at `A`, the lender's share holds the lent cell folded. Read at
the floor `A`, `ExtP` at the lender's share gives `ExtR` at the borrowed continuation's share from
`Θ + (ℓ, A)` to `Θ′ + (ℓ, A)` (`LocTy.ExtP.fold`, `extPFoldTransfer`). `not_extRFoldTransfer`'s
configuration adds a key above `A`, which is not a public move at the floor `A`
(`not_extP_foldConfig`).

**The two `κ` configurations** (`Kappa835N.lean`). Read along `ExtP`, the stop's obligation reaches
both failing points: the world with the key `(ℓ′, α)` is a public extension of the empty world at
any floor above `α` (`extP_world`), and the view at `ℓ′` is any view consistent with the share. So
the stuck `κ = ()` does not meet the obligation (`not_kapRelP_world`, `not_kapRelP_view`), while it
meets `KapRelN` (`kapRelN_not_kapRelP`). That is the gap the relation's stop must close.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-! ### The order -/

/-- **The public order at the floor `lo`**: `ExtR` at `ρ`, every key strictly longer-lived than
`lo` unchanged, and the `imm` records lent strictly above `lo` unchanged. -/
def LocTy.ExtP (lo : Life) (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  Θ.ExtR Θ' ρ ∧ (∀ l b, lo < b → Θ' l b = Θ l b) ∧
    Θ'.imm.filter (fun x => decide (lo < x.2)) = Θ.imm.filter (fun x => decide (lo < x.2))

theorem LocTy.ExtP.extR {lo : Life} {Θ Θ' : LocTy} {ρ : WRes} (h : Θ.ExtP lo Θ' ρ) :
    Θ.ExtR Θ' ρ := h.1

theorem LocTy.extP_refl (lo : Life) (Θ : LocTy) (ρ : WRes) : Θ.ExtP lo Θ ρ :=
  ⟨LocTy.extR_refl Θ ρ, fun _ _ _ => rfl, rfl⟩

theorem LocTy.ExtP.trans {lo : Life} {Θ Θ' Θ'' : LocTy} {ρ : WRes} (h₁ : Θ.ExtP lo Θ' ρ)
    (h₂ : Θ'.ExtP lo Θ'' ρ) : Θ.ExtP lo Θ'' ρ :=
  ⟨h₁.1.trans h₂.1, fun l b hb => (h₂.2.1 l b hb).trans (h₁.2.1 l b hb), h₂.2.2.trans h₁.2.2⟩

theorem filter_of_filter {α : Type*} {p q : α → Bool} (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, l.filter p = (l.filter q).filter p
  | [] => rfl
  | x :: l => by
    by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hq]
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hp, filter_of_filter h l]
      · rw [List.filter_cons_of_neg hp, List.filter_cons_of_neg hp, filter_of_filter h l]
    · have hp : ¬ p x = true := fun e => hq (h x e)
      rw [List.filter_cons_of_neg hq, List.filter_cons_of_neg hp, filter_of_filter h l]

/-- A higher floor asks less. -/
theorem LocTy.ExtP.mono {lo lo' : Life} (hlo : lo ≤ lo') {Θ Θ' : LocTy} {ρ : WRes}
    (h : Θ.ExtP lo Θ' ρ) : Θ.ExtP lo' Θ' ρ := by
  refine ⟨h.1, fun l b hb => h.2.1 l b (lt_of_le_of_lt hlo hb), ?_⟩
  have hpq : ∀ x : SRec, decide (lo' < x.2) = true → decide (lo < x.2) = true := fun x hx => by
    simp only [decide_eq_true_eq] at hx ⊢
    exact lt_of_le_of_lt hlo hx
  rw [filter_of_filter hpq Θ'.imm, filter_of_filter hpq Θ.imm, h.2.2]

/-- At the floor and above it, the part of the world above is unchanged. -/
theorem LocTy.ExtP.above_eq {lo a : Life} {Θ Θ' : LocTy} {ρ : WRes} (h : Θ.ExtP lo Θ' ρ)
    (ha : lo ≤ a) : Θ'.above a = Θ.above a := by
  refine LocTy.ext' (fun x b => ?_) ?_
  · simp only [LocTy.above_apply]
    by_cases hab : a < b
    · rw [if_pos hab, if_pos hab, h.2.1 x b (lt_of_le_of_lt ha hab)]
    · rw [if_neg hab, if_neg hab]
  · simp only [LocTy.above_imm]
    have hpq : ∀ x : SRec, decide (a < x.2) = true → decide (lo < x.2) = true := fun x hx => by
      simp only [decide_eq_true_eq] at hx ⊢
      exact lt_of_le_of_lt ha hx
    rw [filter_of_filter hpq Θ'.imm, filter_of_filter hpq Θ.imm, h.2.2]

/-! ### Public moves -/

/-- **A lend below the floor is public.** -/
theorem LocTy.extP_add {Θ : LocTy} {α lo : Life} (hf : Θ.Fresh α) (hα : α ≤ lo) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) (ρ : WRes) : Θ.ExtP lo (Θ.add l α F) ρ :=
  ⟨(LocTy.extA_add hf l F).extR ρ,
    fun x _ hb => LocTy.add_keep Θ l F x (ne_of_gt (lt_of_le_of_lt hα hb)), rfl⟩

/-- **An `imm` record lent below the floor is public**, at a resource in its lend's stratum. -/
theorem LocTy.extP_addImm (Θ : LocTy) (r : FrameRec) {α lo : Life} (hα : α ≤ lo) {ρ : WRes}
    (hρ : ρ.InStratum α) : Θ.ExtP lo (Θ.addImm (r, α)) ρ := by
  refine ⟨LocTy.extR_addImm Θ r hρ, fun _ _ _ => rfl, ?_⟩
  simp only [LocTy.addImm_imm]
  rw [List.filter_cons_of_neg (by simpa using hα)]

/-- **A lend's exit is public at the lend's own floor**: at a resource in the lend's stratum, the
world without the key is a public extension of the world with it, read at the floor the lend set.
Read at a floor above the lend it is not (the key at `α` is above that floor's keys only when
`lo < α`, and `ExtP` keeps every key strictly above the floor). -/
theorem LocTy.extP_of_add (Θ : LocTy) (l : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α)
    {ρ : WRes} (hρ : ρ.InStratum α) : (Θ.add l α F).ExtP α Θ ρ :=
  ⟨LocTy.extR_of_add Θ l F hρ, fun x _ hb => (LocTy.add_keep Θ l F x (ne_of_gt hb)).symm, rfl⟩

/-! ### The fold -/

/-- **`ExtP` at the floor `A` is carried across a Mut Frame's fold at `A`.** The lender's share
`ρo` and the borrowed continuation's share `ρi` agree on borrow cells shorter-lived than `A` (the
fold changes only the cell lent at `A` and its content, which lies in `Res_A`). Read at the floor
`A`, a public extension of the lender's world is an `ExtR` extension of the lend's world, at the
borrowed share. -/
theorem LocTy.ExtP.fold {Θ Θ' : LocTy} {A : Life} {ρo ρi : WRes} (h : Θ.ExtP A Θ' ρo)
    (hf : Θ.Fresh A) (hI : ∀ x ∈ Θ.imm, x.2 ≠ A)
    (hc : ∀ a, a < A → CellIn ρi a → CellIn ρo a) (l : Loc) (F : Nat → Val → SPropS Loc Val A) :
    (Θ.add l A F).ExtR (Θ'.add l A F) ρi := by
  refine ⟨fun l₀ a G hG _ => ?_, fun x hx hcx => ?_⟩
  · by_cases ha : a = A
    · subst ha
      by_cases hl : l₀ = l
      · subst hl
        rw [LocTy.add_self] at hG
        refine ⟨by rw [LocTy.add_self]; exact hG, ?_⟩
        rw [LocTy.above_add _ _ (lt_irrefl a), LocTy.above_add _ _ (lt_irrefl a)]
        exact h.above_eq le_rfl
      · rw [LocTy.add_other Θ hl] at hG
        exact absurd (hf l₀ a (by rw [hG]; simp)) (lt_irrefl _)
    · rw [LocTy.add_keep Θ l F l₀ ha] at hG
      have hAa : A < a := hf l₀ a (by rw [hG]; simp)
      refine ⟨by rw [LocTy.add_keep Θ' l F l₀ ha, h.2.1 l₀ a hAa]; exact hG, ?_⟩
      rw [LocTy.above_add _ _ (not_lt_of_gt hAa), LocTy.above_add _ _ (not_lt_of_gt hAa)]
      exact h.above_eq (le_of_lt hAa)
  · change x ∈ Θ.imm at hx
    change x ∈ Θ'.imm
    rcases lt_or_ge A x.2 with hA | hA
    · have hm : x ∈ Θ.imm.filter (fun x => decide (A < x.2)) :=
        List.mem_filter.mpr ⟨hx, by simpa using hA⟩
      rw [← h.2.2] at hm
      exact (List.mem_filter.mp hm).1
    · have hlt : x.2 < A := lt_of_le_of_ne hA (hI x hx)
      exact h.1.2 x hx (hc _ hlt hcx)

/-- The configuration of `not_extRFoldTransfer`, read along `ExtP` at the lend's lifetime. -/
def ExtPFoldTransfer : Prop :=
  ∀ (Θ Θ' : LocTy) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (v : Val),
    Θ.Fresh A → (∀ x ∈ Θ.imm, x.2 ≠ A) → Θ.ExtP A Θ' (ResU.single l (CellU.ownOf v)) →
    (Θ.add l A F).ExtR (Θ'.add l A F)
      (ResU.single l (CellU.mutOf A v PMap.empty (ResU.inStratum_empty A) (fun _ _ => True) trivial))

/-- **`ExtP` is carried across the fold** where `ExtR` is not (`not_extRFoldTransfer`). -/
theorem extPFoldTransfer : ExtPFoldTransfer := by
  intro Θ Θ' l A F v hf hI h
  refine h.fold hf hI (fun a ha hc => ?_) l F
  obtain ⟨m, ψ, e, -, hle⟩ := hc
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at e
    cases Option.some.inj e
    rw [CellU.at_mutOf] at hle
    exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl _)
  · rw [ResU.single_get_ne _ hm] at e
    cases e

/-- **The key added above the lend is not a public move at the lend's floor**:
`not_extRFoldTransfer`'s world `∅ + (1, β)`, `A < β`. -/
theorem not_extP_foldConfig {A β : Life} (hAβ : A < β) (G : Nat → Val → SPropS Loc Val β)
    (ρ : WRes) : ¬ LocTy.empty.ExtP A (LocTy.empty.add 1 β G) ρ := by
  intro h
  have := h.2.1 1 β hAβ
  rw [LocTy.add_self] at this
  simp [LocTy.empty] at this

namespace Public835N
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Lifetime (LSub LifeVar)

/-! ### The stop's obligation along `ExtP` -/

/-- **The handled continuation owed along the public order** (DNB's `K⟦τ⟧`, read at `U`): at
every public extension of the stop's world at the floor `lo`, every view consistent with the
share and every record list, `κ` is in `𝒞⟦C⟧`. -/
def KapRelP (lo : Life) (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, Θ.ExtP lo Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls,
    cN₀ (ℍ := ℍ) C δ Θ' c n ls (forceE C κ.1) ρ

/-- **The world with the key `(ℓ′, α)` is a public extension of the empty world** at every floor
the key is below. -/
theorem extP_world (x : LifeVar) (δ : LSub) {α lo : Life} (hα : α ≤ lo) (l' : Loc) (ρ : WRes) :
    LocTy.empty.ExtP lo (Θ₁ (ℍ := ℍ) x δ α l') ρ :=
  LocTy.extP_add (fun _ _ h => absurd rfl h) hα l' _ ρ

/-- Above the key, the same world is a private move. -/
theorem not_extP_world (x : LifeVar) (δ : LSub) {α lo : Life} (hlo : lo < α) (l' : Loc)
    (ρ : WRes) : ¬ LocTy.empty.ExtP lo (Θ₁ (ℍ := ℍ) x δ α l') ρ := by
  intro h
  have := h.2.1 l' α hlo
  rw [LocTy.add_self] at this
  simp [LocTy.empty] at this

/-- **The world configuration is excluded by the public reading**: the stuck `κ = ()` is not owed
along `ExtP` at the empty world, at any floor above the key. -/
theorem not_kapRelP_world (x : LifeVar) (δ : LSub) {N α b lo : Life} (hNα : N < α) (hα : α ≤ lo)
    {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some α) :
    ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x α) LocTy.empty 1 Val.unit (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ (extP_world x _ hα l' _) (Θ₁_ok x _ hNα l') c
    (consistentX_single_mut (consistentX_empty c) hcm) [])

/-- **The view configuration is excluded by the public reading**: at the world with the key, the
obligation reaches the view that puts `ℓ′` at `α`. -/
theorem not_kapRelP_view (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) (lo : Life)
    {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some α) :
    ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') 1 Val.unit
      (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ (LocTy.extP_refl _ _ _) (Θ₁_ok x _ hNα l') c
    (consistentX_single_mut (consistentX_empty c) hcm) [])

/-- **`KapRelN` does not give the public reading**: at the empty world the stuck `κ = ()` meets
`KapRelN` (`kapRelN_world`) and fails `KapRelP` at every floor above the key. The stop of a run at
one location typing owes less than the public reading asks. -/
theorem kapRelN_not_kapRelP (x : LifeVar) (δ : LSub) {N α b lo : Life} (hNα : N < α)
    (hα : α ≤ lo) {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some α) :
    KapRelN (ℍ := ℍ) (LocTy.empty.view c)
        (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α) LocTy.empty c))
        (fun k _ v ρ => retN₀ (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α) LocTy.empty k v ρ)
        (entN .lin (bMut x) (fun k v ρ => vN₀ (ℍ := ℍ) .unit (δ.extend x α) LocTy.empty k v ρ)
          (fun k v ρ => vN₀ (ℍ := ℍ) (bMut x) (δ.extend x α) LocTy.empty k v ρ ∧ ConsistentX c ρ)
          (finN₀ (ℍ := ℍ) (.ret .unit) (δ.extend x α) LocTy.empty c))
        none 2 [] Val.unit (ρb m b) ∧
      ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x α) LocTy.empty 1 Val.unit (ρb m b) :=
  ⟨kapRelN_world x _ c [], not_kapRelP_world x δ hNα hα hml c hcm hcl⟩

end Public835N

end BoCa.Fig16.LogRel.Core.Chain.SI

end
