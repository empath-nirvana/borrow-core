import Support.Model.Tree.Port.Strata

/-!
# `↓α` read as a stratum below `α`, over the tree-stratified carrier

Written by hand, not generated. `↓α` (row 5.12) is read as the printed proofs read it: a
stratum `D` strictly below every member of `α` such that a lifetime strictly above `D` is at or
above every member (`WCactus.DownOf`); a covering child is one (`WCactus.downOf_covers`). With it,
the walk and composition strata of `Support/Model/Outlives.lean` that read `↓α`, over `CellUT K`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `↓α` as the printed proofs read it (`Life.down_sqsubset`, `Life.le_of_down_lt`): a stratum
`D` strictly below every member of `α`, such that a lifetime strictly above `D` is at or above
every member of `α`. -/
def WCactus.DownOf (K : WCactus) (D A : TSet) : Prop :=
  K.Above D A ∧ ∀ y, (∀ x ∈ D.set, K.lt x y) → ∀ a ∈ A.set, K.le a y

/-- A covering child of `a` is `↓a` (`Cactus.Covers`, row 5.12 in a tree). -/
theorem WCactus.downOf_covers {K : WCactus} {c a : Life} (h : K.Covers c a) :
    K.DownOf (TSet.single c) (TSet.single a) := by
  refine ⟨fun x hx y hy => ?_, fun y hy x hx => ?_⟩
  · simp only [TSet.single_set, Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact h.1
  · simp only [TSet.single_set, Finset.mem_singleton] at hx
    subst hx
    exact h.le_of_lt (hy c (Finset.mem_singleton_self c))

/-- **At the chain, the printed `↓a` is a `DownOf` of `a`**: the hypothesis `hD` that 6.27,
6.52 and 6.59 carry is discharged there by the printed `↓a` (row 5.12, `a + 1`). -/
theorem WCactus.chain_downOf (a : Life) :
    WCactus.chain.DownOf (TSet.single (Life.down a)) (TSet.single a) :=
  WCactus.downOf_covers (K := WCactus.chain) (Cactus.chainC_covers_down a)

/-- A cell in `Res_D`, `D = ↓α`, has its witness in `Res_α`. -/
theorem CellUT.wit_inStratum_of_down {ψ : CellUT Loc Val K} {D α : TSet} (hD : K.DownOf D α)
    (h : ψ.InStratum D) : ψ.wit.InStratum α := by
  have key : ∀ (t : TSet), K.Above D t → ∀ x ∈ α.set, ∃ y ∈ t.set, K.le x y := by
    intro t ht x hx
    obtain ⟨y, hy⟩ := t.ne
    exact ⟨y, hy, hD.2 y (fun d hd => ht d hd y hy) x hx⟩
  cases ψ with
  | own v => intro l χ e; exact absurd e (by simp [CellUT.wit])
  | imm i => exact ResUT.InStratum.mono (key _ h) (CellUT.wit_inStratum_imm (i := i))
  | «mut» m => exact ResUT.InStratum.mono (key _ h) (CellUT.wit_inStratum_mut (m := m))

/-- `BoLo.flat_inStratum_inv` at one location. -/
theorem ResUT.flat_inStratum_inv_at {ρ σ : ResUT BoCa.Loc BoCa.Val K} {α : TSet}
    (h : ResUT.Flat ρ σ) {l : BoCa.Loc}
    (hσ : ∀ φ, σ.get l = some φ → φ.InStratum α)
    {ψ : CellUT BoCa.Loc BoCa.Val K} (hl : ρ.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, hχ, hkχ, hle⟩ := BoLo.agW_get_at ha hl hk
    have hσl : σ.get l = some χ :=
      ResUT.CompS.get_right_of_immFree hc (ExST.immFree he) hχ
    exact hle α (hσ χ hσl)
  · exact hσ ψ (ResUT.CompS.get_left_of_ne_imm hc (ExST.get_of_ne_imm he hl hk) hk).2

/-- `Res_α` is inherited by a `●`-factor. -/
theorem ResUT.CompS.inStratum_left {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompS ρ₁ ρ₂ ρ)
    {α : TSet} (hρ : ρ.InStratum α) : ρ₁.InStratum α := by
  intro l ψ e₁
  rcases ResUT.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ l _ f
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    cases Option.some.inj f₁
    exact ((CellUT.CompS.inStratum hC α).mp (hρ l _ f)).1

theorem ResUT.CompS.inStratum_right {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompS ρ₁ ρ₂ ρ)
    {α : TSet} (hρ : ρ.InStratum α) : ρ₂.InStratum α :=
  ResUT.CompS.inStratum_left (ResUT.CompS.comm h) hρ

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `BoLo.inStratum_comp` at one location. -/
theorem ResUT.inStratum_comp_at {α : TSet}
    {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α)
    {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    (h₁ : ∀ φ, ρ₁.get l = some φ → φ.InStratum α)
    (h₂ : ∀ φ, ρ₂.get l = some φ → φ.InStratum α)
    {ψ : CellUT Loc Val K} (e : ρ.get l = some ψ) : ψ.InStratum α := by
  rcases ResUT.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hCc⟩
  · rw [f] at e; exact absurd e (by simp)
  · rw [f] at e; cases Option.some.inj e; exact h₁ _ f₁
  · rw [f] at e; cases Option.some.inj e; exact h₂ _ f₂
  · rw [f] at e; cases Option.some.inj e; exact hC _ _ _ hCc (h₁ _ f₁) (h₂ _ f₂)

/-- `Cell_α` is closed under `●`. -/
theorem CellUT.compS_hC (α : TSet) : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K,
    CellUT.CompS ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ hC h₁ h₂ => (CellUT.CompS.inStratum hC α).mpr ⟨h₁, h₂⟩

/-- `ResUT.CompS.inStratum_left` at one location. -/
theorem ResUT.CompS.inStratum_left_at {ρ₁ ρ₂ ρ : ResUT Loc Val K}
    (h : ResUT.CompS ρ₁ ρ₂ ρ) {α : TSet} {l : Loc}
    (hρ : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT Loc Val K} (e₁ : ρ₁.get l = some ψ) : ψ.InStratum α := by
  rcases ResUT.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ _ f
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    cases Option.some.inj f₁
    exact ((CellUT.CompS.inStratum hC α).mp (hρ _ f)).1

theorem ResUT.CompS.inStratum_right_at {ρ₁ ρ₂ ρ : ResUT Loc Val K}
    (h : ResUT.CompS ρ₁ ρ₂ ρ) {α : TSet} {l : Loc}
    (hρ : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT Loc Val K} (e₂ : ρ₂.get l = some ψ) : ψ.InStratum α :=
  ResUT.CompS.inStratum_left_at (ResUT.CompS.comm h) hρ e₂

/-- The exclusive walk keeps the stratum at one location.
`[about ours: `BoLo.ExWT.inStratum` at one location]` -/
theorem ExWT.inStratum_at
    {R : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    {C : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K →
      CellUT BoCa.Loc BoCa.Val K → Prop}
    (hC : ∀ (α : TSet) ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α →
        ψ.InStratum α)
    {ρ σ : ResUT BoCa.Loc BoCa.Val K} (h : ExWT R C ρ σ) {α : TSet}
    {D : TSet} (hD : K.DownOf D α) (hd : ρ.InStratum D) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT BoCa.Loc BoCa.Val K} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  cases h with
  | mk hs hw hb hnm hσ =>
      rename_i nm b w
      have hbs : ResUT.InStratum α b := by
        refine BoLo.inStratum_bigComp (hC α) hb ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, hφ, he⟩ := ExWitsT.mem hw p hp
        exact BoLo.ExWT.inStratum hC he α (CellUT.wit_inStratum_of_down hD (hd _ _ hφ))
      refine ResUT.inStratum_comp_at (hC α) hσ ?_ (fun φ e => hbs l φ e) hg
      intro φ e
      exact ResUT.inStratum_comp_at (hC α) hnm
        (fun χ f => hl χ (ResUT.restrict_eq_some.mp f).1)
        (fun χ f => hl χ (ResUT.restrict_eq_some.mp f).1) e

/-- The aliasable walk keeps the stratum at one location.
`[about ours: `BoLo.AgWT.inStratum` at one location]` -/
theorem AgWT.inStratum_at {ρ σ : ResUT BoCa.Loc BoCa.Val K} (h : AgWT ρ σ) {α : TSet}
    {D : TSet} (hD : K.DownOf D α) (hd : ρ.InStratum D) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT BoCa.Loc BoCa.Val K} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      have hbms : ResUT.InStratum α bm := by
        refine BoLo.inStratum_bigComp (BoLo.compR_hC α) hbm ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, hφ, hag⟩ := AgWitsMT.mem hwm p hp
        exact BoLo.AgWT.inStratum hag α (CellUT.wit_inStratum_of_down hD (hd _ _ hφ))
      have hbis : ResUT.InStratum α bi := by
        refine BoLo.inStratum_bigComp (BoLo.compR_hC α) hbi ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, ev, av, hφ, hex, hag, hc⟩ := AgWitsIT.mem hwi p hp
        exact BoLo.inStratum_comp (BoLo.compR_hC α) hc
          (BoLo.ExWT.inStratum BoLo.compR_hC hex α
            (CellUT.wit_inStratum_of_down hD (hd _ _ hφ)))
          (BoLo.AgWT.inStratum hag α (CellUT.wit_inStratum_of_down hD (hd _ _ hφ)))
      refine ResUT.inStratum_comp_at (BoLo.compR_hC α) hσ ?_ (fun φ e => hbis l φ e) hg
      intro φ e
      exact ResUT.inStratum_comp_at (BoLo.compR_hC α) ha
        (fun χ f => hl χ (ResUT.restrict_eq_some.mp f).1)
        (fun χ f => hbms l χ f) e

/-- `BoLo.flat_inStratum` at one location, for a resource in `Res_{↓α}`.
`[about ours: the first elided step of `[TR]` Lemma 6.50's proof, at one
location]` -/
theorem ResUT.flat_inStratum_at {ρ σ : ResUT BoCa.Loc BoCa.Val K} {α : TSet}
    (h : ResUT.Flat ρ σ) {D : TSet} (hD : K.DownOf D α) (hd : ρ.InStratum D) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT BoCa.Loc BoCa.Val K} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ResUT.inStratum_comp_at (BoLo.compS_hC α) hc
    (fun φ f => ExWT.inStratum_at BoLo.compS_hC he hD hd hl f)
    (fun φ f => AgWT.inStratum_at ha hD hd hl f) hg

/-- `[TR]` Lemma 6.50 at one location, for a resource in `Res_{↓α}`.
`[about ours: `[TR]` Lemma 6.50 (p. 16) at one location]` -/
theorem ResUT.updV_outlives_at {ρ ρ' : ResUT BoCa.Loc BoCa.Val K} {α : TSet}
    {D : TSet} (hD : K.DownOf D α) (hd : ρ.InStratum D) (hu : ResUT.UpdV ρ ρ') {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellUT BoCa.Loc BoCa.Val K} (hg : ρ'.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  refine ResUT.flat_inStratum_inv_at hσ' (fun χ hχ => ?_) hg
  rcases CellUT.rep' χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, _, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 l s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResUT.Flat.functional hτ hσ
    exact ResUT.flat_inStratum_at hσ hD hd hl hgg
  · obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hgg⟩ :=
      (hu.1.2 l b P).mpr ⟨w, ξ, hξ, hP, ⟨σ', hσ', hχ⟩⟩
    cases ResUT.Flat.functional hτ hσ
    exact (ResUT.flat_inStratum_at hσ hD hd hl hgg : K.Above α b)

end BoCa.Fig16.Tree

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `↭` keeps the stratum.
`[about ours: `[TR]` Lemma 6.50 read as a statement about `Res_α`]` -/
theorem ResUT.updV_inStratum {ρ ρ' : ResUT BoCa.Loc BoCa.Val K} {α : TSet}
    (hd : ρ.InStratum α) (hu : ResUT.UpdV ρ ρ') : ρ'.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hσα : ResUT.InStratum α σ := BoLo.flat_inStratum hσ hd
  refine BoLo.flat_inStratum_inv hσ' ?_
  intro m χ hχ
  rcases CellUT.rep' χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, _, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 m s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResUT.Flat.functional hτ hσ
    exact hσα m _ hgg
  · obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hgg⟩ :=
      (hu.1.2 m b P).mpr ⟨w, ξ, hξ, hP, ⟨σ', hσ', hχ⟩⟩
    cases ResUT.Flat.functional hτ hσ
    exact (hσα m _ hgg : K.Above α b)

/-- An `own` or a `mut` cell sits in its own flattening unchanged.  `[about ours:
the step `[TR]` 6.27's proof reads off `⦇−⦈` at an exclusive cell]` -/
theorem ResUT.flat_get_of_ne_imm {Loc Val : Type} {ρ σ : ResUT Loc Val K}
    (h : ρ.Flat σ) {l : Loc} {ψ : CellUT Loc Val K}
    (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) : σ.get l = some ψ := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact (ResUT.CompS.get_left_of_ne_imm hc (ExST.get_of_ne_imm he hg hk) hk).2


/-- `ρ = ρ/ℓ ● ℓ ↦ ρ(ℓ)`.
`[about ours: `[TR]` p. 5's `/` against `●`, at one location]` -/
theorem ResUT.del_compS {ρ : ResUT Loc Val K} {l : Loc} {ψ : CellUT Loc Val K}
    (hg : ρ.get l = some ψ) : ResUT.CompS (ρ.del l) (ResUT.single l ψ) ρ := by
  classical
  refine ⟨ResUT.Compat.of_disjoint (fun m => ?_), fun m => ?_⟩
  · by_cases hm : m = l
    · exact Or.inl (by rw [hm]; exact ResUT.del_get_self ρ l)
    · exact Or.inr (ResUT.single_get_ne ψ hm)
  · by_cases hm : m = l
    · subst hm
      show OptCompT CellUT.CompS ((ρ.del m).get m) ((ResUT.single m ψ).get m) (ρ.get m)
      rw [ResUT.del_get_self, ResUT.single_get_self]
      exact hg
    · show OptCompT CellUT.CompS ((ρ.del l).get m) ((ResUT.single l ψ).get m) (ρ.get m)
      rw [ResUT.del_get_ne ρ hm, ResUT.single_get_ne ψ hm]
      cases e : ρ.get m with
      | none => rfl
      | some χ => rfl


end BoCa.Fig16.Tree

end
