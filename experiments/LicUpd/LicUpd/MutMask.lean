import LicUpd.Growth

/-!
# LicUpd — K8: under growth, a new image masks a frame's frozen `mut` cell

**The configuration.**
- The frame `F = 2 ↦ imm({γ}, loc 1, 1 ↦ mut(b, t, ∅, ⊤))` holds a frozen `mut` cell at `1`,
  beneath an `imm` cell (`γ ⊏ b`).
- `ρ ⇝ π` is K1: the lent cell `0 ↦ imm({α}, loc 1, 1 ↦ own(t))`, and the getter's image
  `1 ↦ imm({α}, t, ∅)`. It meets the growth clause (`UpdVG.of_lic k1_accepted`).
- In `⦇F ● ρ⦈`, `1` reads `mut(b, t, ∅, ⊤) ○ own(t) = mut(b, t, ∅, ⊤)`.
- In `⦇F ● π⦈`, `1` reads `mut(b, t, ∅, ⊤) ○ imm({α}, t, ∅) = imm({α}, t, ∅)`, by `○`'s
  `mut ○ imm = imm`.

So `↭`'s `mut` clause, which the growth clause leaves unchanged, fails at the composite
(`updMutFrameG_fails`). **6.48's `mut` half does not hold under growth as a lemma over all
resources.**

Typed worlds exclude this configuration: `TI`'s `NoMut` forbids a `mut` cell anywhere at a
location a record's escrow owns, and the image sits at such a location. So the repair is a
premise on 6.48 read off the typed world. That changes 6.48's statement and its callers'
proofs. It is not a second clause in `↭`, but it is reported as a stop point.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

abbrev bK8 : Life := OrderDual.toDual 0
abbrev γK8 : Life := OrderDual.toDual 1

theorem γK8_lt_bK8 : γK8 < bK8 := OrderDual.toDual_lt_toDual.mpr Nat.zero_lt_one

/-- The frozen `mut(b, t, ∅, ⊤)`. -/
abbrev mutK8 (t : Val) : CellU Loc Val :=
  CellU.mutOf bK8 t PMap.empty (inStratum_emptyW _) (fun _ _ => True) trivial

abbrev kapK8 (t : Val) : WRes := ResU.single 1 (mutK8 t)

theorem kapK8_inStratum (t : Val) : (kapK8 t).InStratum (LSet.singleton γK8).join :=
  ResU.inStratum_single 1 ((CellU.inStratum_mutOf _ _ _ _ _ _ _).mpr γK8_lt_bK8)

abbrev cellF8 (t : Val) : CellU Loc Val :=
  CellU.immOf (LSet.singleton γK8) (Val.loc 1) (kapK8 t) (kapK8_inStratum t)

/-- The frame `F = 2 ↦ imm({γ}, loc 1, 1 ↦ mut(b, t, ∅, ⊤))`. -/
abbrev fK8 (t : Val) : WRes := ResU.single 2 (cellF8 t)

section K8
variable (α : Life) (t : Val)

theorem flatR_kapK8 : ResU.FlatR (kapK8 t) (kapK8 t) :=
  ⟨PMap.empty, kapK8 t, AgW.single_mut agW_empty,
    ExW.single_mut exW_empty (ResU.comp_empty_right _), ResU.comp_empty_left _⟩

theorem compatR_F8 : ResU.CompatR (fK8 t) (kapK8 t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 2
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

def agF8 : WRes := ResU.compR (fK8 t) (kapK8 t) (compatR_F8 t)

theorem agF8_comp : ResU.CompR (fK8 t) (kapK8 t) (agF8 t) := ResU.compR_spec _ _ _

theorem agW_fK8 : AgW (fK8 t) (agF8 t) := AgW.single_imm (flatR_kapK8 t) (agF8_comp t)

theorem allImm_fK8 : ∀ l ψ, (fK8 t).get l = some ψ → ψ.kind = Kind.imm := by
  intro l ψ h
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
  rfl

theorem agF8_get1 : (agF8 t).get 1 = some (mutK8 t) :=
  comp_get_right (agF8_comp t) (ResU.single_get_ne _ (by decide)) (ResU.single_get_self _ _)

theorem agF8_get_none {l : Loc} (h1 : l ≠ 1) (h2 : l ≠ 2) : (agF8 t).get l = none :=
  comp_get_none (agF8_comp t) (ResU.single_get_ne _ h2) (ResU.single_get_ne _ h1)

/-! ### `X = F ● ρ` -/

theorem compat_X8 : ResU.CompatS (fK8 t) (rhoK1 α t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 2
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

def xK8 : WRes := ResU.compS (fK8 t) (rhoK1 α t) (compat_X8 α t)

theorem xK8_comp : ResU.CompS (fK8 t) (rhoK1 α t) (xK8 α t) := ResU.compS_spec _ _ _

theorem compatR_X8 : ResU.CompatR (agF8 t) (agK1 α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  by_cases h1 : l = 1
  · subst h1
    rw [agF8_get1] at e₁
    rw [agK1_get1] at e₂
    cases Option.some.inj e₁
    cases Option.some.inj e₂
    exact ⟨_, CellU.CompR.mutOwn _ _ _ _ _ _⟩
  · by_cases h0 : l = 0
    · subst h0
      rw [agF8_get_none t (by decide) (by decide)] at e₁
      cases e₁
    · rw [agK1_get_other α t h0 h1] at e₂
      cases e₂

def agX8 : WRes := ResU.compR (agF8 t) (agK1 α t) (compatR_X8 α t)

theorem agX8_comp : ResU.CompR (agF8 t) (agK1 α t) (agX8 α t) := ResU.compR_spec _ _ _

theorem flat_xK8 : ResU.Flat (xK8 α t) (agX8 α t) :=
  (ResU.Flat.split (xK8_comp α t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, agF8 t, agK1 α t, agX8 α t,
      ExW.empty_of_all_imm (allImm_fK8 t), ExW.empty_of_all_imm (allImm_rhoK1 α t),
      ResU.comp_empty_left _, agW_fK8 t, agW_rhoK1 α t, agX8_comp α t,
      ResU.comp_empty_left _⟩

theorem agX8_get1 : (agX8 α t).get 1 = some (mutK8 t) := by
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agX8_comp α t) (agF8_get1 t) (agK1_get1 α t)
  rw [e]
  exact congrArg some (CellU.CompR.functional hc (CellU.CompR.mutOwn _ _ _ _ _ _))

/-! ### `Z = F ● π` -/

theorem piK1_get2 : (piK1 α t).get 2 = none :=
  comp_get_none (piK1_comp α t) (ResU.single_get_ne _ (by decide))
    (ResU.single_get_ne _ (by decide))

theorem compat_Z8 : ResU.CompatS (fK8 t) (piK1 α t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 2
    · subst h; exact Or.inr (piK1_get2 α t)
    · exact Or.inl (ResU.single_get_ne _ h)

def zK8 : WRes := ResU.compS (fK8 t) (piK1 α t) (compat_Z8 α t)

theorem zK8_comp : ResU.CompS (fK8 t) (piK1 α t) (zK8 α t) := ResU.compS_spec _ _ _

theorem compatR_Z8 : ResU.CompatR (agF8 t) (agPi α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  by_cases h1 : l = 1
  · subst h1
    rw [agF8_get1] at e₁
    rw [agPi_get1] at e₂
    cases Option.some.inj e₁
    cases Option.some.inj e₂
    exact ⟨_, CellU.CompR.mutImm _ _ _ _ _ _ _ _⟩
  · by_cases h0 : l = 0
    · subst h0
      rw [agF8_get_none t (by decide) (by decide)] at e₁
      cases e₁
    · rw [agPi_get_other α t h0 h1] at e₂
      cases e₂

def agZ8 : WRes := ResU.compR (agF8 t) (agPi α t) (compatR_Z8 α t)

theorem agZ8_comp : ResU.CompR (agF8 t) (agPi α t) (agZ8 α t) := ResU.compR_spec _ _ _

theorem flat_zK8 : ResU.Flat (zK8 α t) (agZ8 α t) :=
  (ResU.Flat.split (zK8_comp α t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, agF8 t, agPi α t, agZ8 α t,
      ExW.empty_of_all_imm (allImm_fK8 t), exS_piK1 α t,
      ResU.comp_empty_left _, agW_fK8 t, agW_piK1 α t, agZ8_comp α t,
      ResU.comp_empty_left _⟩

theorem agZ8_get1 : (agZ8 α t).get 1 = some (imgCell α t) := by
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agZ8_comp α t) (agF8_get1 t) (agPi_get1 α t)
  rw [e]
  exact congrArg some (CellU.CompR.functional hc (CellU.CompR.mutImm _ _ _ _ _ _ _ _))

/-- **K8.** 6.48's `mut` half fails under the growth clause. -/
theorem updMutFrameG_fails (α : Life) (t : Val) :
    ¬ (∀ F ρ π X Z : WRes, UpdVG ρ π → ResU.CompS F ρ X → ResU.CompS F π Z →
        ResU.Valid X → ResU.Valid Z → ResU.UpdMut X Z) := by
  intro H
  have h := H (fK8 t) (rhoK1 α t) (piK1 α t) (xK8 α t) (zK8 α t)
    (UpdVG.of_lic (k1_accepted α t)) (xK8_comp α t) (zK8_comp α t)
    ⟨_, flat_xK8 α t⟩ ⟨_, flat_zK8 α t⟩
  obtain ⟨v', χ', h', hw', σ', hσ', e'⟩ := (h 1 bK8 (fun _ _ => True)).mp
    ⟨t, PMap.empty, inStratum_emptyW _, trivial, agX8 α t, flat_xK8 α t, agX8_get1 α t⟩
  rw [ResU.Flat.functional hσ' (flat_zK8 α t), agZ8_get1 α t] at e'
  exact CellU.immOf_ne_mutOf (Option.some.inj e')

end K8

theorem not_updMutFrameG :
    ¬ (∀ F ρ π X Z : WRes, UpdVG ρ π → ResU.CompS F ρ X → ResU.CompS F π Z →
        ResU.Valid X → ResU.Valid Z → ResU.UpdMut X Z) :=
  updMutFrameG_fails (OrderDual.toDual 0) (Val.loc 0)

end BoCa.Fig16.LicUpd

end
