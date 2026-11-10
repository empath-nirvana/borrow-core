import LicUpd.Lic

/-!
# LicUpd — K1: a getter's image against `↭` and against G1

K1 (`scratch-archive/kernel/999/lender-exits.md` §1.1) has two resources:
- the start `ρ = 0 ↦ imm({α}, loc 1, χ)` with `χ = 1 ↦ own(t)`, the lent cell and its escrow;
- the end `π = ρ ● 1 ↦ imm({α}, t, ∅)`, which also holds the image a getter returns.

Both flattenings are computed in full:
- `⦇ρ⦈ = {0 ↦ cell, 1 ↦ own(t)}`;
- `⦇π⦈ = {0 ↦ cell, 1 ↦ imm({α}, t, ∅)}`, by `○`'s `own ○ imm = imm`.

- `k1_refused`: today's `↭` (`UpdImm`) refuses the run.
- `k1_accepted`: G1 (`UpdVLic`) accepts it. The image is derivable in one projection step.
- `k1_frame_copy`: the same holds under a one-cell frame holding a copy of the lent cell.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

variable (α : Life) (t : Val)

/-- The escrow `χ = 1 ↦ own(t)`. -/
abbrev chiK1 (t : Val) : WRes := ResU.single 1 (CellU.ownOf t)

theorem chiK1_inStratum (a : Life) (t : Val) : (chiK1 t).InStratum a :=
  ResU.inStratum_single_own a 1 t

/-- The lent cell `imm({α}, loc 1, χ)`. -/
abbrev cellK1 (α : Life) (t : Val) : CellU Loc Val :=
  CellU.immOf (LSet.singleton α) (Val.loc 1) (chiK1 t) (chiK1_inStratum _ t)

/-- The start `ρ = 0 ↦ imm({α}, loc 1, χ)`. -/
abbrev rhoK1 (α : Life) (t : Val) : WRes := ResU.single 0 (cellK1 α t)

/-- The image `imm({α}, t, ∅)`. -/
abbrev imgCell (α : Life) (t : Val) : CellU Loc Val :=
  CellU.immOf (LSet.singleton α) t PMap.empty
    (ResU.inStratum_empty _ : (PMap.empty : WRes).InStratum _)

/-- The image at `1`. -/
abbrev imgK1 (α : Life) (t : Val) : WRes := ResU.single 1 (imgCell α t)

theorem compat_K1 : ResU.CompatS (rhoK1 α t) (imgK1 α t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 0
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

/-- The end `π = ρ ● 1 ↦ imm({α}, t, ∅)`. -/
def piK1 : WRes := ResU.compS (rhoK1 α t) (imgK1 α t) (compat_K1 α t)

theorem piK1_comp : ResU.CompS (rhoK1 α t) (imgK1 α t) (piK1 α t) := ResU.compS_spec _ _ _

/-! ### `⦇ρ⦈` -/

theorem flatR_chiK1 : ResU.FlatR (chiK1 t) (chiK1 t) :=
  ⟨PMap.empty, chiK1 t, AgW.single_own 1 t, ExW.single_own 1 t, ResU.comp_empty_left _⟩

theorem compatR_K1 : ResU.CompatR (rhoK1 α t) (chiK1 t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 0
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

/-- `ag(ρ)`. -/
def agK1 : WRes := ResU.compR (rhoK1 α t) (chiK1 t) (compatR_K1 α t)

theorem agK1_comp : ResU.CompR (rhoK1 α t) (chiK1 t) (agK1 α t) := ResU.compR_spec _ _ _

theorem agW_rhoK1 : AgW (rhoK1 α t) (agK1 α t) := AgW.single_imm (flatR_chiK1 t) (agK1_comp α t)

theorem allImm_rhoK1 : ∀ l ψ, (rhoK1 α t).get l = some ψ → ψ.kind = Kind.imm := by
  intro l ψ h
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
  rfl

theorem flat_rhoK1 : ResU.Flat (rhoK1 α t) (agK1 α t) :=
  ⟨PMap.empty, agK1 α t, ExW.empty_of_all_imm (allImm_rhoK1 α t), agW_rhoK1 α t,
    ResU.comp_empty_left _⟩

theorem agK1_get0 : (agK1 α t).get 0 = some (cellK1 α t) :=
  comp_get_left (agK1_comp α t) (ResU.single_get_self _ _) (ResU.single_get_ne _ (by decide))

theorem agK1_get1 : (agK1 α t).get 1 = some (CellU.ownOf t) :=
  comp_get_right (agK1_comp α t) (ResU.single_get_ne _ (by decide)) (ResU.single_get_self _ _)

theorem agK1_get_other {l : Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) : (agK1 α t).get l = none :=
  comp_get_none (agK1_comp α t) (ResU.single_get_ne _ h0) (ResU.single_get_ne _ h1)

/-! ### `⦇π⦈` -/

theorem flatR_empty : ResU.FlatR (PMap.empty : WRes) PMap.empty :=
  ⟨PMap.empty, PMap.empty, agW_empty, exW_empty, ResU.comp_empty_left _⟩

theorem agW_imgK1 : AgW (imgK1 α t) (imgK1 α t) :=
  AgW.single_imm flatR_empty (ResU.comp_empty_right _)

theorem allImm_imgK1 : ∀ l ψ, (imgK1 α t).get l = some ψ → ψ.kind = Kind.imm := by
  intro l ψ h
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
  rfl

/-- `⦇1 ↦ imm({α}, t, ∅)⦈` is itself. -/
theorem flat_imgK1 : ResU.Flat (imgK1 α t) (imgK1 α t) :=
  ⟨PMap.empty, imgK1 α t, ExW.empty_of_all_imm (allImm_imgK1 α t), agW_imgK1 α t,
    ResU.comp_empty_left _⟩

theorem compatR_pi : ResU.CompatR (agK1 α t) (imgK1 α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₂
  rw [agK1_get1] at e₁
  cases Option.some.inj e₁
  exact ⟨_, CellU.CompR.ownImm _ _ _ _⟩

/-- `ag(π) = ag(ρ) ○ ag(image)`. -/
def agPi : WRes := ResU.compR (agK1 α t) (imgK1 α t) (compatR_pi α t)

theorem agPi_comp : ResU.CompR (agK1 α t) (imgK1 α t) (agPi α t) := ResU.compR_spec _ _ _

theorem flat_piK1 : ResU.Flat (piK1 α t) (agPi α t) :=
  (ResU.Flat.split (piK1_comp α t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, agK1 α t, imgK1 α t, agPi α t,
      ExW.empty_of_all_imm (allImm_rhoK1 α t), ExW.empty_of_all_imm (allImm_imgK1 α t),
      ResU.comp_empty_left _, agW_rhoK1 α t, agW_imgK1 α t, agPi_comp α t,
      ResU.comp_empty_left _⟩

theorem agPi_get0 : (agPi α t).get 0 = some (cellK1 α t) :=
  comp_get_left (agPi_comp α t) (agK1_get0 α t) (ResU.single_get_ne _ (by decide))

theorem agPi_get1 : (agPi α t).get 1 = some (imgCell α t) := by
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agPi_comp α t) (agK1_get1 α t) (ResU.single_get_self _ _)
  rw [e, CellU.CompR.functional hc (CellU.CompR.ownImm _ _ _ _)]

theorem agPi_get_other {l : Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) : (agPi α t).get l = none :=
  comp_get_none (agPi_comp α t) (agK1_get_other α t h0 h1) (ResU.single_get_ne _ h1)

theorem flatAt_rhoK1 {l : Loc} {c : CellU Loc Val} (h : (rhoK1 α t).FlatAt l c) :
    (agK1 α t).get l = some c := by
  obtain ⟨σ, hσ, e⟩ := h
  rwa [ResU.Flat.functional hσ (flat_rhoK1 α t)] at e

theorem flatAt_piK1 {l : Loc} {c : CellU Loc Val} (h : (piK1 α t).FlatAt l c) :
    (agPi α t).get l = some c := by
  obtain ⟨σ, hσ, e⟩ := h
  rwa [ResU.Flat.functional hσ (flat_piK1 α t)] at e

/-! ### Today's `↭` refuses K1 -/

/-- **K1 is refused by `UpdImm`.** `⦇π⦈(1)` is the image and `⦇ρ⦈(1)` is `own(t)`. -/
theorem k1_refused : ¬ ResU.UpdImm (rhoK1 α t) (piK1 α t) := by
  intro h
  obtain ⟨σ, hσ, e⟩ := (h 1 (LSet.singleton α) t PMap.empty
    (ResU.inStratum_empty _ : (PMap.empty : WRes).InStratum _)).mpr
    ⟨agPi α t, flat_piK1 α t, agPi_get1 α t⟩
  rw [ResU.Flat.functional hσ (flat_rhoK1 α t), agK1_get1] at e
  exact CellU.ownOf_ne_immOf (Option.some.inj e)

theorem k1_refused_updV : ¬ ResU.UpdV (rhoK1 α t) (piK1 α t) :=
  fun h => k1_refused α t h.1.1

/-! ### G1 accepts K1 -/

/-- The image is derivable from `⦇ρ⦈` in one projection step from the lent cell. -/
theorem k1_derivable : Derivable (agK1 α t) 1 (imgCell α t) :=
  Derivable.proj (Derivable.base (agK1_get0 α t) rfl) (ResU.single_get_self _ _)
    (fun x hx => ⟨x, hx, le_refl x⟩) ⟨chiK1 t, ResU.comp_empty_left _⟩

theorem agK1_not_mut {l : Loc} {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩}
    (e : (agK1 α t).get l = some (CellU.mutOf b v χ h P hw)) : False := by
  by_cases h0 : l = 0
  · subst h0; rw [agK1_get0] at e; exact CellU.immOf_ne_mutOf (Option.some.inj e)
  · by_cases h1 : l = 1
    · subst h1; rw [agK1_get1] at e; exact CellU.ownOf_ne_mutOf (Option.some.inj e)
    · rw [agK1_get_other α t h0 h1] at e; cases e

theorem agPi_not_mut {l : Loc} {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩}
    (e : (agPi α t).get l = some (CellU.mutOf b v χ h P hw)) : False := by
  by_cases h0 : l = 0
  · subst h0; rw [agPi_get0] at e; exact CellU.immOf_ne_mutOf (Option.some.inj e)
  · by_cases h1 : l = 1
    · subst h1; rw [agPi_get1] at e; exact CellU.immOf_ne_mutOf (Option.some.inj e)
    · rw [agPi_get_other α t h0 h1] at e; cases e

theorem updMut_K1 : ResU.UpdMut (rhoK1 α t) (piK1 α t) := by
  intro l b P
  constructor
  · rintro ⟨v, χ, h, hw, hf⟩
    exact (agK1_not_mut α t (flatAt_rhoK1 α t hf)).elim
  · rintro ⟨v, χ, h, hw, hf⟩
    exact (agPi_not_mut α t (flatAt_piK1 α t hf)).elim

theorem k1_lic : UpdImmLic (rhoK1 α t) (piK1 α t) := by
  refine ⟨fun l s v χ h hf => ?_, fun l s v χ h hf => ?_⟩
  · have e := flatAt_rhoK1 α t hf
    refine ⟨agPi α t, flat_piK1 α t, ?_⟩
    by_cases h0 : l = 0
    · subst h0
      rw [agK1_get0] at e
      rw [agPi_get0]
      exact e
    · by_cases h1 : l = 1
      · subst h1
        rw [agK1_get1] at e
        exact (CellU.ownOf_ne_immOf (Option.some.inj e)).elim
      · rw [agK1_get_other α t h0 h1] at e
        cases e
  · have e := flatAt_piK1 α t hf
    by_cases h0 : l = 0
    · subst h0
      refine Or.inl ⟨agK1 α t, flat_rhoK1 α t, ?_⟩
      rw [agPi_get0] at e
      rw [agK1_get0]
      exact e
    · by_cases h1 : l = 1
      · subst h1
        rw [agPi_get1] at e
        rw [← Option.some.inj e]
        exact Or.inr ⟨agK1 α t, flat_rhoK1 α t, k1_derivable α t⟩
      · rw [agPi_get_other α t h0 h1] at e
        cases e

/-- **K1 is accepted by G1.** -/
theorem k1_accepted : UpdVLic (rhoK1 α t) (piK1 α t) :=
  ⟨⟨k1_lic α t, updMut_K1 α t⟩, ⟨_, flat_rhoK1 α t⟩, ⟨_, flat_piK1 α t⟩⟩

/-! ### A one-cell frame holding a copy of the lent cell -/

theorem rhoK1_self : ResU.CompS (rhoK1 α t) (rhoK1 α t) (rhoK1 α t) := by
  have h₃ : (chiK1 t).InStratum (LSet.singleton α ∪ LSet.singleton α).join :=
    ResU.InStratum.sup (chiK1_inStratum _ t) (chiK1_inStratum _ t)
  have hc := ResU.compS_single_imm 0 (LSet.singleton α) (LSet.singleton α) (Val.loc 1) (chiK1 t)
    (chiK1_inStratum _ t) (chiK1_inStratum _ t) h₃
  have e : CellU.immOf (LSet.singleton α ∪ LSet.singleton α) (Val.loc 1) (chiK1 t) h₃ =
      cellK1 α t :=
    CellU.immOf_congr (LSet.union_self (LSet.singleton α)) rfl rfl h₃ (chiK1_inStratum _ t)
  rw [e] at hc
  exact hc

theorem piK1_frame : ResU.CompS (rhoK1 α t) (piK1 α t) (piK1 α t) := by
  obtain ⟨x, hx, hxw⟩ := (ResU.CompS.assoc (rhoK1 α t) (rhoK1 α t) (imgK1 α t) (piK1 α t)).mpr
    ⟨rhoK1 α t, rhoK1_self α t, piK1_comp α t⟩
  rwa [ResU.CompS.functional hx (piK1_comp α t)] at hxw

/-- **The frame property at a one-cell frame.** A frame holding a copy of the lent cell
composes with each side to that side (copies are idempotent, 6.43), and G1 still accepts. -/
theorem k1_frame_copy {X Z : WRes} (hX : ResU.CompS (rhoK1 α t) (rhoK1 α t) X)
    (hZ : ResU.CompS (rhoK1 α t) (piK1 α t) Z) : UpdVLic X Z := by
  rw [ResU.CompS.functional hX (rhoK1_self α t), ResU.CompS.functional hZ (piK1_frame α t)]
  exact k1_accepted α t

end BoCa.Fig16.LicUpd

end
