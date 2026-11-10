import LicUpd.Six59G

/-!
# LicUpd — K9: `Six52G` as stated fails. A bracket's end must absorb every image at its lifetime

**The configuration.**
- A bracketed reborrow at `α` takes the empty image (`ρ = ∅`, `ρ_reb = ∅`).
- Its inner run starts at `ρ_e = 0 ↦ imm({γ}, loc 1, 1 ↦ own t)`, a view at a longer `γ ⊐ α`
  (`ρ_e ∈ Res_α`).
- The run makes a getter's image at the bracket's own lifetime:
  `π = ρ_e ● 1 ↦ imm({α}, t, ∅)`. The image is derivable from the `γ` view (`α ⊑ γ`), so the
  run meets the growth clause (`k9_run`).
- 6.52 subtracts only `ρ_reb = ∅`, so the garbage minus `ρ_reb` is `π`, which holds a cell at
  `α` and is not in `Res_α`.

At the language level: a view at `'γ`, used as `'α` by subtyping inside a bracket at `'α`,
passes through `load`, giving an image at `'α`. At the bracket's end that image is still in the
garbage.

**Consequence.** 6.52 under growth must subtract, at the bracket's end, every derivable image at
the bracket's lifetime, wherever its ancestor is. Lifetimes `⊑ α` that are not the bracket's
own (`x ⊏ α`) are covered by the same reading. This is the lend-end absorption of the design,
applied at every lifetime end. It changes 6.52's and 6.59's statements, the subtracted part
included, and 6.150's exit reads them. It is reported as a finding.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

section K9
variable (γ α : Life) (t : Val)

theorem compat_G : ResU.CompatS (rhoK1 γ t) (imgK1 α t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 0
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

/-- `π = ρ_e ● 1 ↦ imm({α}, t, ∅)`. -/
def piG : WRes := ResU.compS (rhoK1 γ t) (imgK1 α t) (compat_G γ α t)

theorem piG_comp : ResU.CompS (rhoK1 γ t) (imgK1 α t) (piG γ α t) := ResU.compS_spec _ _ _

theorem compatR_G : ResU.CompatR (agK1 γ t) (imgK1 α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₂
  rw [agK1_get1] at e₁
  cases Option.some.inj e₁
  exact ⟨_, CellU.CompR.ownImm _ _ _ _⟩

def agG : WRes := ResU.compR (agK1 γ t) (imgK1 α t) (compatR_G γ α t)

theorem agG_comp : ResU.CompR (agK1 γ t) (imgK1 α t) (agG γ α t) := ResU.compR_spec _ _ _

theorem flat_piG : ResU.Flat (piG γ α t) (agG γ α t) :=
  (ResU.Flat.split (piG_comp γ α t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, agK1 γ t, imgK1 α t, agG γ α t,
      ExW.empty_of_all_imm (allImm_rhoK1 γ t), ExW.empty_of_all_imm (allImm_imgK1 α t),
      ResU.comp_empty_left _, agW_rhoK1 γ t, agW_imgK1 α t, agG_comp γ α t,
      ResU.comp_empty_left _⟩

theorem agG_get0 : (agG γ α t).get 0 = some (cellK1 γ t) :=
  comp_get_left (agG_comp γ α t) (agK1_get0 γ t) (ResU.single_get_ne _ (by decide))

theorem agG_get1 : (agG γ α t).get 1 = some (imgCell α t) := by
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agG_comp γ α t) (agK1_get1 γ t) (ResU.single_get_self _ _)
  rw [e]
  exact congrArg some (CellU.CompR.functional hc (CellU.CompR.ownImm _ _ _ _))

theorem agG_get_other {l : Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) : (agG γ α t).get l = none :=
  comp_get_none (agG_comp γ α t) (agK1_get_other γ t h0 h1) (ResU.single_get_ne _ h1)

theorem agG_not_mut {l : Loc} {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩}
    (e : (agG γ α t).get l = some (CellU.mutOf b v χ h P hw)) : False := by
  by_cases h0 : l = 0
  · subst h0; rw [agG_get0] at e; exact CellU.immOf_ne_mutOf (Option.some.inj e)
  · by_cases h1 : l = 1
    · subst h1; rw [agG_get1] at e; exact CellU.immOf_ne_mutOf (Option.some.inj e)
    · rw [agG_get_other γ α t h0 h1] at e; cases e

/-- The image at `α` is derivable from the view at `γ`, for `α ⊑ γ`. -/
theorem k9_derLt (hαγ : α ≤ γ) : DerLt (agK1 γ t) 1 t PMap.empty α :=
  DerLt.proj (DerLt.base (agK1_get0 γ t) (show (LSet.singleton γ).mem γ from rfl))
    (ResU.single_get_self _ _) ⟨chiK1 t, ResU.comp_empty_left _⟩ hαγ

/-- **The inner run meets the growth clause.** -/
theorem k9_run (hαγ : α ≤ γ) : UpdVG (rhoK1 γ t) (piG γ α t) := by
  refine ⟨⟨⟨fun l s v χ h hf => ?_, fun l s v χ h hf x hx => ?_⟩, fun l b P => ?_⟩,
    ⟨_, flat_rhoK1 γ t⟩, ⟨_, flat_piG γ α t⟩⟩
  · obtain ⟨σ, hσ, e⟩ := hf
    rw [ResU.Flat.functional hσ (flat_rhoK1 γ t)] at e
    refine ⟨s, h, fun _ hx => hx, agG γ α t, flat_piG γ α t, ?_⟩
    by_cases h0 : l = 0
    · subst h0
      rw [agK1_get0] at e
      rw [agG_get0]
      exact e
    · by_cases h1 : l = 1
      · subst h1
        rw [agK1_get1] at e
        exact (CellU.ownOf_ne_immOf (Option.some.inj e)).elim
      · rw [agK1_get_other γ t h0 h1] at e
        cases e
  · obtain ⟨σ, hσ, e⟩ := hf
    rw [ResU.Flat.functional hσ (flat_piG γ α t)] at e
    by_cases h0 : l = 0
    · subst h0
      rw [agG_get0] at e
      exact Or.inl ⟨s, h, ⟨agK1 γ t, flat_rhoK1 γ t, by rw [agK1_get0]; exact e⟩, hx⟩
    · by_cases h1 : l = 1
      · subst h1
        rw [agG_get1] at e
        obtain ⟨hs, hv, hχ⟩ := CellU.immOf_inj (Option.some.inj e)
        subst hs
        subst hv
        subst hχ
        have hxα : x = α := hx
        rw [hxα]
        exact Or.inr ⟨agK1 γ t, flat_rhoK1 γ t, k9_derLt γ α t hαγ⟩
      · rw [agG_get_other γ α t h0 h1] at e
        cases e
  · constructor
    · rintro ⟨v, χ, h, hw, σ, hσ, e⟩
      rw [ResU.Flat.functional hσ (flat_rhoK1 γ t)] at e
      exact (agK1_not_mut γ t e).elim
    · rintro ⟨v, χ, h, hw, σ, hσ, e⟩
      rw [ResU.Flat.functional hσ (flat_piG γ α t)] at e
      exact (agG_not_mut γ α t e).elim

theorem rhoK1_inStratum (hαγ : α < γ) : (rhoK1 γ t).InStratum α :=
  ResU.inStratum_single 0 ((CellU.inStratum_immOf _ _ _ _ _).mpr hαγ)

/-- **K9: `Six52G` fails.** -/
theorem six52G_fails (t : Val) (hαγ : α < γ) : ¬ Six52G := by
  intro H
  obtain ⟨ψ, -, hcomp, hψ⟩ := H α PMap.empty PMap.empty (rhoK1 γ t) PMap.empty (piG γ α t)
    (rhoK1 γ t) (piG γ α t) (reb_empty (inStratum_emptyW α)) (ResU.comp_empty_left _)
    (ResU.comp_empty_left _) (k9_run γ α t (le_of_lt hαγ)) (rhoK1_inStratum γ α t hαγ)
    (inStratum_emptyW α)
  rw [restrictDom_empty] at hcomp
  have hψeq : piG γ α t = ψ := ResU.CompS.functional hcomp (ResU.comp_empty_right ψ)
  have h1 : (piG γ α t).get 1 = some (imgCell α t) :=
    comp_get_right (piG_comp γ α t) (ResU.single_get_ne _ (by decide)) (ResU.single_get_self _ _)
  rw [hψeq] at h1
  exact lt_irrefl α (hψ 1 _ h1)

end K9

theorem not_six52G : ¬ Six52G :=
  six52G_fails (OrderDual.toDual 0) (OrderDual.toDual 1) (Val.loc 0)
    (OrderDual.toDual_lt_toDual.mpr Nat.zero_lt_one)

end BoCa.Fig16.LicUpd

end
