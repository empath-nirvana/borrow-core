import LicUpd.Absorb

/-!
# LicUpd — two of the three open items, refuted at concrete configurations

- **`not_licFrame`: 6.48 fails under G1 as defined.**
  - The frame `F = 1 ↦ imm({β}, t, ∅)` is a second image of the same escrow cell, at `β ≠ α`.
  - In `⦇F ● ρ⦈`, `1` reads `imm({β}, t, ∅)` (`imm ○ own = imm`).
  - In `⦇F ● π⦈`, `1` reads `imm({β} ∪ {α}, t, ∅)`, because K1's image joins `F`'s copy.
  - G1's start→end clause keeps `UpdImm`'s exact cell, so the composite run is refused while
    K1 itself is accepted.
  - The defect is that clause. A start view whose lifetime set grows by a derivable image's
    lifetime is not kept as the same cell.
- **`not_licBridge`: the bridge as stated fails.**
  - `LicBridge` lets `c` be any `α`-reborrow image of the escrow inside the garbage, `∅`
    included.
  - At `c = ∅`, K1's run would have to update `∅` to `1 ↦ imm({α}, t, ∅)`, which `↭` refuses.
  - The statement needs `c` to cover every new image. `LicBridgeAll` adds this: the garbage
    minus `c|dom(ρ_P|mut,own)` lies in `Res_α`. It stays open.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `LicFrame` -/

section Frame
variable (α β : Life) (t : Val)

theorem compat_FX : ResU.CompatS (imgK1 β t) (rhoK1 α t) :=
  ResU.Compat.of_disjoint fun l => by
    by_cases h : l = 1
    · subst h; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ h)

/-- `X = F ● ρ`. -/
def xK7 : WRes := ResU.compS (imgK1 β t) (rhoK1 α t) (compat_FX α β t)

theorem xK7_comp : ResU.CompS (imgK1 β t) (rhoK1 α t) (xK7 α β t) := ResU.compS_spec _ _ _

theorem piK1_get1 : (piK1 α t).get 1 = some (imgCell α t) :=
  comp_get_right (piK1_comp α t) (ResU.single_get_ne _ (by decide)) (ResU.single_get_self _ _)

theorem compat_FZ : ResU.CompatS (imgK1 β t) (piK1 α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₁
  rw [piK1_get1] at e₂
  cases Option.some.inj e₂
  exact ⟨_, _, _, _, _, _, rfl, rfl⟩

/-- `Z = F ● π`. -/
def zK7 : WRes := ResU.compS (imgK1 β t) (piK1 α t) (compat_FZ α β t)

theorem zK7_comp : ResU.CompS (imgK1 β t) (piK1 α t) (zK7 α β t) := ResU.compS_spec _ _ _

theorem agW_piK1 : AgW (piK1 α t) (agPi α t) :=
  (AgW.split (piK1_comp α t)).mpr ⟨agK1 α t, imgK1 α t, agW_rhoK1 α t, agW_imgK1 α t, agPi_comp α t⟩

theorem compatR_X : ResU.CompatR (imgK1 β t) (agK1 α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₁
  rw [agK1_get1] at e₂
  cases Option.some.inj e₂
  exact ⟨_, CellU.CompR.immOwn _ _ _ _⟩

def agX : WRes := ResU.compR (imgK1 β t) (agK1 α t) (compatR_X α β t)

theorem agX_comp : ResU.CompR (imgK1 β t) (agK1 α t) (agX α β t) := ResU.compR_spec _ _ _

theorem flat_xK7 : ResU.Flat (xK7 α β t) (agX α β t) :=
  (ResU.Flat.split (xK7_comp α β t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, imgK1 β t, agK1 α t, agX α β t,
      ExW.empty_of_all_imm (allImm_imgK1 β t), ExW.empty_of_all_imm (allImm_rhoK1 α t),
      ResU.comp_empty_left _, agW_imgK1 β t, agW_rhoK1 α t, agX_comp α β t,
      ResU.comp_empty_left _⟩

theorem agX_get1 : (agX α β t).get 1 = some (imgCell β t) := by
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agX_comp α β t) (ResU.single_get_self _ _) (agK1_get1 α t)
  rw [e]
  exact congrArg some (CellU.CompR.functional hc (CellU.CompR.immOwn _ _ _ _))

theorem compatR_Z : ResU.CompatR (imgK1 β t) (agPi α t) := by
  intro l ψ₁ ψ₂ e₁ e₂
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₁
  rw [agPi_get1] at e₂
  cases Option.some.inj e₂
  exact ⟨_, CellU.CompR.strict ⟨_, _, _, _, _, _, rfl, rfl⟩⟩

def agZ : WRes := ResU.compR (imgK1 β t) (agPi α t) (compatR_Z α β t)

theorem agZ_comp : ResU.CompR (imgK1 β t) (agPi α t) (agZ α β t) := ResU.compR_spec _ _ _

theorem exS_piK1 : ExS (piK1 α t) PMap.empty :=
  (ExS.split (piK1_comp α t)).mpr ⟨PMap.empty, PMap.empty,
    ExW.empty_of_all_imm (allImm_rhoK1 α t), ExW.empty_of_all_imm (allImm_imgK1 α t),
    ResU.comp_empty_left _⟩

theorem flat_zK7 : ResU.Flat (zK7 α β t) (agZ α β t) :=
  (ResU.Flat.split (zK7_comp α β t)).mpr
    ⟨PMap.empty, PMap.empty, PMap.empty, imgK1 β t, agPi α t, agZ α β t,
      ExW.empty_of_all_imm (allImm_imgK1 β t), exS_piK1 α t,
      ResU.comp_empty_left _, agW_imgK1 β t, agW_piK1 α t, agZ_comp α β t,
      ResU.comp_empty_left _⟩

/-- `⦇F ● π⦈(1)` is not `F`'s copy `imm({β}, t, ∅)`: it carries `α` as well. -/
theorem agZ_get1_ne (hαβ : α ≠ β) : (agZ α β t).get 1 ≠ some (imgCell β t) := by
  intro h
  obtain ⟨ψ, e, hc⟩ := comp_get_both (agZ_comp α β t) (ResU.single_get_self _ _) (agPi_get1 α t)
  rw [h] at e
  have hψ : ψ = imgCell β t := (Option.some.inj e).symm
  have hmem : (LSet.singleton β).mem α :=
    CellU.CompR.ls_imm (CellU.CompR.comm hc) rfl hψ (show (LSet.singleton α).mem α from rfl)
  exact hαβ hmem

/-- **`LicFrame` fails at K1 with a second image as frame.** -/
theorem licFrame_fails (t : Val) (hαβ : α ≠ β) : ¬ LicFrame := by
  intro H
  have h := H (rhoK1 α t) (piK1 α t) (imgK1 β t) (xK7 α β t) (zK7 α β t) (k1_accepted α t)
    (xK7_comp α β t) (zK7_comp α β t) ⟨_, flat_xK7 α β t⟩ ⟨_, flat_zK7 α β t⟩
  obtain ⟨σ, hσ, e⟩ := h.1.1.1 1 (LSet.singleton β) t PMap.empty (inStratum_emptyW _)
    ⟨agX α β t, flat_xK7 α β t, agX_get1 α β t⟩
  rw [ResU.Flat.functional hσ (flat_zK7 α β t)] at e
  exact agZ_get1_ne α β t hαβ e

end Frame

theorem not_licFrame : ¬ LicFrame :=
  licFrame_fails (OrderDual.toDual 0) (OrderDual.toDual 1) (Val.loc 0) (by decide)

/-! ### `LicBridge` -/

theorem restrictDom_empty (σ : WRes) : ResU.restrictDom (PMap.empty : WRes) σ = PMap.empty :=
  PMap.ext fun l => by
    show (if (σ.get l).isSome then (PMap.empty : WRes).get l else none) = (PMap.empty : WRes).get l
    split <;> rfl

theorem reb_empty {β : Life} {R : WRes} (h : R.InStratum β) : ResU.Reb β R PMap.empty :=
  ⟨h, [], PMap.empty, ⟨by simp, fun _ => by simp⟩, BigComp.nil, ⟨R, ResU.comp_empty_left _⟩,
    fun _ _ hm => absurd hm (by simp)⟩

/-- **`LicBridge` fails at K1 with `c = ∅`.** -/
theorem licBridge_fails (α : Life) (t : Val) : ¬ LicBridge := by
  intro H
  have h := H α (chiK1 t) PMap.empty PMap.empty PMap.empty (imgK1 α t) PMap.empty (imgK1 α t)
    (rhoK1 α t) (piK1 α t) 0 (LSet.singleton α) (Val.loc 1) (chiK1_inStratum _ t)
    (reb_empty (chiK1_inStratum _ t))
    ⟨imgK1 α t, by rw [restrictDom_empty]; exact ResU.comp_empty_left _⟩
    (ResU.comp_empty_right _) (ResU.comp_empty_left _) (ResU.CompS.comm (piK1_comp α t))
    (ResU.comp_empty_left _) (inStratum_emptyW _) (inStratum_emptyW _) (k1_accepted α t)
  obtain ⟨σ, hσ, e⟩ := (h.1.1 1 (LSet.singleton α) t PMap.empty (inStratum_emptyW _)).mpr
    ⟨imgK1 α t, flat_imgK1 α t, ResU.single_get_self _ _⟩
  rw [flat_empty_eq hσ, PMap.empty_get] at e
  cases e

theorem not_licBridge : ¬ LicBridge := licBridge_fails (OrderDual.toDual 0) (Val.loc 0)

/-- **Open: the bridge with `c` covering every new image.** `LicBridge` with the extra
premise that the garbage minus `c|dom(ρ_P|mut,own)` lies in `Res_α`: no image at a lifetime
`⊑ α` is left outside `c`. -/
def LicBridgeAll : Prop :=
  ∀ (α : Life) (ρP c ρb ρ' ρp ρρb ρ'p X Z : WRes) (l₀ : Loc) (s : LSet) (v : Val)
    (hs : ρP.InStratum s.join),
    ResU.Reb α ρP c →
    (∃ χ, ResU.CompS χ (c.restrictDom ρP.exclPart) ρp ∧ χ.InStratum α) →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb X →
    ResU.CompS ρ' ρp ρ'p → ResU.CompS ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs)) Z →
    ResU.CompS c ρb ρρb →
    ρb.InStratum α → ρ'.InStratum α →
    UpdVLic X Z → ResU.UpdV ρρb ρ'p

end BoCa.Fig16.LicUpd

end
