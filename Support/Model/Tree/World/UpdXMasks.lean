import Support.Model.Tree.World.Config
import Support.Model.Tree.World.StepKeep

/-!
# `EndT`'s masks: needed, and no wider

`EndT` (`TreeWp/Rel.lean`) masks `↭` at the run's own records: their lent locations and escrow
locations (`recMask`), on the start side at the records the run starts with and on the end side
at those it ends with.

**Needed.** A lend left open at a stop turns `ℓ ↦ own(loc m) ● m ↦ own(())` into the lend cell
`ℓ ↦ imm({α}, loc m, m ↦ own(()))` beside the borrower's view `m ↦ imm({β}, (), ∅)` (the world of
`cactusT_config`, before the view is handed to a child). That is an update masked at the record
the run now owns (`lend_open_admitted`), and it is no update with the mask removed
(`lend_open_needs_mask`): `↭`'s `imm` clause reads the lend cell at `ℓ` on one side only. This is
why `crwpG` dropped `↭`.

**No wider.** At every location neither side masks, `UpdX` is row 5.27's `imm` clause
(`updX_refl_imm`), and a location is masked only where one of the run's own records reads it.
The copy of the frame's lent cell (`copy_end_refused`) is at a location no record of the run's
reads, and is refused.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-- A cell at depth of the lend cell beside the view is at `ℓ` or `m`. -/
theorem cellAt_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {x : BoCa.Loc}
    {ψ : TCell KC} (h : CellAt W x ψ) : x = ℓC ∨ x = mC := by
  cases h with
  | top e =>
      rcases compS_back hW e with ⟨χ, e', -, -⟩ | ⟨χ, e', -, -⟩
      · exact Or.inl (ResUT.single_get_eq_some e').1
      · exact Or.inr (ResUT.single_get_eq_some e').1
  | @nest _ m _ χ _ e h' =>
      rcases compS_back hW e with ⟨χ', e', -, w'⟩ | ⟨χ', e', -, w'⟩
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
        rw [← w'] at h'
        have hw : (lendCell (K := KC) αC mC).wit = escR mC := by simp [lendCell, CellUT.wit_immOf]
        rw [hw] at h'
        cases h' with
        | top e'' => exact Or.inr (ResUT.single_get_eq_some e'').1
        | nest e'' h'' =>
            obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e''
            exact absurd h'' CellAt.not_empty
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
        rw [← w'] at h'
        have hw : (viewCell (K := KC) βC).wit = PMap.empty := by simp [viewCell, CellUT.wit_immOf]
        rw [hw] at h'
        exact absurd h' CellAt.not_empty

/-- The flattening of the lend cell beside the view holds borrows at `ℓ` and `m` only, and holds
the lend cell at `ℓ`. -/
theorem flat_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {τ : TRes KC}
    (hτ : ResUT.Flat W τ) :
    (∀ x ψ, τ.get x = some ψ → ψ.kind ≠ Kind.own → x = ℓC ∨ x = mC) ∧
    τ.get ℓC = some (lendCell αC mC) := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  have hall : ∀ l ψ, W.get l = some ψ → ψ.kind = Kind.imm := fun l ψ el => by
    rcases compS_back hW el with ⟨χ, e', k, -⟩ | ⟨χ, e', k, -⟩
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'; rw [← k]; simp [lendCell]
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'; rw [← k]; simp [viewCell]
  obtain rfl : e = PMap.empty := ExST.functional he (exST_all_imm hall)
  have hτa : τ = a := ResUT.CompS.functional hc (ResUT.comp_empty_left _)
  subst hτa
  refine ⟨fun x ψ eψ hk => ?_, (ag_config hW ha).1⟩
  obtain ⟨ψ₀, c₀, -⟩ := agW_cellAt ha x ψ eψ hk
  exact cellAt_config hW c₀

/-- **The lend left open at a stop is an update masked at the record the run owns.** -/
theorem lend_open_admitted {W₀ W : TRes KC}
    (h₀ : ResUT.CompS (ResUT.single ℓC (CellUT.ownOf (BoCa.Val.loc mC)))
      (ResUT.single mC (CellUT.ownOf BoCa.Val.unit)) W₀)
    (hW : ResUT.CompS parentRes childRes W) (hv : ResUT.Valid W) :
    UpdX (K := KC) (K' := KC) (sem wC.Θ) (recMask ([] : List (FrameRecT KC)))
      (recMask [recE (K := KC) ℓC mC]) W₀ W := by
  obtain ⟨-, hf₀⟩ := valid_two_own (BoCa.Val.loc mC) BoCa.Val.unit h₀
  obtain ⟨τ, hτ⟩ := hv
  have hown : ∀ x ψ, W₀.get x = some ψ → ψ.kind = Kind.own := fun x ψ e => by
    rcases compS_back h₀ e with ⟨χ, e', k, -⟩ | ⟨χ, e', k, -⟩
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'; rw [← k]; simp
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'; rw [← k]; simp
  refine ⟨W₀, τ, hf₀, hτ, fun l => ⟨fun ψ e hk _ => absurd (hown l ψ e) hk,
    fun ψ' e hk hm => ?_⟩⟩
  exfalso
  apply hm
  refine ⟨recE ℓC mC, List.mem_singleton_self _, ?_⟩
  rcases (flat_config hW hτ).1 l ψ' e hk with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (.top (ψ := CellUT.ownOf BoCa.Val.unit) (ResUT.single_get_self _ _) (by simp))

/-- **Without the mask it is no update**: the lend cell at `ℓ` is read on one side only. -/
theorem lend_open_needs_mask {W₀ W : TRes KC}
    (h₀ : ResUT.CompS (ResUT.single ℓC (CellUT.ownOf (BoCa.Val.loc mC)))
      (ResUT.single mC (CellUT.ownOf BoCa.Val.unit)) W₀)
    (hW : ResUT.CompS parentRes childRes W) :
    ¬ UpdX (K := KC) (K' := KC) (sem wC.Θ) (recMask ([] : List (FrameRecT KC)))
      (recMask ([] : List (FrameRecT KC))) W₀ W := by
  rintro ⟨σ, τ, hσ, hτ, hx⟩
  obtain ⟨-, hf₀⟩ := valid_two_own (BoCa.Val.loc mC) BoCa.Val.unit h₀
  obtain rfl := ResUT.Flat.functional hσ hf₀
  obtain ⟨-, ψ, e, hxc⟩ := (hx ℓC).2 _ (flat_config hW hτ).2 (by simp [lendCell])
    (by simp [recMask])
  rcases compS_back h₀ e with ⟨χ, e', k, -⟩ | ⟨χ, e', k, -⟩
  · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
    have := hxc.1; rw [← k] at this; simp [lendCell] at this
  · exact absurd (ResUT.single_get_eq_some e').1 (by decide)

end BoCa.Fig16.Tree.Wp

end
