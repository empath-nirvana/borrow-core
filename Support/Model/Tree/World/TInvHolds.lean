import Support.Model.Tree.World.TInvEnd
import Support.Model.Tree.World.TInvReread
import Support.Model.Tree.World.TInvBase

/-!
# Every `TWNT` world satisfies `TIT`

`[spec §62]`. Induction on `TWNT`, each constructor by the preservation lemma ported from
`Core/Invariant.lean` (`tit_alloc`, `tit_frame`, `tit_reb`,
`tit_rebDeep`, `tit_mutFold`, `tit_mutUnfold`, `tit_free`, `tit_store`, `tit_end`,
`tit_endReb`), and `reread` by `tit_reread`. The `rebEndDeep` case reads the escrow's `own`
cells off `DeepInv` at the reborrowed view.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-- **Every `TWNT` world satisfies `TIT`.** -/
theorem TWNT.inv {K : WCactus} {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (h : TWNT K Θ tc W ps rs) : TIT K Θ W ps rs := by
  induction h with
  | empty => exact tit_empty _
  | alloc _ _ _ hW _ ih => exact tit_alloc hW ih
  | immFrame T hα hW₀ hX hW hden hW' hv hds ih =>
      exact tit_frame hW₀.valid hX hW hden hW' hv hds ih
  | reb r hW₀ hr hle hreb hden _ _ hW hv ih =>
      exact tit_reb hW₀.valid hr hle hreb hden hW hv ih
  | rebDeep r hW₀ hr hch hcell hreb hden hβc _ _ hW hv ih =>
      exact tit_rebDeep hW₀.valid hr hch hcell hreb hden hβc hW hv ih
  | mutFold hW₀ hX hW hW' _ ih => exact tit_mutFold hW₀.valid hX hW hW' ih
  | mutUnfold _ hW hX hW' _ ih => exact tit_mutUnfold hW hX hW' ih
  | free _ hW _ ih => exact tit_free hW ih
  | store _ hW hW' _ ih => exact tit_store hW hW' ih
  | immEnd r hW₀ hr hc hX' hW' hv hps hrs ih =>
      exact tit_end hW₀.valid hr hc hX' hW' hv hps hrs ih
  | rebEnd r hW₀ hr hle hreb hW hβ ih =>
      exact tit_endReb hW₀.valid hle hreb hW hβ
        (fun r' hr' u hu => ih.2.2.2.1 r' hr' r hr u hu) ih
  | @rebEndDeep K Θ tc W W' c ps rs r p l₀ S₀ u₀ s w₀ hs β hW₀ hr hch hle hreb hW hβ ih =>
      have hvW := hW₀.valid
      have hexcl : ∀ r' ∈ rs, ∀ u, w₀.get r'.le ≠ some (CellUT.ownOf u) := by
        intro r' hr' u hu
        obtain ⟨aW, haW⟩ := agW_of_valid hvW
        obtain ⟨a', ha'⟩ := agW_of_valid (ResUT.Valid.split hW hvW).1
        obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgWT.split hW).mp haW
        rw [AgWT.functional ha'' ha'] at hcomp
        obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgWT.get_imm ha' hle (CellUT.kind_immOf _ _ _ _)
        obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp eχ (by rw [kχ]; simp)
        obtain ⟨-, -, o, -, -⟩ := ih.1.1 r hr p l₀ S₀ u₀ hch aW haW ψ₀ e₀ k₀
        rw [w₀', wχ, CellUT.wit_immOf] at o
        exact ih.2.2.2.1 r' hr' r hr u (o _ u hu)
      exact tit_endReb hvW hle hreb hW hβ hexcl ih
  | reread hT hE hag hW hps hrs _ ih => exact tit_reread hT.valid hE hag hW hps hrs ih

/-- **`TWNT.InvHolds`.** -/
theorem twnt_invHolds : TWNT.InvHolds :=
  fun _ _ _ _ _ _ h => h.inv

end BoCa.Fig16.Tree.Wp

end
