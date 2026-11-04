import Support.Model.Tree.World.FdEsc

/-!
# Two templates of one escrow  `[spec §62]`

`TmplSpecT` (`World/Records.lean`) asks of a template only that it is a typed image at some
lifetime. At `ref 1` over `m ↦ own(())` every `m ↦ imm({β}, (), ∅)` is one (`view_reb`,
`view_typed`), so at a tree with two lifetimes the specification has two solutions, and a re-reading
keeps an `imm` cell's lifetime set (`RC.imm`), so no world is a re-reading of both
(`tmplSpecT_two`). `tmplT`, the `Classical` choice, picks one of them at each tree, and nothing in
the specification relates the pick at a grown tree to the pick before. That is the reason the
template is stored in the record, where the re-reading carries it (`docs/new-core/scope-791.md` O1).

At `ref 1` the canonical images still agree (`canonT_view`): `relRes` re-takes the template at the
reborrow's lifetime. The two solutions here differ in the template's own lifetime only.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-- `m ↦ imm({β}, (), ∅)` meets the template's specification at `ref 1` over `m ↦ own(())`. -/
theorem tmplSpecT_view (Θ : CodeTy) (β : Life) (m : BoCa.Loc) :
    TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) (viewRes β m) :=
  ⟨β, view_reb β m, view_typed Θ β m, ⟨_, (agW_of_valid (valid_view β m)).choose_spec⟩,
    view_cov Θ β m⟩

/-- **Two solutions of the template's specification, with no common re-reading**: at distinct
lifetimes `β₁ ≠ β₂`, both views meet `TmplSpecT`, and no world at any tree re-reads both. -/
theorem tmplSpecT_two (Θ : CodeTy) (Θ' : LocTy) {β₁ β₂ : Life} (hβ : β₁ ≠ β₂) (m : BoCa.Loc) :
    TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) (viewRes β₁ m) ∧
    TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) (viewRes β₂ m) ∧
    ∀ x : TRes K', ¬ (RR Θ' (viewRes (K := K) β₁ m) x ∧ RR Θ' (viewRes (K := K) β₂ m) x) := by
  refine ⟨tmplSpecT_view Θ β₁ m, tmplSpecT_view Θ β₂ m, fun x ⟨h₁, h₂⟩ => ?_⟩
  obtain ⟨ψ, eψ, hc₁⟩ := h₁.get_some (ResUT.single_get_self m (viewCell β₁))
  obtain ⟨ψ₂, eψ₂, hc₂⟩ := h₂.get_some (ResUT.single_get_self m (viewCell β₂))
  rw [eψ] at eψ₂
  cases Option.some.inj eψ₂
  cases hc₁ with
  | imm _ i i' hs _ _ _ =>
  cases hc₂ with
  | imm _ j _ hs' _ _ _ =>
  have e : TSet.single β₁ = TSet.single β₂ := hs.symm.trans hs'
  have := congrArg TSet.set e
  simp only [TSet.single_set, Finset.singleton_inj] at this
  exact hβ this

end BoCa.Fig16.Tree.Wp

end
