import Support.Model.Tree.World.FdEsc
import Support.Model.Tree.CarrierGraftEx

/-!
# A two-branch configuration at the grafted tree

`[spec §62]`. The pieces of a configuration at `K₁` (`Tree/CarrierGraftEx.lean`): the parent's
resource, at its lend `α`, is `ℓ ↦ imm({α}, loc m, m ↦ own(()))` (`parentRes`); a child's, at
`β ⊏ α`, is the record's canonical image `m ↦ imm({β}, (), ∅)` (`childRes`). `ag_config` reads
the aliasable walk of their composite. `World/UpdXMasks.lean` reads a lend left open at it.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-! ### The configuration -/

/-- The tree: `β = 1` nested in `α = 2`. -/
abbrev KC : WCactus := K₁

/-- `α`, the parent's lend. -/
abbrev αC : Life := OrderDual.toDual 2

/-- `β`, the child's reborrow. -/
abbrev βC : Life := OrderDual.toDual 1

theorem βC_lt_αC : KC.lt βC αC := K₁_lt

/-- The world: the tree, the empty store typing, the `Classical` template choice. -/
abbrev wC : TWd := ⟨graftP, fun _ => none, tmplT KC (fun _ => none)⟩

/-- `ℓ = 1`, `m = 2`. -/
abbrev ℓC : BoCa.Loc := 1
abbrev mC : BoCa.Loc := 2

theorem ℓC_ne_mC : ℓC ≠ mC := by decide

/-- The parent's resource: the lent cell. -/
def parentRes : TRes KC := ResUT.single ℓC (lendCell αC mC)

/-- The child's resource: the canonical image. -/
def childRes : TRes KC := viewRes βC mC

/-- The world's aliasable walk at `ℓ` and `m`: the lent cell, and the image. -/
theorem ag_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {a : TRes KC}
    (ha : AgWT W a) :
    a.get ℓC = some (lendCell αC mC) ∧ a.get mC = some (viewCell βC) := by
  obtain ⟨a₃, ac, ha₃, hac, hc⟩ := (AgWT.split hW).mp ha
  obtain rfl := ag_view hac
  obtain ⟨hl, hm⟩ := ag_lend ℓC_ne_mC ha₃
  refine ⟨(ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ ℓC_ne_mC)).trans hl, ?_⟩
  rcases ResUT.Comp.get hc mC with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, e, hC⟩
  · rw [hm] at f; cases f
  · rw [viewRes, ResUT.single_get_self] at f; cases f
  · rw [hm] at f; cases f
  · rw [hm] at f₁; cases Option.some.inj f₁
    rw [viewRes, ResUT.single_get_self] at f₂; cases Option.some.inj f₂
    rw [e, CellUT.CompR.functional hC (CellUT.CompR.ownImm _ _ _ _)]
    rfl

end BoCa.Fig16.Tree.Wp

end
