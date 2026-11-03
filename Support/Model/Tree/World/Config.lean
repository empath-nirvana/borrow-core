import Support.Model.Tree.World.FdEsc
import Support.Model.Tree.CarrierGraftEx

/-!
# The escrow's frame condition and the cactus invariant

`FdEsc ℓ R Y` (`TreeWp/ImmEndEsc.lean`) is what `immEnd` asks of the rest of the world: `Y`'s
flattening holds nothing at the lent location `ℓ` nor at any location of `ex(R)`. At a join's
resume of the task owning the record, `Y` is the other branches.

**The configuration** (`cactusT_config`). Two branches: the parent, at its lend `α`, holds
`ℓ ↦ imm({α}, loc m, m ↦ own(()))` and owns the record; a child, at `β ⊏ α`, holds the record's
canonical image `m ↦ imm({β}, (), ∅)` and owns nothing. Every clause of `CactusInvT` holds: the
world is the branches' composition, the records proper are the parent's, `RecInv` (a `TWNT`
world at the world's choice, tagged at `α`), `WInv` (covered, lowering to the memory
`ℓ ↦ loc m, m ↦ ()`), and each branch is at its point. The child fails `FdEsc` at `m`
(`cactusT_not_fdEsc`). This is program (b) after a child reborrows the parent's `imm` lend and
before the join.

**What excludes it at a join is the points.** A join resuming the parent reads `JoinPtT`: no
other branch's point is inside the parent's lend. The child's point is `β ⊑ α`
(`config_not_joinPt`), and every point the child's resource sits on is inside `α`
(`config_branch_inside`): its image is at `β ⊑ α`, as `RebRecLeT` makes every image of a lineage
location. Without points (`CactusInvT` before this round) nothing excluded the configuration.

`FdEscOfBranchT` states `FdEsc` from `TWNT`, the frame's lifetime, a branch point the rest's top
cells sit on, and that point not inside the frame: `joinFd_of_branch`'s hypotheses
(`tree-life`) read at `FdEsc` and at the top cells (the strata carry a top cell's branch to every
cell beneath it).
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
