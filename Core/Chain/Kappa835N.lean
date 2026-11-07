import Core.Chain.ExtRLit791
import Core.Chain.SI.HandleN
import Core.Chain.Cancel791N

/-!
# `κ` read at `vN`: Core's `vC_kTy_of_kapRel` at the chain  `[spec §19, §27]`

`docs/new-core/scope-831-interface.md` §10.1, E10. Core's handler (`ewp_handle_vals`,
`Core/EffFin.lean`) hands each clause `κ` with `KapRel` at the stop's list and reads it at `κ`'s
type `kTy Σ R q B F` by `vC_kTy_of_kapRel`: `KapRel` is Kripke along `Ext` from the stop's list,
which is `vC`'s `U` at that list, since one world, the record list, indexes both. At the chain the
clause gets `KapRelN` (`SI/HandleN.lean`): the handled continuation owed at the run's view `Θ.view
c`, at the tables read at `Θ` and `c`, and along `extF` from the stop's list. `vN`'s `U` clause at
`kTy` asks it at every `Θ′` with `Θ.ExtR Θ′ ρ`, every view consistent with `κ`'s share, and every
list.

The answer type `Mut 'x 1` at the stuck `κ = ()` (`bMut`, `kTyC`, `kTy_eq`): no `Mut` value
exists at the empty world. The world `∅ + (ℓ′, α) ↦ 𝒱⟦1⟧` (`Θ₁`) is an `ExtA` extension, so `U`
reaches it; it holds the answer `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `κ` applied to it is stuck from the
typed world of two cells (`ExtRLit791.world_two`). `kTy`'s value at the stuck thunk fails at every
world `U` reaches that world from, at a view putting `ℓ′` at `α` (`not_kTy_at`, `not_kTy_of_extR`,
`Core/Chain/ConfigsKW835N.lean`).

`ExtRFoldTransfer` is what a stop's share made Kripke along `ExtR` (route 2) asks of the Mut
Frame's fold: the borrowed continuation's share holds the lent cell `mut` at `A`, the lender's holds
it folded to `own`. `not_extRFoldTransfer`: `ExtR` at the lender's share admits a key added above
`A`, which `ExtR` at the borrowed share refuses. It is `SI/ExtF.lean`'s `not_extFoldTransfer` (D8)
at the world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Lifetime (LSub LifeVar)

/-! ### Core's step at the chain -/

/-- The answer type of the configurations: `Mut 'x 1`. -/
abbrev bMut (x : LifeVar) : VTy := .mut (.var x) .unit

/-- `κ`'s type at a must-resume operation answering `Mut 'x 1`, at the empty row answering `1`:
`U((Mut 'x 1 ⊸ F 1) & ⊤)`. -/
abbrev kTyC (x : LifeVar) : CTy := .amp (.arr (bMut x) (CTy.effOf [] .unit)) .top

theorem kTy_eq (x : LifeVar) : kTy [] .unit .lin (bMut x) (.ret .unit) = .thunk (kTyC x) := rfl

/-! ### Route 2 at the Mut Frame's fold -/

/-- The configuration of a Mut Frame's fold at the world: `ExtR` at the lender's share (the lent
cell folded to `own`) from `Θ` to `Θ′` gives `ExtR` at the borrowed continuation's share (the cell
`mut` at `A`) from the lend's world `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`. -/
def ExtRFoldTransfer : Prop :=
  ∀ (Θ Θ' : LocTy) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (v : Val),
    Θ.OK → Θ'.OK → Θ.Fresh A → Θ'.Fresh A → Θ.ExtR Θ' (ResU.single l (CellU.ownOf v)) →
    (Θ.add l A F).ExtR (Θ'.add l A F)
      (ResU.single l (CellU.mutOf A v PMap.empty (ResU.inStratum_empty A) (fun _ _ => True) trivial))

/-- **`ExtR` is not carried across a fold**: a key added above the lend's lifetime is admitted at the
lender's share, which holds no borrow cell, and refused at the borrowed continuation's share, whose
cell at `A` asks that nothing be added above `A`. -/
theorem not_extRFoldTransfer : ¬ ExtRFoldTransfer := by
  intro h
  let A : Life := OrderDual.toDual 1
  let β : Life := OrderDual.toDual 0
  have hAβ : A < β := OrderDual.toDual_lt_toDual.mpr (by decide)
  let G : Nat → Val → SPropS Loc Val β := fun _ _ _ => True
  have hG : DownFam β G := fun _ _ _ _ => trivial
  let Θ' : LocTy := LocTy.empty.add 1 β G
  have hfr : Θ'.Fresh A := LocTy.fresh_add (N := A) (fun _ _ h => absurd rfl h) le_rfl hAβ 1 G
  have hOK : Θ'.OK := ⟨LocTy.down_add LocTy.empty_down 1 hG, ⟨A, hfr⟩⟩
  let F : Nat → Val → SPropS Loc Val A := fun _ _ _ => True
  have hE : LocTy.empty.ExtR Θ' (ResU.single 0 (CellU.ownOf Val.unit)) :=
    ⟨fun _ _ _ hF _ => by simp at hF, fun _ hx _ => by simp at hx⟩
  have h' := (h LocTy.empty Θ' 0 A F Val.unit LocTy.empty_ok hOK (fun _ _ h => absurd rfl h) hfr
    hE).1 0 A F (LocTy.add_self _ _ _ _)
    ⟨0, _, ResU.single_get_self _ _, by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c,
      by rw [CellU.at_mutOf]⟩
  have h₁ := congrArg (fun Θ : LocTy => Θ 1 β) h'.2
  have hβA : β ≠ A := ne_of_gt hAβ
  simp only [LocTy.above_apply, if_pos hAβ, LocTy.add_keep _ _ _ _ hβA, Θ'] at h₁
  rw [LocTy.add_self] at h₁
  simp at h₁

end BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N

end
