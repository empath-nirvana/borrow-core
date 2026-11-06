import Core.Chain.Shape791N

/-!
# `U` is not local along a lend under `ExtA`  `[spec §62]`

`docs/new-core/scope-791-loctype.md` §8, open question 1: is `U`'s Kripke order the world-relative
`LocTy.ExtA` or Core's resource-relative `Ext`? `vN_extA` holds at every type, `U` included
(`Goal791N`). Locality does not hold at `U` (`u_not_local`): a thunk valid at the world with a
lend at `α`, holding nothing, is not valid at the world without the lend.

The configuration. The world `Θ₁ = ∅ + (ℓ, α) ↦ F`; `α < b`; the thunk `λx. () ()` of type
`U(Mut @b 1 ⊸ F 1)` with the empty resource. Along `ExtA` from `Θ₁` nothing is added above `α`, so
no extension of `Θ₁` has a key at `b`, no `Mut @b 1` argument exists there, and the thunk is valid
at `Θ₁` (`thunk_at_lend`). From the empty world `ExtA` reaches `∅ + (ℓ′, b) ↦ 𝒱⟦1⟧`, where
`ℓ′ ↦ mut(b, (), ∅, 𝒱⟦1⟧)` is a `Mut @b 1` value, and the thunk applied to it is stuck
(`thunk_not_at_empty`).

Core's `Ext ls ls′ ρ` constrains only the records above the borrows of `ρ`; at the empty resource
it constrains nothing, so in Core a thunk valid at `Θ₁` is valid at every list, and the thunk
here is not a value at `Θ₁`. The obstruction is the order's, not the thunk's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LocalU791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.Shape791N (stuckV)
open BoCa.BoLo (Heap Step1 Head Kont)
open BoCa.Lifetime (LSub LifeVar)

/-- `U(Mut @x 1 ⊸ F 1)`. -/
def tyU (x : LifeVar) : VTy := .thunk (.arr (.mut (.var x) .unit) (.ret .unit))

/-- `𝒱⟦1⟧`, as a payload over the world. -/
def unitPL (δ : LSub) : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit δ Θ j u r

/-- **At the world with the lend, the thunk is valid**: no extension along `ExtA` has a key at
`b`, so the argument clause is vacuous. -/
theorem thunk_at_lend (x : LifeVar) (δ : LSub) {α b : Life} (hαb : α < b) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) (n : Nat) :
    vN (ℍ := ℍ) (tyU x) (δ.extend x b) (LocTy.empty.add l α F) n stuckV PMap.empty := by
  intro Θ' hE _ c _ ls Θ'' hE' _ c' k _ w ρv ρ' _ hv _
  exfalso
  obtain ⟨β, hβ, l', _, _, _, _, _, _, _, hl, _⟩ := hv
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  have E := LocTy.extA_trans hE hE'
  have habove := congrFun (congrFun (E.2 l α (by rw [LocTy.add_self]; simp)) l') b
  simp only [LocTy.above, if_pos hαb] at habove
  rw [habove, LocTy.add_keep _ _ _ _ (ne_of_gt hαb)] at hl
  cases hl

/-- **At the empty world, the thunk is not valid**: the extension `∅ + (ℓ′, b) ↦ 𝒱⟦1⟧` holds a
`Mut @b 1` argument, and the thunk applied to it is stuck after its β step. -/
theorem thunk_not_at_empty (x : LifeVar) (δ : LSub) {N b : Life} (hNb : N < b) (l' : Loc) :
    ¬ vN (ℍ := ℍ) (tyU x) (δ.extend x b) LocTy.empty 2 stuckV PMap.empty := by
  intro h
  let P := unitPL (ℍ := ℍ) (δ.extend x b)
  let Θ' := LocTy.empty.add l' b (famL b P LocTy.empty)
  have hfam : DownFam b (famL b P LocTy.empty) := vN_fam_down .unit _ b _
  have hOK : Θ'.OK := ⟨LocTy.down_add LocTy.empty_down l' hfam,
    ⟨N, LocTy.fresh_add (N := N) (fun _ _ h => absurd rfl h) le_rfl hNb l' _⟩⟩
  have hE : LocTy.empty.ExtA Θ' := LocTy.extA_add (fun _ _ h => absurd rfl h) l' _
  have hw : famL b P LocTy.empty 2 Val.unit ⟨PMap.empty, ResU.inStratum_empty b⟩ :=
    ⟨rfl, rfl⟩
  let cell : WRes := ResU.single l' (CellU.mutOf b Val.unit PMap.empty
    (ResU.inStratum_empty b) (famL b P LocTy.empty 2) hw)
  have hv : vN (ℍ := ℍ) (.mut (.var x) .unit) (δ.extend x b) Θ' 2 (Val.loc l') cell :=
    ⟨b, interp_ext_self δ x b, lend_mutL LocTy.empty l' b P le_rfl _ hw⟩
  have hexS : ExS cell cell := ExW.single_mut exW_empty (ResU.comp_empty_right _)
  let c' : Loc → Option Life := fun y => if y = l' then some b else none
  have hcons : ConsistentX c' cell := by
    intro e he y ψ hg _
    obtain rfl := ExS.functional he hexS
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some hg
    simp [c']
  have h2 := h Θ' hE hOK (fun _ => none) (consistentX_empty _) [] Θ' (LocTy.extA_refl _) hOK c'
    2 le_rfl (Val.loc l') cell cell (ResU.comp_empty_left _) hv hcons
  change erwp (ℍ := ℍ) _ _ _ 2 [] (.app stuckV.1 (.val (Val.loc l'))) cell at h2
  rw [erwp_eq] at h2
  -- the frame: the empty one; the world: `ℓ′ ↦ own(())` allocated, then lent at `b`
  have hvo : ResU.Valid (ResU.single l' (CellU.ownOf Val.unit)) := ResU.valid_single_own l' _
  have hvc : ResU.Valid cell := ResU.valid_single_mut_of_wit (compS_empty_left _) hvo
  have hT : TWNC cell [] (rsOf []) :=
    TWNC.mutFold (TWNC.alloc TWNC.empty lower_empty rfl (compS_empty_left _) hvo)
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _) hvc
  have htg : Tagged cell [] [] := fun y hy => absurd hy (by simp)
  obtain ⟨σm, hσm⟩ := hvc
  let μ : Heap := fun y => (σm.get y).map CellU.erase
  have hl : ResU.Lower cell μ := ⟨σm, hσm, fun _ => rfl⟩
  have hfd : FinDom μ := by
    obtain ⟨d, hd⟩ := σm.finite
    exact ⟨d, fun y hy => hd y (fun e => hy (by simp [μ, e]))⟩
  have hstep := (step1Only_plug (ℍ := ℍ) (Head.beta μ (.app .unit Val.unit.1) (Val.loc l')) rfl
    .hole).1
  have hbody : Kont.hole.plug (Expr.subst 0 (Val.loc l') (.app .unit Val.unit.1)) =
      Kont.hole.plug (.app .unit Val.unit.1) := by
    simp [Kont.plug, Expr.subst, Val.unit]
  rw [hbody] at hstep
  have hfin : Final (ℍ := ℍ) μ (Kont.hole.plug (.app .unit Val.unit.1)) :=
    fun _ _ hs => stuck_no_step (stuckAt_unit_app Val.unit) .hole hs
  have hE2 := h2 PMap.empty cell [] μ (ResU.hash_symm (ResU.hash_empty_right ⟨σm, hσm⟩))
    (ResU.comp_empty_left _) hT htg hl hfd 1 _ _ (by omega) (.more hstep (.refl _ _)) hfin
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := hE2
  rcases hq with ⟨v, hv, -⟩ | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · have : IsVal (Kont.hole.plug (.app .unit Val.unit.1)) := hv ▸ v.2
    exact (stuckAt_unit_app (ℍ := ℍ) Val.unit).not_val this
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

/-- **`U` is not local along a lend under `ExtA`.** A thunk holding nothing (so in every stratum)
is valid at the world with a lend at `α` and not at the world without it. -/
theorem u_not_local :
    ∃ (x : LifeVar) (δ : LSub) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α)
      (v : Val) (ρ : WRes), ρ.InStratum α ∧
      vN (ℍ := ℍ) (tyU x) δ (LocTy.empty.add l α F) 2 v ρ ∧
      ¬ vN (ℍ := ℍ) (tyU x) δ LocTy.empty 2 v ρ := by
  let α : Life := OrderDual.toDual 2
  let b : Life := OrderDual.toDual 1
  have hαb : α < b := OrderDual.toDual_lt_toDual.mpr (by decide)
  exact ⟨0, LSub.empty.extend 0 b, 0, α, fun _ _ _ => True, stuckV, PMap.empty,
    ResU.inStratum_empty α, thunk_at_lend 0 _ hαb 0 _ 2, thunk_not_at_empty 0 _ hαb 1⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.LocalU791

end
