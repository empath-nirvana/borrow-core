import Core.Chain.Field791N

/-!
# #791: the compatibility lemmas' hypotheses discharged  `[spec §62]`

`withbor2S_compat`, `withbor3S_compat` and `withborFS_compat` take the finaliser's semantic
judgment `hd` beside `Const791.OK`'s clauses. Here each is instantiated with every hypothesis
discharged, so none of them is vacuous:

* **The finalisers.** `dRelease = λr. ()` at `Mut @a A ⊸ 1` (`dRelease_sem`), the borrow left as
  garbage (Core's `releaseMut`); `dFree = λr. free r` at `Ref 1 ⊸ 1` (`dFree_sem`), the cell
  freed.
* **The constants at the hardest case's row** (`hardestRow`, `park` as `TJN` types it), the bound
  Core's rules fix at the empty context (`LifeCtx.empty.meetOfDom`): `withbor2S_inst`,
  `withbor3S_inst`, `withborFS_inst`.
* **A callback that performs an operation while holding the borrow** (`cbPerform_sem`):
  `λ_. λu. perform op ()` at a one-operation suspending row, the borrow live across the stop.

The finalisers are read semantically; `λr. ()` is not a `CDerives` term at `Mut @a A ⊸ 1` (the
judgment consumes a live `Mut` only through `forget`), so these instances discharge the compat
lemmas' hypotheses, not `Const791.OK`'s `CDerives` clause.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 defines_meetOfDom_empty)
open BoCa.BoLo (Head Kont performE opPayload freeE)
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (noOwn_single_mut)

/-! ### The finalisers -/

/-- `λr. ()`: the borrow left as garbage. -/
def dRelease : Expr := .val (Val.lam (.val .unit))

/-- `λr. free r`. -/
def dFree : Expr := .val (Val.lam (freeE (.var 0)))

theorem dRelease_closed : closedAt 0 dRelease = true := by decide

theorem dFree_closed : closedAt 0 dFree = true := by decide

/-- **`λr. ()` is a finaliser of a `Mut` source**: at `Mut @a A ⊸ 1`, every `a` and `A`. -/
theorem dRelease_sem (a : Lifetime.Life) (A : VTy) :
    SemJN (ℍ := ℍ) LifeCtx.empty [] dRelease (.val (.lolli (.mut a A) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dRelease = dRelease from psub_closedAt dRelease γ dRelease_closed le_rfl]
  refine erwp_val (v := Val.lam (.val .unit)) ?_
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨_, _, _, _, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (.val .unit)).1 (.val (Val.loc l))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst, Val.unit, Expr.val]
  exact erwp_garbage (compS_empty_left _) (noOwn_single_mut l)
    (erwp_val (v := Val.unit) ⟨rfl, rfl⟩)

/-- **`λr. free r` is a finaliser of a `Ref 1` source.** -/
theorem dFree_sem :
    SemJN (ℍ := ℍ) LifeCtx.empty [] dFree (.val (.lolli (.ref .unit) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dFree = dFree from psub_closedAt dFree γ dFree_closed le_rfl]
  refine erwp_val (v := Val.lam (freeE (.var 0))) ?_
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, u, σ, rfl, hcl, rfl, rfl⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (freeE (.var 0))).1 (.val (Val.loc l))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l) (freeE (.var 0))) =
      Kont.hole.plug (freeE (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, freeE]
  rw [e]
  refine erwp_free hΦ (opTableN_local _) .hole l Val.unit
    ⟨_, PMap.empty, hcl, rfl, erwp_val (v := Val.unit) ⟨rfl, rfl⟩⟩

/-! ### The constants at the hardest case's row -/

/-- **`withbor (2)` at the hardest case's row**, every hypothesis of `withbor2S_compat`
discharged: `Ref 1` lent at the bound `LifeCtx.empty.meetOfDom`, finalised by `dFree`. -/
theorem withbor2S_inst (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor2UTy x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dFree) PMap.empty :=
  withbor2S_compat defines_meetOfDom_empty
    ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id (hardestRow_suspend x _) dFree_closed dFree_sem δ Θ n

/-- **`withbor (3)` at the hardest case's row**, every hypothesis of `withbor3S_compat`
discharged: a `Mut @a 1` source reborrowed, finalised by `dRelease`. -/
theorem withbor3S_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor3UTy a x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dRelease) PMap.empty :=
  withbor3S_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) dRelease_closed
    (dRelease_sem a .unit) δ Θ n

/-- **The field reborrow at the hardest case's row**, every hypothesis of `withborFS_compat`
discharged: a `Mut @a (Ref 1)` source, its field reborrowed, finalised by `dRelease`. -/
theorem withborFS_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ)
      (.bang (BoCa.Fig16.Tree.Wp.Goal791.withborFSTy a x LifeCtx.empty.meetOfDom .unit .unit
        hardestRow)) δ Θ n (BoCa.Fig16.Tree.Wp.Goal791.withborFV dRelease) PMap.empty :=
  withborFS_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) dRelease_closed
    (dRelease_sem a (.ref .unit)) δ Θ n

/-! ### A callback that performs while holding the borrow -/

/-- A must-resume operation `1 ↠^lin 1`. -/
def linSig (n i : UInt32) : OpSig := ⟨n, i, .lin, .unit, .unit, .ret .unit, false⟩

theorem linSig_suspend {n i : UInt32} (hn : n ≠ 0) (x : LifeVar) (bnd : Lifetime.Life) :
    Row.Suspend [linSig n i] x bnd := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨by simp [linSig], hn, id, id, .unit, .unit, fun h => by simp [capB, linSig] at h⟩

/-- `λ_. λu. perform op ()`: the callback stops at `op` holding the borrow `u`, and answers with
the operation's answer, the borrow released (left as garbage) at the return. -/
def cbPerform (n i : UInt32) : Val :=
  Val.lam (.val (Val.lam (performE (.val (opPayload n i Val.unit)))))

/-- **A callback of the suspending lend that performs while holding the borrow**: `cbPerform` is
a value of `∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] 1)` at the one-operation row `[linSig n i]`. Its
stop is taken with the borrow in the continuation's share. -/
theorem cbPerform_sem {x : LifeVar} {bnd : Lifetime.Life} {A : VTy} {δ : LSub} (n i : UInt32)
    (Θ : LocTy) (k₀ : Nat) :
    vN (ℍ := ℍ) (cbUTy x bnd (.mut (.var x) A) .unit [linSig n i]) δ Θ k₀ (cbPerform n i)
      PMap.empty := by
  intro Θ'' _ hOK c _ ls
  refine fun α _ c' k _ v ρv ρ' hc hv _ => ?_
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨β, hβ, b, -, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c'
  rw [cN_effOf]
  have hTd := opTableN_down (tabN_down (ℍ := ℍ) (CTy.effOf [linSig n i] (.box (.var x) .unit))
    (δ.extend x α) Θ'' hOK.1 c')
  have hQ : PostN.Down
      (fun k _ v ρ => vN (ℍ := ℍ) (.box (.var x) .unit) (δ.extend x α) Θ'' k v ρ) :=
    fun k _ v ρ h => vN_down _ _ _ k v ρ h
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl (.appL .hole (Val.loc l))) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have hcl : closedAt 0 (performE (.val (opPayload n i Val.unit))) = true := by
    simp [closedAt, performE, opPayload, Val.unit, Val.i32]
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
        (performE (.val (opPayload n i Val.unit))))) =
      Kont.hole.plug (performE (.val (opPayload n i Val.unit))) := by
    rw [subst_closedAt _ _ hcl (Nat.zero_le _), subst_closedAt _ _ hcl (Nat.zero_le _)]
  rw [e]
  refine erwp_perform (T := tabN (ℍ := ℍ) (CTy.effOf [linSig n i] (.box (.var x) .unit))
      (δ.extend x α) Θ'' c')
      (en := entN .lin .unit (fun k v ρ => vN (ℍ := ℍ) .unit (δ.extend x α) Θ'' k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) .unit (δ.extend x α) Θ'' k v ρ)
        (finN (ℍ := ℍ) (.ret .unit) (δ.extend x α) Θ'' c')) .hole rfl
    (by simp [CTy.effOf, tabN, extTabN, linSig]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩ ?_
  intro ls' _ k' _ w' τ₁ τ₂ hB hcτ
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hcτ)
  exact erwp_garbage (compS_empty_left _) (noOwn_single_mut l)
    (erwp_val (v := Val.unit) ⟨α, interp_ext_self δ x α, ⟨rfl, rfl⟩, ResU.inStratum_empty α⟩)

/-! ### `Const791.OK` inhabited, finaliser judgment included -/

/-- **`w2`'s antecedent holds**, its finaliser `free : Ref 1 ⊸ 1` derived by `CDerives.free` at
the payload `1`. -/
theorem w2_ok (x : LifeVar) :
    (Const791.w2 x LifeCtx.empty.meetOfDom .unit .unit hardestRow (.val (.prim .free))).OK :=
  ⟨defines_meetOfDom_empty, ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩, id, id, hardestRow_suspend x _,
    rfl, .free .nil⟩

/-- `dRelease` is Core's `forget`. -/
theorem dRelease_eq_forget : dRelease = BoCa.forget := rfl

/-- **`w3`'s antecedent holds** at the instance's constant, its finaliser `dRelease`, Core's
`forget`, derived by `CDerives.releaseMut`. -/
theorem w3_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.w3 a x LifeCtx.empty.meetOfDom .unit .unit hardestRow dRelease).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend x _, dRelease_closed, .releaseMut .nil⟩

/-- **`wF`'s antecedent holds** at the instance's constant, its finaliser `dRelease` at
`Mut @a (Ref 1) ⊸ 1` derived by `CDerives.releaseMut`. -/
theorem wF_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.wF a x LifeCtx.empty.meetOfDom .unit .unit hardestRow dRelease).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend x _, dRelease_closed, .releaseMut .nil⟩

/-! ### The constant applied to a callback that performs while holding the borrow -/

/-- **`withbor (2)` applied to a cell and to `cbPerform`**: at the one-operation row
`[linSig n i]`, `withborU dFree ℓ cbPerform` runs at `F_Σ(Ref 1 ⊗ 1)` from `ℓ ↦ own(())`. The
callback stops at the must-resume operation with the borrow of `ℓ` in the continuation's share
(`cbPerform_sem`); `withbor2S_compat` gives the rest. -/
theorem withbor2S_perform (x : LifeVar) {n i : UInt32} (hn : n ≠ 0) (δ : LSub) (Θ : LocTy)
    (hOK : Θ.OK) (c : Loc → Option Life) (k : Nat) (ls : List SRec) (l : Loc) :
    cN (ℍ := ℍ) (CTy.effOf [linSig n i] (.tensor (.ref .unit) .unit)) δ Θ c k ls
      (.app (.app (withborUV dFree).1 (.val (Val.loc l))) (.val (cbPerform n i)))
      (ResU.single l (CellU.ownOf Val.unit)) := by
  have hcon : ConsistentX c (ResU.single l (CellU.ownOf (Loc := Loc) Val.unit)) :=
    consistentX_of_top (ResU.inStratum_single_own _ l Val.unit) c
  have hv : vN (ℍ := ℍ) (.ref .unit) δ Θ k (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) :=
    ⟨l, Val.unit, PMap.empty, rfl, ResU.comp_empty_right _, rfl, rfl⟩
  have h := (withbor2S_compat (ℍ := ℍ) (A := .unit) (B := .unit) defines_meetOfDom_empty ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩
    id id (linSig_suspend (i := i) hn x _) dFree_closed dFree_sem δ Θ k).2 Θ (LocTy.extR_refl _ _) hOK c
    (consistentX_empty c) ls
  have h2 := h c k le_rfl (Val.loc l) _ _ (compS_empty_left _) hv hcon
  exact h2 c k le_rfl (cbPerform n i) PMap.empty _
    (ResU.comp_empty_right _) (cbPerform_sem n i Θ k) hcon

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
