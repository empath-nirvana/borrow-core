import Core.Chain.SliceKW835N
import Core.Chain.FamCancel836N

/-!
# The #791 constants at the typed world  `[spec §62]`

`ConstN₀`, `ConstsN₀` and `FundamentalN₀` at `SemJN`: a constant is a value of `!` its type at
`vN`, and the fundamental property is read at `SemJN`. Each constant's `constN_*` is the
compatibility lemma at `cN` (`withbor2S_compat`, `withbor3S_compat`, `withborFS_compat`,
`withloadS_compat`, `sliceBorrowMS_compat`), its finaliser's judgment read by the fundamental
property; `constsN_of` gathers them. The instances at the hardest case's row discharge every
hypothesis of each compatibility lemma, the finalisers read at `SemJN` (`dFree_sem`,
`dRelease_sem`, `dArrFree_sem`).
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
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 defines_meetOfDom_empty withborFSTy withborFV)
open BoCa.BoLo (Head Kont performE opPayload freeE)
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (noOwn_single_mut)

/-! ### The constants' statements at `SemJN` -/

/-- **A #791 constant is a value of `!` its type at the typed world**, at every `δ`, world and
index, from its rule's premises (`ConstN₀` at `vN`). -/
def ConstN (c : Const791) : Prop :=
  c.OK → ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Θ.OK →
    vN (ℍ := ℍ) (.bang c.ty) δ Θ n c.val PMap.empty

/-- Every #791 constant inside the fragment, at the typed world (`ConstsN₀` at `vN`). -/
def ConstsN : Prop := ∀ c : Const791, c.InFrag → ConstN (ℍ := ℍ) c

/-- **The fundamental property at the typed world, on the fragment** (`FundamentalN₀` at
`SemJN`): every derivation of the existing judgment whose context and type lie in the fragment. -/
def FundamentalN : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → JdgInFrag Γ j = true →
    SemJN (ℍ := ℍ) Δ Γ e j

/-! ### Each constant -/

/-- **`ConstN` for `withbor (2)` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_w2 (hF : FundamentalN (ℍ := ℍ)) {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hfr : (Const791.w2 x bnd A B S d).InFrag) :
    ConstN (ℍ := ℍ) (.w2 x bnd A B S d) := by
  rintro ⟨hbnd, hO, hA, hB, hS, hdc, hder⟩ δ Θ n _
  have hL : (VTy.ref A).inFrag = true := by
    simp_all [Const791.InFrag, Const791.ty, withbor2UTy, withborUTy, VTy.inFrag, CTy.inFrag]
  exact withbor2S_compat hbnd hO hA hB hS hdc (hF _ _ _ _ hder (jdgInFrag_lolli hL)) δ Θ n

/-- **`ConstN` for `withbor (3)` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_w3 (hF : FundamentalN (ℍ := ℍ)) {a : Lifetime.Life} {x : LifeVar}
    {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr}
    (hfr : (Const791.w3 a x bnd A B S d).InFrag) : ConstN (ℍ := ℍ) (.w3 a x bnd A B S d) := by
  rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
  have hL : (VTy.mut a A).inFrag = true := by
    simp_all [Const791.InFrag, Const791.ty, withbor3UTy, withborUTy, VTy.inFrag, CTy.inFrag]
  exact withbor3S_compat hbnd hA hB hS hdc (hF _ _ _ _ hder (jdgInFrag_lolli hL)) δ Θ n

/-- **`ConstN` for the field reborrow at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_wF (hF : FundamentalN (ℍ := ℍ)) {a : Lifetime.Life} {x : LifeVar}
    {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr}
    (hfr : (Const791.wF a x bnd A B S d).InFrag) : ConstN (ℍ := ℍ) (.wF a x bnd A B S d) := by
  rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
  have hL : (VTy.mut a (.ref A)).inFrag = true := by
    simp_all [Const791.InFrag, Const791.ty, withborFSTy, withborUTy, VTy.inFrag, CTy.inFrag]
  exact withborFS_compat hbnd hA hB hS hdc (hF _ _ _ _ hder (jdgInFrag_lolli hL)) δ Θ n

/-- **`ConstN` for `withload` at a suspending row**, from its rule's premises. -/
theorem constN_wl {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} : ConstN (ℍ := ℍ) (.wl a x bnd A B S) := by
  rintro ⟨hbnd, hA, hB, hS⟩ δ Θ n _
  exact withloadS_compat hbnd hA hB hS δ Θ n

/-- **`ConstN` for `slice_borrow_mut` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_sm (hF : FundamentalN (ℍ := ℍ)) {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hfr : (Const791.sm x bnd A B S d).InFrag) :
    ConstN (ℍ := ℍ) (.sm x bnd A B S d) := by
  rintro ⟨hbnd, hOA, hOB, hA, hB, hS, hdc, hder⟩ δ Θ n _
  have hL : (VTy.array A).inFrag = true := by
    simp_all [Const791.InFrag, Const791.ty, sliceBorrowMUTy, withborUTy, VTy.inFrag, CTy.inFrag]
  exact sliceBorrowMS_compat hbnd hOA hOB hA hB hS hdc (hF _ _ _ _ hder (jdgInFrag_lolli hL)) δ Θ n

/-- **`ConstsN` from the fundamental property at the typed world**: each of the five constants
inside the fragment, the finalisers' judgments read by the fundamental property. -/
theorem constsN_of (hF : FundamentalN (ℍ := ℍ)) : ConstsN (ℍ := ℍ)
  | .w2 .., hfr => constN_w2 hF hfr
  | .w3 .., hfr => constN_w3 hF hfr
  | .wF .., hfr => constN_wF hF hfr
  | .wl .., _ => constN_wl
  | .sm .., hfr => constN_sm hF hfr

/-! ### The finalisers at `SemJN` -/

/-- **`λr. ()` is a finaliser of a `Mut` source, at `SemJN`** (`dRelease_sem₀`). -/
theorem dRelease_sem (a : Lifetime.Life) (A : VTy) :
    SemJN (ℍ := ℍ) LifeCtx.empty [] dRelease (.val (.lolli (.mut a A) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dRelease = dRelease from psub_closedAt dRelease γ dRelease_closed le_rfl]
  refine cN_ret_of (erwp_val (v := Val.lam (.val .unit)) ?_)
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨_, _, _, _, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (.val .unit)).1 (.val (Val.loc l))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst, Val.unit, Expr.val]
  exact erwp_garbage (compS_empty_left _) (noOwn_single_mut l)
    (erwp_val (v := Val.unit) ⟨rfl, rfl⟩)

/-- **`λr. free r` is a finaliser of a `Ref 1` source, at `SemJN`** (`dFree_sem₀`). -/
theorem dFree_sem :
    SemJN (ℍ := ℍ) LifeCtx.empty [] dFree (.val (.lolli (.ref .unit) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dFree = dFree from psub_closedAt dFree γ dFree_closed le_rfl]
  refine cN_ret_of (erwp_val (v := Val.lam (freeE (.var 0))) ?_)
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, u, σ, rfl, hcl, rfl, rfl⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  refine cN_ret_of ?_
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

/-- **`λa. drop (λu. (), a)` is a finaliser of an `Array 1` source, at `SemJN`**
(`dArrFree_sem₀`): the cells are freed in order by `dropFill` (`dropFill_wpN`). -/
theorem dArrFree_sem :
    SemJN (ℍ := ℍ) LifeCtx.empty [] dArrFree (.val (.lolli (.array .unit) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dArrFree = dArrFree from psub_closedAt dArrFree γ dArrFree_closed le_rfl]
  refine cN_ret_of
    (erwp_val (v := Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))) ?_)
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv hcon
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, cn, rfl, -, hs⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) .unit δ Θ'' k v ρ) :=
    fun k _ v ρ h => vN_down _ _ _ k v ρ h
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))).1
      (.val (Val.arr l cn))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.arr l cn)
      (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))) =
      Kont.hole.plug (.app (.val (.prim .drop)) (.val (Val.pair dropU (Val.arr l cn)))) := by
    simp [Kont.plug, Expr.subst, dropU, Val.pair, Val.lam, Val.unit, Expr.val, Val.prim]
  rw [e]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
    (fun μ => step1Only_plug (Head.drop μ dropU l cn) rfl .hole) ?_
  exact dropFill_wpN hOK dropU l (dropU_sem δ Θ'' k) cn.toNat 0 k ls' ρ' c'' le_rfl hcon
    (by simpa using hs)

/-! ### The constants at the hardest case's row -/

/-- **`withbor (2)` at the hardest case's row, at `vN`**, every hypothesis of `withbor2S_compat`
discharged: `Ref 1` lent at the bound `LifeCtx.empty.meetOfDom`, finalised by `dFree`. -/
theorem withbor2S_inst (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor2UTy x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dFree) PMap.empty :=
  withbor2S_compat defines_meetOfDom_empty
    ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id (hardestRow_suspend x _) dFree_closed dFree_sem δ Θ n

/-- **`withbor (3)` at the hardest case's row, at `vN`**, every hypothesis of `withbor3S_compat`
discharged: a `Mut @a 1` source reborrowed, finalised by `dRelease`. -/
theorem withbor3S_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor3UTy a x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dRelease) PMap.empty :=
  withbor3S_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) dRelease_closed
    (dRelease_sem a .unit) δ Θ n

/-- **The field reborrow at the hardest case's row, at `vN`**, every hypothesis of
`withborFS_compat` discharged: a `Mut @a (Ref 1)` source, its field reborrowed, finalised by
`dRelease`. -/
theorem withborFS_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withborFSTy a x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborFV dRelease) PMap.empty :=
  withborFS_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) dRelease_closed
    (dRelease_sem a (.ref .unit)) δ Θ n

/-- **`withload` at the hardest case's row, at `vN`**, every hypothesis of `withloadS_compat`
discharged: an `Imm @a 1` source at the bound `LifeCtx.empty.meetOfDom`. -/
theorem withloadS_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withloadUTy a x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      withloadV PMap.empty :=
  withloadS_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) δ Θ n

/-- **`ConstN` at the hardest case's `withload`, at `vN`**, its antecedent discharged
(`wl_ok`). -/
theorem constN_wl_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat)
    (hΘ : Θ.OK) :
    vN (ℍ := ℍ) (.bang (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).ty) δ Θ n
      (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).val PMap.empty :=
  constN_wl (wl_ok a x) δ Θ n hΘ

/-- **`slice_borrow_mut` at the hardest case's row, at `vN`**, every hypothesis of
`sliceBorrowMS_compat` discharged: an `Array 1` lent cell by cell at the bound
`LifeCtx.empty.meetOfDom`, finalised by `dArrFree`. -/
theorem sliceBorrowMS_inst (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (sliceBorrowMUTy x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dArrFree) PMap.empty :=
  sliceBorrowMS_compat defines_meetOfDom_empty ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩
    ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id (hardestRow_suspend x _) dArrFree_closed
    dArrFree_sem δ Θ n

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
