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

/-! ### A callback that performs while holding the borrow -/

/-- **A callback of the suspending lend that performs while holding the borrow, at `vN`**
(`cbPerform_sem₀`): `cbPerform` is a value of `∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] 1)` at the
one-operation row `[linSig n i]`. Its stop is taken at the floor of its world, with the borrow in
the continuation's share; at every world the entry owes, the answer `()` returns `['x] ()` with the
borrow left as garbage. -/
theorem cbPerform_sem {x : LifeVar} {bnd : Lifetime.Life} {A : VTy} {δ : LSub} (n i : UInt32)
    (Θ : LocTy) (k₀ : Nat) :
    vN (ℍ := ℍ) (cbUTy x bnd (.mut (.var x) A) .unit [linSig n i]) δ Θ k₀ (cbPerform n i)
      PMap.empty := by
  intro Θ'' _ hOK c _ ls
  refine fun α _ c' k _ v ρv ρ' hc hv _ => ?_
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨β, hβ, b, -, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hv
  rw [cN_effOf]
  intro lo
  have hΦ := LocTy.view_down hOK.1 c'
  have hTd : (opTableK lo (tabN (ℍ := ℍ) (CTy.effOf [linSig n i] (.box (.var x) .unit))
      (δ.extend x α) (⟨Θ'', c', lo⟩ : KW))).Down :=
    opTableK_downI (tabN_downI_OK _ _ _)
  have hQ : ∀ z : KW, PostN.Down
      (fun k _ v ρ => vN (ℍ := ℍ) (.box (.var x) .unit) (δ.extend x α) z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down _ _ _ k v ρ h
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := (⟨Θ'', c', lo⟩ : KW)) hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl (.appL .hole (Val.loc l))) ?_
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := (⟨Θ'', c', lo⟩ : KW)) hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have hcl : closedAt 0 (performE (.val (opPayload n i Val.unit))) = true := by
    simp [closedAt, performE, opPayload, Val.unit, Val.i32]
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
        (performE (.val (opPayload n i Val.unit))))) =
      Kont.hole.plug (performE (.val (opPayload n i Val.unit))) := by
    rw [subst_closedAt _ _ hcl (Nat.zero_le _), subst_closedAt _ _ hcl (Nat.zero_le _)]
  rw [e]
  refine erwpK_performG (K := .hole) (by simp [Kont.HasHnd])
    (by simp [CTy.effOf, tabN, extTabK, linSig]; rfl) (by simp [entNK, linSig])
    (compS_empty_left _) (show vN (ℍ := ℍ) .unit (δ.extend x α) Θ'' k Val.unit PMap.empty from
      ⟨rfl, rfl⟩) (fun h => by simp [entNK, linSig] at h) lo le_rfl ?_
    (fun _ _ _ _ h => absurd (by simp [entNK, linSig]) h)
  intro y _ ls' _ k' _ w' τ₁ τ₂ hB hcτ
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hB
  obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hcτ)
  exact erwpK_garbage (compS_empty_left _) (noOwn_single_mut l)
    (erwpK_val (KW.postK_refl y)
      (v := Val.unit) ⟨α, interp_ext_self δ x α, ⟨rfl, rfl⟩, ResU.inStratum_empty α⟩)

/-- **`withbor (2)` applied to a cell and to `cbPerform`, at `cN`** (`withbor2S_perform₀`): at the
one-operation row `[linSig n i]`, `withborU dFree ℓ cbPerform` runs at `F_Σ(Ref 1 ⊗ 1)` from
`ℓ ↦ own(())`. The callback stops at the must-resume operation with the borrow of `ℓ` in the
continuation's share (`cbPerform_sem`); `withbor2S_compat` gives the rest. -/
theorem withbor2S_perform (x : LifeVar) {n i : UInt32} (hn : n ≠ 0) (δ : LSub) (Θ : LocTy)
    (hOK : Θ.OK) (c : Loc → Option Life) (k : Nat) (ls : List SRec) (l : Loc) :
    cN (ℍ := ℍ) (CTy.effOf [linSig n i] (.tensor (.ref .unit) .unit)) δ Θ c k ls
      (.app (.app (withborUV dFree).1 (.val (Val.loc l))) (.val (cbPerform n i)))
      (ResU.single l (CellU.ownOf Val.unit)) := by
  have hcon : ConsistentX c (ResU.single l (CellU.ownOf (Loc := Loc) Val.unit)) :=
    consistentX_of_top (ResU.inStratum_single_own _ l Val.unit) c
  have hv : vN (ℍ := ℍ) (.ref .unit) δ Θ k (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) :=
    ⟨l, Val.unit, PMap.empty, rfl, ResU.comp_empty_right _, rfl, rfl⟩
  have h := (withbor2S_compat (ℍ := ℍ) (A := .unit) (B := .unit) defines_meetOfDom_empty
    ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id (linSig_suspend (i := i) hn x _) dFree_closed dFree_sem
    δ Θ k).2 Θ (LocTy.extR_refl _ _) hOK c (consistentX_empty c) ls
  have h2 := h c k le_rfl (Val.loc l) _ _ (compS_empty_left _) hv hcon
  exact h2 c k le_rfl (cbPerform n i) PMap.empty _
    (ResU.comp_empty_right _) (cbPerform_sem n i Θ k) hcon

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
