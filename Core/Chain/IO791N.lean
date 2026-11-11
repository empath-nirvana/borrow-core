import Core.Chain.Externs791N
import Core.Chain.Nest844N

/-!
# #791's end goal at a lent capability cell, resumed and cancelled  `[spec §72]`

`docs/new-core/scope-host-externs.md` §6.1, §7 (K1.4). `prog791` with the lent cell `stdout`'s:

    handle_wait (
      o ← mk_output 1;
      (o, u) ← withbor o (Λ'0. λm. m ← write_byte [] (m, 'h'); wait (); m ← write_byte [] (m, 'i');
                                    release m; ['0] ());
      u; consume (take_output o))
    with H

* `ioC`: `withbor (2)` over `Ref Output` at the row `[wait]`, `wait : 1 ↠^cancel 1`, finalised by
  `dTakeOutput`, the cell handed back to the host by `take_output`; `ioC_okAt` is
  `Const791.OKAt` at the externs' context `ioX` (`take_output`, `mk_output`, `write_byte`).
* The callback captures `write_byte` and writes through its borrow on both sides of `wait`.
* The handler of `wait` is inside the program. `clRes` resumes `κ` in tail position; `clCan`
  cancels it, and the lend's frame runs the finaliser on the cell (`erwp_kappaC_cancel`).
* `progIO_res_orDiverges`, `progIO_can_orDiverges`: `goal791N` at the externs given their models
  (`externsMeetN_of_model`), from `HandlerLawN` alone.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.IO791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 defines_meetOfDom_empty ansC_of_suspend)
open BoCa.BoLo (performE)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV)
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N (goal791N HandlerLawN dTakeOutput consumable_outRep
  externsMeetN_of_model ExternsMeetN)
open BoCa.Fig16.LogRel.Core.Chain.SI.Nest844N (callbackCapU ctxOwnFree_of hnd letpairW appVW seqCW)

/-! ### The externs, the row and the constant -/

/-- `Output`. -/
abbrev OutT : VTy := .opq .output

/-- The externs' context: `take_output`, `mk_output`, `write_byte`.  `[spec §72]` -/
abbrev ioX : Ctx VTy :=
  [⟨externTy (takeOutputC OutT), true⟩, ⟨externTy (mkOutputC OutT), true⟩,
    ⟨externTy (writeByteC OutT), true⟩]

/-- The externs' models, in `ioX`'s order. -/
abbrev ioγ : List Val := [takeCapV, mkOutputV, writeByteV]

/-- `wait : 1 ↠^cancel 1`, the operation `0` of the name `7`, its cancel row `F 1`. -/
abbrev ioE : List (Qual × VTy × VTy) := [(.cancel, .unit, .unit)]
/-- The name of `wait`. -/
abbrev ioN : UInt32 := 7
/-- `wait`'s signature. -/
def ioSig : OpSig := ⟨ioN, 0, .cancel, .unit, .unit, .ret .unit, false⟩
/-- The callback's row, and the handled row. -/
abbrev ioRow : Row := [ioSig]

theorem ioRow_eq : Row.ofEff ioN ioE 0 ++ [] = ioRow := rfl

theorem ioRow_suspend (Δ : LifeCtx) (x : LifeVar) (bnd : Lifetime.Life) :
    ioRow.Suspend Δ x bnd := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨by simp [ioSig], by decide, id, id, .unit, .unit, fun _ => trivial⟩

theorem ioRow_not_unr : ¬ ioRow.Unr := by
  rintro ⟨o, ho, h⟩; simp only [List.mem_singleton] at ho; subst ho; cases h

/-- **The lend of the `Output` cell**: `withbor (2)` at `[wait]`, finalised by `take_output`.
`[spec §72]` -/
abbrev ioC : Const791 := .w2 0 LifeCtx.empty.meetOfDom OutT .unit ioRow dTakeOutput

/-- `dTakeOutput` at the externs' context: `take_output` is its slot `0`, the others unused. -/
theorem d_dTakeOutputX {Δ : LifeCtx} :
    CDerives Δ ioX dTakeOutput (.val (.lolli (.ref OutT) .unit)) :=
  .thunkV rfl (.lam (.ret (.lolliE (splitP_left_all _)
    (appP (.var (by csoloP)) (.bangE (.var (by csoloP))))
    (consume_wf consumable_outRep (kill_dead _)))))

/-- **`ioC` meets its rule's premises at the externs' context.**  `[spec §72]` -/
theorem ioC_okAt : ioC.OKAt LifeCtx.empty ioX :=
  ⟨defines_meetOfDom_empty, ⟨.top, fun _ _ => ⟨_, rfl⟩, .opq⟩, id, id, ioRow_suspend _ 0 _,
    ⟨_, defines_meetOfDom_empty, ansC_of_suspend (ioRow_suspend _ 0 _)⟩, by decide,
    d_dTakeOutputX⟩

/-! ### Splits that copy the externs -/

section
variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem bindQ {M N : Expr} {A : VTy} {C : CTy}
    (hM : CDerives Δ (partP M 0 Γ).1 M (.comp (.ret A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (partP M 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (bindE M N) (.comp C) :=
  .bind (partP_split M 0 Γ) hM hN

theorem effLetQ {M N : Expr} {A B : VTy} {S : Row}
    (hW : S.Cancels → (partP M 0 Γ).2.OwnFree) (hU : S.Unr → Ctx.Banged (partP M 0 Γ).2)
    (hM : CDerives Δ (partP M 0 Γ).1 M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (partP M 0 Γ).2) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (bindE M N) (.comp (CTy.effOf S B)) :=
  .effLet (partP_split M 0 Γ) hW hU hM hN

theorem seqQ {V M : Expr} {C : CTy} (hV : CDerives Δ (partP V 0 Γ).1 V (.val .unit))
    (hM : CDerives Δ (partP V 0 Γ).2 M (.comp C)) : CDerives Δ Γ (.seq V M) (.comp C) :=
  .unitE (partP_split V 0 Γ) hV hM

theorem letpairQ {V M : Expr} {A B : VTy} {C : CTy}
    (hV : CDerives Δ (partP V 0 Γ).1 V (.val (.tensor A B)))
    (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (partP V 0 Γ).2) M (.comp C)) :
    CDerives Δ Γ (.letpair V M) (.comp C) :=
  .tensorE (partP_split V 0 Γ) hV hM

theorem appVQ {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hM : CDerives Δ (partP M 0 Γ).1 M (.comp (.arr A C)))
    (hx : Ctx.SoloP (partP M 0 Γ).2 i A) : CDerives Δ Γ (.app M (.var i)) (.comp C) :=
  .app (partP_split M 0 Γ) hM hx

end

/-! ### The callback -/

/-- The byte `n`. -/
def u8E (n : UInt8) : Expr := .val ⟨.prim (.lit (.u8 n)), .prim⟩

/-- `write_byte [] (m, b)`, `write_byte` at slot `wb`, the borrow at slot `m`. -/
def wbE (wb m : Nat) (b : UInt8) : Expr := .app (.app (.var wb) (.val .unit)) (.pair (.var m) (u8E b))

/-- The callback: `Λ'0. λm. m ← write_byte [] (m, 'h'); wait (); m ← write_byte [] (m, 'i');
release m; ['0] ()`, in the context `o, ioC, take_output, mk_output, write_byte`. -/
def cbIO : Expr :=
  .val (.lam (.val (.lam
    (bindE (wbE 6 0 104)
      (bindE (performE (opArgE ioN 0 (.val .unit)))
        (.seq (.var 0)
          (bindE (wbE 8 1 105)
            (.seq (.app forget (.var 0)) (.val .unit)))))))))

/-- The callback's lifetime context: `'0 ⊏ ⊓∅`. -/
abbrev Δcb : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

theorem Δcb_lt_top : Δcb.EntailsLt (.var 0) .top :=
  BoCa.Programs.entailsLt_of_bound (u := LifeCtx.empty.meetOfDom) rfl
    (fun _ _ h => ⟨_, h, le_rfl⟩)

/-- `write_byte [] (m, b) : Mut '0 Output`, at every context where `m` is the borrow's only live
non-persistent slot and `write_byte` is live. -/
theorem d_wbE {Γ : Ctx VTy} {wb m : Nat} (b : UInt8)
    (hm : Ctx.SoloP (partP (.var m) 0 (partP (.pair (.var m) (u8E b)) 0 Γ).1).1 m
      (.mut (.var 0) OutT))
    (hl : Ctx.DeadP (partP (.var m) 0 (partP (.pair (.var m) (u8E b)) 0 Γ).1).2)
    (hw : Ctx.SoloP (partP (.pair (.var m) (u8E b)) 0 Γ).2 wb (externTy (writeByteC OutT))) :
    CDerives Δcb Γ (wbE wb m b) (.val (.mut (.var 0) OutT)) := by
  refine appP (A := .tensor (.mut (.var 0) OutT) (.int .w8)) (pairP (.var hm) (.lit (.u8 b) hl)) ?_
  have h := CDerives.allEV (Δ := Δcb) (a := .var 0)
    (CDerives.bangE (A := VTy.all 0 .top
      (.lolli (.tensor (.mut (.var 0) OutT) (.int .w8)) (.mut (.var 0) OutT))) (.var hw)) Δcb_lt_top
  rwa [show (VTy.lolli (.tensor (.mut (.var 0) OutT) (.int .w8)) (.mut (.var 0) OutT)).instLife 0
    (.var 0) = .lolli (.tensor (.mut (.var 0) OutT) (.int .w8)) (.mut (.var 0) OutT) by decide] at h

/-- The callback's type. -/
abbrev cbIOTy : VTy := cbUTy 0 LifeCtx.empty.meetOfDom (.mut (.var 0) OutT) .unit ioRow

/-- The context the callback is typed in: `o` dead, `ioC` and the externs live. -/
abbrev Γcb : Ctx VTy := ⟨.ref OutT, false⟩ :: ctx791 [ioC] ++ ioX

theorem d_cbIO : CDerives LifeCtx.empty Γcb cbIO (.val cbIOTy) := by
  refine callbackCapU rfl (fun y u h => ?_) (fun s hs hl => ?_) ?_
  · simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  · simp only [Γcb, ctx791, List.map, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact absurd hl Bool.false_ne_true
    all_goals simp [VFree, CFree, Const791.ty, withbor2UTy, withborUTy, cbUTy,
      takeOutputC, mkOutputC, writeByteC, outRep, bytesTy, bytesBody, CTy.effOf, ioSig,
      Lifetime.Life.mentions]
    all_goals decide
  refine bindQ (.ret (d_wbE 104 (by csoloP) (by cdeadP) (by csoloP))) ?_
  refine effLetQ (fun _ => ctxOwnFree_of rfl) (fun h => absurd h ioRow_not_unr)
    (.effPerform (o := ioSig) rfl rfl rfl (.unitI (by cdeadP))) ?_
  refine seqQ (.var (by csoloP)) ?_
  refine bindQ (.ret (d_wbE 105 (by csoloP) (by cdeadP) (by csoloP))) ?_
  refine .unitE (splitP_left_all _) (appP (.var (by csoloP)) (.releaseMut (by cdeadP))) ?_
  exact .effSub (S := []) (RowLe.nil _) (.ret (.boxI (.unitI (kill_dead _).toP)
    ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
      dead_noLive (P := fun s => VOutlives _ _ s.ty) (kill_dead _) s hs hl⟩))

/-! ### The handled body, the clauses and the programs -/

/-- The handled body: `o ← mk_output 1; cb; w ← ioC; (o, u) ← w o cb; u;
consume (take_output o)`. -/
def bodyIO : Expr :=
  bindE (.app (.var 2) (i32E 1))
    (bindE cbIO
      (bindE (.var 2)
        (bindE (.app (.app (.var 0) (.var 2)) (.var 1))
          (.letpair (.var 0) (.seq (.var 0)
            (.app (consumeE outRep) (.app (.var 7) (.var 1))))))))

theorem d_bodyIO :
    CDerives LifeCtx.empty (ctx791 [ioC] ++ ioX) bodyIO (.comp (CTy.effOf ioRow .unit)) := by
  refine bindQ (A := .ref OutT)
    (.ret (appP (.lit (.i32 1) (by cdeadP)) (.bangE (.var (by csoloP))))) ?_
  refine bindQ (.ret d_cbIO) ?_
  refine bindQ (.ret (.bangE (.var (by csoloP)))) ?_
  refine effLetQ (A := .tensor (.ref OutT) .unit) (fun _ => ctxOwnFree_of rfl)
    (fun h => absurd h ioRow_not_unr)
    (appVQ (appVQ (.force (T := .thunk _) (C := .arr (.ref OutT) (.arr cbIOTy
      (CTy.effOf ioRow (.tensor (.ref OutT) .unit))))  ?_ rfl) ?_) ?_) ?_
  · csoloP
  · csoloP
  · csoloP
  refine letpairQ (.var (by csoloP)) (seqQ (.var (by csoloP)) ?_)
  exact .effSub (S := []) (RowLe.nil _) (.ret (.lolliE (A := outRep) (splitP_left_all _)
    (appP (A := .ref OutT) (.var (by csoloP))
      (.bangE (A := .lolli (.ref OutT) outRep) (.var (by csoloP))))
    (consume_wf consumable_outRep (kill_dead _))))

/-- The clauses' type at the handler of `wait`. -/
abbrev clTy : VTy := clauseTy [] .unit (.cancel, .unit, .unit) (.ret .unit)

/-- The resuming clause: `λp. let (a, κ) = p; κ (inj₁ ()) a`, `κ` resumed in tail position. -/
def clRes : Val := Val.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ Val.unit))) (.var 1)))

/-- The cancelling clause: `λp. let (a, κ) = p; a; κ (inj₂ ())`. -/
def clCan : Val := Val.lam (.letpair (.var 0) (.seq (.var 1) (.app (.var 0) (.val (Val.inj₂ Val.unit)))))

theorem d_clRes {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val clRes) (.val clTy) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine letpairW (.var (by csolo)) ?_
  exact appVW (.proj₁ (.force (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf [] .unit)) (.ret .unit))
    (by csolo) rfl)) (by csolo)

theorem d_clCan {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val clCan) (.val clTy) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine letpairW (.var (by csolo)) ?_
  exact seqCW (.var (by csolo))
    (.proj₂ (.force (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf [] .unit)) (.ret .unit)) (by csolo) rfl))

/-- **The program** at the clause `cl`: `handle_wait bodyIO with (λx. x, cl)`.  `[spec §72]` -/
def progIO (cl : Val) : Expr := hndExpr ioN (ioE.map Prod.fst) (hnd cl) bodyIO

theorem d_progIO {cl : Val} (hcl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ (.val cl) (.val clTy)) :
    CDerives LifeCtx.empty (ctx791 [ioC] ++ ioX) (progIO cl) (.comp (.ret .unit)) :=
  .effHandleV (cs := rcsNil) (E := ioE) (fs := finsNil) (S := []) (A := .unit)
    (splitP_right_all _) (kill_dead _).toP (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI (deadSplit (kill_dead _)) (CancelIntercept.d_idVΓ (kill_dead _) [] .unit)
      (.tensorI (deadSplit (kill_dead _)) (hcl (kill_dead _)) (.unitI (kill_dead _).toP)))
    (by decide) (by simp) (by simp) rfl d_bodyIO

/-- **The resumed program**: the handler of `wait` resumes `κ` in tail position. -/
def progIO_res : Expr := progIO clRes

/-- **The cancelled program**: the handler of `wait` cancels `κ`; the lend's finaliser hands the
cell back to the host by `take_output`. -/
def progIO_can : Expr := progIO clCan

/-! ### `Goal791N` at the two programs -/

/-- The externs, each given its model, meet their contracts. -/
theorem ioX_meetsN (h : HandlerLawN (ℍ := ℍ)) : ExternsMeetN (ℍ := ℍ) ioX ioγ :=
  externsMeetN_of_model h (Γ := ioX) (γ := ioγ)
    (.cons ⟨rfl, by simp [stdModel]⟩ (.cons ⟨rfl, by simp [stdModel]⟩
      (.cons ⟨rfl, by simp [stdModel]⟩ .nil)))

/-- **`Goal791N` at `progIO_res`**: the run that writes through a lent `Output` cell across `wait`
and resumes is safe, ends at the empty memory, or diverges, from `HandlerLawN`, the externs given
their models.  `[spec §72]` -/
theorem progIO_res_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll ([ioC].map (fun c => c.valAt ioγ) ++ ioγ) progIO_res) :=
  goal791N h [ioC] ioX ioγ progIO_res .unit (by simpa using ioC_okAt) (ioX_meetsN h)
    (d_progIO fun h => d_clRes h) rfl

/-- **`Goal791N` at `progIO_can`**: the run that writes through a lent `Output` cell, is cancelled
at `wait`, and has the cell taken back by the lend's finaliser is safe, ends at the empty memory,
or diverges, from `HandlerLawN`, the externs given their models.  `[spec §72]` -/
theorem progIO_can_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll ([ioC].map (fun c => c.valAt ioγ) ++ ioγ) progIO_can) :=
  goal791N h [ioC] ioX ioγ progIO_can .unit (by simpa using ioC_okAt) (ioX_meetsN h)
    (d_progIO fun h => d_clCan h) rfl

end BoCa.Fig16.LogRel.Core.Chain.SI.IO791N

end
