import Core.Chain.Adequacy791N

/-!
# A scalar loan from existing main rules (#1119, route (2))

The lend is `Const791.w2` at the suspending row `wait`. Its callback hands the borrow
`m : Mut 'x 1` to an inner handler as the payload of the linear operation `loan`
(`9.0 : Mut 'x 1 ↠ Mut 'x 1`). The handler's clause is a tail clause (`effHandleT`). Its
answering function `g = λp. wait (); p` runs a computation that suspends at the outer `wait` while
it holds `p`, then resumes `κ` with `p` itself. The callback releases the returned borrow, and the
lender takes the cell back. The program is typed by `CDerives` at the context of `w2`, so
`goal791N` concludes `OrDiverges`, as for `prog791`.
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
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 defines_meetOfDom_empty ansC_of_suspend)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free')
open BoCa.Fig16.LogRel.Core.EffPrograms (callbackUW)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV)

/-- The loan operation: `Mut 'x 1 ↠^lin Mut 'x 1`. -/
abbrev loanE : List (Qual × VTy × VTy) := [(.lin, .mut (.var 0) .unit, .mut (.var 0) .unit)]
abbrev loanN : UInt32 := 9
/-- The row the callback's body runs at: `loan`, then `wait`. -/
abbrev loanRow : Row := Row.ofEff loanN loanE 0 finsNil ++ waitRow
abbrev loanSig : OpSig := ⟨loanN, 0, .lin, .mut (.var 0) .unit, .mut (.var 0) .unit, .ret .unit, false⟩

/-- `loan m`. -/
def loanPerform : Expr := performE (opArgE loanN 0 (.var 0))

/-- The callback's body: `m' ← loan m; release m'; ['x] ()`. -/
def loanBody : Expr :=
  .app (.val (.lam (.seq (.app forget (.var 0)) (.val .unit)))) loanPerform

/-- The answering function: `λp. wait (); p`. -/
def loanG : Val := Val.lam (.app (.val (.lam (.seq (.var 0) (.var 1)))) waitPerform)

/-- The inner handler: `h_ret = λx. x`, `loan`'s clause the tail clause of `loanG`. -/
def loanH : Expr := .pair (.val idV) (tailTuple loanE 0 (.pair (.val loanG) (.val .unit)))

/-- The callback: `Λ. λm. handle_9 (loanBody) with loanH`. -/
def loanCbE : Expr := .val (.lam (.val (.lam (hndExpr loanN (loanE.map Prod.fst) loanH loanBody))))

theorem d_loanG {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom) Γ (.val loanG)
      (.val (ansTy waitRow waitRow (.box (.var 0) .unit) (.lin, .mut (.var 0) .unit, .mut (.var 0) .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .effLet (A := .unit) (.right (deadSplit hΓ))
    (fun h => absurd h waitRow_not_cancels) (fun h => absurd h waitRow_not_unr)
    (.effPerform (o := waitSig) rfl rfl rfl (.unitI (by cdead))) ?_
  refine .unitE (.left (.right (deadSplit hΓ))) (.var (by csolo)) ?_
  exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.var (by csolo)))

theorem d_loanCbE {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ loanCbE (.val cbTy) := by
  refine callbackUW ok_empty rfl hΓ ?_
  refine .effHandleT (S := waitRow) (SN := waitRow) (A := .box (.var 0) .unit)
    (R := .box (.var 0) .unit) (fs := finsNil)
    (.right (.dead (deadSplit hΓ))) (by cdead) (.val _) (.pair (.val _) (.val _)) ?_
    (by decide) (by decide)
    (by intro o ho; simp [Row.ofEff] at ho; subst ho; decide) (by simp) (RowLe.refl _)
    (by intro o ho; simp [Row.ofEff] at ho; subst ho; decide) ?_
  · exact .tensorI (.dead (.dead (deadSplit hΓ))) (CancelIntercept.d_idVΓ (by cdead) _ _)
      (.tensorI (.dead (.dead (deadSplit hΓ))) (d_loanG (by cdead)) (.unitI (by cdead)))
  · refine .effLet (A := .mut (.var 0) .unit) (.left (.dead (deadSplit hΓ)))
      (fun h => ?_) (fun h => ?_) (.effPerform (o := loanSig) (by simp [Row.find, Row.ofEff])
        rfl rfl (.var (by csolo))) ?_
    · exfalso
      obtain ⟨o, ho, h'⟩ := h
      simp [Row.ofEff] at ho
      rcases ho with rfl | rfl <;> exact h' rfl
    · exfalso
      obtain ⟨o, ho, h'⟩ := h
      simp [Row.ofEff] at ho
      rcases ho with rfl | rfl <;> cases h'
    refine .unitE (.left (.dead (.dead (deadSplit hΓ))))
      (appW (.var (by csolo)) (.releaseMut (by cdead))) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
        dead_noLive (P := fun s => VOutlives _ _ s.ty) (by cdead) s hs hl⟩))

/-- The lender: `r ← alloc (); cb; w ← withbor; (r, b) ← w r cb; b; free r`, with the loan's
callback. -/
def bodyL : Expr :=
  bindE (.app alloc' (.val .unit))
    (bindE loanCbE
      (bindE (.var 2)
        (.app (.val (.lam (.letpair (.var 0) (.seq (.var 0) (.app free' (.var 1))))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

theorem d_bodyL :
    CDerives LifeCtx.empty [⟨.bang lendC.ty, true⟩] bodyL (.comp (CTy.effOf waitRow .unit)) := by
  refine .bind (A := .ref .unit) (.right .nil)
    (.ret (appW (.unitI (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (.right (.right .nil)) (.ret (d_loanCbE (by cdead))) ?_
  refine .bind (.right (.right (.left .nil)))
    (.ret (.bangE (.var (.there (.there (.here .nil)))))) ?_
  refine .effLet (A := .tensor (.ref .unit) .unit) (.left (.left (.left (.dead .nil))))
    (fun h => absurd h waitRow_not_cancels) (fun h => absurd h waitRow_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead .nil)))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead .nil)))) (.force (T := .thunk _) (.here (by cdead)) rfl)
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (.dead (.dead (.dead (.dead .nil))))) (.var (.here (by cdead))) ?_
    refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (by csolo)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (appW (.var (by csolo)) (.free (by cdead))))

/-- **The loan program**: `handle_7 bodyL with waitH`, `wait` handled outside the lend. -/
def progLoan : Expr := hndExpr waitN (waitE.map Prod.fst) waitH bodyL

theorem d_progLoan :
    CDerives LifeCtx.empty (ctx791 [lendC]) progLoan (.comp (.ret .unit)) := by
  refine .effHandleT (S := []) (SN := []) (A := .unit) (R := .unit) (fs := finsNil)
    (.right .nil) (.cons .nil) (.val _) (.pair (.val _) (.val _)) ?_ (by decide) (by decide)
    (by simp) (by simp) (RowLe.nil []) (by simp) d_bodyL
  exact .tensorI (.dead .nil) (CancelIntercept.d_idVΓ (.cons .nil) [] .unit)
    (.tensorI (.dead .nil) (CancelIntercept.d_idVΓ (.cons .nil) [] .unit) (.unitI (.cons .nil)))

/-- **`Goal791N` at the loan program**: the run that lends a cell `mut`, hands the borrow to a
handler, suspends at `wait` while the handler holds it, and resumes with the same borrow, is safe,
leak-free, or diverges, from `HandlerLawN`. -/
theorem progLoan_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll (vals791 [lendC]) progLoan) := by
  have hg : OrDiverges (ℍ := ℍ)
      (substAll (([lendC] : List Const791).map (fun c => c.valAt []) ++ []) progLoan) :=
    goal791N h [lendC] [] [] progLoan .unit goal791N_premises_inst.1 .nil
      ((List.append_nil _).symm ▸ d_progLoan) rfl
  rwa [Const791.map_valAt_nil, List.append_nil] at hg

#print axioms d_progLoan
#print axioms progLoan_orDiverges
#print axioms goal791N
#print axioms fundamentalN_all

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
