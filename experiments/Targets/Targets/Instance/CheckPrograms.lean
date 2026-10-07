import Core.EffPrograms
import Targets.Instance.Machine

/-!
# The Instance — the statement checks' programs, typed by today's kernel

Each program a statement check runs is typed here by `CDerivesNU`, today's unr-free rules, and so
by `tier1Open` at our instance (`der_tier1Open_ret`).  Typing derivations only; their runs and the
checks are `Targets/Instance/Checks.lean`'s.

* `d_nLogOutsideNU`: Core's `nLogOutside` (`Core/EffPrograms.lean`), whose `with_log` clause resumes
  `κ` by applying it (`κ (inj₁ ()) v`), with the premise `Row.NU` at its effect rules.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Lifetime (LifeCtx)
open BoCa.BoLo (performE raiseE)
open Targets (CDerivesNU RowForm EffCtx orowRF)

/-! ### Rows -/

theorem nu_nil : Row.NU [] := fun _ _ _ h => by simp [Row.find] at h

theorem nu_of_all {S : Row} (h : ∀ o ∈ S, o.abort = true ∨ o.q ≠ .unr) : Row.NU S :=
  fun _ _ o hf => h o (Row.find_mem hf).1

/-! ### `with_log` and `to_result`, unr-free -/

theorem d_hrLNU {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ hrL (.val (retTy [] A (.tensor A Flag))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) nu_nil (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
        (.sumI₁ (.unitI (.cons hΓ.toP)))))))

/-- `drop f` at `1 ⊕ 1`, the flag at index `0` of a context otherwise dead. -/
theorem d_dropB0NU {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ (⟨Flag, true⟩ :: Γ) (dropB (.var 0)) (.val .unit) :=
  .ofRet (.sumE (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
    (.ret (.var (.here (Ctx.Dead.cons hΓ).toP))) (.ret (.var (.here (Ctx.Dead.cons hΓ).toP))))

theorem d_clLNU {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ clL (.val (clauseTy [] (.tensor A Flag) (.aff, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effLet (A := .tensor A Flag) nu_nil (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun _ => dead_noLive (by cdead)) ?_ ?_
  · refine .app (.left (.right (.dead (deadSplit hΓ)))) ?_ (.there (.here (by cdead)))
    exact .proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] (.tensor A Flag))) (CTy.effOf [] .unit))
      (.here (by cdead)))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    refine .unitE (.left (.right (deadSplit (by cdead)))) (d_dropB0NU (by cdead)) ?_
    exact .effSub (S := []) nu_nil (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.tensorI (.dead (.left (deadSplit (by cdead)))) (.var (.there (.here (by cdead))))
        (.sumI₂ (.unitI (by cdead)))))

theorem nu_log : Row.NU (Row.ofEff 2 El 0 ++ []) :=
  nu_of_all fun o ho => by simp [Row.ofEff] at ho; subst ho; right; decide

theorem d_withLogNU {Δ : LifeCtx} {A : VTy} {e : Expr}
    (he : CDerivesNU Δ [⟨retTy [] A (.tensor A Flag), false⟩, ⟨clausesTy [] (.tensor A Flag) El, false⟩] e
      (.comp (CTy.effOf (Row.ofEff 2 El 0 ++ []) A))) :
    CDerivesNU Δ [] (withLog e) (.comp (CTy.effOf [] (.tensor A Flag))) := by
  refine .bind .nil (.ret (.tensorI .nil (d_clLNU (A := A) .nil) (.unitI .nil))) ?_
  refine .bind (.right .nil) (.ret (d_hrLNU (A := A) (.cons .nil))) ?_
  exact .effHandle (E := El) (S := []) nu_log (.left (.left .nil)) (.left (.right .nil))
    (.here (.cons .nil)) (.there (.here .nil)) (by decide) (by simp) (by simp) he

theorem d_hrRNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hS : Row.NU S) (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ hrR (.val (retTy S A (.sum A .unit))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) hS (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.sumI₁ (.var (.here hΓ.toP))))))

theorem d_clsRNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hS : Row.NU S) (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ clsR (.val (clausesTy S (.sum A .unit) Ef)) :=
  .tensorI (deadSplit hΓ)
    (.bangThunkV (dead_noLive hΓ) rfl
      (.lam (.effSub (S := []) hS (fun _ _ _ h => by simp [Row.find] at h)
        (.ret (.sumI₂ (.var (.here hΓ.toP)))))))
    (.unitI hΓ.toP)

theorem d_toResultNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hNU : Row.NU (Row.ofEff 1 Ef 0 ++ S)) (hS : Row.NU S) (hn : ∀ o ∈ S, o.n ≠ 1)
    (hΓ : Ctx.Dead Γ)
    (he : CDerivesNU Δ (⟨retTy S A (.sum A .unit), false⟩ ::
      ⟨clausesTy S (.sum A .unit) Ef, false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff 1 Ef 0 ++ S) A))) :
    CDerivesNU Δ Γ (toResult e) (.comp (CTy.effOf S (.sum A .unit))) := by
  refine .bind (deadSplit hΓ) (.ret (d_clsRNU (A := A) hS hΓ)) ?_
  refine .bind (.right (deadSplit hΓ)) (.ret (d_hrRNU (A := A) hS (Ctx.Dead.cons hΓ))) ?_
  exact .effHandle (E := Ef) hNU (.left (.left (deadSplit hΓ))) (.left (.right (deadSplit hΓ)))
    (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) (by decide) hn (by simp) he

/-! ### `nLogOutside` -/

/-- `log (); raise ()`'s row: `Fail`, then `Log`. -/
abbrev SLF : Row := Row.ofEff 1 Ef 0 ++ (Row.ofEff 2 El 0 ++ [])

theorem nu_SLF : Row.NU SLF :=
  nu_of_all fun o ho => by
    simp [Row.ofEff] at ho
    rcases ho with rfl | rfl
    · left; rfl
    · right; decide

theorem d_logThenRaiseNU {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ logThenRaise (.comp (CTy.effOf SLF B)) :=
  .effLet (A := .unit) nu_SLF (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ)
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff]))
    (.effPerform (o := logSig) nu_SLF rfl rfl (.unitI hΓ.toP))
    (.effRaise (o := failSig) rfl rfl .unit (.unitI (.drop rfl hΓ.toP)))

/-- **`nLogOutside` is typed by today's unr-free kernel.** -/
theorem d_nLogOutsideNU :
    CDerivesNU LifeCtx.empty [] nLogOutside (.comp (.ret (.tensor (.sum .zero .unit) Flag))) := by
  refine d_withLogNU (A := .sum .zero .unit) ?_
  exact d_toResultNU (A := .zero) nu_SLF nu_log (by simp [Row.ofEff]) (by cdead)
    (d_logThenRaiseNU (by cdead))

/-! ### Handlers with the identity return clause -/

/-- `handle_n e with (λx. x, (cl, ()))`: one clause, the return clause the identity. -/
def withH (n : UInt32) (cl e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE (.val (.lam (.var 0))) (hndTerm n 0 1 e))

theorem d_idRetNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hS : Row.NU S)
    (hΓ : Ctx.Dead Γ) : CDerivesNU Δ Γ (.val (.lam (.var 0))) (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) hS (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.var (.here hΓ.toP)))))

theorem d_withHNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {q : Qual} {B C : VTy}
    {n : UInt32} {cl e : Expr} (hNU : Row.NU (Row.ofEff n [(q, B, C)] 0 ++ S)) (hS : Row.NU S)
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hΓ : Ctx.Dead Γ)
    (hcl : CDerivesNU Δ Γ cl (.val (clauseTy S A (q, B, C))))
    (he : CDerivesNU Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A [(q, B, C)], false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff n [(q, B, C)] 0 ++ S) A))) :
    CDerivesNU Δ Γ (withH n cl e) (.comp (CTy.effOf S A)) := by
  refine .bind (deadSplit hΓ) (.ret (.tensorI (deadSplit hΓ) hcl (.unitI hΓ.toP))) ?_
  refine .bind (.right (deadSplit hΓ)) (.ret (d_idRetNU (A := A) hS (Ctx.Dead.cons hΓ))) ?_
  exact .effHandle (E := [(q, B, C)]) hNU (.left (.left (deadSplit hΓ)))
    (.left (.right (deadSplit hΓ))) (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) hn0
    hnS (by simp) he

/-- `λ_. ()`, a clause at an abortive operation `1 ↠ 0`. -/
def abortCl : Expr := .val (.lam (.val .unit))

theorem d_abortClNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} (hS : Row.NU S) (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ abortCl (.val (clauseTy S .unit (.aff, .unit, .zero))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) hS (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.unitI (.drop rfl hΓ.toP)))))

/-- `λ(x, k). k (inj₂ ())`: the clause that cancels its continuation (Core's `c₁`,
`Core/EffCancel.lean`). -/
def cancelCl : Expr := .val (.lam (.letpair (.var 0) (.app (.var 0) (.val (Val.inj₂ Val.unit)))))

theorem d_cancelClNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ cancelCl (.val (clauseTy S .unit (.aff, .unit, .unit))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
      (.proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S .unit)) (CTy.effOf S .unit))
        (.here (.drop rfl (Ctx.Dead.cons hΓ).toP))))))

/-! ### Check 2's programs: `prog₃`'s shape

Check 2 typed these at the kernel whose `[then]` took its finaliser at the row's abortive
operations.  At option A (SPEC §24) a finaliser lets no raise escape, and these finalisers raise
the name `21` to a handler outside them, so no derivation of today's rules types them. -/

/-- `raise : 1 ↠ 0` of the names `20` and `21` and `cancel`'s operation `1 ↠ 1` of the name
`2`, each affine. -/
abbrev Eab : List (Qual × VTy × VTy) := [(.aff, .unit, .zero)]

abbrev Ecan : List (Qual × VTy × VTy) := [(.aff, .unit, .unit)]

abbrev S₂₁ : Row := Row.ofEff 21 Eab 0 ++ []

abbrev S₂ : Row := Row.ofEff 2 Ecan 0 ++ S₂₁

abbrev S₂₀ : Row := Row.ofEff 20 Eab 0 ++ S₂

theorem nu_ofEff_aff {n : UInt32} {A B : VTy} {S : Row} (hS : Row.NU S) :
    Row.NU (Row.ofEff n [(.aff, A, B)] 0 ++ S) := by
  intro m i o h
  rw [Row.find_append] at h
  rcases hf : Row.find (Row.ofEff n [(.aff, A, B)] 0) m i with _ | o'
  · rw [hf] at h; exact hS m i o h
  · rw [hf] at h
    have h' : o' = o := Option.some.inj h
    subst h'
    obtain ⟨-, j, hj, -, rfl⟩ := Row.find_ofEff n _ 0 m i _ hf
    obtain rfl : j = 0 := by simp at hj; omega
    right; simp

theorem nu_S₂₁ : Row.NU S₂₁ := nu_ofEff_aff nu_nil
theorem nu_S₂ : Row.NU S₂ := nu_ofEff_aff nu_S₂₁
theorem nu_S₂₀ : Row.NU S₂₀ := nu_ofEff_aff nu_S₂

/-- The finaliser: `raise` of the name `21`. -/
def finD : Expr := raiseE (opArgE 21 0 (.val .unit))

/-- `perform (2, 0, ()) then x. x unwind raise (21, 0, ())`. -/
def thenProg : Expr := thenE (.var 0) finD (performE (opArgE 2 0 (.val .unit)))

/-- **`prog₃`'s shape** (`Core/EffCancel.lean`): the handler of the name `2` cancels the continuation
of `perform (2, 0, ())`, inside which a handler of the name `20` and a finaliser that raises the
name `21` stand; the handler of the name `21`, outside the cancelled region, catches that raise
when the cancel re-raises it at the canceller. -/
def prog₃T : Expr := withH 21 abortCl (withH 2 cancelCl (withH 20 abortCl thenProg))

/-- `raise (1, 0, ()) then x. x unwind raise (21, 0, ())`, under handlers of `1` and `21`: the
finaliser's raise of `21` supersedes the pending raise of `1`. -/
def thenRaiseProg : Expr := thenE (.var 0) finD (raiseE (opArgE 1 0 (.val .unit)))

abbrev S₁ : Row := Row.ofEff 1 Eab 0 ++ S₂₁

theorem nu_S₁ : Row.NU S₁ := nu_ofEff_aff nu_S₂₁

/-- **The unwind's program**: `handle_21 (handle_1 (raise (1, 0, ()) then x. x unwind raise (21, 0,
())))`. -/
def unwindProg : Expr := withH 21 abortCl (withH 1 abortCl thenRaiseProg)

/-! ### Check 3's programs: E1′'s `sched` around code that moves across frames -/

/-- `sched`'s return clause `λx. ret (λ_. ret x)` (A's `schedRet` at our instance). -/
def schedRetE : Expr := .lam (.lam (.var 1))

/-- `sched`'s clause `λ(_, k). ret (λ_. k.resume () to g. g ())` (A's `schedCl` at our
instance). -/
def schedClE : Expr :=
  .lam (.letpair (.var 0) (.lam (bindE (resumeE (.var 1) .unit) (appE (.var 0) .unit))))

/-- `sched`'s answer: a thunk `U(1 → F X)`. -/
abbrev schedR (X : VTy) : VTy := .thunk (.arr .unit (.ret X))

theorem d_schedRetNU {Δ : LifeCtx} {Γ : Ctx VTy} {X : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ schedRetE (.val (retTy [] X (schedR X))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.ret (.thunkV rfl (.lam (.ret (.var (.skip rfl (.here hΓ.toP))))))))

theorem d_schedClNU {Δ : LifeCtx} {Γ : Ctx VTy} {X : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ schedClE (.val (clauseTy [] (schedR X) (.aff, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .ret (.thunkV rfl (.lam ?_))
  -- `k.resume () to g. g ()`, under `_ : 1`, `k`, `x : 1`
  refine .bind (A := schedR X) (.right (.left (.right (.dead (deadSplit hΓ))))) ?_ ?_
  · -- `k.resume ()`: `(λy. k (inj₁ ()) y) ()`
    refine .bind (A := .unit) (.dead (.right (.dead (.dead (deadSplit hΓ)))))
      (.ret (.unitI (by cdead))) ?_
    refine .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ)))))) ?_ (.here (by cdead))
    exact .proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] (schedR X))) (CTy.effOf [] .unit))
      (.there (.there (.here (by cdead)))))
  · -- `g ()`: `(λz. g z) ()`
    refine .bind (A := .unit) (.right (.right (.dead (.right (.dead (deadSplit hΓ))))))
      (.ret (.unitI (by cdead))) ?_
    refine .app (.right (.left (.left (.dead (.left (.dead (deadSplit hΓ)))))))
      (.force (C := .arr .unit (.ret X))
        (.there (.here (.drop rfl (.cons (.drop rfl (Ctx.Dead.cons hΓ).toP))))))
      (.here (by cdead))

/-- `handle_n e with (ret, (cl, ()))`: one clause and a return clause. -/
def withHT (n : UInt32) (ret cl e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE ret (hndTerm n 0 1 e))

theorem d_withHTNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R : VTy} {q : Qual} {B C : VTy}
    {n : UInt32} {ret cl e : Expr} (hNU : Row.NU (Row.ofEff n [(q, B, C)] 0 ++ S))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hΓ : Ctx.Dead Γ)
    (hcl : CDerivesNU Δ Γ cl (.val (clauseTy S R (q, B, C))))
    (hret : CDerivesNU Δ (⟨clausesTy S R [(q, B, C)], false⟩ :: Γ) ret (.val (retTy S A R)))
    (he : CDerivesNU Δ (⟨retTy S A R, false⟩ :: ⟨clausesTy S R [(q, B, C)], false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff n [(q, B, C)] 0 ++ S) A))) :
    CDerivesNU Δ Γ (withHT n ret cl e) (.comp (CTy.effOf S R)) := by
  refine .bind (deadSplit hΓ) (.ret (.tensorI (deadSplit hΓ) hcl (.unitI hΓ.toP))) ?_
  refine .bind (.right (deadSplit hΓ)) (.ret hret) ?_
  exact .effHandle (E := [(q, B, C)]) hNU (.left (.left (deadSplit hΓ)))
    (.left (.right (deadSplit hΓ))) (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) hn0
    hnS (by simp) he

/-- `tick : 1 ↠ 1`, linear. -/
abbrev Elin : List (Qual × VTy × VTy) := [(.lin, .unit, .unit)]

/-- `sched`'s clause at a linear operation: the same term, `k` linear. -/
theorem d_schedClLinNU {Δ : LifeCtx} {Γ : Ctx VTy} {X : VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ schedClE (.val (clauseTy [] (schedR X) (.lin, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .ret (.thunkV rfl (.lam ?_))
  refine .bind (A := schedR X) (.right (.left (.right (.dead (deadSplit hΓ))))) ?_ ?_
  · refine .bind (A := .unit) (.dead (.right (.dead (.dead (deadSplit hΓ)))))
      (.ret (.unitI (by cdead))) ?_
    refine .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ)))))) ?_ (.here (by cdead))
    exact .proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] (schedR X))) .top)
      (.there (.there (.here (by cdead)))))
  · refine .bind (A := .unit) (.right (.right (.dead (.right (.dead (deadSplit hΓ))))))
      (.ret (.unitI (by cdead))) ?_
    refine .app (.right (.left (.left (.dead (.left (.dead (deadSplit hΓ)))))))
      (.force (C := .arr .unit (.ret X))
        (.there (.here (.drop rfl (.cons (.drop rfl (Ctx.Dead.cons hΓ).toP))))))
      (.here (by cdead))

abbrev S₁₁ : Row := Row.ofEff 11 Elin 0 ++ []

theorem nu_ofEff_lin {n : UInt32} {A B : VTy} {S : Row} (hS : Row.NU S) :
    Row.NU (Row.ofEff n [(.lin, A, B)] 0 ++ S) := by
  intro m i o h
  rw [Row.find_append] at h
  rcases hf : Row.find (Row.ofEff n [(.lin, A, B)] 0) m i with _ | o'
  · rw [hf] at h; exact hS m i o h
  · rw [hf] at h
    have h' : o' = o := Option.some.inj h
    subst h'
    obtain ⟨-, j, hj, -, rfl⟩ := Row.find_ofEff n _ 0 m i _ hf
    obtain rfl : j = 0 := by simp at hj; omega
    right; simp

theorem nu_S₁₁ : Row.NU S₁₁ := nu_ofEff_lin nu_nil

/-- `withSchedLin e`: `sched` at the linear operation `11.0`, answering `U(1 → F 1)`. -/
def withSchedLin (e : Expr) : Expr := withHT 11 schedRetE schedClE e

theorem d_withSchedLinNU {Δ : LifeCtx} {e : Expr}
    (he : CDerivesNU Δ [⟨retTy [] .unit (schedR .unit), false⟩,
      ⟨clausesTy [] (schedR .unit) Elin, false⟩] e (.comp (CTy.effOf S₁₁ .unit))) :
    CDerivesNU Δ [] (withSchedLin e) (.comp (.ret (schedR .unit))) :=
  d_withHTNU nu_S₁₁ (by decide) (by simp) .nil (d_schedClLinNU .nil)
    (d_schedRetNU (Ctx.Dead.cons .nil)) he

/-- The algebraicity check's left side: `(tick () to x. ret x) to y. ret ()`. -/
def algL : Expr := bindE (bindE (performE (opArgE 11 0 (.val .unit))) (.var 0)) (.val .unit)

/-- Its right side: `tick () to x. (ret x to y. ret ())`. -/
def algR : Expr := bindE (performE (opArgE 11 0 (.val .unit))) (bindE (.var 0) (.val .unit))

theorem d_algLNU {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ algL (.comp (CTy.effOf S₁₁ .unit)) := by
  refine .effLet (A := .unit) nu_S₁₁ (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ)
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff])) ?_ ?_
  · refine .effLet (A := .unit) nu_S₁₁ (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ)
      (fun h => absurd h (by simp [Row.Unr, Row.ofEff]))
      (.effPerform (o := ⟨11, 0, .lin, .unit, .unit⟩) nu_S₁₁ rfl rfl (.unitI hΓ.toP)) ?_
    exact .effSub (S := []) nu_S₁₁ (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.var (.here hΓ.toP)))
  · exact .effSub (S := []) nu_S₁₁ (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.unitI (.drop rfl hΓ.toP)))

/-- **The algebraicity check's program**: `sched` around the left side. -/
def algProg : Expr := withSchedLin algL

theorem d_algProgNU : CDerivesNU LifeCtx.empty [] algProg (.comp (.ret (schedR .unit))) :=
  d_withSchedLinNU (d_algLNU (by cdead))

/-- `c = λ_. tick () to _. ret ()`: code that performs the operation `sched` catches. -/
def tickCE : Expr := .lam (bindE (performE (opArgE 11 0 (.val .unit))) (.val .unit))

/-- A's tail-resumptive clause `λ(a, k). c a to b. k.resume b` at `c = tickCE`, at our
instance. -/
def tailClE : Expr :=
  .lam (.letpair (.var 0) (bindE (appE tickCE (.var 1)) (resumeE (.var 1) (.var 0))))

theorem d_tickCENU {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ tickCE (.comp (.arr .unit (CTy.effOf S₁₁ .unit))) := by
  refine .lam ?_
  refine .effLet (A := .unit) nu_S₁₁ (.right (deadSplit hΓ))
    (fun h => absurd h (by simp [Row.Weak, Row.ofEff]))
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff])) ?_ ?_
  · exact .effPerform (o := ⟨11, 0, .lin, .unit, .unit⟩) nu_S₁₁ rfl rfl (.unitI (Ctx.Dead.cons hΓ).toP)
  · exact .effSub (S := []) nu_S₁₁ (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.unitI (.drop rfl (.drop rfl hΓ.toP))))

theorem d_tailClNU {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesNU Δ Γ tailClE (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  -- `c a to b. k.resume b`, at a row of linear operations
  refine .effLet (A := .unit) nu_S₁₁ (.right (.left (.dead (deadSplit hΓ))))
    (fun h => absurd h (by simp [Row.Weak, Row.ofEff]))
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff])) ?_ ?_
  · -- `c a`: `(λx. c x) a`
    refine .bind (A := .unit) (.dead (.left (.dead (deadSplit hΓ)))) (.ret (.var (by csolo))) ?_
    exact .app (.right (.dead (.dead (.dead (deadSplit hΓ))))) (d_tickCENU (by cdead))
      (.here (by cdead))
  · -- `k.resume b`: `(λy. k (inj₁ ()) y) b`
    refine .bind (A := .unit) (.left (.right (.dead (.dead (deadSplit hΓ)))))
      (.ret (.var (by csolo))) ?_
    refine .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ)))))) ?_ (.here (by cdead))
    exact .proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S₁₁ .unit)) .top)
      (.there (.there (.here (by cdead)))))

/-- **The tail-resumption check's program**: `sched` around the handler of `5`, whose clause is
A's tail-resumptive clause, around `perform (5, 0, ())`. -/
def tailProg : Expr :=
  withSchedLin (withHT 5 (.lam (.var 0)) tailClE (performE (opArgE 5 0 (.val .unit))))

theorem d_tailProgNU : CDerivesNU LifeCtx.empty [] tailProg (.comp (.ret (schedR .unit))) := by
  refine d_withSchedLinNU ?_
  exact d_withHTNU (S := S₁₁) (A := .unit) (R := .unit) (nu_ofEff_lin nu_S₁₁) (by decide)
    (by simp [Row.ofEff]) (by cdead) (d_tailClNU (by cdead)) (d_idRetNU nu_S₁₁ (by cdead))
    (.effPerform (o := ⟨5, 0, .lin, .unit, .unit⟩) (nu_ofEff_lin nu_S₁₁) rfl rfl
      (.unitI (by cdead)))

end Targets.Inst

end
