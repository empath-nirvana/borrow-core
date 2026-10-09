import Targets.Instance.E2

/-!
# The Instance — E10 (the reconciler) at `J₁`: `timeout`

`timeout = λb. handle wait {return x ⇒ x; wait (_, k) ⇒ cancel k; return ff} (b ())` is typed once,
at `U(∀ρ:any. U(1 ⊸ F_{wait ⊙ ρ} bool) ⊸ F_ρ bool)` (`derV_timeoutR_J₁`): at each instance its
handler is typed at the row without `wait`, and its clause cancels the affine `κ` and drops the
payload with the cancel, so its `[let]` holds nothing.  Its one typing serves a body at every
`wait ⊙ ε` (`polyUseOpen_timeoutR_J₁`), and it calls its body under its own handler only
(`callsThrough_timeoutR`).  `[Core σ=[]]`

E10's other parts are not derived here, and no obstruction is machine-checked.  `retry` calls its
body from its handler's clause and from the handled computation, so the body is at `!U C` (the
clause's context is persistent at `[handle]` at a value form) and is forced, and Core's `force`
reads a `U C` slot only (as for E2a–E2c, `Targets/Instance/E2.lean`).  The reconciler's loop is
built by `unfold`, which our instance writes as the stepped codata value `etaN` (`unfoldE`); no rule
of the tied kernel types that value (E3, `Targets/Status.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont performE raiseE hndE hndVal opPayload)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt RowEnv)

/-- `wait (_, k) ⇒ cancel k; return ff`. -/
def timeoutClE : Expr := .lam (.letpair (.var 0) (bindE (cancelE (.var 0)) (.inj₁ .unit)))

/-- `timeout`'s handler: `return x ⇒ x`, and its clause. -/
def timeoutRH : Expr := .pair (.lam (.var 0)) (clausesE [timeoutClE])

theorem isVal_timeoutRH : IsVal timeoutRH := .pair .lam (.pair .lam .unit)

/-- `timeout` at the name `nw` and the tags `qs`. -/
def timeoutRE (nw : UInt32) (qs : Expr) : Expr :=
  .lam ((handleK nw qs (.lam (.var 0)) [timeoutClE]).plug (appE (.var 0) .unit))

/-- `timeout`'s polymorphic body, the body's row `S` before the row variable:
`U(1 ⊸ F_{S ⊙ ρ} bool) ⊸ F_ρ bool`. -/
def tmC (S : Row) : OCTy :=
  .arr (.thunk (.arr .unit (effAt S (OVTy.ofV boolT)))) (effAt [] (OVTy.ofV boolT))

theorem tmC_den (S : Row) (η : RowEnv) (r : Row) :
    (tmC S).den (Function.update η ρ₀ r) =
      .arr (.thunk (.arr .unit (CTy.effOf (S ++ r) boolT))) (CTy.effOf r boolT) := by
  simp [tmC, effAt, OCTy.den, OVTy.den, OVTy.den_ofV]

theorem tmC_rFree (S : Row) : (tmC S).RFree :=
  ⟨OCTy.rFree_ofC (.arr .unit (.ret boolT)), OVTy.rFree_ofV boolT⟩

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem timeoutR_val (lw : (orowAlg Ξ).Lab) :
    ((𝕁).timeoutR lw).1 = timeoutRE lw.1 (qsOf Ξ lw.1) := rfl

/-- **`wait (_, k) ⇒ cancel k; return ff`** at an affine `1 ↠ 1`, at every row: the payload is
dropped with the cancel, so the `[let]`'s continuation holds nothing. -/
theorem d_timeoutCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) :
    CDerivesAt Ξ Δ Γ timeoutClE (.val (clauseTy S boolT (.aff, .unit, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effLet (A := .unit) (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => fun s hs hl => ?_) (fun _ => fun s hs hl => ?_) ?_ ?_
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hΓ s hs hl
  · exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S boolT)) (CTy.effOf S .unit))
      (.here (.drop rfl (.cons hΓ.toP))))
  · exact .effSub (rowLe_nil S) (.ret (.sumI₁ (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))

theorem d_timeoutRH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) :
    CDerivesAt Ξ Δ Γ timeoutRH
      (.val (.tensor (retTy S boolT boolT) (clausesTy S boolT [(.aff, .unit, .unit)]))) :=
  .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.var (.here hΓ.toP)))))
    (.tensorI (deadSplit hΓ) (d_timeoutCl hΓ S) (.unitI hΓ.toP))

/-- **`timeout` at an instance**: the handler at the row without `wait`. -/
theorem d_timeoutR {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {r : Row}
    (hr : RowAt Ξ r) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] (timeoutRE lw.1 (qsOf Ξ lw.1))
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf (rowOf lw ++ r) boolT)))
        (CTy.effOf r boolT))) := by
  have hcb : RowLe (rowOf lw ++ r)
      (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 ++ Row.dropName lw.1 r) := by
    have h₁ := rowLe_ofEff_dropName (rowAt_rowOf_append lw hr) lw.1
      fun i o hf _ => fin_rowOf_append lw (rowAt_rowOf_append lw hr) i o hf
    rwa [dropName_rowOf_append, hlw] at h₁
  refine .lam (.effSub (rowLe_dropName lw.1 r) ?_)
  refine d_handleL lw hlw (rowAt_dropName hr lw.1) (fun o ho => ne_of_mem_dropName o ho)
    isVal_timeoutRH (d_timeoutRH (kill_dead _) _) ?_
  exact .effSub hcb (d_callVar0 .nil)

/-- **E10: `timeout` is typed once**, at `U(∀ρ:any. U(1 ⊸ F_{wait ⊙ ρ} bool) ⊸ F_ρ bool)`. -/
theorem derV_timeoutR_J₁ {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).derV [] ((𝕁).timeoutR lw) (polyTy (tmC (rowOf lw))) := by
  have hcl : closedAt 0 (timeoutRE lw.1 (qsOf Ξ lw.1)) = true := by
    simpa using closedAt_of_derives (d_timeoutR (Δ := LifeCtx.empty) hlw (rowAt_nil Ξ)).toCDerives
  exact derV_poly_J₁ (b := (handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE]).plug
    (appE (.var 0) .unit)) (tmC_rFree _) trivial hcl fun r η _ hrt => by
      rw [tmC_den]; exact d_timeoutR hlw hrt

/-- **E10's `timeout` schema at `J₁`**: its one typing serves a body at every `wait ⊙ ε`, `ε`
without `wait`, the use at `ε`. -/
theorem polyUseOpen_timeoutR_J₁ (hΞ : Ξ.NU) (lw : (orowAlg Ξ).Lab) :
    (𝕁).PolyUseOpen [polyTy (tmC (rowOf lw))] lw (fun g => (𝕁).call ((𝕁).var 0) g)
      (𝕁).bool (𝕁).bool := by
  intro ε ε' M hlack hcomp hM
  have hε' : ε' = ⟨rowOf lw ++ ε.ops, ε.tail⟩ := by
    have : (orowAlg Ξ).comp ((orowAlg Ξ).lift lw) ε = some ⟨rowOf lw ++ ε.ops, ε.tail⟩ := rfl
    exact (Option.some.inj (hcomp.symm.trans this))
  subst hε'
  have hops := names_of_lacks hlack
  obtain ⟨S, A', hS, hSt⟩ := hM.1 (fun _ => []) (envAt_nil Ξ)
  have hS' : CTy.effOf (orowRF.den Ξ ⟨rowOf lw ++ ε.ops, ε.tail⟩ (J₁.env Ξ (fun _ => [])))
      ((OVTy.ofV boolT).den (fun _ => [])) = CTy.effOf S A' := hS
  obtain ⟨hSeq, -⟩ := effOf_inj hS'
  have hat : RowAt Ξ ε.ops := by
    intro n i o hf
    obtain ⟨hmem, hn, -⟩ := Row.find_mem hf
    have hne : n ≠ lw.1 := by rw [← hn]; exact hops o hmem
    apply hSt n i o
    rw [← hSeq]
    show Row.find ((rowOf lw ++ ε.ops) ++ _) n i = some o
    rw [List.append_assoc, Row.find_append, rowOf, Targets.find_ofEff_other _ hne, Option.none_or,
      Row.find_append, hf, Option.some_or]
  exact der_callPoly_J₁ (Cp := tmC (rowOf lw)) (A := boolT) (B := boolT) hΞ (tmC_rFree _) trivial
    boolT_not_loop (fun η => by rw [tmC_den]; simp [List.append_assoc]) hM
    (tiedAt_F (fun _ => rfl) hat _)

/-- **`timeout` calls its body under its own handler only**: from `let t = timeout in t (λ_. M)`,
the run reaches `M` by store-keeping steps, under `timeout`'s handler frame, which catches only
`wait` and holds no finaliser. -/
theorem callsThrough_timeoutR (lw : (orowAlg Ξ).Lab) {M : Expr} (hM : closedAt 0 M = true) :
    (𝕁).CallsThrough (· ≠ lw) ((𝕁).lets [(𝕁).timeoutR lw] ((𝕁).call ((𝕁).var 0) ((𝕁).lam M)))
      M := by
  have hLM : closedAt 0 (Expr.lam M) = true := by simpa [closedAt] using closedAt_of_zero hM 1
  have hHc : closedAt 0 (hndValE lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE]) = true := by
    simp [hndValE, clausesE, closedAt, qsOf, closedAt_qualsVal, timeoutClE, cancelE, bindE]
  have hfc : closedAt 0 (Expr.lam ((handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0))
      [timeoutClE]).plug (appE (.var 0) .unit))) = true := by
    have := closedAt_of_zero hHc 1
    simp [handleK, Kont.plug, appE, closedAt, Expr.shift, this]
  have h₁ := quiet_call_lam (ℍ := ℍ) hfc hM
  have e : Expr.subst 0 (Val.lam M) ((handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0))
      [timeoutClE]).plug (appE (.var 0) .unit)) =
      (handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE]).plug (appE (.lam M) .unit) := by
    show Expr.app (Expr.app (Expr.subst 0 (Val.lam M) (.prim .hnd))
        (Expr.subst 0 (Val.lam M) (hndValE lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE])))
      (Expr.subst 0 (Val.lam M) (appE (.var 0) .unit)) = _
    rw [subst_closedAt _ _ hHc (le_refl _), appE_var0_subst rfl (Val.lam M) hLM]
    rfl
  rw [e] at h₁
  have h₂ := (quiet_appE (ℍ := ℍ) .hole (.lam M) Val.unit).plug
    (handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE])
  have h₃ := (quiet_beta (ℍ := ℍ) .hole M Val.unit).plug
    (handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE])
  rw [subst_closedAt M Val.unit hM (le_refl _)] at h₃
  obtain ⟨q, hc, -⟩ := h₁.trans (h₂.trans h₃)
  refine ⟨handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE], fun m hm => ?_,
    ⟨fun x => by simp, fun s => by simp, trivial⟩, pureSteps_of_chain hc⟩
  have hm' : lw.1 ≠ m.1 := fun h => hm (Subtype.ext h.symm)
  show Kont.HasHnd m.1 (handleK lw.1 (qsOf Ξ lw.1) (.lam (.var 0)) [timeoutClE]) = false
  simp [handleK, hndValE, Kont.HasHnd, hm']

end Typing

end Targets.Inst

end
