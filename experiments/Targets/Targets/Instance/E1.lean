import Targets.Instance.EHof

/-!
# The Instance — E1 (no colouring) at `J₁`: the typings

`hof` is typed once (`derV_hof_J₁`), and its one typing serves the three callbacks of E1's program,
the pure one, one raising `exn` and one performing `wait`, each at its own row
(`der_threeUses_J₁`), and E1′'s program, whose callback suspends and whose handler answers a
closure holding the continuation (`der_usesS_J₁`).  The polymorphic slot `f` is closed by a λ-value
Core types at every instance (`ClosingAt`); each use reads the closing at the instance of its row.
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont performE raiseE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt RVar RowEnv)

/-! ### The programs, as our instance writes them -/

/-- `λ_. return tt`. -/
def pureCbE : Expr := .lam (.inj₂ .unit)

/-- `λ_. raise exn ()`. -/
def failCbE (n : UInt32) : Expr := .lam (raiseE (opArgE n 0 .unit))

/-- `λ_. wait (); return tt`. -/
def asyncCbE (n : UInt32) : Expr := .lam (bindE (performE (opArgE n 0 .unit)) (.inj₂ .unit))

/-- E1's program with `f` filled by `W`. -/
def threeUsesW (W : Expr) (ne nw : UInt32) (qe qw : Expr) : Expr :=
  bindE (appE W pureCbE)
    (bindE ((handleK ne qe (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug (appE W (failCbE ne)))
      (bindE ((handleK nw qw (.lam (.var 0)) [resumeClE]).plug (appE W (asyncCbE nw)))
        (.pair (.var 2) (.pair (.var 1) (.var 0)))))

/-- E1′'s program with `f` filled by `W`. -/
def usesSW (W : Expr) (nw : UInt32) (qw : Expr) : Expr :=
  bindE ((handleK nw qw schedRetE [schedClE]).plug (appE W (asyncCbE nw)))
    (bindE (appE W pureCbE) (bindE (appE (.var 1) .unit) (.pair (.var 1) (.var 0))))

section E1
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem fillS_threeUses {σ : ℕ → Option Val} {W : Val} (hW : σ 0 = some W)
    (hWc : closedAt 0 W.1 = true) (le lw : (orowAlg Ξ).Lab) :
    fillS σ 0 ((𝕁).threeUses le lw) = threeUsesW W.1 le.1 lw.1 (qsOf Ξ le.1) (qsOf Ξ lw.1) := by
  simp only [A.EffectSystem.threeUses, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.toResult, A.EffectSystem.resumer, A.EffectSystem.pureCb, A.EffectSystem.failCb,
    A.EffectSystem.asyncCb, A.EffectSystem.resumeCl, A.EffectSystem.tt]
  simp only [ourInst, List.map]
  simp [threeUsesW, pureCbE, failCbE, asyncCbE, resumeClE, fillS, appE, bindE, handleK, hndValE,
    Kont.plug, hW, Expr.shift, clausesE, resumeE, qsOf, performE, raiseE, opArgE, Val.i32,
    fillS_closed σ _ _ (closedAt_qualsVal _ _), shift_closedAt W.1 1 hWc]

theorem fillS_usesS {σ : ℕ → Option Val} {W : Val} (hW : σ 0 = some W)
    (hWc : closedAt 0 W.1 = true) (lw : (orowAlg Ξ).Lab) :
    fillS σ 0 ((𝕁).usesS lw) = usesSW W.1 lw.1 (qsOf Ξ lw.1) := by
  simp only [A.EffectSystem.usesS, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.sched, A.EffectSystem.schedRet, A.EffectSystem.schedCl, A.EffectSystem.pureCb,
    A.EffectSystem.asyncCb, A.EffectSystem.tt]
  simp only [ourInst, List.map]
  simp [usesSW, schedRetE, schedClE, pureCbE, asyncCbE, fillS, appE, bindE, handleK, hndValE,
    Kont.plug, hW, Expr.shift, clausesE, resumeE, qsOf, performE, opArgE, Val.i32,
    fillS_closed σ _ _ (closedAt_qualsVal _ _), shift_closedAt W.1 1 hWc]

/-- The instances of `hof`'s closing at every unr-free row tied to the context. -/
theorem hofClosing_inst {Δ : LifeCtx} {η : RowEnv} {W : Val}
    (hWty : ∀ C', (polyTy (hofC boolT)).PolyInstAt Ξ η C' → CDerivesAt Ξ Δ [] (.val W) (.comp C')) :
    ∀ r : Row, Row.NU r → RowAt Ξ r → CDerivesAt Ξ Δ [] W.1
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf r boolT))) (CTy.effOf r boolT))) := by
  intro r hr hrt
  have := hWty _ ⟨r, ⟨hr, fun _ _ => trivial⟩, hrt, rfl⟩
  rwa [hofC_den] at this

/-- **E1's program, `f` filled by a closing of `hof`'s type**: its three uses at the pure row,
`exn`'s row and `wait`'s row. -/
theorem d_threeUsesW {W : Expr} (hWc : closedAt 0 W = true)
    (hWi : ∀ r : Row, Row.NU r → RowAt Ξ r → CDerivesAt Ξ LifeCtx.empty [] W
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf r boolT))) (CTy.effOf r boolT))))
    (hΞ : Ξ.NU) {le lw : (orowAlg Ξ).Lab} {q : Qual}
    (hle : Ξ le.1 = [(q, .unit, .zero)]) (hq : q ≠ .lin) (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    CDerivesAt Ξ LifeCtx.empty [⟨.unit, false⟩] (threeUsesW W le.1 lw.1 (qsOf Ξ le.1) (qsOf Ξ lw.1))
      (.comp (.ret (.tensor boolT (.tensor (.sum boolT .unit) boolT)))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  have hRe := rowAt_ofEff_lab le hle
  have hRw := rowAt_ofEff_lab lw hlw
  refine .bind (deadSplit hΓ₀) (d_appClosed hΓ₀ hWc (hWi [] row_nu_nil (rowAt_nil Ξ))
    (d_cbDead hΓ₀ (.ret (.sumI₂ (.unitI .nil))))) ?_
  refine .bind (A := .sum boolT .unit) (.right (deadSplit hΓ₀)) ?_ ?_
  · refine d_handleL le hle (S := []) (rowAt_nil Ξ) (by simp) isVal_toResultH
      (d_toResultH (kill_dead _) [] boolT hq) ?_
    exact d_appClosed (.cons hΓ₀) hWc (hWi _ (rowNU_of_rowAt hΞ hRe) hRe)
      (d_cbDead (.cons hΓ₀) (d_raiseLab .nil le hle hq boolT))
  refine .bind (A := boolT) (.right (.right (deadSplit hΓ₀))) ?_ ?_
  · refine d_handleL lw hlw (S := []) (rowAt_nil Ξ) (by simp) isVal_resumerH
      (d_resumerH (kill_dead _) [] boolT (q := .aff) (A := .unit) (by decide) rfl) ?_
    refine d_appClosed (.cons (.cons hΓ₀)) hWc (hWi _ (rowNU_of_rowAt hΞ hRw) hRw)
      (d_cbDead (.cons (.cons hΓ₀)) ?_)
    exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil) (d_performLab lw hlw rfl (.unitI .nil))
      (.effSub (rowLe_nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))
  exact .ret (.tensorI (.right (.right (.left (.dead .nil))))
    (.var (.there (.there (.here (.cons .nil)))))
    (.tensorI (.right (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil)))))
      (.var (.here (.cons (.cons (.cons .nil)))))))

/-- **`sched`'s clause**, `wait (_, k) ⇒ λ_. resume k () to g. g ()`, at the affine `1 ↠ 1`: the
closure it answers holds `k`, and its binder is dead. -/
theorem d_schedClAt {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ schedClE (.val (clauseTy [] (schedR boolT) (.aff, .unit, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .ret (.thunkV rfl (.lamDead (S := []) ?_))
  -- the closure's body: `resume k () to g. g ()`, `k` at `1`, the clause's argument at `2`
  refine .bind (A := (schedR boolT)) (.dead (.left (.left (.dead (deadSplit hΓ))))) ?_ ?_
  · refine .bind (A := .unit) (.dead (.right (.left (.dead (deadSplit hΓ)))))
      (.ret (.unitI (.cons (.cons (.drop rfl (.cons hΓ.toP)))))) ?_
    exact .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ))))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] (schedR boolT))) (CTy.effOf [] .unit))
        (.there (.there (.here (.cons (.cons hΓ.toP)))))))
      (.here (.cons (.cons (.cons (.cons hΓ.toP)))))
  · refine .bind (A := .unit) (.right (.dead (.dead (.dead (.dead (deadSplit hΓ))))))
      (.ret (.unitI (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))) ?_
    exact .app (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.force (C := .arr .unit (.ret boolT)) (.there (.here (.cons (.cons (.cons (.cons hΓ.toP)))))))
      (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))

/-- `sched`'s handler value, at the affine `1 ↠ 1`, answering the closure. -/
theorem d_schedH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ (.pair schedRetE (clausesE [schedClE]))
      (.val (.tensor (retTy [] boolT (schedR boolT)) (clausesTy [] (schedR boolT) [(.aff, .unit, .unit)]))) :=
  .tensorI (deadSplit hΓ)
    (d_lamBang hΓ (.ret (.thunkV rfl (.lamDead (S := []) (.ret (.var (.there (.here hΓ.toP))))))))
    (.tensorI (deadSplit hΓ) (d_schedClAt hΓ) (.unitI hΓ.toP))

theorem isVal_schedH : IsVal (.pair schedRetE (clausesE [schedClE])) := .pair .lam (.pair .lam .unit)

/-- **E1′'s program, `f` filled by a closing of `hof`'s type**: the callback suspends, `sched`
answers a closure holding the continuation, which is called after `f` runs again. -/
theorem d_usesSW {W : Expr} (hWc : closedAt 0 W = true)
    (hWi : ∀ r : Row, Row.NU r → RowAt Ξ r → CDerivesAt Ξ LifeCtx.empty [] W
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf r boolT))) (CTy.effOf r boolT))))
    (hΞ : Ξ.NU) {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    CDerivesAt Ξ LifeCtx.empty [⟨.unit, false⟩] (usesSW W lw.1 (qsOf Ξ lw.1))
      (.comp (.ret (.tensor boolT boolT))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  have hRw := rowAt_ofEff_lab lw hlw
  refine .bind (A := (schedR boolT)) (deadSplit hΓ₀) ?_ ?_
  · refine d_handleL lw hlw (S := []) (rowAt_nil Ξ) (by simp) isVal_schedH
      (d_schedH (kill_dead _)) ?_
    refine d_appClosed hΓ₀ hWc (hWi _ (rowNU_of_rowAt hΞ hRw) hRw) (d_cbDead hΓ₀ ?_)
    exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil) (d_performLab lw hlw rfl (.unitI .nil))
      (.effSub (rowLe_nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))
  refine .bind (A := boolT) (.right (deadSplit hΓ₀)) (d_appClosed (.cons hΓ₀) hWc
    (hWi [] row_nu_nil (rowAt_nil Ξ)) (d_cbDead (.cons hΓ₀) (.ret (.sumI₂ (.unitI .nil))))) ?_
  refine .bind (A := boolT) (.right (.left (deadSplit hΓ₀))) ?_ ?_
  · refine .bind (A := .unit) (.dead (.right (deadSplit hΓ₀))) (.ret (.unitI (.cons (.cons hΓ₀.toP))))
      ?_
    exact .app (.right (.dead (.left (deadSplit hΓ₀))))
      (.force (C := .arr .unit (.ret boolT)) (.there (.there (.here hΓ₀.toP))))
      (.here (.cons (.cons hΓ₀.toP)))
  exact .ret (.tensorI (.right (.left (.dead (deadSplit hΓ₀)))) (.var (.there (.here (.cons hΓ₀.toP))))
    (.var (.here (.cons (.cons hΓ₀.toP)))))

/-- **E1's program is typed at `J₁`**, `f` at `hof`'s polymorphic type. -/
theorem der_threeUses_J₁ (hΞ : Ξ.NU) {le lw : (orowAlg Ξ).Lab} {q : Qual}
    (hle : Ξ le.1 = [(q, .unit, .zero)]) (hq : q ≠ .lin) (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).der [polyTy (hofC boolT)] ((𝕁).threeUses le lw) ((𝕁).F (𝕁).EA.unit (𝕁).ty1) := by
  refine ⟨tiedAt_unit J₁ _, .inl ⟨[], by simp, slots_polyTy (hofC_rFree boolT) trivial,
    OVTy.rFree_ofV (.tensor boolT (.tensor (.sum boolT .unit) boolT)), fun η _ _ σ hσ => ?_⟩⟩
  obtain ⟨W, hW, -, hWc, hWty⟩ := closingAt_one (polyTy_isPoly _) hσ
  show CDerivesAt Ξ LifeCtx.empty (octxStrip η (liveCtx [polyTy (hofC boolT)]))
    (fillS σ 0 ((𝕁).threeUses le lw)) (.comp (.ret (.tensor boolT (.tensor (.sum boolT .unit) boolT))))
  rw [fillS_threeUses hW hWc, octxStrip_live_cons_poly η (polyTy_isPoly _) []]
  exact d_threeUsesW hWc (hofClosing_inst hWty) hΞ hle hq hlw

/-- **E1′'s program is typed at `J₁`**, `f` at `hof`'s polymorphic type. -/
theorem der_usesS_J₁ (hΞ : Ξ.NU) {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).der [polyTy (hofC boolT)] ((𝕁).usesS lw)
      ((𝕁).F (𝕁).EA.unit ((𝕁).Tensor (𝕁).bool (𝕁).bool)) := by
  refine ⟨tiedAt_unit J₁ _, .inl ⟨[], by simp, slots_polyTy (hofC_rFree boolT) trivial,
    OVTy.rFree_ofV (.tensor boolT boolT), fun η _ _ σ hσ => ?_⟩⟩
  obtain ⟨W, hW, -, hWc, hWty⟩ := closingAt_one (polyTy_isPoly _) hσ
  show CDerivesAt Ξ LifeCtx.empty (octxStrip η (liveCtx [polyTy (hofC boolT)]))
    (fillS σ 0 ((𝕁).usesS lw)) (.comp (.ret (.tensor boolT boolT)))
  rw [fillS_usesS hW hWc, octxStrip_live_cons_poly η (polyTy_isPoly _) []]
  exact d_usesSW hWc (hofClosing_inst hWty) hΞ hlw

/-! ### The callbacks' bodies, each at its own row -/

/-- A closed program Core's tied kernel types at a closed row tied to the context is typed at
`J₁`. -/
theorem der_J₁_closedRow {ε : ORow} (hε : ε.tail = none) (hat : RowAt Ξ ε.ops) {e : Expr}
    {A : VTy} (hcl : closedAt 0 e = true)
    (h : CDerivesAt Ξ LifeCtx.empty [] e (.comp (CTy.effOf ε.ops A))) :
    (𝕁).der [] e ((𝕁).F ε (OVTy.ofV A)) := by
  refine ⟨tiedAt_F (fun _ => rfl) hat _, .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil,
    OVTy.rFree_ofV A, fun η _ _ σ _ => ?_⟩⟩
  show CDerivesAt Ξ LifeCtx.empty [] (fillS σ 0 e)
    (.comp (CTy.effOf (ε.ops ++ (match ε.tail with | none => [] | some ρ => η ρ))
      ((OVTy.ofV A).den η)))
  rw [fillS_closed σ e 0 hcl, hε, List.append_nil, OVTy.den_ofV]
  exact h

/-- `return tt` at the pure row. -/
theorem der_retTt_J₁ : (𝕁).der [] ((𝕁).ret (𝕁).tt) ((𝕁).F (𝕁).EA.unit (𝕁).bool) :=
  der_J₁_ret (Ξ := Ξ) (A := boolT) rfl (.ret (.sumI₂ (.unitI .nil)))

/-- `raise exn ()` at `exn`'s row. -/
theorem der_raise_J₁ {le : (orowAlg Ξ).Lab} {q : Qual} (hle : Ξ le.1 = [(q, .unit, .zero)])
    (hq : q ≠ .lin) (B : VTy) :
    (𝕁).der [] ((𝕁).raise le 0 (𝕁).unitV) ((𝕁).F ((𝕁).EA.lift le) (OVTy.ofV B)) := by
  refine der_J₁_closedRow rfl (rowAt_rowOf le) rfl ?_
  show CDerivesAt Ξ LifeCtx.empty [] (raiseE (opArgE le.1 0 .unit))
    (.comp (CTy.effOf (Row.ofEff le.1 (Ξ le.1) 0) B))
  have h := d_raiseLab (Δ := LifeCtx.empty) .nil le hle hq B
  rwa [List.append_nil, ← hle] at h

/-- `wait (); return tt` at `wait`'s row. -/
theorem der_waitTt_J₁ {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).der [] ((𝕁).bind ((𝕁).perform lw 0 (𝕁).unitV) ((𝕁).ret (𝕁).tt))
      ((𝕁).F ((𝕁).EA.lift lw) (𝕁).bool) := by
  refine der_J₁_closedRow (A := boolT) rfl (rowAt_rowOf lw) rfl ?_
  show CDerivesAt Ξ LifeCtx.empty [] (bindE (performE (opArgE lw.1 0 .unit)) (.inj₂ .unit))
    (.comp (CTy.effOf (Row.ofEff lw.1 (Ξ lw.1) 0) boolT))
  have h : CDerivesAt Ξ LifeCtx.empty [] (bindE (performE (opArgE lw.1 0 .unit)) (.inj₂ .unit))
      (.comp (CTy.effOf (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 ++ []) boolT)) :=
    .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil) (d_performLab lw hlw rfl (.unitI .nil))
      (.effSub (rowLe_nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))
  rwa [List.append_nil, ← hlw] at h

end E1

end Targets.Inst

end
