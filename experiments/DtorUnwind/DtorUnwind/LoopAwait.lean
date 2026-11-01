import DtorUnwind.Await
import DtorUnwind.Loop
import Core.DivRuntime

/-!
# Stage 7: a task that loops, borrowing its own cell and awaiting each turn, under a scheduler
that stores `κ`, with the fuel inside the scheduler

The task:

    c ← open 1;
    loop { borrow mut c { v → v += 10; await; v += 1 } }        -- c a File, closed on every exit

`[handle]` around a body whose row holds `Div` is typed only by `effHandleT`/`effHandleL`
(decision 68, `effHandleV`'s `hdv`), and neither stores `κ`. Here the fuel is **inside** the
scheduler: the scheduler handles `div_fuel k (λ_. loop)`, whose row is `Div`-free (`div_fuel`
handles `tick`), so the storing clauses of stages 2 and 5 apply as they are.

* The loop is `iterate` over the state `c`. Each turn is stage 6's segmentation, returning `c`
  (`segR`): the lend ends before the suspension, `[let-dtor]` holds `c` across it, and a fresh
  lend follows.
* The loop's `tick` is held by `[let-dtor]` too: the loop's row has `cancelled`, so `[let]` would
  refuse the live file across the tick.
* The step's *close* is `c`'s destructor (stage 3): fuel exhaustion closes the file.
* A cancel unwinds the turn's `[let-dtor]` frame, which closes the file.
* A dropped `κ` (`κ.2`, stage 5) cancels the captured turn, the same unwind.

Every program here is a closed `CDerives` derivation for every budget `k`: `resourceSafety`
covers it, and `eval` checks the closes.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind
open BoCa.Fig16.LogRel.Core.DtorUnwind.Files
open BoCa.Fig16.LogRel.Core.DtorUnwind.Suspend
open BoCa.Fig16.LogRel.Core.DtorUnwind.Await
open BoCa.Fig16.LogRel.Core.DtorUnwind.Lend (deadOwnFree)
open BoCa.Fig16.LogRel.Core.AwaitCancel (Esched csSched)
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-! ### Segments that hand the source back -/

/-- Stage 6's segments around `M`, answering the source. -/
def segR (cb₁ cb₂ b M : Expr) : Expr :=
  bindE (app2 withbor (.var 0) cb₁)
    (.letpair (.var 0)
      (letDE [none, some b]
        (bindE (app2 withbor (.var 2) cb₂) (.letpair (.var 0) (.var 1)))
        M))

theorem d_segR {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {Src CB : VTy} {S SD : Row}
    {cb₁ cb₂ b M : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' withbor (.val (.lolli Src (.lolli CB (.tensor Src .unit)))))
    (hcb₁ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb₁ (.val CB))
    (hcb₂ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb₂ (.val CB))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr Src (CTy.effOf SD .unit))))
    (hNZ : S.NZ) (hUq : S.Uniq) (hUnr : ¬ S.UnrD) (hDS : RowLe SD S)
    (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives Δ (⟨Src, true⟩ :: Γ) (segR cb₁ cb₂ b M) (.comp (CTy.effOf S Src)) := by
  refine .bind (A := .tensor Src .unit) (.left (deadSplit hΓ))
    (.ret (.lolliE (.right (deadSplit hΓ)) (hcb₁ _ (.cons hΓ))
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (hw _ (.cons hΓ))))) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP))) ?_
  have hds : Dtors Δ SD (⟨.unit, true⟩ :: ⟨Src, true⟩ :: ⟨.tensor Src .unit, false⟩ ::
      ⟨Src, false⟩ :: Γ) [none, some b] :=
    .pers rfl (.drop hb (.tail (by cdead)))
  refine CDerives.effLetD (A := .unit) (split_kill _).toP hNZ hUq (fun h => absurd h hUnr) hDS
    hSDc hSDd hfin hds (hM _ (kill_dead _)) ?_
  refine .bind (A := .tensor Src .unit) (.right (.right (.left (.dead (.dead (deadSplit hΓ))))))
    (.ret (.lolliE (.dead (.dead (.right (.dead (.dead (deadSplit hΓ)))))) (hcb₂ _ (by cdead))
      (.lolliE (.dead (.dead (.left (.dead (.dead (deadSplit hΓ))))))
        (.var (.there (.there (.here (by cdead))))) (hw _ (by cdead))))) ?_
  refine .tensorE (.left (.right (.right (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.var (.here (by cdead))) ?_
  exact .effSub (RowLe.nil S) (.ret (.var (.skip rfl (.here (.cons (.drop rfl (.drop rfl
    (.cons (.cons (.cons hΓ.toP))))))))))

/-! ### The loop's rows -/

/-- The facts `[let-dtor]` needs of a row, bundled. -/
structure RowOK (S : Row) : Prop where
  nz : S.NZ
  uq : S.Uniq
  unr : ¬ S.UnrD
  le : RowLe SD S
  fin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin

/-- `tick` added in front of a row whose names are not `Div`'s. -/
theorem rowOK_tick {S : Row} (h : RowOK S) (hd : ∀ o ∈ S, o.n ≠ divEff) :
    RowOK (tickSig :: S) where
  nz := by
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · decide
    · exact h.nz o ho
  uq := by
    refine List.Pairwise.cons (fun o ho hk => hd o ho ?_) h.uq
    exact hk.1.symm
  unr := by
    rintro ⟨o, ho, hu⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · rcases hu with hu | ⟨hc, -⟩
      · cases hu
      · simp [tickSig, capB] at hc
    · exact h.unr ⟨o, ho, hu⟩
  le := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := h.le n i o hf
    refine ⟨o', ?_, hle⟩
    have hm := (Row.find_mem hf').1
    obtain ⟨-, rfl, rfl⟩ := Row.find_mem hf'
    unfold Row.find
    rw [List.find?_cons_of_neg (by
      simp only [decide_eq_true_eq, not_and]
      intro hn; exact absurd (by rw [hn]; rfl) (hd o' hm))]
    exact hf'
  fin := by
    intro n i o hf hr
    unfold Row.find at hf
    rw [List.find?_cons] at hf
    split at hf
    · cases hf; simp [OpSig.finRead, tickSig, capB] at hr
    · exact h.fin n i o hf hr

theorem rowOK_SY : RowOK SY := ⟨SY_nz, SY_uniq, SY_not_unrD, SD_le_SY, hfin_y⟩
theorem rowOK_S2 : RowOK Cancel.S2 :=
  ⟨Cancel.S2_nz, Cancel.S2_uniq, Cancel.S2_not_unrD, Cancel.SD_le_S2, Cancel.hfin_await⟩

theorem SY_noDiv : ∀ o ∈ SY, o.n ≠ divEff := by
  intro o ho
  simp only [SY, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> decide

theorem S2_noDiv : ∀ o ∈ Cancel.S2, o.n ≠ divEff := by
  intro o ho
  simp only [Cancel.S2, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> decide

/-! ### The loop -/

/-- The step `λc. ⟨c′ ← segR …; inr c′, drop_File c⟩`. -/
def stepT (cb : UInt32 → Expr) (M : Expr) : Val :=
  .lam (withPair (bindE (.var 2) (bindE (segR (cb 10) (cb 1) dFileB M) (.inj₂ (.var 0))))
    (.app (.val (.lam dFileB)) (.var 2)))

abbrev Ans : VTy := .sum .unit .unit

theorem d_stepT {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} (hS : RowOK S) {cb : UInt32 → Expr}
    (hcb : ∀ k (Γ' : Ctx VTy), Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' (cb k) (.val CBm))
    {M : Expr}
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives LifeCtx.empty Γ (.val (stepT cb M)) (.val (iterStepTy S File .unit .unit)) := by
  refine Loop.d_stepD hΓ ?_ d_dFile hS.le
  refine .bind (A := File) (.dead (.dead (.left (deadSplit hΓ))))
    (.ret (.var (.there (.there (.here hΓ.toP))))) ?_
  have hd : Ctx.Dead (⟨VTy.unit, false⟩ :: ⟨VTy.sum .unit .unit, false⟩ :: ⟨File, false⟩ :: Γ) :=
    by cdead
  refine .effLet (A := File) (.left (deadSplit hd)) (fun _ => deadOwnFree (.cons hd))
    (fun _ => banged_dead (.cons hd))
    (d_segR hd d_withborI32 (hcb 10) (hcb 1) d_dFile hS.nz hS.uq hS.unr hS.le SD_not_cancels
      SD_divB hS.fin hM) ?_
  exact .effSub (RowLe.nil S) (.ret (.sumI₂ (.var (.here (.cons hd.toP)))))

/-- The loop's body, its dead binder at `0` and the file at `1`:
`let n = tick () in case n {next → iterate (stepT, c) | close → drop_File c to u. inr u}`, the
file held across the tick by `[let-dtor]`. -/
def loopT (step : Val) : Expr :=
  letDE [none, some dFileB]
    (.case (.var 0)
      (bindE (.val (.prim .iterate)) (bindE (.pair (.val step) (.var 4)) (.app (.var 1) (.var 0))))
      (bindE (.app (.val (.lam dFileB)) (.var 3)) (.inj₂ (.var 0))))
    tickE

theorem d_loopT {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} (hS : RowOK S)
    (hd : ∀ o ∈ S, o.n ≠ divEff) {step : Val}
    (hstep : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' (.val step) (.val (iterStepTy (tickSig :: S) File .unit .unit))) :
    CDerives LifeCtx.empty (⟨.unit, false⟩ :: ⟨File, true⟩ :: Γ) (loopT step)
      (.comp (CTy.effOf (tickSig :: S) Ans)) := by
  have hT := rowOK_tick hS hd
  have hds : Dtors LifeCtx.empty SD (⟨.unit, false⟩ :: ⟨File, true⟩ :: Γ) [none, some dFileB] :=
    .dead (.drop d_dFile (.tail hΓ))
  refine CDerives.effLetD (A := nextTy) (split_kill _).toP hT.nz hT.uq (fun h => absurd h hT.unr)
    hT.le SD_not_cancels SD_divB hT.fin hds
    (.effPerform (S := tickSig :: S) (o := tickSig) (by simp [Row.find, List.find?]) rfl rfl
      (.unitI (kill_dead _).toP)) ?_
  refine .sumE (.left (.dead (.right (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP)))) ?_ ?_
  · refine .bind (.right (.dead (.dead (.right (deadSplit hΓ)))))
      (.ret (.bangE (.iterate (tickSig :: S) File .unit .unit (Row.divB_tick _)
        (.cons (.cons (.cons (.cons hΓ.toP))))))) ?_
    refine .bind (.right (.right (.dead (.dead (.left (deadSplit hΓ))))))
      (.ret (.tensorI (.dead (.dead (.dead (.dead (.right (deadSplit hΓ))))))
        (hstep _ (by cdead))
        (.var (.there (.there (.there (.there (.here hΓ.toP)))))))) ?_
    exact .app (.right (.left (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.force (C := .arr (.tensor (iterStepTy (tickSig :: S) File .unit .unit) File)
        (CTy.effOf (tickSig :: S) Ans))
        (.there (.here (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))
      (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))
  · refine .effLet (A := .unit) (split_kill' _).toP (fun _ => deadOwnFree (kill_dead _))
      (fun _ => banged_dead (kill_dead _))
      (.effSub hT.le (.app (split_kill _).toP (d_dFile _ (kill_dead _))
        (.skip rfl (.there (.there (.here hΓ.toP)))))) ?_
    exact .effSub (RowLe.nil _) (.ret (.sumI₂ (.var (.here (kill_dead _).toP))))

/-- The task under the fuel: `c ← alloc 1; t ← (λ_. loopT, k); df ← div_fuel; r ← df t; dropB r`. -/
def taskBody (step : Val) (k : UInt32) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val (Val.i32 1)))
    (bindE (.pair (.val (.lam (loopT step))) (.val (Val.i32 k)))
      (bindE (.val divFuelV) (bindE (.app (.var 0) (.var 1)) (.case (.var 0) (.var 0) (.var 0)))))

theorem d_taskBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} (hS : RowOK S)
    (hd : ∀ o ∈ S, o.n ≠ divEff) {step : Val}
    (hstep : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' (.val step) (.val (iterStepTy (tickSig :: S) File .unit .unit)))
    (k : UInt32) :
    CDerives LifeCtx.empty Γ (taskBody step k) (.comp (CTy.effOf S .unit)) := by
  refine .bind (A := File) (deadSplit hΓ)
    (.ret (appW (.lit (.i32 1) (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (A := .tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: S) Ans))) I32)
    (.left (deadSplit hΓ))
    (.ret (.tensorI (.left (deadSplit hΓ)) (.thunkV rfl (.lamDead (d_loopT hΓ hS hd hstep)))
      (.lit (.i32 k) (.cons hΓ.toP)))) ?_
  refine .bind (.right (.dead (deadSplit hΓ)))
    (.ret (.bangE (.divFuel S Ans hd (.cons (.cons hΓ.toP))))) ?_
  refine .effLet (A := Ans) (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => deadOwnFree (by cdead)) (fun _ => banged_dead (by cdead)) ?_ ?_
  · exact .app (.left (.right (.dead (deadSplit hΓ))))
      (.force (C := .arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: S) Ans))) I32)
        (CTy.effOf S Ans)) (.here (.cons (.cons hΓ.toP))))
      (.there (.here (.cons hΓ.toP)))
  · exact .sumE (.left (deadSplit (by cdead))) (.var (.here (by cdead)))
      (.effSub (RowLe.nil S) (.ret (.var (.here (by cdead)))))
      (.effSub (RowLe.nil S) (.ret (.var (.here (by cdead)))))

/-! ### The schedulers -/

/-- The immediate scheduler answering every `await` with `dec`. -/
def schedWith (dec : Val) (e : Expr) : Expr :=
  bindE Cancel.clsS (bindE Cancel.hrS (bindE (hndTerm 1 [.lin, .cancel] 0 1 e)
    (bindE (.val dec) (.app (.var 1) (.var 0)))))

theorem d_schedWith {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {dec : Val}
    (hdec : ∀ Γ' : Ctx VTy, Ctx.DeadP Γ' → CDerives LifeCtx.empty Γ' (.val dec) (.val EffPrograms.Flag))
    {e : Expr}
    (he : CDerives LifeCtx.empty (⟨retTy SD .unit Cancel.StR, false⟩ ::
      ⟨clausesTy SD Cancel.StR Esched Cancel.fs2, false⟩ :: kill Γ)
      e (.comp (CTy.effOf Cancel.S2 .unit))) :
    CDerives LifeCtx.empty Γ (schedWith dec e) (.comp (CTy.effOf SD EffPrograms.Flag)) := by
  refine .bind (split_kill Γ).toP (.ret (.tensorI (deadSplit (kill_dead Γ))
    (Cancel.d_clS (kill_dead Γ)) (.tensorI (deadSplit (kill_dead Γ)) (Cancel.d_ccS (kill_dead Γ))
      (.unitI (kill_dead Γ).toP)))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (Cancel.d_hrS (.cons (kill_dead Γ)))) ?_
  refine .effLet (A := Cancel.StR) (.left (.left (split_kill Γ).toP))
    (fun h => absurd h SD_not_cancels) (fun h => absurd h Cancel.SD_not_unr) ?_ ?_
  · refine CDerives.effHandleCs (S := SD) (E := Esched) (n := 1) (A := .unit) (R := Cancel.StR)
      Cancel.fs2 csSched
      (.left (.left (deadSplit (kill_dead Γ)))) (.left (.right (deadSplit (kill_dead Γ))))
      (.here (.cons (kill_dead Γ).toP)) (.there (.here (kill_dead Γ).toP))
      (by decide) (by simp [fcloseSig]) (by simp) (by decide) ?_
    rw [Cancel.ofEff_S2]
    exact he
  · refine .bind (A := EffPrograms.Flag) (.right (.dead (.dead (deadSplit hΓ))))
      (.ret (hdec _ (by cdead))) ?_
    exact .app (.right (.left (.dead (.dead (deadSplit hΓ)))))
      (.force (C := .arr EffPrograms.Flag (CTy.effOf SD EffPrograms.Flag)) (.there (.here (by cdead))))
      (.here (by cdead))

/-! ### The closed programs, at every budget -/

def cancV' : Val := Val.inj₂ Val.unit
def goV : Val := Val.inj₁ Val.unit

def stepY : Val := stepT cbAdd yM
def stepA : Val := stepT cbAdd (awaitE 1)

theorem d_stepY (Γ' : Ctx VTy) (h : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' (.val stepY) (.val (iterStepTy (tickSig :: SY) File .unit .unit)) :=
  d_stepT h (rowOK_tick rowOK_SY SY_noDiv) (fun k _ h => d_cbAdd h k)
    (fun _ h => .effPerform (S := tickSig :: SY) (o := ySig) rfl rfl rfl (.unitI h.toP))

theorem d_stepA (Γ' : Ctx VTy) (h : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' (.val stepA)
      (.val (iterStepTy (tickSig :: Cancel.S2) File .unit .unit)) :=
  d_stepT h (rowOK_tick rowOK_S2 S2_noDiv) (fun k _ h => d_cbAdd h k)
    (fun _ h => .effAwait h rfl (AwaitCancel.cancellable_await _) rfl rfl
      AwaitCancel.cancelTarget_cancelled)

/-- (a) `y` resumed every turn; the fuel closes the loop. -/
def progRes (k : UInt32) : Expr := withFs (yH clRes (taskBody stepY k))
/-- (c) the first turn's `κ` stored and dropped (`κ.2`). -/
def progDrop (k : UInt32) : Expr := withFs (yH clDrop (taskBody stepY k))
/-- (b) cancelled at the first `await` (level-triggered). -/
def progCancel (k : UInt32) : Expr := withFs (schedWith cancV' (taskBody stepA k))
/-- (a′) every `await` resumed by the scheduler; the fuel closes the loop. -/
def progGo (k : UInt32) : Expr := withFs (schedWith goV (taskBody stepA k))

theorem d_progRes (k : UInt32) : CDerives LifeCtx.empty [] (progRes k) (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  exact d_yH (.cons (.cons .nil)) d_clRes
    (d_taskBody (by cdead) rowOK_SY SY_noDiv d_stepY k)

theorem d_progDrop (k : UInt32) : CDerives LifeCtx.empty [] (progDrop k) (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  exact d_yH (.cons (.cons .nil)) d_clDrop
    (d_taskBody (by cdead) rowOK_SY SY_noDiv d_stepY k)

theorem d_progCancel (k : UInt32) :
    CDerives LifeCtx.empty [] (progCancel k) (.comp (.ret EffPrograms.Flag)) := by
  refine d_withFsG (S := []) (A := EffPrograms.Flag) (by simp) rfl ?_
  show CDerives _ _ _ (.comp (CTy.effOf SD EffPrograms.Flag))
  exact d_schedWith (.cons (.cons .nil)) (fun _ h => .sumI₂ (.unitI h))
    (d_taskBody (by cdead) rowOK_S2 S2_noDiv d_stepA k)

theorem d_progGo (k : UInt32) :
    CDerives LifeCtx.empty [] (progGo k) (.comp (.ret EffPrograms.Flag)) := by
  refine d_withFsG (S := []) (A := EffPrograms.Flag) (by simp) rfl ?_
  show CDerives _ _ _ (.comp (CTy.effOf SD EffPrograms.Flag))
  exact d_schedWith (.cons (.cons .nil)) (fun _ h => .sumI₁ (.unitI h))
    (d_taskBody (by cdead) rowOK_S2 S2_noDiv d_stepA k)

/-- **Resource safety at every budget**, on each exit. -/
theorem progRes_safe (k : UInt32) : Safe (ℍ := ℍ) (progRes k) :=
  fun hs => resourceSafety (by decide) (d_progRes k) hs
theorem progDrop_safe (k : UInt32) : Safe (ℍ := ℍ) (progDrop k) :=
  fun hs => resourceSafety (by decide) (d_progDrop k) hs
theorem progCancel_safe (k : UInt32) : Safe (ℍ := ℍ) (progCancel k) :=
  fun hs => resourceSafety AwaitCancel.flag_persistent (d_progCancel k) hs
theorem progGo_safe (k : UInt32) : Safe (ℍ := ℍ) (progGo k) :=
  fun hs => resourceSafety AwaitCancel.flag_persistent (d_progGo k) hs

/-! ### The runs: the descriptor the file is closed with -/

def logRes (k : UInt32) : Expr := withLogCell (withFsLog (yH clRes (taskBody stepY k)))
def logDrop (k : UInt32) : Expr := withLogCell (withFsLog (yH clDrop (taskBody stepY k)))
def logCancel (k : UInt32) : Expr := withLogCell (withFsLog (schedWith cancV' (taskBody stepA k)))
def logGo (k : UInt32) : Expr := withLogCell (withFsLog (schedWith goV (taskBody stepA k)))

/-- Budget `0`: closed at the first tick, before any turn: `1`. -/
theorem res0_run : logIs (logRes 0) 1 = true := by decide
/-- Budget `1`: one turn resumed, then the fuel closes the loop: `1 + 11`. -/
theorem res1_run : logIs (logRes 1) 12 = true := by decide
set_option maxRecDepth 100000 in
/-- Budget `3`: three turns resumed, then closed: `1 + 33`. -/
theorem res3_run : logIs (logRes 3) 34 = true := by decide
/-- `κ` dropped at the first turn's `y`: closed on the cancel's unwind after segment 1: `11`. -/
theorem drop3_run : logIs (logDrop 3) 11 = true := by decide
/-- Cancelled at the first `await`: `11`. -/
theorem cancel3_run : logIs (logCancel 3) 11 = true := by decide
set_option maxRecDepth 100000 in
/-- Every `await` resumed by the scheduler: `34`. -/
theorem go3_run : logIs (logGo 3) 34 = true := by decide

/-! ### "Or it diverges": the unfueled program, stated, not derived

The real task has no budget: the runtime's `Div` clause (`DivRuntime.rtH`, every tick answered
*next*) in place of `div_fuel k`. Inside the scheduler that handler is not a `CDerives` term, and
the scheduler around the loop's `Div` row is `handle_general` (R-4). The statement below
elaborates; it is the target, not proved. Two routes would prove it:
* a simulation: every run prefix of the unfueled program with `n` ticks is matched, up to the
  `Div` handler's frame, by a run prefix of the fueled one at every budget `k ≥ n`, whose runs
  `progRes_safe` covers (a binary relation on configurations, which Core does not have);
* `handle_general`, then `runtime_every_run`. -/

/-- The task with the runtime's `Div` handler in place of `div_fuel`. -/
def taskBodyRt (step : Val) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val (Val.i32 1)))
    (BoCa.BoLo.hndE DivRuntime.rtH (bindE (.val .unit) (loopT step)))

def progResRt : Expr := withFs (yH clRes (taskBodyRt stepY))
def progDropRt : Expr := withFs (yH clDrop (taskBodyRt stepY))
def progCancelRt : Expr := withFs (schedWith cancV' (taskBodyRt stepA))

/-- **Safe, or it diverges**: every configuration a run reaches goes on or is a value; a value is
reached at the empty memory (every cell freed); every release finds its cell. -/
def OrDiverges (P : Expr) : Prop :=
  ∀ {μ : Heap} {e : Expr}, Steps (ℍ := ℍ) Adequacy.emptyMem P μ e →
    (IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e') ∧
    (IsVal e → μ = Adequacy.emptyMem) ∧
    (∀ (K : Kont) (ℓ : Loc), e = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ ℓ = some u)

/-- The stage-7 target for the unfueled task: not derived, obstruction not verified. -/
def Stage7Unfueled : Prop :=
  OrDiverges (ℍ := ℍ) progResRt ∧ OrDiverges (ℍ := ℍ) progDropRt ∧
    OrDiverges (ℍ := ℍ) progCancelRt

end BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait

end
