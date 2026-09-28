import Core.Folds

/-!
# Core — driving a delayed computation, and programs by `fixD`  `[spec §7]`

**The driver.** `driveE n` observes a loop `d : U(Loop A B)` at most `n` times: it returns
`inj₁ a` if a `next` finished with `a`, and otherwise closes `d` after the `n`-th observation
and returns `inj₂ b`, its residual.  It is a `CDerives` derivation at `F(A ⊕ B)` for every `n`
(`d_driveL`; at the delay `D A = Loop A 1`, `d_drive`), so
for a closed `e : U(D A)`, `e to d. driveE n` is an ordinary closed computation and the existing
adequacy applies to it unchanged (`drive_runs_unit`, `drive_runs_nat`: from the empty memory to
`now` or `closed`, and the empty memory).

**Programs**, each a `CDerives` derivation with no hand proof, run from the empty memory with no
cell left:

* `loopProg`: `fixD (λs. ⟨return later s, return s⟩) ()`, the loop that never finishes, observed
  five times and closed.
* `countDownProg`: `fixD` over the state `(n, acc) : N ⊗ N` — `now acc` at `n = 0`, else
  `later (n - 1, acc + 1)` — from `(3, 0)`, driven to its result `3`.
* `counterProg`: `fixD` over a cell `r : Ref N`.  Each `next` increments the cell in place by two
  `swap`s and emits `later r`; `close` frees the cell.  It never finishes; it is observed four
  times and closed.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The driver -/

/-- Observe `d` (index 0) at most `n` times, then close it. -/
def driveE : ℕ → Expr
  | 0 => bindE (.app (.var 0) (.val (.inj₂ .unit))) (.inj₂ (.var 0))
  | n + 1 => bindE (.app (.var 0) (.val (.inj₁ .unit))) (.case (.var 0) (.inj₁ (.var 0)) (driveE n))

theorem CDerives.loopOut {Δ Γ e A B} (h : CDerives Δ Γ e (.comp (.loop A B))) :
    CDerives Δ Γ e (.comp (loopUnroll A B)) := by
  rw [← CTy.loop_unroll]; exact .nuOut (CTy.loopBody_nuOk A B) h

theorem CDerives.loopIn {Δ Γ e A B} (h : CDerives Δ Γ e (.comp (loopUnroll A B))) :
    CDerives Δ Γ e (.comp (.loop A B)) :=
  .nuIn (CTy.loopBody_nuOk A B) (by rw [CTy.loop_unroll]; exact h)

/-- `d : U(Loop A B) ⊢ driveE n : F(A ⊕ B)`: observe at most `n` times, and close with the
residual `B` if the loop has not finished.  `[spec §7, §11]` -/
theorem d_driveL {Δ : LifeCtx} (A B : VTy) :
    ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ →
      CDerives Δ (⟨.thunk (.loop A B), true⟩ :: Γ) (driveE n) (.comp (.ret (.sum A B)))
  | 0, _, hΓ =>
      .bind (.left (deadSplit hΓ))
        (.proj₂ (.loopOut (.force (.here hΓ))))
        (.ret (.sumI₂ (.var (.here (.cons hΓ)))))
  | n + 1, _, hΓ =>
      .bind (.left (deadSplit hΓ))
        (.proj₁ (.loopOut (.force (.here hΓ))))
        (.sumE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
          (.ret (.sumI₁ (.var (.here (.cons (.cons hΓ))))))
          (d_driveL A B n (.cons (.cons hΓ))))

/-- `d : U(D A) ⊢ driveE n : F(A ⊕ 1)`: the driver at the delay, `Loop A 1`. -/
theorem d_drive {Δ : LifeCtx} (A : VTy) (n : ℕ) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.thunk (.delay A), true⟩ :: Γ) (driveE n) (.comp (.ret (.sum A .unit))) :=
  d_driveL A .unit n hΓ

/-- **The driver is an ordinary program**: for a closed `e : U(D A)` and every `n`,
`e to d. driveE n` is a closed computation of `F(A ⊕ 1)`. -/
theorem drive_derives {A : VTy} {e : Expr}
    (he : CDerives LifeCtx.empty [] e (.val (.thunk (.delay A)))) (n : ℕ) :
    CDerives LifeCtx.empty [] (bindE e (driveE n)) (.comp (.ret (.sum A .unit))) :=
  .bind .nil (.ret he) (d_drive A n .nil)

/-- The outcome of a driven run: `now` with a value of `A`, or closed. -/
theorem vC_sum_unit_pure {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hA : ∀ {ls a ρ}, vC true A ls δ a ρ → ρ = PMap.empty) (h : vC true (.sum A .unit) ls δ v ρ) :
    ρ = PMap.empty ∧ ((∃ a, v = .inj₁ a ∧ vC true A ls δ a PMap.empty) ∨ v = .inj₂ .unit) := by
  rcases h with ⟨a, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, ha⟩ | ⟨u, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, hu⟩
  · subst hσ₀
    rw [← eq_of_compS_empty_left hc] at ha
    obtain rfl := hA ha
    exact ⟨rfl, Or.inl ⟨a, rfl, ha⟩⟩
  · subst hσ₀
    obtain ⟨rfl, rfl⟩ := hu
    obtain rfl := eq_of_compS_empty_left hc
    exact ⟨rfl, Or.inr rfl⟩

/-- **Adequacy for `D 1`**: for a closed `e : U(D 1)` and every `n`, observing `n` times then
closing runs from the empty memory to `now ()` or `closed`, and the empty memory. -/
theorem drive_runs_unit {e : Expr}
    (he : CDerives LifeCtx.empty [] e (.val (.thunk (.delay .unit)))) (n : ℕ) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem (bindE e (driveE n)) Adequacy.emptyMem (.val v) ∧
      (v = .inj₁ .unit ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] (bindE e (driveE n))
      (fun _ v => Fig16.BoLo.pure (v = .inj₁ .unit ∨ v = .inj₂ .unit)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives (drive_derives he n))
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := .unit) (fun h => h.1) hv
    · exact ⟨rfl, Or.inl (by rw [ha.2])⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

/-- **Adequacy for `D N`**: the same, with a numeral as the result. -/
theorem drive_runs_nat {e : Expr}
    (he : CDerives LifeCtx.empty [] e (.val (.thunk (.delay natN)))) (n : ℕ) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem (bindE e (driveE n)) Adequacy.emptyMem (.val v) ∧
      ((∃ k, v = .inj₁ (num k)) ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] (bindE e (driveE n))
      (fun _ v => Fig16.BoLo.pure ((∃ k, v = .inj₁ (num k)) ∨ v = .inj₂ .unit))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives (drive_derives he n))
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := natN) (fun h => (vC_natN h).1) hv
    · obtain ⟨-, k, rfl⟩ := vC_natN ha
      exact ⟨rfl, Or.inl ⟨k, rfl⟩⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

/-! ### A delayed computation from a step and a state -/

/-- `s₀ to s. fixD step to f. ⟨(f s) π₁, (f s) π₂⟩ to d. driveE n`: the thunk
`⟨(f s) π₁, (f s) π₂⟩` is `fixD step s₀` as a value of `U(D A)`. -/
def progD (A : VTy) (s₀ : Expr) (step : Val) (n : ℕ) : Expr :=
  bindE s₀ (bindE (.app (.val (fixDV A)) (.val step))
    (bindE (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      (driveE n)))

/-- `f : U(S ⊸ D A), s : S ⊢ (f s) πᵢ`, inside `withPair`'s two binders. -/
theorem d_fs {A S : VTy} :
    CDerives LifeCtx.empty (withCtx [⟨.thunk (.arr S (.delay A)), true⟩, ⟨S, true⟩])
      (.app (.var 2) (.var 3)) (.comp (.delay A)) :=
  .app (.dead (.dead (.left (.right .nil)))) (.force (.there (.there (.here (.cons .nil)))))
    (.there (.there (.there (.here .nil))))

/-- `⟨(f s) π₁, (f s) π₂⟩ : U(D A)`. -/
theorem d_thunkFS {A S : VTy} :
    CDerives LifeCtx.empty [⟨.thunk (.arr S (.delay A)), true⟩, ⟨S, true⟩]
      (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      (.val (.thunk (.delay A))) :=
  .thunkV rfl (.delayIn (.withI (.proj₁ (.delayOut d_fs)) (.proj₂ (.delayOut d_fs))))

theorem d_progD {A S : VTy} {s₀ : Expr} {step : Val}
    (hs₀ : CDerives LifeCtx.empty [] s₀ (.val S))
    (hstep : CDerives LifeCtx.empty [⟨S, false⟩] (.val step)
      (.val (.bang (.thunk (stepDC A S))))) (n : ℕ) :
    CDerives LifeCtx.empty [] (progD A s₀ step n) (.comp (.ret (.sum A .unit))) :=
  .bind .nil (.ret hs₀)
    (.bind (.right .nil)
      (.ret (.bangE (.lolliE (deadSplit (.cons .nil)) hstep (.fixD A S (.cons .nil)))))
      (.bind (.left (.left .nil)) (.ret d_thunkFS) (d_drive A n (.cons (.cons .nil)))))

/-- A run's outcome when it ends with no cell left: `inj₁` of a numeral, or `inj₂ ()`. -/
def delayOutcome : Outcome → Option (Option Nat)
  | .value ⟨.inj₁ e, _⟩ false => (numOf e).map some
  | .value ⟨.inj₂ .unit, _⟩ false => some none
  | _ => none

/-- A run's outcome when it ends with no cell left: `inj₁ ()` or `inj₂ ()`. -/
def delayOutcomeU : Outcome → Option Bool
  | .value ⟨.inj₁ .unit, _⟩ false => some true
  | .value ⟨.inj₂ .unit, _⟩ false => some false
  | _ => none

/-! ### (b) The loop that never finishes -/

/-- `λs. ⟨return inj₂ s, return s⟩ : 1 ⊸ F(1 ⊕ 1) & F 1`: always `later`. -/
def loopStep : Val := .lam (withPair (.inj₂ (.var 2)) (.var 2))

theorem d_loopStep {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val loopStep) (.val (.bang (.thunk (stepDC .unit .unit)))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI
    (.ret (.sumI₂ (.var (.there (.there (.here hΓ))))))
    (.ret (.var (.there (.there (.here hΓ)))))))

/-- `loop = fixD loopStep ()`, observed `n` times and closed. -/
def loopProg (n : ℕ) : Expr := progD .unit (.val .unit) loopStep n

theorem loopProg_derives (n : ℕ) :
    CDerives LifeCtx.empty [] (loopProg n) (.comp (.ret (.sum .unit .unit))) :=
  d_progD (.unitI .nil) (d_loopStep (.cons .nil)) n

/-- **The loop, observed five times and closed**: from the empty memory to `inj₂ ()` (closed)
or `inj₁ ()`, and the empty memory. -/
theorem loopProg_runs : ∃ v : Val,
    BoCa.BoLo.Steps Adequacy.emptyMem (loopProg 5) Adequacy.emptyMem (.val v) ∧
      (v = .inj₁ .unit ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] (loopProg 5)
      (fun _ v => Fig16.BoLo.pure (v = .inj₁ .unit ∨ v = .inj₂ .unit)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives (loopProg_derives 5))
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := .unit) (fun h => h.1) hv
    · exact ⟨rfl, Or.inl (by rw [ha.2])⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

/-- The interpreter: closed after five `later`s, no cell left. -/
theorem loopProg_eval : delayOutcomeU (eval (loopProg 5)) = some false := by decide

/-! ### (a) A terminating loop: count down, counting up -/

/-- `natN` unrolls to `1 ⊕ N`. -/
theorem natN_unroll : VTy.inst natN natBody = .sum .unit natN := rfl

/-- `next` at `(n, acc)`: `now acc` at `n = 0`, else `later (n - 1, acc + 1)`. -/
def countDownNext : Expr :=
  .letpair (.var 2)
    (.case (.var 1) (.seq (.var 0) (.inj₁ (.var 1))) (.inj₂ (.pair (.var 0) (.inj₂ (.var 1)))))

/-- `close` at `(n, acc)`: free both numerals. -/
def countDownClose : Expr :=
  .letpair (.var 2) (.seq (.app freeNatE (.var 1)) (.app freeNatE (.var 0)))

/-- `λp. ⟨countDownNext, countDownClose⟩ : N ⊗ N ⊸ F(N ⊕ N ⊗ N) & F 1`. -/
def countDownStep : Val := .lam (withPair countDownNext countDownClose)

theorem d_countDownStep {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val countDownStep)
      (.val (.bang (.thunk (stepDC natN (.tensor natN natN))))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · refine .tensorE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ)))) ?_
    refine .sumE (.right (.left (.dead (.dead (.dead (deadSplit hΓ))))))
      (natN_unroll ▸ CDerives.unroll (A := natBody) (.var (.there (.here (.cons (.cons (.cons hΓ))))))) ?_ ?_
    · exact .unitE (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ)))))))
        (.ret (.sumI₁ (.var (.there (.here (.cons (.cons (.cons (.cons hΓ)))))))))
    · exact .ret (.sumI₂ (.tensorI (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ)))))))
        (.roll natBody_noMut natN_closed
          (.sumI₂ (.var (.there (.here (.cons (.cons (.cons (.cons hΓ)))))))))))
  · refine .tensorE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ)))) ?_
    refine .unitE (.right (.left (.dead (.dead (.dead (deadSplit hΓ))))))
      (.lolliE (.dead (.left (.dead (.dead (.dead (deadSplit hΓ))))))
        (.var (.there (.here (.cons (.cons (.cons hΓ))))))
        (d_freeNat (.cons (.cons (.cons (.cons (.cons hΓ)))))))
      (.ret (.lolliE (.left (.dead (.dead (.dead (.dead (deadSplit hΓ))))))
        (.var (.here (.cons (.cons (.cons (.cons hΓ))))))
        (d_freeNat (.cons (.cons (.cons (.cons (.cons hΓ))))))))

/-- `fixD countDownStep (3, 0)`, driven at most ten times. -/
def countDownProg : Expr := progD natN (.pair (.val (num 3)) (.val (num 0))) countDownStep 10

theorem countDownProg_derives :
    CDerives LifeCtx.empty [] countDownProg (.comp (.ret (.sum natN .unit))) :=
  d_progD (.tensorI .nil (d_num .nil 3) (d_num .nil 0)) (d_countDownStep (.cons .nil)) 10

/-- **The count, driven to its result**: from the empty memory to `now k` for a numeral `k`, or
`closed`, and the empty memory. -/
theorem countDownProg_runs : ∃ v : Val,
    BoCa.BoLo.Steps Adequacy.emptyMem countDownProg Adequacy.emptyMem (.val v) ∧
      ((∃ k, v = .inj₁ (num k)) ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] countDownProg
      (fun _ v => Fig16.BoLo.pure ((∃ k, v = .inj₁ (num k)) ∨ v = .inj₂ .unit))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives countDownProg_derives)
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := natN) (fun h => (vC_natN h).1) hv
    · obtain ⟨-, k, rfl⟩ := vC_natN ha
      exact ⟨rfl, Or.inl ⟨k, rfl⟩⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

/-- The interpreter: `now 3`, no cell left. -/
theorem countDownProg_eval : delayOutcome (eval countDownProg) = some (some 3) := by decide

/-! ### (c) A loop that owns a cell -/

/-- `next` at `r : Ref N`: `swap r () to (r₁, n). swap r₁ (n + 1) to (r₂, u). u; later r₂`. -/
def counterNext : Expr :=
  .letpair (.app (.app swap (.var 2)) (.val .unit))
    (.letpair (.app (.app swap (.var 1)) (.inj₂ (.var 0))) (.seq (.var 0) (.inj₂ (.var 1))))

/-- `close` at `r`: free the cell and its numeral. -/
def counterClose : Expr := .app freeNatE (.app (.val (.prim .free)) (.var 2))

/-- `λr. ⟨counterNext, counterClose⟩ : Ref N ⊸ F(1 ⊕ Ref N) & F 1`. -/
def counterStep : Val := .lam (withPair counterNext counterClose)

theorem d_counterStep {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val counterStep)
      (.val (.bang (.thunk (stepDC .unit (.ref natN))))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · refine .tensorE (B := natN) (.dead (.dead (.left (deadSplit hΓ))))
      (.lolliE (.dead (.dead (.right (deadSplit hΓ)))) (.unitI (.cons (.cons (.cons hΓ))))
        (.lolliE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ))))
          (.swap (.cons (.cons (.cons hΓ)))))) ?_
    refine .tensorE (B := .unit) (.left (.left (.dead (.dead (.dead (deadSplit hΓ))))))
      (.lolliE (.left (.right (.dead (.dead (.dead (deadSplit hΓ))))))
        (.roll natBody_noMut natN_closed
          (.sumI₂ (.var (.here (.cons (.cons (.cons (.cons hΓ))))))))
        (.lolliE (.dead (.left (.dead (.dead (.dead (deadSplit hΓ))))))
          (.var (.there (.here (.cons (.cons (.cons hΓ))))))
          (.swap (.cons (.cons (.cons (.cons (.cons hΓ)))))))) ?_
    exact .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))
      (.ret (.sumI₂ (.var (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
  · exact .ret (.lolliE (.dead (.dead (.left (deadSplit hΓ))))
      (.lolliE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ))))
        (.free (.cons (.cons (.cons hΓ)))))
      (d_freeNat (.cons (.cons (.cons hΓ)))))

/-- `fixD counterStep (alloc 0)`, observed four times and closed. -/
def counterProg : Expr := progD .unit (.app (.val (.prim .alloc)) (.val (num 0))) counterStep 4

theorem counterProg_derives :
    CDerives LifeCtx.empty [] counterProg (.comp (.ret (.sum .unit .unit))) :=
  d_progD (.lolliE .nil (d_num .nil 0) (.alloc .nil)) (d_counterStep (.cons .nil)) 4

/-- **The counter, observed four times and closed**: from the empty memory to `inj₂ ()` or
`inj₁ ()`, and the empty memory; `close` has freed the cell. -/
theorem counterProg_runs : ∃ v : Val,
    BoCa.BoLo.Steps Adequacy.emptyMem counterProg Adequacy.emptyMem (.val v) ∧
      (v = .inj₁ .unit ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] counterProg
      (fun _ v => Fig16.BoLo.pure (v = .inj₁ .unit ∨ v = .inj₂ .unit)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives counterProg_derives)
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := .unit) (fun h => h.1) hv
    · exact ⟨rfl, Or.inl (by rw [ha.2])⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

set_option maxRecDepth 100000 in
/-- The interpreter: closed after four `later`s, no cell left. -/
theorem counterProg_eval : delayOutcomeU (eval counterProg) = some false := by decide

end BoCa.Fig16.LogRel.Core

end
