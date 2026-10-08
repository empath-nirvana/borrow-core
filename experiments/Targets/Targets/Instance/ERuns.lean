import Targets.Instance.E1

/-!
# The Instance — the (E) programs' runs: tools

* `runsTo_of_calm`: a program that reaches a value calmly (quietly, and around cells it allocates
  and releases, `Calm`) runs to it under every runner, showing no event: every complete run is that
  run up to the cells' locations (`obsFrom_calm_iff`).
* `cellQuiet_resumeCl`: the clause `op (_, k) ⇒ resume k ()` at a linear or affine operation
  resumes the handled computation in place, around `κ`'s cell (SPEC §25).
* `quiet_hunwind`: a raise caught by a handler of its name, with no frame between.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE opPayload hndE hndVal kappa clauseAt capTag kappaAt
  kappaC kappaCBody kappaCell freeE)
open Targets (RowForm EffCtx HeadChain)

section Obs
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- The complete runs from a value: the empty run, answering the value, showing nothing. -/
theorem obsFrom_val_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (v : Val) (w : OVal)
    (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, v.1), s) w tr ↔ w.1 = v.1 ∧ tr = [] := by
  constructor
  · rintro ⟨q, ⟨hp, -⟩, hv, htr⟩
    cases hp with
    | nil => exact ⟨hv.symm, htr.symm⟩
    | cons hst _ => exact (no_rstep_val R v hst).elim
  · rintro ⟨hw, rfl⟩
    exact ⟨[], ⟨.nil, isVal_val μ v⟩, hw.symm, rfl⟩

/-- **A program that reaches a value calmly runs to it, showing no event**, under every runner. -/
theorem runsTo_of_calm (R : (𝕊).Runner) {e : Expr} {v : Val} (h : Calm (ℍ := ℍ) e (.val v)) :
    (𝕊).RunsTo R e (OVal.ofVal v) [] := by
  have key : ∀ w tr, (𝕊).ObsFrom R ((𝕊).rinit R e) w tr ↔ w.1 = v.1 ∧ tr = [] := fun w tr =>
    (obsFrom_calm_iff R (μ := Adequacy.emptyMem) (s := R.s₀) finDom_empty h w tr).trans
      (obsFrom_val_iff R v w tr)
  refine ⟨(key _ _).mpr ⟨rfl, rfl⟩, fun q hq => ?_⟩
  obtain ⟨⟨w, hw⟩, -⟩ := hq.2
  have hk := (key w ((𝕊).obs q)).mp ⟨q, hq, hw, rfl⟩
  refine ⟨hw.trans ?_, hk.2⟩
  exact hk.1

end Obs

/-! ### Calls -/

/-- `f V` with `f` the variable `0`, the variable filled by a closed `W`. -/
theorem appE_var0_subst {V : Expr} (hV : closedAt 0 V = true) (W : Val)
    (hW : closedAt 0 W.1 = true) : (appE (.var 0) V).subst 0 W = appE W.1 V := by
  simp only [appE, Expr.shift, Expr.subst]
  rw [subst_closedAt V W hV (Nat.zero_le _), shift_closedAt W.1 1 hW (Nat.zero_le _),
    val_shift_closed hW]
  simp [Expr.subst]

/-- **`let f = λx. b in f (λ_. M)`** reaches `b` with the callback for `x`, by β-steps. -/
theorem quiet_call_lam {b M : Expr} (hb : closedAt 0 (Expr.lam b) = true)
    (hM : closedAt 0 M = true) :
    Quiet (ℍ := ℍ) (bindE (.lam b) (appE (.var 0) (.lam M))) (b.subst 0 (Val.lam M)) := by
  have hLM : closedAt 0 (Expr.lam M) = true := by simpa [closedAt] using closedAt_of_zero hM 1
  have h₁ := quiet_beta (ℍ := ℍ) .hole (appE (.var 0) (.lam M)) (Val.lam b)
  rw [appE_var0_subst hLM (Val.lam b) hb] at h₁
  exact h₁.trans ((quiet_appE (ℍ := ℍ) .hole (.lam b) (Val.lam M)).trans
    (quiet_beta (ℍ := ℍ) .hole b (Val.lam M)))

/-- **`hof` calls its callback**: `let f = hof in f (λ_. M)` reaches `M` by β-steps. -/
theorem quiet_hof_call {M : Expr} (hM : closedAt 0 M = true) :
    Quiet (ℍ := ℍ) (bindE hofE (appE (.var 0) (.lam M))) M := by
  have hLM : closedAt 0 (Expr.lam M) = true := by simpa [closedAt] using closedAt_of_zero hM 1
  refine (quiet_call_lam (b := appE (.var 0) .unit) rfl hM).trans ?_
  rw [appE_var0_subst rfl (Val.lam M) hLM]
  refine (quiet_appE (ℍ := ℍ) .hole (.lam M) Val.unit).trans ?_
  have h := quiet_beta (ℍ := ℍ) .hole M Val.unit
  rwa [subst_closedAt M Val.unit hM (le_refl _)] at h

/-! ### Catches -/

theorem resumeE_var0_subst (κ : Val) (hκ : closedAt 0 κ.1 = true) :
    (resumeE (.var 0) .unit).subst 0 κ = resumeE κ.1 .unit := by
  have h1 : Expr.shift 1 0 κ.1 = κ.1 := shift_closedAt κ.1 1 hκ (Nat.zero_le _)
  simp only [resumeE, Expr.subst, Expr.shift, val_shift_closed hκ, h1]
  simp [Expr.subst]

theorem closedAt_resumeE {k : Expr} (hk : closedAt 0 k = true) :
    closedAt 0 (resumeE k .unit) = true := by
  have h1 : Expr.shift 1 0 k = k := shift_closedAt k 1 hk (Nat.zero_le _)
  simp [resumeE, closedAt, h1, closedAt_of_zero hk 1]

/-- **A raise caught by a handler of its name**, the raise directly in the handler's body. -/
theorem quiet_hunwind (K₀ : Kont) (n i : UInt32) (qs hr hs c v : Val)
    (hc : clauseAt hs.1 i.toNat = some c) :
    Quiet (ℍ := ℍ) (K₀.plug (hndE (hndVal n qs hr hs) (raiseE (.val (opPayload n i v)))))
      (K₀.plug (.app (.val c) (.val v))) :=
  Quiet.head K₀ (fun μ => Head.hunwind μ n i qs hr hs c v .hole hc rfl) rfl rfl

/-- `op (_, k) ⇒ resume k ()`, as a value. -/
def resumeClV : Val := ⟨resumeClE, .lam⟩

/-- The resumer's clauses, as a value. -/
def resumerCsV : Val := ⟨clausesE [resumeClE], .pair .lam .unit⟩

/-- **The resumer's catch, around `κ`'s cell**: at a linear or affine operation, the clause
`op (_, k) ⇒ resume k ()` resumes the handled computation at `()` in place.  The catch and the
allocation; at the cell's location `ℓ`, `κ`'s β-step, the clause and `κ`'s resume branch up to the
release of `ℓ`; after it, the rest of the resume branch (`kappaC_resume_parts`). -/
theorem cellQuiet_resumeCl (aff : Bool) (K₀ : Kont) (n : UInt32) (qs hr : Val) (K : Kont)
    (v : Val) (hK : K.HasHnd n = false)
    (htag : kappaAt (capTag qs.1 (0 : UInt32).toNat) n (hndVal n qs hr resumerCsV) K =
      kappaCell aff n (hndVal n qs hr resumerCsV) K)
    (hH : closedAt 0 (hndVal n qs hr resumerCsV).1 = true) (hKc : closedAt 0 (K.plug .unit) = true) :
    CellQuiet (ℍ := ℍ)
      (K₀.plug (hndE (hndVal n qs hr resumerCsV) (K.plug (performE (.val (opPayload n 0 v))))))
      (K₀.plug (hndE (hndVal n qs hr resumerCsV) (K.plug (.val Val.unit)))) := by
  set H := hndVal n qs hr resumerCsV with hHdef
  have hh : ∀ μ, Head (ℍ := ℍ) μ (hndE H (K.plug (performE (.val (opPayload n 0 v))))) μ
      (.app (.val resumeClV) (.pair (.val v) (kappaCell aff n H K))) := by
    intro μ
    have h := Head.hop (ℍ := ℍ) μ n 0 qs hr resumerCsV resumeClV v K
      (clauseAt_clausesE [resumeClE] 0 .lam rfl) hK
    rwa [htag] at h
  refine ⟨K₀.comp (.appR (.val resumeClV) (.pairR v
    (.appR (.val (Val.lam (kappaCBody aff n H K))) .hole))), ?_, fun ℓ => ?_⟩
  · rw [Kont.plug_comp]
    exact Quiet.head K₀ hh rfl rfl
  refine ⟨K₀.comp (Kont.appL (Kont.seq .hole (kResV H K)) Val.unit), ?_, ?_⟩
  · rw [Kont.plug_comp, Kont.plug_comp]
    have hκc : closedAt 0 (kappaC aff ℓ n H K) = true := closedAt_kappaC aff ℓ n hH hKc
    have hb₀ := Quiet.head (ℍ := ℍ) (.appR (.val resumeClV) (.pairR v .hole))
      (fun μ => Head.beta μ (kappaCBody aff n H K) (Val.loc ℓ)) rfl rfl
    rw [kappaCBody_subst] at hb₀
    refine (hb₀.plug K₀).trans ?_
    let κ : Val := ⟨kappaC aff ℓ n H K, isVal_kappaC aff ℓ n H K⟩
    have h₁ := quiet_beta (ℍ := ℍ) K₀ (.letpair (.var 0) (resumeE (.var 0) .unit)) (Val.pair v κ)
    have e₁ : Expr.subst 0 (Val.pair v κ) (.letpair (.var 0) (resumeE (.var 0) .unit)) =
        .letpair (.val (Val.pair v κ)) (resumeE (.var 0) .unit) := by
      simp [Expr.subst, resumeE, Expr.shift, Val.pair]
    rw [e₁] at h₁
    refine (show Quiet (ℍ := ℍ) (K₀.plug (.app (.val resumeClV) (.pair (.val v) (kappaC aff ℓ n H K))))
      _ from h₁).trans ?_
    have h₂ := quiet_letpair (ℍ := ℍ) K₀ v κ (resumeE (.var 0) .unit)
    have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0) (resumeE (.var 0) .unit)) =
        resumeE κ.1 .unit := by
      rw [val_shift_closed (v := κ) hκc, resumeE_var0_subst κ hκc,
        subst_closedAt _ v (closedAt_resumeE hκc) (le_refl _)]
    rw [e₂] at h₂
    refine h₂.trans ?_
    refine (quiet_resumeE (ℍ := ℍ) K₀ κ.1 Val.unit).trans ?_
    exact (kappaC_resume_parts aff ℓ n H K Val.unit).1.plug K₀
  · rw [Kont.plug_comp]
    exact (kappaC_resume_parts aff ℓ n H K Val.unit).2.plug K₀

end Targets.Inst

end
