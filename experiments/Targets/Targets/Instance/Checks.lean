import Targets.Instance.CheckPrograms
import Targets.A.UnaryLaws
import Targets.Instance.Restricted.NoInterception

/-!
# The Instance — four statement checks, each a typed program and its computed run

Each check runs a program typed by today's kernel (`tier1Open`, at an admissible effect context
`ΞA`) on our machine, and reads a statement of A on the run.  A run is computed by `look`
(`Targets/Base/Look.lean`) and is a path of `ourInst` (`rpath_chainPath`); where a statement asks
about every run, determinism (`rstep_det`) makes the computed run the only one.

1. **S6 reads uses through A's encoding of `resume`** (`not_contUse_directResume`).  `ResumeAt`
   matches `resume κ w`, which our instance encodes A-normally (`resumeE`, `w to y. κ (inj₁ ()) y`).
   Core's own `with_log` clause (`clL`) resumes by applying `κ` (`κ (inj₁ ()) v`).  On
   `nLogOutside`'s complete run at a data answer, `κ` is caught once and used never.
2. **S5's events name only the effect context's labels** (`not_noIntercept_undeclared`,
   `not_unwindOrder_undeclared`).  A finaliser that raises a name the context does not declare
   ends at `finEnd none` (`errOf`), which no `Ended` of A's reads, while SPEC §19 keeps its error
   and re-raises it at the canceller (`prog₃T`); in an unwind, its raise supersedes the pending one
   and is no `S.raise` (`unwindProg`).
3. **`RunsAlike` compares answers as terms** (`not_algLaw_ourInst`, `not_tailLaw_ourInst`).  Under
   E1′'s `sched`, which answers a closure over the continuation it catches, the two sides of
   algebraicity and of the tail-resumptive law capture different continuations, and their answers
   differ as terms.  `EtaHold`'s witness, a forwarding handler of `l` whose clause performs `l`,
   is not built: `[handle]` types the clauses at the outer row, and its premise `hnS` (SPEC §19,
   "`n` not in `Σ`") keeps the handled name out of that row.  That reading of the rule is not
   checked here; no derivation of the witness was attempted.
4. **`NoInterception` does not give `NoIntercept`** (`not_noIntercept_of_noInterception`).  `J₄`
   types one program, which holds no `ccatch`, no `cfin` and no handler named `0`; its cancelled
   region's finaliser performs the operation the region's dying handler catches.  So the S5 route
   at Core takes `FinAlone` (`Targets/Base/CoreCancel.lean`), a fact about what typed finalisers do
   at run time.

Checks 1–3 also hold at the admissible context `ΞA` (`not_contUse_ΞA`, `not_noIntercept_ΞA`,
`not_unwindOrder_ΞA`, `not_unaryLaws_ΞA`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow lookRun lookEnd lookRun_sound
  NoInterception okE okE_sound models_empty)

/-! ### An admissible effect context -/

/-- Two names at each signature the (E) programs use, and no other: `exn` at `1, 7`, `wait` at
`2, 8`, `yield` at `3, 9`, `log` at `4, 10`, `tick` at `5, 11`, `kube` at `6, 12`. -/
def ΞA : EffCtx := fun n =>
  if n = 1 ∨ n = 7 then [(.aff, .unit, .zero)]
  else if n = 2 ∨ n = 8 then [(.aff, .unit, .unit)]
  else if n = 3 ∨ n = 9 then [(.aff, boolT, .unit)]
  else if n = 4 ∨ n = 10 then [(.lin, boolT, .unit)]
  else if n = 5 ∨ n = 11 then [(.lin, .unit, .unit)]
  else if n = 6 ∨ n = 12 then [(.lin, .unit, boolT)]
  else []

theorem ΞA_cases (n : UInt32) : ΞA n = [] ∨ ΞA n ∈ eSigs := by
  unfold ΞA eSigs
  split_ifs <;> simp

/-- **`ΞA` is admissible.** -/
theorem admEff_ΞA : AdmEff ΞA := by
  refine ⟨?_, ?_, ?_⟩
  · intro n q A B h hq
    rcases ΞA_cases n with h0 | h0
    · rw [h0] at h; simp at h
    · simp only [eSigs, List.mem_cons, List.mem_nil_iff, or_false] at h0
      rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp_all
  · intro n q A B h x
    rcases ΞA_cases n with h0 | h0
    · rw [h0] at h; simp at h
    · simp only [eSigs, List.mem_cons, List.mem_nil_iff, or_false] at h0
      rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h <;>
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h <;>
        obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [VFree, boolT]
  · intro E hE
    simp only [eSigs, List.mem_cons, List.mem_nil_iff, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, 7, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩
    · exact ⟨2, 8, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩
    · exact ⟨3, 9, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩
    · exact ⟨4, 10, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩
    · exact ⟨5, 11, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩
    · exact ⟨6, 12, by decide, by decide, by decide, by simp [ΞA], by simp [ΞA]⟩

/-! ### Programs at our instance -/

section Inst
variable {Ξ : EffCtx}

/-- A closed program `CDerivesNU` types at `F A` is typed at our instance by `tier1Open`, at the
pure row. -/
theorem der_tier1Open_ret {e : Expr} {A : VTy}
    (h : CDerivesNU LifeCtx.empty [] e (.comp (.ret A))) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] e
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F (orowAlg Ξ).unit (OVTy.ofV A)) := by
  refine .inl ⟨[], by simp, ?_⟩
  refine ⟨fun _ h => absurd h List.not_mem_nil, OVTy.rFree_ofV A, fun η _ => ?_⟩
  show CDerivesNU LifeCtx.empty [] e (.comp (CTy.effOf ([] ++ []) (OVTy.den η (OVTy.ofV A))))
  rw [OVTy.den_ofV]
  exact h

theorem r₀_respects {RF : RowForm} {J : OurTyping RF} :
    (ourInst (ℍ := ℍ) RF Ξ J).R₀.Respects := fun _ _ _ h => h.elim

theorem answers_unit {J : OurTyping orowRF} (R : (ourInst (ℍ := ℍ) orowRF Ξ J).Runner) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).Answers R (orowAlg Ξ).unit := by
  intro l i h
  obtain ⟨-, h⟩ := h
  have := h (fun _ => [])
  simp [Targets.Row.Has, Row.find] at this

/-- A configuration at a Core value is an answer. -/
theorem isVal_val {RF : RowForm} {J : OurTyping RF} (μ : Heap) (v : Val) :
    (ourInst (ℍ := ℍ) RF Ξ J).IsVal (μ, v.1) := by
  refine ⟨⟨OVal.ofVal v, rfl⟩, fun ev c' h => ?_⟩
  change OStep (ℍ := ℍ) RF Ξ (μ, v.1) ev c' at h
  generalize hc : (μ, v.1) = c at h
  cases h with
  | mach hh =>
      simp only [Prod.mk.injEq] at hc
      exact hh.not_isVal (Kont.isVal_of_plug _ (hc.2 ▸ v.2))
  | again =>
      simp only [Prod.mk.injEq] at hc
      exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) _ (hc.2 ▸ isOVal_of_isVal v.2)
  | fin =>
      simp only [Prod.mk.injEq] at hc
      exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) _ (hc.2 ▸ isOVal_of_isVal v.2)

end Inst

/-! ### Check 1: S6 and Core's direct resumption -/

/-- `nLogOutside`'s run, as `look` computes it. -/
abbrev nLogRun : List (Kont × Expr × Expr) := lookRun 20 nLogOutside

theorem nLogRun_length : nLogRun.length = 20 := by decide

theorem nLogRun_end : lookEnd 20 nLogOutside = .pair (.inj₂ .unit) (.inj₂ .unit) := by rfl

/-- `with_log`'s answer clause and its clause, as A-values. -/
def hrLV : OVal := ⟨hrL, .lam⟩

def clLV : OVal := ⟨clL, .lam⟩

/-- What lies between `with_log`'s handler and the `log` it catches: `to_result`'s handler and
`□ to _. raise ()`. -/
def nLogK : Kont :=
  .appR (.app (.prim .hnd) (hndValE 1 hrR [.lam (.inj₂ (.var 0))])) (.appR (.lam raiseU) .hole)

/-- The configuration before the catch: `with_log`'s handler around `nLogK[log ()]`. -/
theorem nLogRun_catch :
    (chainTerms nLogOutside nLogRun)[4]? =
      some ((handleK 2 hrL [clL]).plug (nLogK.plug (performE (opArgE 2 0 (.val .unit))))) := by
  rfl

/-- No configuration of the run holds `A`'s `resume` at an evaluation position. -/
theorem nLogRun_noResume :
    ∀ t ∈ chainTerms nLogOutside nLogRun, (evalSubs t).any resumeShape = false := by
  decide

/-- No configuration of the run cancels a continuation at an evaluation position. -/
theorem nLogRun_noCancel :
    ∀ t ∈ chainTerms nLogOutside nLogRun, (evalSubs t).any kappaCancelShape = false := by
  decide

section Check1
variable (Ξ : EffCtx)

/-- The label of the name `2`, where `Ξ` declares `log`'s signature there. -/
def lab2 (h2 : Ξ 2 = [(.aff, .unit, .unit)]) : (orowAlg Ξ).Lab :=
  ⟨2, by decide, by rw [h2]; simp, by rw [h2]; simp⟩

theorem captureE_val {n : UInt32} {r : Expr} {cs : List Expr} (h : IsVal (hndValE n r cs))
    (K : Kont) : captureE n r cs K = kappa n ⟨_, h⟩ K := by
  unfold captureE; rw [dif_pos h]

theorem isVal_hndValE_log : IsVal (hndValE 2 hrL [clL]) :=
  .pair .prim (.pair .lam (.pair .lam .unit))

/-- **Check 1: S6, as written, fails at our instance.**  `nLogOutside`, typed by today's kernel,
runs to `(inj₂ (), inj₂ ())`, a data answer, catching `with_log`'s continuation once.  Its clause
resumes the continuation by applying it, Core's encoding of `κ.resume v`, and not through `A`'s
`resume κ w` (`resumeE`).  So `ContUse` counts no use, and its exactly-once clause fails. -/
theorem not_contUse_directResume (h2 : Ξ 2 = [(.aff, .unit, .unit)]) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).ContUse := by
  intro hC
  let S := ourInst (ℍ := ℍ) orowRF Ξ tier1Open
  let l := lab2 Ξ h2
  let κ : OVal := S.capture l (S.hnd hrLV [clLV]) nLogK
  let q := chainPath S.R₀ Adequacy.emptyMem () nLogRun
  have hchain := lookRun_sound (ℍ := ℍ) 20 nLogOutside
  have hpath : S.RPath S.R₀ (S.rinit S.R₀ nLogOutside) q := rpath_chainPath S.R₀ hchain
  have hder := der_tier1Open_ret (Ξ := Ξ) d_nLogOutsideNU
  obtain ⟨-, -, h3⟩ := hC S.R₀ r₀_respects nLogOutside (orowAlg Ξ).unit _ (answers_unit S.R₀)
    hder q hpath κ
  have hdata : S.DataTy (OVTy.ofV (.tensor (.sum .zero .unit) Flag)) :=
    .tensor (.sum .zero .unit) (.sum .unit .unit)
  have hlast : S.IsVal (S.lastC (S.rinit S.R₀ nLogOutside) q).1 := by
    have hl : S.lastC (S.rinit S.R₀ nLogOutside) q =
        ((Adequacy.emptyMem, lookEnd 20 nLogOutside), ()) := lastC_chainPath S.R₀ hchain
    rw [hl, nLogRun_end]
    exact isVal_val Adequacy.emptyMem (Val.pair (Val.inj₂ .unit) (Val.inj₂ .unit))
  have hterm : ∀ j, j < q.length → ∃ t ∈ chainTerms nLogOutside nLogRun,
      S.term (S.cfgAt (S.rinit S.R₀ nLogOutside) q j).1 = t := by
    intro j hj
    have hj' : j < (chainTerms nLogOutside nLogRun).length := by
      rw [chainTerms_length]; simp only [q, chainPath, List.length_map] at hj; omega
    refine ⟨_, List.getElem_mem hj', ?_⟩
    have hc : S.cfgAt (S.rinit S.R₀ nLogOutside) q j =
        ((Adequacy.emptyMem, (chainTerms nLogOutside nLogRun)[j]), ()) :=
      cfgAt_chainPath S.R₀ nLogOutside nLogRun j (List.getElem?_eq_getElem hj')
    rw [hc]
    rfl
  -- no use of `κ`
  have hres : S.resumes (S.rinit S.R₀ nLogOutside) q κ = 0 := by
    unfold A.EffectSystem.resumes
    refine List.countP_eq_zero.mpr fun j hj => ?_
    simp only [decide_eq_true_eq]
    rintro ⟨hjq, K₀, w, hK₀⟩
    obtain ⟨t, ht, ht'⟩ := hterm j hjq
    have := nLogRun_noResume t ht
    rw [← ht', hK₀] at this
    rw [show S.plug K₀ (S.resume κ w) = K₀.plug (resumeE κ.1 w.1) from rfl,
      any_evalSubs_plug K₀ (resumeShape_resumeE _ _)] at this
    exact absurd this (by decide)
  have hcan : S.cancels (S.rinit S.R₀ nLogOutside) q κ = 0 := by
    unfold A.EffectSystem.cancels
    refine List.countP_eq_zero.mpr fun j hj => ?_
    simp only [decide_eq_true_eq]
    rintro ⟨hjq, K₀, hK₀⟩
    obtain ⟨t, ht, ht'⟩ := hterm j hjq
    have := nLogRun_noCancel t ht
    rw [← ht', hK₀] at this
    have hκ : κ.1 = kappa 2 ⟨_, isVal_hndValE_log⟩ nLogK := captureE_val isVal_hndValE_log nLogK
    rw [show S.plug K₀ (S.cancel κ) = K₀.plug (cancelE κ.1) from rfl, hκ,
      any_evalSubs_plug K₀ (kappaCancelShape_cancelE _ _ _)] at this
    exact absurd this (by decide)
  -- one catch of `κ`, at an affine operation
  have hcatch : 0 < S.caughtAff (S.rinit S.R₀ nLogOutside) q κ := by
    unfold A.EffectSystem.caughtAff
    refine List.countP_pos_iff.mpr ⟨4, ?_, ?_⟩
    · simp only [q, chainPath, List.length_map, nLogRun_length, List.mem_range]; omega
    simp only [decide_eq_true_eq]
    refine ⟨by simp only [q, chainPath, List.length_map, nLogRun_length]; omega,
      .hole, l, hrLV, [clLV], nLogK, 0, S.unitV,
      ⟨OVTy.ofV .unit, OVTy.ofV .unit, clsOf .aff .unit⟩, ?_, ?_, ?_, rfl,
      by decide, rfl⟩
    · have hc : S.cfgAt (S.rinit S.R₀ nLogOutside) q 4 =
          ((Adequacy.emptyMem, (handleK 2 hrL [clL]).plug
            (nLogK.plug (performE (opArgE 2 0 (.val .unit))))), ()) :=
        cfgAt_chainPath S.R₀ nLogOutside nLogRun 4 nLogRun_catch
      rw [hc]
      rfl
    · show nLogK.HasHnd 2 = false
      rfl
    · show ((Ξ 2).map _)[0]? = _
      rw [h2]
      rfl
  have hu : S.uses (S.rinit S.R₀ nLogOutside) q κ = S.caught (S.rinit S.R₀ nLogOutside) q κ :=
    h3 hdata hlast
  have hu' : S.resumes (S.rinit S.R₀ nLogOutside) q κ + S.cancels (S.rinit S.R₀ nLogOutside) q κ =
      S.caughtLin (S.rinit S.R₀ nLogOutside) q κ + S.caughtAff (S.rinit S.R₀ nLogOutside) q κ := hu
  rw [hres, hcan] at hu'
  omega

end Check1

/-- **Check 1 at an admissible effect context**: done's A-conjunct asks `ContUse` at `ΞA`. -/
theorem not_contUse_ΞA : AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).ContUse :=
  ⟨admEff_ΞA, not_contUse_directResume ΞA (by simp [ΞA])⟩

/-! ### Check 2: S5 and the names an effect context does not declare -/

/-- The three handlers of `prog₃T`, at run time: identity return clauses; `λ_. ()` at the names
`21` and `20`, and the cancelling clause at the name `2`. -/
def H21E : Expr := hndValE 21 (.lam (.var 0)) [.lam .unit]

def H20E : Expr := hndValE 20 (.lam (.var 0)) [.lam .unit]

def H2E : Expr := hndValE 2 (.lam (.var 0)) [.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit)))]

theorem isVal_H2E : IsVal H2E := .pair .prim (.pair .lam (.pair .lam .unit))

/-- The canceller's context: the handler of `21`. -/
def p3K₀ : Kont := handleK 21 (.lam (.var 0)) [.lam .unit]

/-- The cancelled region below the handler of `2`: the handler of `20` around the finaliser
frame. -/
def p3K : Kont :=
  .appR (.app (.prim .hnd) H20E)
    (.appR (.app (.prim .ubind) (.pair (.lam (.var 0)) (.lam finD))) .hole)

/-- The cancel's state at its start: the region's names `[2, 20]`, nothing kept. -/
abbrev p3cs : Val := cancelVal [2, 20] none

/-- After the finaliser raised `21`: that error kept. -/
abbrev p3cs' : Val := cancelVal [2, 20] (some (opPayload 21 0 Val.unit))

/-- The configuration that cancels: `κ (inj₂ ())` in the canceller's context. -/
theorem p3_c₀ : lookEnd 9 prog₃T = p3K₀.plug (cancelE (kappa 2 ⟨H2E, isVal_H2E⟩ p3K)) := by rfl

/-- The cancel's start, three administrative steps on. -/
theorem p3_c : lookEnd 12 prog₃T = p3K₀.plug (Targets.cancelOf 2 ⟨H2E, isVal_H2E⟩ p3K) := by rfl

/-- The cancel's next three steps: the finaliser fires (`ufinC`), its thunk is applied, and its
raise of `21` ends it (`cferr`). -/
theorem p3_run :
    (lookRun 3 (lookEnd 12 prog₃T)).map (fun x => x.2.1) =
      [ubindE (Val.pair (Val.lam (.var 0)) (Val.lam finD)) (raiseE (.val p3cs)),
       .app (.lam finD) .unit,
       cfinE p3cs (Kont.hole.plug (raiseE (.val (opPayload 21 0 Val.unit))))] := by rfl

theorem p3_terms :
    chainTerms (lookEnd 12 prog₃T) (lookRun 3 (lookEnd 12 prog₃T)) =
      [p3K₀.plug (Targets.cancelOf 2 ⟨H2E, isVal_H2E⟩ p3K),
       p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩ ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug
         (cfinE p3cs (.app (.lam finD) .unit))))),
       p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩ ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug
         (cfinE p3cs finD)))),
       p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩ ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug
         (raiseE (.val p3cs')))))] := by rfl

/-- Where the finaliser runs once fired: the canceller's context, `ccatch`, the region's
handlers, and the cancel-mode frame. -/
def p3Kf : Kont :=
  p3K₀.comp (.appR (.prim .ccatch) (.appR (.app (.prim .hnd) H2E)
    (.appR (.app (.prim .hnd) H20E) (.appR (.app (.prim .cfin) p3cs.1) .hole))))

theorem p3_t₂ : p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
    ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (cfinE p3cs finD)))) = p3Kf.plug finD := by
  rfl

theorem raiseShape_finD : raiseShape 21 finD = true := rfl

/-- No configuration of the cancel but the one where it runs holds the finaliser at an evaluation
position. -/
theorem p3_noFinD₁ : (evalSubs (p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
    ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (cfinE p3cs (.app (.lam finD) .unit))))))).any
      (raiseShape 21) = false := by decide

theorem p3_noFinD₃ : (evalSubs (p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
    ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (raiseE (.val p3cs'))))))).any
      (raiseShape 21) = false := by decide

/-- After the finaliser's raise ends it, no cancel-mode frame is left. -/
theorem p3_noCfin₃ : (evalSubs (p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
    ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (raiseE (.val p3cs'))))))).any
      cfinShape = false := by decide

theorem cfinShape_p3Kf (t : Expr) : (evalSubs (p3Kf.plug t)).any cfinShape = true := by
  have : p3Kf.plug t = (p3K₀.comp (.appR (.prim .ccatch) (.appR (.app (.prim .hnd) H2E)
      (.appR (.app (.prim .hnd) H20E) .hole)))).plug (cfinE p3cs t) := by
    simp only [p3Kf, Kont.plug_comp]; rfl
  rw [this]
  exact any_evalSubs_plug _ (p := cfinShape) rfl

theorem not_isOVal_finD : ¬ IsOVal finD :=
  not_isOVal_prim_app (p := .raise) (by decide) _

/-- The only `raise` at an evaluation position of the finaliser is the finaliser itself, of the
name `21`. -/
theorem plug_raise_finD {K : Kont} {n i : UInt32} {x : Expr}
    (h : K.plug (raiseE (opArgE n i x)) = finD) : n = 21 := by
  cases K with
  | hole =>
      simp only [Kont.plug, finD, raiseE, opArgE, Expr.app.injEq, Expr.pair.injEq, Val.i32,
        Expr.val, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at h
      exact h.2.1
  | appR f K =>
      simp only [Kont.plug, finD, raiseE, opArgE, Expr.app.injEq] at h
      obtain ⟨-, h⟩ := h
      cases K with
      | hole => simp [Kont.plug] at h
      | pairL K e =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          cases K <;> simp [Kont.plug, Val.i32] at h
      | pairR v K =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨-, h⟩ := h
          cases K with
          | hole => simp [Kont.plug] at h
          | pairL K e => simp only [Kont.plug, Expr.pair.injEq] at h; cases K <;> simp [Kont.plug, Val.i32] at h
          | pairR v K => simp only [Kont.plug, Expr.pair.injEq] at h; cases K <;> simp [Kont.plug] at h
          | _ => simp [Kont.plug] at h
      | _ => simp [Kont.plug] at h
  | appL K v =>
      simp only [Kont.plug, finD, raiseE, Expr.app.injEq] at h
      cases K <;> simp [Kont.plug] at h
  | _ => simp [Kont.plug, finD, raiseE] at h

section Check2
variable (Ξ : EffCtx)

theorem cancelOfE_val {n : UInt32} {r : Expr} {cs : List Expr} (h : IsVal (hndValE n r cs))
    (K : Kont) : cancelOfE n r cs K = Targets.cancelOf n ⟨_, h⟩ K := by
  unfold cancelOfE; rw [dif_pos h]

/-- `prog₃T`'s handler of the name `2`, as an A-handler. -/
def p3H : OVal × List OVal :=
  (⟨.lam (.var 0), .lam⟩, [⟨.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))), .lam⟩])

theorem errOf_undeclared {m : UInt32} (hm : Ξ m = []) (j : UInt32) (w : Val) :
    errOf orowRF Ξ m j w = none := by
  unfold errOf
  rw [dif_neg]
  rintro ⟨l, hl⟩
  exact l.2.2.1 (by rw [show l.1 = m from hl]; exact hm)

/-- The three steps of the cancel: the finaliser fires, its thunk is applied, and its raise of
`21` ends it, the end an error that `Ξ` names no label of. -/
def p3q (h21 : Ξ 21 = []) :
    List ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Event ×
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RConf (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀) :=
  [(.fire finD, ((Adequacy.emptyMem, p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
      ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (cfinE p3cs (.app (.lam finD) .unit)))))), ())),
   (.tau, ((Adequacy.emptyMem, p3Kf.plug finD), ())),
   (.finEnd none, ((Adequacy.emptyMem, p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
      ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (raiseE (.val p3cs')))))), ()))]

theorem p3_path (h21 : Ξ 21 = []) :
    chainPath (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀ Adequacy.emptyMem ()
      (lookRun 3 (lookEnd 12 prog₃T)) = p3q (ℍ := ℍ) Ξ h21 := by
  have h1 := p3_run
  have h2' := p3_terms
  unfold chainTerms at h2'
  simp only [chainPath]
  generalize lookRun 3 (lookEnd 12 prog₃T) = L at h1 h2'
  have hlen : L.length = 3 := by
    have := congrArg List.length h1; simpa using this
  obtain ⟨x₁, x₂, x₃, rfl⟩ := A.EffectSystem.eq_three hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h1 h2'
  obtain ⟨a₁, a₂, a₃, -⟩ := h1
  obtain ⟨-, e₁, e₂, e₃, -⟩ := h2'
  simp only [List.map_cons, List.map_nil, p3q, a₁, a₂, a₃, e₁, e₂, e₃]
  rw [labelOf_fire (by intro h; exact (plug_raise_ne_val .hole _ ⟨_, h⟩) rfl), labelOf_tau_of rfl,
    labelOf_cferr, errOf_undeclared Ξ h21, p3_t₂]
  rfl

/-- **Check 2: S5's `NoIntercept`, as written, fails at our instance.**  `prog₃T`, typed by today's
kernel, cancels a continuation whose region holds a finaliser that raises the name `21`, which a
handler outside the region catches.  At an effect context that does not declare `21`, the
finaliser's end is no `Ended` of A's (`S.raise` raises only labels), so the run, which fires the
finaliser and keeps its error as SPEC §19 builds, follows no cancel trace. -/
theorem not_noIntercept_undeclared (h2 : Ξ 2 = [(.aff, .unit, .unit)]) (h21 : Ξ 21 = []) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).NoIntercept := by
  intro hNI
  let S := ourInst (ℍ := ℍ) orowRF Ξ tier1Open
  let l := lab2 Ξ h2
  let c₀ : S.RConf S.R₀ := ((Adequacy.emptyMem, lookEnd 9 prog₃T), ())
  let c : S.RConf S.R₀ := ((Adequacy.emptyMem, lookEnd 12 prog₃T), ())
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ prog₃T) c₀ :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 9 prog₃T)
  have hc₀ : S.term c₀.1 = S.plug p3K₀ (S.cancel (S.capture l p3H p3K)) := by
    show lookEnd 9 prog₃T = p3K₀.plug (cancelE (captureE 2 _ _ p3K))
    rw [show captureE 2 (↑p3H.1) (List.map Subtype.val p3H.2) p3K = kappa 2 ⟨H2E, isVal_H2E⟩ p3K
      from captureE_val isVal_H2E p3K]
    exact p3_c₀
  have hpure : S.PureSteps c₀.1 c.1 :=
    pureSteps_of_chain (RF := orowRF) (Ξ := Ξ) (J := tier1Open) (μ := Adequacy.emptyMem)
      (lookRun_sound (ℍ := ℍ) 3 (lookEnd 9 prog₃T))
  have hc : S.term c.1 = S.plug p3K₀ (S.cancelOf l p3H p3K) := by
    show lookEnd 12 prog₃T = p3K₀.plug (cancelOfE 2 _ _ p3K)
    rw [show cancelOfE 2 (↑p3H.1) (List.map Subtype.val p3H.2) p3K =
      Targets.cancelOf 2 ⟨H2E, isVal_H2E⟩ p3K from cancelOfE_val isVal_H2E p3K]
    exact p3_c
  have hpath : S.RPath S.R₀ c (p3q (ℍ := ℍ) Ξ h21) := by
    rw [← p3_path Ξ h21]
    exact rpath_chainPath S.R₀ (lookRun_sound (ℍ := ℍ) 3 _)
  have hT := hNI S.R₀ r₀_respects prog₃T (orowAlg Ξ).unit (OVTy.ofV .unit) (answers_unit S.R₀)
    (der_tier1Open_ret d_prog₃TNU) c₀ c p3K₀ l p3H p3K _ hreach hc₀ hpure rfl hc hpath
  have hfins : S.fins p3K = [finD] := rfl
  rw [hfins] at hT
  generalize hq' : p3q (ℍ := ℍ) Ξ h21 = q' at hT
  cases hT with
  | stop => unfold p3q at hq'; cases hq'
  | @fire c' c₁ c₂ D fs err Kf q₀ q'' hst hpp hKf hft =>
      have hKf' : c₂.1.2 = Kf.plug finD := hKf
      unfold p3q at hq'
      obtain ⟨hx₁, hrest⟩ := List.cons.inj hq'
      rcases q₀ with _ | ⟨y, _ | ⟨z, _ | ⟨w, q₀⟩⟩⟩
      · -- the finaliser is not yet at an evaluation position
        cases hpp
        have := any_evalSubs_plug Kf raiseShape_finD
        rw [← hKf', ← (Prod.mk.inj hx₁).2] at this
        exact absurd this (by rw [p3_noFinD₁]; decide)
      · -- the finaliser runs, and its end is no `Ended`
        simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hq''⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp'
            -- `Kf` is where the finaliser runs
            obtain ⟨-, hc₂⟩ := Prod.mk.inj hy
            have hKf₂ : Kf = p3Kf := by
              have h : p3Kf.plug finD = Kf.plug finD := by rw [← hKf', ← hc₂]
              exact (plug_inj_ctx (fun h' => not_isOVal_finD (isOVal_of_isVal h')) h).symm
            generalize hfs0 : ([] : List (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Term) = fs0 at hft
            generalize her0 : (none : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Err) = er0 at hft
            cases hft with
            | running hal =>
                -- the finaliser's end is a step at its cancel-mode frame, not a step of it alone
                subst hq'' hKf₂
                cases hal with
                | @cons _ _ _ t t' _ _ h₁ h₂ _ _ _ =>
                    have h₂' : p3K₀.plug (ccatchE (hndE ⟨H2E, isVal_H2E⟩
                        ((Kont.appR (.app (.prim .hnd) H20E) .hole).plug (raiseE (.val p3cs'))))) =
                        p3Kf.plug t' := h₂
                    have := cfinShape_p3Kf t'
                    rw [← h₂', p3_noCfin₃] at this
                    exact absurd this (by decide)
            | @ended _ _ _ _ qa c' r c'' qb hal hend _ _ =>
                subst hKf₂
                rcases qa with _ | ⟨a, qa⟩
                · simp only [List.nil_append, List.cons.injEq] at hq''
                  obtain ⟨-, -⟩ := hq''
                  cases hal
                  -- the finaliser raised `21`, which no label of `Ξ` names
                  have hc₂' : c₂.1.2 = p3Kf.plug finD := by rw [← hc₂]
                  rcases r with _ | ⟨m, j, w⟩
                  · obtain ⟨v, hv⟩ := hend
                    have hv' : p3Kf.plug finD = p3Kf.plug v.1 := hc₂'.symm.trans hv
                    exact not_isOVal_finD (plug_inj_hole p3Kf hv' ▸ v.2)
                  · obtain ⟨K, hK, -, -⟩ := hend
                    have hK' : p3Kf.plug finD =
                        p3Kf.plug (K.plug (raiseE (opArgE m.1 (UInt32.ofNat j) w.1))) :=
                      hc₂'.symm.trans hK
                    have hm := plug_raise_finD (plug_inj_hole p3Kf hK').symm
                    exact m.2.2.1 (by rw [show m.1 = 21 from hm]; exact h21)
                · simp only [List.cons_append, List.cons.injEq] at hq''
                  obtain ⟨-, h⟩ := hq''
                  cases qa <;> simp at h
      · -- after the finaliser's end, it is no longer at an evaluation position
        simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hz, -⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp' with
            | cons _ _ hpp'' =>
                cases hpp''
                have := any_evalSubs_plug Kf raiseShape_finD
                rw [← hKf', ← (Prod.mk.inj hz).2] at this
                exact absurd this (by rw [p3_noFinD₃]; decide)
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨-, -, h⟩ := hrest
        cases h

end Check2

/-- **Check 2 at an admissible effect context.** -/
theorem not_noIntercept_ΞA :
    AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).NoIntercept :=
  ⟨admEff_ΞA, not_noIntercept_undeclared ΞA (by simp [ΞA]) (by simp [ΞA])⟩

/-! ### Check 2, the unwind: a finaliser's raise of an undeclared name supersedes -/

def H1E : Expr := hndValE 1 (.lam (.var 0)) [.lam .unit]

/-- The context of the raise: the handlers of `21` and `1`. -/
def p4K₀ : Kont := (handleK 21 (.lam (.var 0)) [.lam .unit]).comp (handleK 1 (.lam (.var 0)) [.lam .unit])

theorem p4_c : lookEnd 4 unwindProg =
    p4K₀.plug ((thenK (.var 0) finD).plug (raiseE (opArgE 1 0 (.val .unit)))) := by rfl

/-- The unwind's three steps: the finaliser fires (`ufin`), its thunk is applied, and the handler
of `21` catches its raise. -/
theorem p4_run :
    (lookRun 3 (lookEnd 4 unwindProg)).map (fun x => x.2.1) =
      [ubindE (Val.pair (Val.lam (.var 0)) (Val.lam finD))
         (Kont.hole.plug (raiseE (.val (opPayload 1 0 Val.unit)))),
       .app (.lam finD) .unit,
       p4K₀.plug (.seq finD (raiseE (opArgE 1 0 (.val .unit))))] := by rfl

theorem p4_terms :
    chainTerms (lookEnd 4 unwindProg) (lookRun 3 (lookEnd 4 unwindProg)) =
      [p4K₀.plug ((thenK (.var 0) finD).plug (raiseE (opArgE 1 0 (.val .unit)))),
       p4K₀.plug (.seq (.app (.lam finD) .unit) (raiseE (opArgE 1 0 (.val .unit)))),
       p4K₀.plug (.seq finD (raiseE (opArgE 1 0 (.val .unit)))),
       .app (.lam .unit) .unit] := by rfl

theorem p4_noFinD₁ : (evalSubs (p4K₀.plug (.seq (.app (.lam finD) .unit)
    (raiseE (opArgE 1 0 (.val .unit)))))).any (raiseShape 21) = false := by decide

theorem p4_K₀_ne (X : Expr) : p4K₀.plug X ≠ .app (.lam .unit) .unit := by
  simp [p4K₀, handleK, Kont.plug_comp, Kont.plug]

theorem p4_halone (K₂ Kp : Kont) (t' : Expr) :
    ((p4K₀.comp K₂).comp Kp).plug t' ≠ .app (.lam .unit) .unit := by
  intro h; rw [Kont.plug_comp, Kont.plug_comp] at h; exact p4_K₀_ne _ h

theorem thenK_hasHnd (n : UInt32) : (thenK (.var 0) finD).HasHnd n = false := rfl

theorem not_thenK_eq_handler {K₁ K₂ : Kont} {n : UInt32} {r : Expr} {cs : List Expr}
    (h : thenK (.var 0) finD = K₂.comp ((handleK n r cs).comp K₁)) : False := by
  have h' := congrArg (fun K : Kont => K.HasHnd n) h
  simp only [thenK_hasHnd, hasHnd_comp] at h'
  simp [handleK, hndValE, Kont.HasHnd] at h'

theorem finHead_hnd (H e : Expr) : finHead (.app (.app (.prim .hnd) H) e) = false := rfl

section Check2u
variable (Ξ : EffCtx)

/-- The label of the name `1`, where `Ξ` declares `exn`'s signature there. -/
def lab1 (h1 : Ξ 1 = [(.aff, .unit, .zero)]) : (orowAlg Ξ).Lab :=
  ⟨1, by decide, by rw [h1]; simp, by rw [h1]; simp⟩

/-- The unwind's path. -/
def p4q : List ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Event ×
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RConf (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀) :=
  [(.fire finD, ((Adequacy.emptyMem,
      p4K₀.plug (.seq (.app (.lam finD) .unit) (raiseE (opArgE 1 0 (.val .unit))))), ())),
   (.tau, ((Adequacy.emptyMem, p4K₀.plug (.seq finD (raiseE (opArgE 1 0 (.val .unit))))), ())),
   (.tau, ((Adequacy.emptyMem, .app (.lam .unit) .unit), ()))]

theorem p4_path :
    chainPath (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀ Adequacy.emptyMem ()
      (lookRun 3 (lookEnd 4 unwindProg)) = p4q (ℍ := ℍ) Ξ := by
  have h1 := p4_run
  have h2' := p4_terms
  unfold chainTerms at h2'
  simp only [chainPath]
  generalize lookRun 3 (lookEnd 4 unwindProg) = L at h1 h2'
  have hlen : L.length = 3 := by
    have := congrArg List.length h1; simpa using this
  obtain ⟨x₁, x₂, x₃, rfl⟩ := A.EffectSystem.eq_three hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h1 h2'
  obtain ⟨a₁, a₂, a₃, -⟩ := h1
  obtain ⟨-, e₁, e₂, e₃, -⟩ := h2'
  simp only [List.map_cons, List.map_nil, p4q, a₁, a₂, a₃, e₁, e₂, e₃]
  rw [labelOf_fire (by intro h; exact (plug_raise_ne_val .hole _ ⟨_, h⟩) rfl), labelOf_tau_of rfl,
    show p4K₀.plug (.seq finD (raiseE (opArgE 1 0 (.val .unit)))) =
      Expr.app (.app (.prim .hnd) H21E) _ from rfl, labelOf_tau_of (finHead_hnd _ _)]
  rfl

theorem thenK_finD_shift : thenK (.var 0) finD =
    Kont.appR (.app (.prim .ubind) (.pair (.lam (.var 0)) (.lam finD))) .hole := rfl

/-- **Check 2, the unwind: S5's `UnwindOrder`, as written, fails at our instance.**
`unwindProg`, typed by today's kernel, raises the declared name `1` through a finaliser frame
whose finaliser raises `21`, which a handler outside catches.  At an effect context that does
not declare `21`, the finaliser's raise is no `S.raise` of A's, so the run, which fires the
finaliser and lets its raise supersede the pending one as SPEC §19 builds, follows no unwind
trace. -/
theorem not_unwindOrder_undeclared (h1 : Ξ 1 = [(.aff, .unit, .zero)]) (h21 : Ξ 21 = []) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).UnwindOrder := by
  intro hU
  let S := ourInst (ℍ := ℍ) orowRF Ξ tier1Open
  let l := lab1 Ξ h1
  let c : S.RConf S.R₀ := ((Adequacy.emptyMem, lookEnd 4 unwindProg), ())
  let K : S.Kont := S.kcomp S.hole (S.kcomp (S.thenF (.var 0) finD) S.hole)
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ unwindProg) c :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 4 unwindProg)
  have hstd : S.Std K := .frame (K₁ := S.hole) (K₂ := S.hole) trivial (.inr ⟨_, _, rfl⟩)
    (.clear trivial)
  have hc : S.term c.1 = S.plug p4K₀ (S.plug K (S.raise l 0 S.unitV)) := p4_c
  have hcK : S.catches K l = false := rfl
  have hpath : S.RPath S.R₀ c (p4q (ℍ := ℍ) Ξ) := by
    rw [← p4_path Ξ]
    exact rpath_chainPath S.R₀ (lookRun_sound (ℍ := ℍ) 3 _)
  have hT := hU S.R₀ r₀_respects unwindProg (orowAlg Ξ).unit (OVTy.ofV .unit) (answers_unit S.R₀)
    (der_tier1Open_ret d_unwindProgNU) c p4K₀ K l 0 S.unitV _ hreach hstd hc hcK hpath
  generalize hq' : p4q (ℍ := ℍ) Ξ = q' at hT
  generalize hK' : K = K' at hT
  cases hT with
  | stop => unfold p4q at hq'; cases hq'
  | out _ _ hclear =>
      subst hK'
      exact hclear.1 _ rfl
  | @caught _ _ K₁ K₂ H m _ _ _ hKeq _ _ _ =>
      subst hK'
      exact not_thenK_eq_handler (K₁ := K₁) (K₂ := K₂) (n := m.1) (r := H.1.1)
        (cs := H.2.map Subtype.val) hKeq
  | @fire _ c₁ c₂ _ K₁ K₂ N D Kp m j w q₀ q'' hKeq _ _ _ hst hpp _ _ hKf hpend =>
      subst hK'
      unfold p4q at hq'
      obtain ⟨hx₁, hrest⟩ := List.cons.inj hq'
      have hD : D = finD := by
        have := (Prod.mk.inj hx₁).1
        injection this with h; exact h.symm
      subst hD
      have hKf' : c₂.1.2 = ((p4K₀.comp K₂).comp Kp).plug finD := hKf
      rcases q₀ with _ | ⟨y, _ | ⟨z, _ | ⟨w', q₀⟩⟩⟩
      · cases hpp
        have := any_evalSubs_plug ((p4K₀.comp K₂).comp Kp) raiseShape_finD
        rw [← hKf', ← (Prod.mk.inj hx₁).2] at this
        exact absurd this (by rw [p4_noFinD₁]; decide)
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hq''⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp'
            obtain ⟨-, hc₂⟩ := Prod.mk.inj hy
            generalize hp : (m, j, w) = pp at hpend
            cases hpend with
            | running hal =>
                subst hq''
                cases hal with
                | @cons _ _ _ t t' _ _ _ h₂ _ _ _ =>
                    have h₂' : Expr.app (.lam .unit) .unit = ((p4K₀.comp K₂).comp Kp).plug t' := h₂
                    exact p4_halone K₂ Kp t' h₂'.symm
            | @returned _ _ _ _ qa c' qb c'' qc hal hend _ _ _ =>
                rcases qa with _ | ⟨a, qa⟩
                · cases hal
                  obtain ⟨v, hv⟩ := hend
                  have hv' : ((p4K₀.comp K₂).comp Kp).plug finD =
                      ((p4K₀.comp K₂).comp Kp).plug v.1 := hKf'.symm.trans hv
                  exact not_isOVal_finD (plug_inj_hole _ hv' ▸ v.2)
                · cases hal with
                  | @cons _ ev c₃ t t' _ _ _ h₂ _ _ _ =>
                      simp only [List.cons_append, List.cons.injEq] at hq''
                      obtain ⟨ha, -⟩ := hq''
                      obtain ⟨-, hc₃⟩ := Prod.mk.inj ha
                      have h₂' : c₃.1.2 = ((p4K₀.comp K₂).comp Kp).plug t' := h₂
                      rw [← hc₃] at h₂'
                      exact p4_halone K₂ Kp t' h₂'.symm
            | @superseded _ _ _ _ qa c' K' m' j' w' qb hal hsup _ _ _ =>
                rcases qa with _ | ⟨a, qa⟩
                · cases hal
                  have hK' : ((p4K₀.comp K₂).comp Kp).plug finD =
                      ((p4K₀.comp K₂).comp Kp).plug
                        (K'.plug (raiseE (opArgE m'.1 (UInt32.ofNat j') w'.1))) :=
                    hKf'.symm.trans hsup
                  have hm := plug_raise_finD (plug_inj_hole _ hK').symm
                  exact m'.2.2.1 (by rw [show m'.1 = 21 from hm]; exact h21)
                · cases hal with
                  | @cons _ ev c₃ t t' _ _ _ h₂ _ _ _ =>
                      simp only [List.cons_append, List.cons.injEq] at hq''
                      obtain ⟨ha, -⟩ := hq''
                      obtain ⟨-, hc₃⟩ := Prod.mk.inj ha
                      have h₂' : c₃.1.2 = ((p4K₀.comp K₂).comp Kp).plug t' := h₂
                      rw [← hc₃] at h₂'
                      exact p4_halone K₂ Kp t' h₂'.symm
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hz, -⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp' with
            | cons _ _ hpp'' =>
                cases hpp''
                have h₃ : c₂.1.2 = .app (.lam .unit) .unit := by rw [← (Prod.mk.inj hz).2]
                rw [h₃] at hKf'
                exact p4_halone K₂ Kp finD hKf'.symm
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨-, -, h⟩ := hrest
        cases h

end Check2u

/-- **Check 2's unwind at an admissible effect context.** -/
theorem not_unwindOrder_ΞA :
    AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).UnwindOrder :=
  ⟨admEff_ΞA, not_unwindOrder_undeclared ΞA (by simp [ΞA]) (by simp [ΞA])⟩

/-! ### Check 3: `RunsAlike` compares answers as terms -/

/-- `sched` at the linear operation `11.0`, at run time. -/
def schedK₀ : Kont := handleK 11 schedRetE [schedClE]

theorem alg_c : lookEnd 2 algProg = schedK₀.plug algL := by rfl

/-- What tells the two answers apart: the continuation's frames `□ to x. ret x` then
`□ to y. ret ()`, plugged. -/
def algPat : Expr → Bool
  | .app (.lam .unit) (.app (.lam (.var 0)) (.var 0)) => true
  | _ => false

theorem alg_endL : isValB (lookEnd 3 (schedK₀.plug algL)) = true ∧
    occursIn algPat (lookEnd 3 (schedK₀.plug algL)) = true ∧
    (lookRun 3 (schedK₀.plug algL)).all (fun x => finHead x.2.1 == false) = true := by decide

theorem alg_endR : isValB (lookEnd 3 (schedK₀.plug algR)) = true ∧
    occursIn algPat (lookEnd 3 (schedK₀.plug algR)) = false := by decide

/-- The tail check's configuration: `sched` around the handler of `5` around `perform (5, 0, ())`. -/
def tailH5 : Kont := handleK 5 (.lam (.var 0)) [tailClE]

theorem tail_c : lookEnd 4 tailProg =
    schedK₀.plug (tailH5.plug (performE (opArgE 5 0 (.val .unit)))) := by rfl

/-- What tells the two answers apart: the handler of `5` around `□ to _. ret ()`, the frames the
right side's continuation holds. -/
def tailPat : Expr → Bool
  | .app (.app (.prim .hnd) _) (.app (.lam .unit) (.var 0)) => true
  | _ => false

theorem tail_endL : isValB (lookEnd 8 (schedK₀.plug (tailH5.plug
      (performE (opArgE 5 0 (.val .unit)))))) = true ∧
    occursIn tailPat (lookEnd 8 (schedK₀.plug (tailH5.plug
      (performE (opArgE 5 0 (.val .unit)))))) = false ∧
    (lookRun 8 (schedK₀.plug (tailH5.plug (performE (opArgE 5 0 (.val .unit)))))).all
      (fun x => finHead x.2.1 == false) = true := by decide

theorem tail_endR : isValB (lookEnd 5 (schedK₀.plug (tailH5.plug (appE tickCE .unit)))) = true ∧
    occursIn tailPat (lookEnd 5 (schedK₀.plug (tailH5.plug (appE tickCE .unit)))) = true := by
  decide

section Check3
variable (Ξ : EffCtx)

/-- The label of the name `11`, where `Ξ` declares a linear `1 ↠ 1` there. -/
def lab11 (h11 : Ξ 11 = [(.lin, .unit, .unit)]) : (orowAlg Ξ).Lab :=
  ⟨11, by decide, by rw [h11]; simp, by rw [h11]; simp⟩

/-- The label of the name `5`, likewise. -/
def lab5 (h5 : Ξ 5 = [(.lin, .unit, .unit)]) : (orowAlg Ξ).Lab :=
  ⟨5, by decide, by rw [h5]; simp, by rw [h5]; simp⟩

/-- A complete run from a configuration whose computed run is `look`'s, to a value with no
finaliser step: its answer and empty trace. -/
theorem obsFrom_chain {μ : Heap} {e : Expr} (k : ℕ) (hv : isValB (lookEnd k e) = true)
    (hfin : (lookRun k e).all (fun x => finHead x.2.1 == false) = true) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).ObsFrom (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀
      ((μ, e), ()) ⟨lookEnd k e, isOVal_of_isVal (isVal_of_isValB _ hv)⟩ [] := by
  have hchain := lookRun_sound (ℍ := ℍ) k e
  refine ⟨chainPath _ μ () (lookRun k e), ⟨rpath_chainPath _ hchain, ?_⟩, ?_,
    obs_chainPath (ℍ := ℍ) (RF := orowRF) (Ξ := Ξ) (J := tier1Open)
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀ μ () _ hfin⟩
  · have hl : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).lastC ((μ, e), ())
        (chainPath (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀ μ () (lookRun k e)) =
        ((μ, lookEnd k e), ()) := lastC_chainPath _ hchain
    rw [hl]
    exact isVal_val μ ⟨_, isVal_of_isValB _ hv⟩
  · have hl : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).lastC ((μ, e), ())
        (chainPath (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀ μ () (lookRun k e)) =
        ((μ, lookEnd k e), ()) := lastC_chainPath _ hchain
    rw [hl]
    rfl

/-- Every complete run's answer from such a configuration is the computed one. -/
theorem obsFrom_chain_unique {μ : Heap} {e : Expr} (k : ℕ) (hv : isValB (lookEnd k e) = true)
    {v : OVal} {tr : List (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Event}
    (h : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).ObsFrom (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).R₀
      ((μ, e), ()) v tr) : v.1 = lookEnd k e := by
  obtain ⟨q, hq, hv', -⟩ := h
  have := complete_chain _ (lookRun_sound (ℍ := ℍ) k e) (isVal_of_isValB _ hv) q hq
  exact hv'.symm.trans this

/-- **Check 3, algebraicity: `AlgLaw`, as written, fails at our instance.**  Under E1′'s
`sched`, which answers a closure over the continuation it catches, the two sides of the law
capture different continuations, `□ to x. ret x` then `□ to y. ret ()` on the left and
`□ to x. (ret x to y. ret ())` on the right, and their answers differ as terms.  The program is
typed by today's kernel. -/
theorem not_algLaw_ourInst (h11 : Ξ 11 = [(.lin, .unit, .unit)]) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).AlgLaw := by
  intro hA
  let S := ourInst (ℍ := ℍ) orowRF Ξ tier1Open
  have hRA := hA (lab11 Ξ h11) 0 S.unitV ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ (.var 0)
    (.val .unit) (by show ((Ξ 11).map _)[0]? = _; rw [h11]; rfl) (by intro h; cases h)
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ algProg) ((Adequacy.emptyMem, lookEnd 2 algProg), ()) :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 2 algProg)
  obtain ⟨hvL, -, hfinL⟩ := alg_endL
  obtain ⟨hvR, hpatR⟩ := alg_endR
  have h := (hRA S.R₀ r₀_respects algProg _ ((Adequacy.emptyMem, lookEnd 2 algProg), ()) schedK₀
    (der_tier1Open_ret d_algProgNU) hreach alg_c _ []).mp
    (by rw [alg_c]; exact obsFrom_chain Ξ 3 hvL hfinL)
  have hR := obsFrom_chain_unique Ξ 3 hvR h
  have := alg_endL.2.1
  rw [show lookEnd 3 (schedK₀.plug algL) = lookEnd 3 (schedK₀.plug algR) from hR] at this
  rw [hpatR] at this
  exact absurd this (by decide)

/-- **Check 3, tail-resumption: `TailLaw`, as written, fails at our instance.**  The clause of `5`
is A's tail-resumptive clause at code that performs `11`, which E1′'s `sched` catches outside.
On the left the code runs outside the handler of `5`, so `sched` catches a continuation of the
clause's frame; on the right it runs inside, so `sched` catches the handler of `5` with it.  The
closures `sched` answers differ as terms.  Every hygiene hypothesis of the law holds: the code's
row has only `11`, which neither the empty context nor the handler catches, and the context
holds no finaliser.  The program is typed by today's kernel. -/
theorem not_tailLaw_ourInst (h11 : Ξ 11 = [(.lin, .unit, .unit)])
    (h5 : Ξ 5 = [(.lin, .unit, .unit)]) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).TailLaw := by
  intro hT
  let S := ourInst (ℍ := ℍ) orowRF Ξ tier1Open
  let c : OVal := ⟨tickCE, .lam⟩
  let εc : (orowAlg Ξ).Eff := (orowAlg Ξ).lift (lab11 Ξ h11)
  have hcder : S.der [] (S.app (S.force c) S.unitV) (S.F εc (OVTy.ofV .unit)) := by
    refine .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, OVTy.rFree_ofV .unit,
      fun η _ => ?_⟩
    show CDerivesNU LifeCtx.empty [] (appE tickCE .unit)
      (.comp (CTy.effOf (Row.ofEff 11 (Ξ 11) 0 ++ []) (OVTy.den η (OVTy.ofV .unit))))
    rw [h11, OVTy.den_ofV]
    exact .bind (A := .unit) .nil (.ret (.unitI .nil))
      (.app (.right .nil) (d_tickCENU (by cdead)) (.here .nil))
  have hRA := hT (lab5 Ξ h5) ⟨.lam (.var 0), .lam⟩ [S.tailCl c] .hole 0 S.unitV
    ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ c εc (OVTy.ofV .unit) rfl
    (by show ((Ξ 5).map _)[0]? = _; rw [h5]; rfl) (by intro h; cases h) rfl hcder
    (fun _ _ _ => rfl)
    (by
      rintro j ⟨-, h⟩
      have := h (fun _ => [])
      simp only [Targets.Row.Has, Option.isSome_iff_exists] at this
      obtain ⟨o, ho⟩ := this
      have h' : Row.find (Row.ofEff 11 (Ξ 11) 0 ++ []) 5 (UInt32.ofNat j) = some o := ho
      rw [Row.find_append] at h'
      rcases hf : Row.find (Row.ofEff 11 (Ξ 11) 0) 5 (UInt32.ofNat j) with _ | o'
      · rw [hf] at h'; simp [Row.find] at h'
      · obtain ⟨h511, -⟩ := Row.find_ofEff _ _ _ _ _ _ hf
        exact absurd h511 (by decide))
    (.inl trivial)
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ tailProg) ((Adequacy.emptyMem, lookEnd 4 tailProg), ()) :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 4 tailProg)
  obtain ⟨hvL, hpatL, hfinL⟩ := tail_endL
  obtain ⟨hvR, hpatR⟩ := tail_endR
  have hterm : S.term ((Adequacy.emptyMem, lookEnd 4 tailProg), ()).1 =
      S.plug schedK₀ (S.handle (lab5 Ξ h5) (S.hnd ⟨.lam (.var 0), .lam⟩ [S.tailCl c])
        (S.plug .hole (S.perform (lab5 Ξ h5) 0 S.unitV))) := tail_c
  have h := (hRA S.R₀ r₀_respects tailProg _ ((Adequacy.emptyMem, lookEnd 4 tailProg), ())
    schedK₀ (der_tier1Open_ret d_tailProgNU) hreach hterm _ []).mp
    (by rw [tail_c]; exact obsFrom_chain Ξ 8 hvL hfinL)
  have hR := obsFrom_chain_unique (e := schedK₀.plug (tailH5.plug (appE tickCE .unit))) Ξ 5 hvR h
  have hR' : lookEnd 8 (schedK₀.plug (tailH5.plug (performE (opArgE 5 0 (.val .unit))))) =
      lookEnd 5 (schedK₀.plug (tailH5.plug (appE tickCE .unit))) := hR
  rw [hR'] at hpatL
  rw [hpatR] at hpatL
  exact absurd hpatL (by decide)

end Check3

/-- **Check 3 at an admissible effect context.** -/
theorem not_unaryLaws_ΞA : AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).AlgLaw ∧
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).TailLaw :=
  ⟨admEff_ΞA, not_algLaw_ourInst ΞA (by simp [ΞA]),
    not_tailLaw_ourInst ΞA (by simp [ΞA]) (by simp [ΞA])⟩

/-! ### Check 4: why the S5 bridges take `FinAlone` -/

/-- A finaliser that performs the operation its cancelled region's handler catches. -/
def finP : Expr := performE (opArgE 2 0 (.val .unit))

/-- `handle_2 (perform (2, 0, ()) then x. x unwind perform (2, 0, ()))`, the clause of `2`
cancelling its continuation. -/
def finAloneProg : Expr :=
  withH 2 cancelCl (thenE (.var 0) finP (performE (opArgE 2 0 (.val .unit))))

/-- **A typing system that types `finAloneProg` alone**, at every type: no typing system of ours,
the witness that typing must supply `FinAlone`. -/
def J₄ : OurTyping orowRF := ⟨fun _ _ _ e _ => e = finAloneProg, OutJ.core, fun _ η => η⟩

/-- `J₄` meets `NoInterception`: its one program holds no `ccatch`, no `cfin` and no handler named
`0`. -/
theorem noInterception_J₄ : NoInterception J₄.read := by
  intro Θ Δ Γ e j h
  obtain ⟨Γ', j', -, -, he, -⟩ := h (fun _ => []) (models_empty Θ)
  subst he
  exact okE_sound _ (by decide)

def H2E' : Expr := hndValE 2 (.lam (.var 0)) [.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit)))]

theorem isVal_H2E' : IsVal H2E' := .pair .prim (.pair .lam (.pair .lam .unit))

/-- The cancelled region: the finaliser frame alone. -/
def p5K : Kont := .appR (.app (.prim .ubind) (.pair (.lam (.var 0)) (.lam finP))) .hole

abbrev p5cs : Val := cancelVal [2] none

theorem p5_c₀ : lookEnd 5 finAloneProg =
    Kont.hole.plug (cancelE (kappa 2 ⟨H2E', isVal_H2E'⟩ p5K)) := by rfl

theorem p5_c : lookEnd 8 finAloneProg =
    Kont.hole.plug (Targets.cancelOf 2 ⟨H2E', isVal_H2E'⟩ p5K) := by rfl

/-- Where the finaliser runs: `ccatch`, the dying handler of `2`, the cancel-mode frame. -/
def p5Kf : Kont :=
  .appR (.prim .ccatch) (.appR (.app (.prim .hnd) H2E') (.appR (.app (.prim .cfin) p5cs.1) .hole))

theorem p5_run :
    (lookRun 3 (lookEnd 8 finAloneProg)).map (fun x => x.2.1) =
      [ubindE (Val.pair (Val.lam (.var 0)) (Val.lam finP)) (raiseE (.val p5cs)),
       .app (.lam finP) .unit,
       hndE ⟨H2E', isVal_H2E'⟩ (cfinE p5cs finP)] := by rfl

theorem p5_terms :
    chainTerms (lookEnd 8 finAloneProg) (lookRun 3 (lookEnd 8 finAloneProg)) =
      [Targets.cancelOf 2 ⟨H2E', isVal_H2E'⟩ p5K,
       ccatchE (hndE ⟨H2E', isVal_H2E'⟩ (cfinE p5cs (.app (.lam finP) .unit))),
       p5Kf.plug finP,
       ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
         (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩ (.appR (.app (.prim .cfin) p5cs.1) .hole))))] := by
  rfl

theorem p5_noFin₁ : (evalSubs (ccatchE (hndE ⟨H2E', isVal_H2E'⟩
    (cfinE p5cs (.app (.lam finP) .unit))))).any performShape = false := by decide

theorem p5_noFin₃ : (evalSubs (ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
    (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩ (.appR (.app (.prim .cfin) p5cs.1) .hole)))))).any
      performShape = false := by decide

theorem p5_noCfin₃ : (evalSubs (ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
    (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩ (.appR (.app (.prim .cfin) p5cs.1) .hole)))))).any
      cfinShape = false := by decide

theorem cfinShape_p5Kf (t : Expr) : (evalSubs (p5Kf.plug t)).any cfinShape = true := by
  have : p5Kf.plug t = (Kont.appR (.prim .ccatch) (.appR (.app (.prim .hnd) H2E') .hole)).plug
      (cfinE p5cs t) := rfl
  rw [this]
  exact any_evalSubs_plug _ (p := cfinShape) rfl

theorem not_isOVal_finP : ¬ IsOVal finP := not_isOVal_prim_app (p := .perform) (by decide) _

section Check4
variable (Ξ : EffCtx)

def p5H : OVal × List OVal :=
  (⟨.lam (.var 0), .lam⟩, [⟨.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))), .lam⟩])

def p5q : List ((ourInst (ℍ := ℍ) orowRF Ξ J₄).Event ×
    (ourInst (ℍ := ℍ) orowRF Ξ J₄).RConf (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀) :=
  [(.fire finP, ((Adequacy.emptyMem,
      ccatchE (hndE ⟨H2E', isVal_H2E'⟩ (cfinE p5cs (.app (.lam finP) .unit)))), ())),
   (.tau, ((Adequacy.emptyMem, p5Kf.plug finP), ())),
   (.tau, ((Adequacy.emptyMem, ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
      (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩ (.appR (.app (.prim .cfin) p5cs.1) .hole))))), ()))]

theorem p5_path :
    chainPath (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀ Adequacy.emptyMem ()
      (lookRun 3 (lookEnd 8 finAloneProg)) = p5q (ℍ := ℍ) Ξ := by
  have h1 := p5_run
  have h2' := p5_terms
  unfold chainTerms at h2'
  simp only [chainPath]
  generalize lookRun 3 (lookEnd 8 finAloneProg) = L at h1 h2'
  have hlen : L.length = 3 := by
    have := congrArg List.length h1; simpa using this
  obtain ⟨x₁, x₂, x₃, rfl⟩ := A.EffectSystem.eq_three hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h1 h2'
  obtain ⟨a₁, a₂, a₃, -⟩ := h1
  obtain ⟨-, e₁, e₂, e₃, -⟩ := h2'
  simp only [List.map_cons, List.map_nil, p5q, a₁, a₂, a₃, e₁, e₂, e₃]
  rw [labelOf_fire (by intro h; exact (plug_raise_ne_val .hole _ ⟨_, h⟩) rfl), labelOf_tau_of rfl,
    labelOf_tau_of (show finHead (hndE ⟨H2E', isVal_H2E'⟩ (cfinE p5cs finP)) = false from rfl)]
  rfl

/-- **Check 4: `NoInterception` does not give `NoIntercept`.**  `J₄` types one program, and that
program holds no `ccatch`, no `cfin` and no handler named `0`; yet its cancelled region's finaliser
performs the operation the region's dying handler catches, so the finaliser does not run alone and
the run follows no cancel trace.  So the S5 bridges need a fact about what typed finalisers do at
run time, `FinAlone`: `NoInterception` is syntactic, and typing must supply the rest. -/
theorem not_noIntercept_of_noInterception (h2 : Ξ 2 = [(.aff, .unit, .unit)]) :
    NoInterception J₄.read ∧ ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₄).NoIntercept := by
  refine ⟨noInterception_J₄, fun hNI => ?_⟩
  let S := ourInst (ℍ := ℍ) orowRF Ξ J₄
  let l := lab2 Ξ h2
  let c₀ : S.RConf S.R₀ := ((Adequacy.emptyMem, lookEnd 5 finAloneProg), ())
  let c : S.RConf S.R₀ := ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ())
  have hder : S.der [] finAloneProg (S.F (orowAlg Ξ).unit (OVTy.ofV .unit)) :=
    .inl ⟨[], by simp, rfl⟩
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ finAloneProg) c₀ :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 5 finAloneProg)
  have hc₀ : S.term c₀.1 = S.plug .hole (S.cancel (S.capture l p5H p5K)) := by
    show lookEnd 5 finAloneProg = Kont.hole.plug (cancelE (captureE 2 _ _ p5K))
    rw [show captureE 2 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      kappa 2 ⟨H2E', isVal_H2E'⟩ p5K from captureE_val isVal_H2E' p5K]
    exact p5_c₀
  have hpure : S.PureSteps c₀.1 c.1 :=
    pureSteps_of_chain (RF := orowRF) (Ξ := Ξ) (J := J₄) (μ := Adequacy.emptyMem)
      (lookRun_sound (ℍ := ℍ) 3 (lookEnd 5 finAloneProg))
  have hc : S.term c.1 = S.plug .hole (S.cancelOf l p5H p5K) := by
    show lookEnd 8 finAloneProg = Kont.hole.plug (cancelOfE 2 _ _ p5K)
    rw [show cancelOfE 2 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      Targets.cancelOf 2 ⟨H2E', isVal_H2E'⟩ p5K from cancelOfE_val isVal_H2E' p5K]
    exact p5_c
  have hpath : S.RPath S.R₀ c (p5q (ℍ := ℍ) Ξ) := by
    rw [← p5_path Ξ]
    exact rpath_chainPath S.R₀ (lookRun_sound (ℍ := ℍ) 3 _)
  have hT := hNI S.R₀ r₀_respects finAloneProg (orowAlg Ξ).unit (OVTy.ofV .unit)
    (answers_unit S.R₀) hder c₀ c .hole l p5H p5K _ hreach hc₀ hpure rfl hc hpath
  have hfins : S.fins p5K = [finP] := rfl
  rw [hfins] at hT
  generalize hq' : p5q (ℍ := ℍ) Ξ = q' at hT
  cases hT with
  | stop => unfold p5q at hq'; cases hq'
  | @fire c' c₁ c₂ D fs err Kf q₀ q'' hst hpp hKf hft =>
      have hKf' : c₂.1.2 = Kf.plug finP := hKf
      unfold p5q at hq'
      obtain ⟨hx₁, hrest⟩ := List.cons.inj hq'
      rcases q₀ with _ | ⟨y, _ | ⟨z, _ | ⟨w, q₀⟩⟩⟩
      · cases hpp
        have := any_evalSubs_plug Kf (p := performShape) (s := finP) rfl
        rw [← hKf', ← (Prod.mk.inj hx₁).2] at this
        exact absurd this (by rw [p5_noFin₁]; decide)
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hq''⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp'
            obtain ⟨-, hc₂⟩ := Prod.mk.inj hy
            have hKf₂ : Kf = p5Kf := by
              have h : p5Kf.plug finP = Kf.plug finP := by rw [← hKf', ← hc₂]
              exact (plug_inj_ctx (fun h' => not_isOVal_finP (isOVal_of_isVal h')) h).symm
            generalize hfs0 : ([] : List (ourInst (ℍ := ℍ) orowRF Ξ J₄).Term) = fs0 at hft
            generalize her0 : (none : (ourInst (ℍ := ℍ) orowRF Ξ J₄).Err) = er0 at hft
            cases hft with
            | running hal =>
                -- the dying handler's catch is not a step of the finaliser alone
                subst hq'' hKf₂
                cases hal with
                | @cons _ _ _ t t' _ _ h₁ h₂ _ _ _ =>
                    have h₂' : ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
                        (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩
                          (.appR (.app (.prim .cfin) p5cs.1) .hole)))) = p5Kf.plug t' := h₂
                    have := cfinShape_p5Kf t'
                    rw [← h₂', p5_noCfin₃] at this
                    exact absurd this (by decide)
            | @ended _ _ _ _ qa c' r c'' qb hal hend _ _ =>
                rcases qa with _ | ⟨a, qa⟩
                · simp only [List.nil_append, List.cons.injEq] at hq''
                  obtain ⟨hev, -⟩ := hq''
                  have := (Prod.mk.inj hev).1
                  cases this
                · simp only [List.cons_append, List.cons.injEq] at hq''
                  obtain ⟨-, h⟩ := hq''
                  cases qa <;> simp at h
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨hy, hz, -⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp' with
            | cons _ _ hpp'' =>
                cases hpp''
                have := any_evalSubs_plug Kf (p := performShape) (s := finP) rfl
                rw [← hKf', ← (Prod.mk.inj hz).2] at this
                exact absurd this (by rw [p5_noFin₃]; decide)
      · simp only [List.append, List.cons.injEq] at hrest
        obtain ⟨-, -, h⟩ := hrest
        cases h

end Check4

end Targets.Inst

end
