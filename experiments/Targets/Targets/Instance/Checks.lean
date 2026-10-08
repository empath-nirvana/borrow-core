import Targets.Instance.CheckPrograms
import Targets.A.UnaryLaws
import Targets.Instance.Restricted.NoInterception

/-!
# The Instance — statement checks, each a typed program and its computed run

Each check is a program typed at our instance and its computed run (a run `look` computes,
`Targets/Base/Look.lean`, is a path of `ourInst`, `rpath_chainPath`; where a statement asks about
every run, determinism, `rstep_det`, makes it the only one).  The statements they read are those of
decision D4: S6 counts a step that applies `κ` as a use (`UseAt`), since Core's clauses apply `κ`
directly; S5's endings are parameterised by what a finaliser may raise (decision D3), and the
finalisers it fires meet the no-interception condition (`FinRow`); `RunsAlike` compares a program's
data answers.

This module holds the admissible context `ΞA`, the programs' typings at our instance, the run of
`nLogOutside` (κ caught, then applied), and the scope of the no-interception condition:

* **The no-interception condition is needed** (`noIntercept_needs_finRow`).  `J₄` types one
  program, which holds no `ccatch`, no `cfin` and no handler named `0` (`NoInterception`); its
  cancelled region's finaliser performs the operation the region's dying handler catches, so it
  does not meet `FinRow`, and the run from the cancel is a prefix of no cancel trace, at every set
  of endings: no continuation of it starts the finaliser again, the run ending at `()` with no
  operation at an evaluation position (`rpath_prefix_chainPath`).  `NoInterception` is syntactic;
  the condition is what typing must give about finalisers.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow lookRun lookEnd lookRun_sound rowAt_nil
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
  refine ⟨fun η _ => ⟨[] ++ [], _, rfl, rowAt_nil Ξ⟩, .inl ⟨[], by simp, ?_⟩⟩
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

/-! ### Check 1's witness: `nLogOutside`'s run -/

/-- `nLogOutside`'s run up to the catch of `log`, as `look` computes it: `log` is affine, so the
catch is followed by the allocation of `κ`'s cell (SPEC §25), which `look` does not take. -/
abbrev nLogRun : List (Kont × Expr × Expr) := lookRun 20 nLogOutside

/-- `with_log`'s answer clause and its clause, as A-values. -/
def hrLV : OVal := ⟨hrL, .lam⟩

def clLV : OVal := ⟨clL, .lam⟩

/-- What lies between `with_log`'s handler and the `log` it catches: `to_result`'s handler and
`□ to _. raise ()`. -/
def nLogK : Kont :=
  .appR (.app (.prim .hnd) (hndValE 1 (qualsVal [.aff]).1 hrR [.lam (.inj₂ (.var 0))]))
    (.appR (.lam raiseU) .hole)

/-- The configuration before the catch: `with_log`'s handler around `nLogK[log ()]`. -/
theorem nLogRun_catch :
    (chainTerms nLogOutside nLogRun)[4]? =
      some ((handleK 2 (qualsVal [.aff]).1 hrL [clL]).plug
        (nLogK.plug (performE (opArgE 2 0 (.val .unit))))) := by
  rfl

section Check1
variable (Ξ : EffCtx)

/-- The label of the name `2`, where `Ξ` declares one operation. -/
def lab2 {p : Qual × VTy × VTy} (h2 : Ξ 2 = [p]) : (orowAlg Ξ).Lab :=
  ⟨2, by decide, by rw [h2]; simp, by rw [h2]; simp⟩

theorem captureE_val {n : UInt32} {qs r : Expr} {cs : List Expr} (h : IsVal (hndValE n qs r cs))
    (K : Kont) : captureE n qs r cs K = kappa n ⟨_, h⟩ K := by
  unfold captureE; rw [dif_pos h]

theorem isVal_hndValE_log : IsVal (hndValE 2 (qualsVal [.aff]).1 hrL [clL]) :=
  .pair .prim (.pair (qualsVal _).2 (.pair .lam (.pair .lam .unit)))

end Check1

theorem cancelOfE_val {n : UInt32} {qs r : Expr} {cs : List Expr} (h : IsVal (hndValE n qs r cs))
    (K : Kont) : cancelOfE n qs r cs K = Targets.cancelOf n ⟨_, h⟩ K := by
  unfold cancelOfE; rw [dif_pos h]

/-! ### Paths from a chain to a value -/

/-- **Every path from the start of a chain of head steps that ends at a value is a prefix of the
chain's path**: each step of the chain is the only step of its configuration (`rstep_det`), and an
answer takes no step. -/
theorem rpath_prefix_chainPath {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}
    (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q₀ : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q₀ e' → IsVal e' →
      ∀ q, (ourInst (ℍ := ℍ) RF Ξ J).RPath R ((μ, e), s) q → q <+: chainPath R μ s q₀
  | _, _, _, .nil, hv, q, hp => by
      cases hp with
      | nil => exact List.nil_prefix
      | cons hst _ => exact (no_rstep_val R ⟨_, hv⟩ hst).elim
  | _, _, _, @HeadChain.cons _ _ K a a' e' q₀ hh hn hq, hv, q, hp => by
      cases hp with
      | nil => exact List.nil_prefix
      | @cons _ ev c₁ q' hst hp' =>
          obtain ⟨rfl, rfl⟩ := rstep_det (hh μ) hn hst
          exact List.cons_prefix_cons.2 ⟨rfl, rpath_prefix_chainPath R hq hv q' hp'⟩

/-- **Where a path that keeps the store ends**: at its start when it is empty, otherwise at its last
configuration. -/
theorem purePath_end {S : A.EffectSystem} {R : S.Runner} {c c' : S.RConf R}
    {q : List (S.Event × S.RConf R)} (h : S.PurePath R c q c') :
    (q = [] ∧ c' = c) ∨ ∃ ev, q.getLast? = some (ev, c') := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons c ev c₁ q c'' _ _ _ ih =>
      rcases ih with ⟨rfl, rfl⟩ | ⟨ev', hl⟩
      · exact .inr ⟨ev, rfl⟩
      · refine .inr ⟨ev', ?_⟩
        cases q with
        | nil => simp at hl
        | cons y q => rw [List.getLast?_cons_cons]; exact hl

/-! ### Check 4: the no-interception condition is needed -/

/-- A finaliser that performs the operation its cancelled region's handler catches. -/
def finP : Expr := performE (opArgE 2 0 (.val .unit))

/-- `handle_2 (perform (2, 0, ()) then x. x unwind perform (2, 0, ()))`, the clause of `2`
cancelling its continuation.  The operation is unrestricted, so `κ` owns no cell (SPEC §25), which
is beside the point of the check. -/
def finAloneProg : Expr :=
  withH 2 .unr cancelCl (thenE (.var 0) finP (performE (opArgE 2 0 (.val .unit))))

/-- **A typing system that types `finAloneProg` alone**, at every type: no typing system of ours,
the witness that the no-interception condition is needed. -/
def J₄ : OurTyping orowRF := ⟨fun _ _ _ e _ => e = finAloneProg, OutJ.core, fun _ η => η,
  fun _ _ _ _ e _ => e = finAloneProg⟩

/-- `J₄` meets `NoInterception`: its one program holds no `ccatch`, no `cfin` and no handler named
`0`. -/
theorem noInterception_J₄ : NoInterception J₄.read := by
  intro Θ Δ Γ e j h
  obtain ⟨Γ', j', -, -, he, -⟩ := h (fun _ => []) (models_empty Θ)
  subst he
  exact okE_sound _ (by decide)

def H2E' : Expr :=
  hndValE 2 (qualsVal [.unr]).1 (.lam (.var 0)) [.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit)))]

theorem isVal_H2E' : IsVal H2E' := .pair .prim (.pair (qualsVal _).2 (.pair .lam (.pair .lam .unit)))

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

/-- The configuration after the dying handler catches the finaliser's operation: the clause of `2`
applied to `((), κ)`, `κ` holding the cancel-mode frame. -/
def p5x₃ : Expr :=
  ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))))
    (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩ (.appR (.app (.prim .cfin) p5cs.1) .hole))))

/-- From there the run — the clause cancels `κ`, the cancel-mode frame catches the cancel, and the
two `ccatch` frames answer — ends at `()` in eight steps. -/
theorem p5x₃_end : lookEnd 8 p5x₃ = Val.unit.1 := by rfl

/-- No configuration of that run holds an operation at an evaluation position. -/
theorem p5x₃_noPerform :
    (chainTerms p5x₃ (lookRun 8 p5x₃)).all (fun t => !(evalSubs t).any performShape) = true := by
  decide

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

/-- **Check 4: the no-interception condition is needed** (decision D4 makes it explicit in S5,
`FinRow`).  `J₄` types one program, and that program holds no `ccatch`, no `cfin` and no handler
named `0`; its run reaches a cancel of `κ`, and the cancel's start.  The cancelled region's
finaliser performs the operation the region's dying handler catches: it does not meet `FinRow` at
any set of endings, and the run from the cancel's start is a prefix of no cancel trace at any set of
endings — no continuation of it, itself a run, follows one. -/
theorem noIntercept_needs_finRow (h2 : Ξ 2 = [(.unr, .unit, .unit)]) :
    NoInterception J₄.read ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₄).der [] finAloneProg
        ((ourInst (ℍ := ℍ) orowRF Ξ J₄).F (orowAlg Ξ).unit (OVTy.ofV .unit)) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₄).RReach (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀
        ((ourInst (ℍ := ℍ) orowRF Ξ J₄).rinit (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀ finAloneProg)
        ((Adequacy.emptyMem, lookEnd 5 finAloneProg), ()) ∧
      lookEnd 5 finAloneProg = (ourInst (ℍ := ℍ) orowRF Ξ J₄).plug .hole
        ((ourInst (ℍ := ℍ) orowRF Ξ J₄).cancel
          ((ourInst (ℍ := ℍ) orowRF Ξ J₄).capture (lab2 Ξ h2) p5H p5K)) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₄).PureSteps (Adequacy.emptyMem, lookEnd 5 finAloneProg)
        (Adequacy.emptyMem, lookEnd 8 finAloneProg) ∧
      lookEnd 8 finAloneProg = (ourInst (ℍ := ℍ) orowRF Ξ J₄).plug .hole
        ((ourInst (ℍ := ℍ) orowRF Ξ J₄).cancelOf (lab2 Ξ h2) p5H p5K) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₄).fins p5K = [finP] ∧
      (∀ FR, ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₄).FinRow FR finP) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₄).RPath (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀
        ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ()) (p5q (ℍ := ℍ) Ξ) ∧
      ∀ FR q', (ourInst (ℍ := ℍ) orowRF Ξ J₄).RPath (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀
          ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ()) (p5q (ℍ := ℍ) Ξ ++ q') →
        ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₄).CancelTrace (ourInst (ℍ := ℍ) orowRF Ξ J₄).R₀ FR
          ((ourInst (ℍ := ℍ) orowRF Ξ J₄).Region (lab2 Ξ h2) p5K) .hole
          ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ()) [finP] none (p5q (ℍ := ℍ) Ξ ++ q') := by
  let S := ourInst (ℍ := ℍ) orowRF Ξ J₄
  have hc₀ : lookEnd 5 finAloneProg = S.plug .hole (S.cancel (S.capture (lab2 Ξ h2) p5H p5K)) := by
    show lookEnd 5 finAloneProg = Kont.hole.plug (cancelE (captureE 2 (qsOf Ξ 2) _ _ p5K))
    rw [show qsOf Ξ 2 = (qualsVal [.unr]).1 by simp [qsOf, h2],
      show captureE 2 (qualsVal [.unr]).1 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      kappa 2 ⟨H2E', isVal_H2E'⟩ p5K from captureE_val isVal_H2E' p5K]
    exact p5_c₀
  have hc : lookEnd 8 finAloneProg = S.plug .hole (S.cancelOf (lab2 Ξ h2) p5H p5K) := by
    show lookEnd 8 finAloneProg = Kont.hole.plug (cancelOfE 2 (qsOf Ξ 2) _ _ p5K)
    rw [show qsOf Ξ 2 = (qualsVal [.unr]).1 by simp [qsOf, h2],
      show cancelOfE 2 (qualsVal [.unr]).1 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      Targets.cancelOf 2 ⟨H2E', isVal_H2E'⟩ p5K from cancelOfE_val isVal_H2E' p5K]
    exact p5_c
  refine ⟨noInterception_J₄, ⟨fun η _ => ⟨[] ++ [], _, rfl, rowAt_nil Ξ⟩, .inl ⟨[], by simp, rfl⟩⟩,
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 5 finAloneProg), hc₀,
    pureSteps_of_chain (RF := orowRF) (Ξ := Ξ) (J := J₄) (μ := Adequacy.emptyMem)
      (lookRun_sound (ℍ := ℍ) 3 (lookEnd 5 finAloneProg)), hc, rfl, ?_, ?_, ?_⟩
  · rintro FR ⟨ε, -, -, ⟨Θ, -, he⟩ | ⟨-, M, he, -⟩⟩
    · have he' : finP = finAloneProg := he
      simp [finP, finAloneProg, withH, bindE, performE] at he'
    · simp [finP, driveE, driveMark, performE] at he
  · rw [← p5_path]
    exact rpath_chainPath S.R₀ (lookRun_sound (ℍ := ℍ) 3 (lookEnd 8 finAloneProg))
  intro FR q' hpath hT
  -- after the dying handler's catch the run is a prefix of the chain to `()`, which holds no
  -- operation at an evaluation position
  have hq'ops : ∀ x ∈ q', (evalSubs x.2.1.2).any performShape = false := by
    have hp3 : S.RPath S.R₀ ((Adequacy.emptyMem, p5x₃), ()) q' := by
      unfold p5q at hpath
      cases hpath with
      | cons _ hp₁ =>
          cases hp₁ with
          | cons _ hp₂ =>
              cases hp₂ with
              | cons _ hp₃ => exact hp₃
    obtain ⟨l', hl'⟩ := rpath_prefix_chainPath S.R₀ (lookRun_sound (ℍ := ℍ) 8 p5x₃)
      (by rw [p5x₃_end]; exact Val.unit.2) q' hp3
    intro x hx
    have hx' : x ∈ chainPath S.R₀ Adequacy.emptyMem () (lookRun 8 p5x₃) := by
      rw [← hl']; exact List.mem_append_left _ hx
    simp only [chainPath, List.mem_map] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    have h := List.all_eq_true.1 p5x₃_noPerform (y.1.plug y.2.2)
      (List.mem_cons_of_mem _ (List.mem_map_of_mem hy))
    simpa using h
  generalize hq' : p5q (ℍ := ℍ) Ξ ++ q' = Q at hT
  cases hT with
  | stop => unfold p5q at hq'; simp at hq'
  | @fire c' c₁ c₂ D fs err Kf q₀ q'' hst hpp hKf hft =>
      have hKf' : c₂.1.2 = Kf.plug finP := hKf
      unfold p5q at hq'
      simp only [List.cons_append, List.nil_append] at hq'
      obtain ⟨hx₁, hrest⟩ := List.cons.inj hq'
      rcases q₀ with _ | ⟨y, _ | ⟨z, _ | ⟨w, q₀⟩⟩⟩
      · cases hpp
        have := any_evalSubs_plug Kf (p := performShape) (s := finP) rfl
        rw [← hKf', ← (Prod.mk.inj hx₁).2] at this
        exact absurd this (by rw [p5_noFin₁]; decide)
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
        obtain ⟨hy, hq''⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp'
            obtain ⟨-, hc₂⟩ := Prod.mk.inj hy
            have hKf₂ : Kf = p5Kf := by
              have h : p5Kf.plug finP = Kf.plug finP := by rw [← hKf', ← hc₂]
              exact (plug_inj_ctx (fun h' => not_isOVal_finP (isOVal_of_isVal h')) h).symm
            -- the dying handler's catch is not a step of the finaliser alone
            have hcat : ∀ (t' : Expr), ccatchE (.app (.lam (.letpair (.var 0) (.app (.var 0)
                (.inj₂ .unit)))) (.pair .unit (kappa 2 ⟨H2E', isVal_H2E'⟩
                  (.appR (.app (.prim .cfin) p5cs.1) .hole)))) ≠ p5Kf.plug t' := by
              intro t' h₂'
              have := cfinShape_p5Kf t'
              rw [← h₂', p5_noCfin₃] at this
              exact absurd this (by decide)
            generalize hfs0 : ([] : List (ourInst (ℍ := ℍ) orowRF Ξ J₄).Term) = fs0 at hft
            generalize her0 : (none : (ourInst (ℍ := ℍ) orowRF Ξ J₄).Err) = er0 at hft
            cases hft with
            | running hal =>
                subst hq'' hKf₂
                cases hal with
                | @cons _ _ _ t t' _ _ h₁ h₂ _ _ _ => exact hcat t' h₂
            | @ended _ _ _ _ qa c' r c'' qb hal hend _ _ _ =>
                rcases qa with _ | ⟨a, qa⟩
                · simp only [List.nil_append, List.cons.injEq] at hq''
                  obtain ⟨hev, -⟩ := hq''
                  have := (Prod.mk.inj hev).1
                  cases this
                · simp only [List.cons_append, List.cons.injEq] at hq''
                  obtain ⟨ha, -⟩ := hq''
                  subst ha hKf₂
                  cases hal with
                  | @cons _ _ _ t t' _ _ h₁ h₂ _ _ _ => exact hcat t' h₂
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
        obtain ⟨hy, hz, -⟩ := hrest
        cases hpp with
        | cons _ _ hpp' =>
            cases hpp' with
            | cons _ _ hpp'' =>
                cases hpp''
                have := any_evalSubs_plug Kf (p := performShape) (s := finP) rfl
                rw [← hKf', ← (Prod.mk.inj hz).2] at this
                exact absurd this (by rw [p5_noFin₃]; decide)
      · -- the finaliser would start after the catch: no configuration there holds an operation
        simp only [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨-, -, hw⟩ := hrest
        rcases purePath_end hpp with ⟨h, -⟩ | ⟨ev, hl⟩
        · cases h
        · rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hl
          have hm : (ev, c₂) ∈ q' := by
            rw [hw]
            exact List.mem_cons.2 (by
              rcases List.mem_cons.1 (List.mem_of_getLast? hl) with h | h
              · exact .inl h
              · exact .inr (List.mem_append_left _ h))
          have h₁ := hq'ops _ hm
          have h₂ := any_evalSubs_plug Kf (p := performShape) (s := finP) rfl
          rw [← hKf'] at h₂
          change (evalSubs c₂.1.2).any performShape = false at h₁
          rw [h₁] at h₂
          cases h₂

end Check4

end Targets.Inst

end
