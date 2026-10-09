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
`nLogOutside` (κ caught, then applied), and the run of a finaliser that performs its cancelled
region's operation:

* **The region a cancel tears down is dead** (`finAlone_dead`).  `J₄` types one program, which
  holds no `ccatch`, no `cfin` and no handler named `0` (`NoInterception`); its cancelled region's
  finaliser performs the operation of the handler whose continuation is cancelled, so it meets
  `FinRow` at no set of endings.  The cancel runs the region with that handler removed (SPEC §19,
  *Cancels*): the finaliser fires and starts, its operation meets no frame that catches it, and the
  run stops there.  That run is a cancel trace at every set of endings.
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
    (K : Kont) : captureE n qs r cs K = kappa ⟨_, h⟩ K := by
  unfold captureE; rw [dif_pos h]

theorem isVal_hndValE_log : IsVal (hndValE 2 (qualsVal [.aff]).1 hrL [clL]) :=
  .pair .prim (.pair (qualsVal _).2 (.pair .lam (.pair .lam .unit)))

end Check1

theorem cancelOfE_val {n : UInt32} {qs r : Expr} {cs : List Expr} (h : IsVal (hndValE n qs r cs))
    (K : Kont) : cancelOfE n qs r cs K = Targets.cancelOf K := by
  unfold cancelOfE; rw [if_pos h]

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
  | @cons c c₁ q c'' _ _ _ ih =>
      rcases ih with ⟨rfl, rfl⟩ | ⟨ev', hl⟩
      · exact .inr ⟨.tau, rfl⟩
      · refine .inr ⟨ev', ?_⟩
        cases q with
        | nil => simp at hl
        | cons y q => rw [List.getLast?_cons_cons]; exact hl

/-! ### Check 4: the region a cancel tears down is dead -/

/-- A finaliser that performs the operation of the handler whose continuation is cancelled. -/
def finP : Expr := performE (opArgE 2 0 (.val .unit))

/-- `handle_2 (perform (2, 0, ()) then x. x unwind perform (2, 0, ()))`, the clause of `2`
cancelling its continuation.  The operation is unrestricted, so `κ` owns no cell (SPEC §25), which
is beside the point of the check. -/
def finAloneProg : Expr :=
  withH 2 .unr cancelCl (thenE (.var 0) finP (performE (opArgE 2 0 (.val .unit))))

/-- **A typing system that types `finAloneProg` alone**, at every type: no typing system of ours. -/
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

theorem p5_c₀ : lookEnd 5 finAloneProg =
    Kont.hole.plug (cancelE (kappa ⟨H2E', isVal_H2E'⟩ p5K)) := by rfl

theorem p5_c : lookEnd 8 finAloneProg =
    Kont.hole.plug (Targets.cancelOf p5K) := by rfl

/-- Where the finaliser runs: the cancel's delimiter and the cancel-mode frame; the handler of `2`
is dead. -/
def p5Kf : Kont :=
  .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1) .hole)

/-- **The region's handler is dead**: from the cancel's start the finaliser fires, and its
`perform 2` meets no frame that catches it, two steps later; the run stops there. -/
theorem finAloneProg_stop :
    lookEnd 2 (lookEnd 8 finAloneProg) = p5Kf.plug finP ∧
      look (p5Kf.plug finP) = .op false p5Kf (opPayload 2 0 Val.unit) 2 := by
  constructor <;> rfl

theorem finE_lam_finP : finE (Expr.lam finP) = finP := rfl

section Check4
variable (Ξ : EffCtx)

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₄

def p5H : OVal × List OVal :=
  (⟨.lam (.var 0), .lam⟩, [⟨.lam (.letpair (.var 0) (.app (.var 0) (.inj₂ .unit))), .lam⟩])

/-- The run from the cancel's start: `[finalise-cancel]`, which leaves `(λ_. finP) ()` under
`cfin`, and the β-step that starts the finaliser. -/
def p5q : List ((𝕁).Event × (𝕁).RConf (𝕁).R₀) :=
  [(.fire finP, ((Adequacy.emptyMem, ccatchE (cfinE (cancelVal none) (.app (.lam finP) .unit))), ())),
   (.tau, ((Adequacy.emptyMem, p5Kf.plug finP), ()))]

/-- `[finalise-cancel]` at the cancel's start, labelled `fire finP`. -/
theorem p5_fire :
    (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ()) (.fire finP)
      ((Adequacy.emptyMem, ccatchE (cfinE (cancelVal none) (.app (.lam finP) .unit))), ()) := by
  have hh := Head.ufinC (ℍ := ℍ) Adequacy.emptyMem (Val.lam (.var 0)) (Val.lam finP) none .hole rfl
  have ho := OStep.mach (RF := orowRF) (Ξ := Ξ) (K := .appR (.prim .ccatch) .hole) hh
  rw [labelOf_fire (show ¬ IsVal (Kont.hole.plug (raiseE (.val (cancelVal none)))) from
    fun h => plug_raise_ne_val .hole _ ⟨_, h⟩ rfl)] at ho
  rw [p5_c]
  exact .mach ho

/-- The β-step that starts the finaliser under `cfin`. -/
theorem p5_beta :
    (𝕁).PureStep (Adequacy.emptyMem, ccatchE (cfinE (cancelVal none) (.app (.lam finP) .unit))) .tau
      (Adequacy.emptyMem, p5Kf.plug finP) := by
  have ho := OStep.mach (RF := orowRF) (Ξ := Ξ) (K := p5Kf)
    (Head.beta (ℍ := ℍ) Adequacy.emptyMem finP Val.unit)
  rw [labelOf_tau_of rfl] at ho
  exact ⟨ho, rfl⟩

/-- The finaliser's `perform 2` takes no step: no frame of `p5Kf` catches it, and the runner that
answers nothing answers nothing. -/
theorem p5_stuck (ev : (𝕁).Event) (c' : (𝕁).RConf (𝕁).R₀) :
    ¬ (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, p5Kf.plug finP), ()) ev c' := by
  intro h
  cases h with
  | mach h' =>
      exact no_ostep_op (r := false) (K := p5Kf) 2 0 (OVal.ofVal Val.unit) rfl
        (by simp [OpFree, p5Kf, Kont.HasHnd]) h'
  | io _ _ hans _ => exact hans.elim

/-- **Check 4: the region a cancel tears down is dead** (SPEC §19, *Cancels*).  `J₄` types one
program, and that program holds no `ccatch`, no `cfin` and no handler named `0`; its run reaches a
cancel of `κ`, and the cancel's start.  The cancelled region's finaliser performs the operation of
the handler whose continuation is cancelled, and meets `FinRow` at no set of endings.  The cancel
runs the region with that handler removed: the finaliser fires, starts, and its operation meets no
frame that catches it, so the run stops there; the region's one action is the finaliser's fire,
and that run is a cancel trace of it at every set of endings. -/
theorem finAlone_dead (h2 : Ξ 2 = [(.unr, .unit, .unit)]) :
    NoInterception J₄.read ∧
      (𝕁).der [] finAloneProg ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV .unit)) ∧
      (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ finAloneProg)
        ((Adequacy.emptyMem, lookEnd 5 finAloneProg), ()) ∧
      lookEnd 5 finAloneProg = (𝕁).plug .hole ((𝕁).cancel ((𝕁).capture (lab2 Ξ h2) p5H p5K)) ∧
      (𝕁).PureSteps (Adequacy.emptyMem, lookEnd 5 finAloneProg)
        (Adequacy.emptyMem, lookEnd 8 finAloneProg) ∧
      lookEnd 8 finAloneProg = (𝕁).plug .hole ((𝕁).cancelOf (lab2 Ξ h2) p5H p5K) ∧
      (𝕁).fins p5K = [finP] ∧
      (∀ FR, ¬ (𝕁).FinRow FR finP) ∧
      (𝕁).RPath (𝕁).R₀ ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ()) (p5q (ℍ := ℍ) Ξ) ∧
      (∀ ev c', ¬ (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, p5Kf.plug finP), ()) ev c') ∧
      (𝕁).acts p5K = [.fire finP] ∧
      ∀ FR, (𝕁).CancelTrace (𝕁).R₀ FR .hole ((Adequacy.emptyMem, lookEnd 8 finAloneProg), ())
        [.fire finP] none (p5q (ℍ := ℍ) Ξ) := by
  have hc₀ : lookEnd 5 finAloneProg = (𝕁).plug .hole ((𝕁).cancel ((𝕁).capture (lab2 Ξ h2) p5H p5K)) := by
    show lookEnd 5 finAloneProg = Kont.hole.plug (cancelE (captureE 2 (qsOf Ξ 2) _ _ p5K))
    rw [show qsOf Ξ 2 = (qualsVal [.unr]).1 by simp [qsOf, h2],
      show captureE 2 (qualsVal [.unr]).1 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      kappa ⟨H2E', isVal_H2E'⟩ p5K from captureE_val isVal_H2E' p5K]
    exact p5_c₀
  have hc : lookEnd 8 finAloneProg = (𝕁).plug .hole ((𝕁).cancelOf (lab2 Ξ h2) p5H p5K) := by
    show lookEnd 8 finAloneProg = Kont.hole.plug (cancelOfE 2 (qsOf Ξ 2) _ _ p5K)
    rw [show qsOf Ξ 2 = (qualsVal [.unr]).1 by simp [qsOf, h2],
      show cancelOfE 2 (qualsVal [.unr]).1 (↑p5H.1) (List.map Subtype.val p5H.2) p5K =
      Targets.cancelOf p5K from cancelOfE_val isVal_H2E' p5K]
    exact p5_c
  have hfire := p5_fire (ℍ := ℍ) Ξ
  have hβ := p5_beta (ℍ := ℍ) Ξ
  refine ⟨noInterception_J₄, ⟨fun η _ => ⟨[] ++ [], _, rfl, rowAt_nil Ξ⟩, .inl ⟨[], by simp, rfl⟩⟩,
    rreach_of_chain (𝕁).R₀ (lookRun_sound (ℍ := ℍ) 5 finAloneProg), hc₀,
    pureSteps_of_chain (RF := orowRF) (Ξ := Ξ) (J := J₄) (μ := Adequacy.emptyMem)
      (lookRun_sound (ℍ := ℍ) 3 (lookEnd 5 finAloneProg)), hc, rfl, ?_,
    .cons hfire (.cons (.mach hβ.1) .nil), p5_stuck Ξ, rfl, fun FR => ?_⟩
  · rintro FR ⟨ε, -, -, ⟨Θ, -, he⟩ | ⟨-, M, he, -⟩⟩
    · have he' : finP = finAloneProg := he
      simp [finP, finAloneProg, withH, bindE, performE] at he'
    · simp [finP, driveE, driveMark, performE] at he
  · have hpp : (𝕁).PurePath (𝕁).R₀
        ((Adequacy.emptyMem, ccatchE (cfinE (cancelVal none) (.app (.lam finP) .unit))), ())
        [(.tau, ((Adequacy.emptyMem, p5Kf.plug finP), ()))]
        ((Adequacy.emptyMem, p5Kf.plug finP), ()) := .cons hβ rfl .nil
    have := A.EffectSystem.CancelTrace.fire (S := 𝕁) (R := (𝕁).R₀) (FR := FR)
      (K₀ := .hole) (as := []) (err := none) (Kf := p5Kf) (q := [])
      (c₂ := ((Adequacy.emptyMem, p5Kf.plug finP), ())) hfire hpp rfl (.running .nil)
    simpa [p5q] using this

end Check4

end Targets.Inst

end
