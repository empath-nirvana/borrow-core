import Targets.Instance.CellRuns
import Targets.A.Soundness

/-!
# The Instance — S5's traces at our machine

A's S5 (`Cancellation`, `Targets/A/Soundness.lean`) reads every run from the start of a cancel or of
an unwind as a prefix of a trace: each finaliser fires, runs alone, and hands the cancel or the
raise on.  This module builds those traces at our machine, from one fact about each fired
finaliser: from the memory it fires at, every run of it continues to `()` (`FinOK`).  Typing gives
that fact (`Targets/I/S5J1.lean`: a finaliser that meets S5's no-interception condition at option A
is a closed program at the pure row, and runs to `()` from every finite memory).

* **A step of `Kf[t]`, `t` stepping, is `t`'s step under `Kf`**, with its label (`ostep_unplug`,
  `rstep_unplug`).  So while the fired finaliser has a step, the run is the finaliser's run alone.
* **The unwind** (`unwind_pfx`): at a raise under a context of A's shape (`Std`) whose finalisers
  are `FinOK` at every finite memory, the innermost finaliser frame fires (`[finalise]`, labelled
  `fire D`), `D ()` reduces to `D` (a β-step), `D` runs alone to `()`, `(); raise p` hands the raise
  on (`[1↦]`), and the unwind goes on through the rest of the context.
* **The cancel** (`cancel_pfx`): at `ccatch (K[raise (0, (0, err))])`, `K` free of `ccatch` and of
  handlers named `0` (at a cancel's start, the dead region `K†`), the innermost frame that stops
  the cancel is a finaliser frame or a running finaliser's `cfin` frame (`frame_of_cancel`).  A
  finaliser frame fires (`[finalise-cancel]`), its finaliser runs alone under `cfin` to `()`, and
  `[cfin-ret]` (labelled `finEnd none`) hands the cancel on.  A `cfin` frame, a finaliser of an
  earlier cancel whose continuation this cancel tears down, is passed by `[cfin-cancel]` (labelled
  `finEnd` of the error kept so far), the earlier cancel's error first (`pend`).  At the end
  `[cancel]` answers `()`, or `[cancel-raise]` raises the kept error at the canceller.  The trace
  reads a kept error at the labels (`keptErrOf`), so the `cfin` frames must hold errors of labels'
  names (`CfinNamed`).

**Every path is a trace once the β-step after a fire is taken** (`FireExt`).  A trace's fire step
carries the administrative steps that start the finaliser (`PurePath c₁ q₀ c₂`, the finaliser at
`c₂`); at our machine the fire step leaves `D ()`, one β-step from `D`.  So a path that stops right
after a fire step is a trace once that step is appended, and every other path is a trace as it
is.  This is S5's prefix-closed reading (`unwindOrder_of_core`, `noIntercept_of_core`), and no
more: the extension is the one step after a fire.  Read whole, S5 fails at `J₁`
(`Targets/I/S5J1.lean`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)
open Targets (RowForm EffCtx orowRF orowAlg)

variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-! ### A step of a context around a term that steps -/

theorem not_isVal_of_step1 {μ μ' : Heap} {t t' : Expr} (h : Step1 (ℍ := ℍ) μ t μ' t') :
    ¬ IsVal t :=
  fun hv => BoCa.BoLo.no_step_val (w := ⟨t, hv⟩) h

/-- **A step of `Kf[t]`, where `t` steps at the same memory, is `t`'s step under `Kf`**, with the
same label: the redex is `t`'s (`plug_cmp`; a redex holds no other at an evaluation position,
`head_nested`). -/
theorem ostep_unplug {μ μ₁ : Heap} {Kf : Kont} {t t₁ : Expr} (ht : Step1 (ℍ := ℍ) μ t μ₁ t₁)
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : Heap × Expr}
    (h : OStep (ℍ := ℍ) RF Ξ (μ, Kf.plug t) ev c') :
    ∃ t', c'.2 = Kf.plug t' ∧ OStep (ℍ := ℍ) RF Ξ (μ, t) ev (c'.1, t') ∧
      Step1 (ℍ := ℍ) μ t c'.1 t' := by
  have hnv : ¬ IsVal t := not_isVal_of_step1 ht
  generalize hc : (μ, Kf.plug t) = c at h
  cases h with
  | @mach μ₀ μ' K a a' hh =>
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      rcases plug_cmp Kf K hnv hh.not_isVal hc with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
      · subst h₂
        refine ⟨K''.plug a', by simp [Kont.plug_comp], ?_, ⟨K'', a, a', h₁, rfl, hh⟩⟩
        rw [h₁]
        exact OStep.mach hh
      · obtain ⟨K₀, a₀, a₀', rfl, -, h₀⟩ := ht
        rw [← Kont.plug_comp] at h₁
        obtain ⟨rfl, rfl⟩ := comp_eq_hole (head_nested hh _ h₁ h₀)
        simp only [Kont.comp, Kont.plug] at h₁
        subst h₁
        rw [h₂, Kont.comp_hole]
        exact ⟨a', rfl, OStep.mach (K := .hole) hh, ⟨.hole, _, _, rfl, rfl, hh⟩⟩
  | again =>
      have h' := ht.plug Kf
      rw [(Prod.mk.inj hc).2] at h'
      exact (no_step1_drive _ h').elim
  | fin =>
      have h' := ht.plug Kf
      rw [(Prod.mk.inj hc).2] at h'
      exact (no_step1_drive _ h').elim

/-- **Under every runner, a step of `Kf[t]`, where `t` steps, is `t`'s step under `Kf`**, with
the same label and the runner's state kept: the runner answers no operation of a configuration
that steps. -/
theorem rstep_unplug {R : (𝕊).Runner} {s : R.St} {μ μ₁ : Heap} {Kf : Kont} {t t₁ : Expr}
    (ht : Step1 (ℍ := ℍ) μ t μ₁ t₁) {ev : (𝕊).Event} {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, Kf.plug t), s) ev c') :
    ∃ t', c' = ((c'.1.1, Kf.plug t'), s) ∧ (𝕊).RStep R ((μ, t), s) ev ((c'.1.1, t'), s) ∧
      Step1 (ℍ := ℍ) μ t c'.1.1 t' := by
  generalize hc : ((μ, Kf.plug t), s) = c at h
  cases h with
  | @mach c₀ ev c₁ s₀ h' =>
      cases hc
      obtain ⟨t', ht', ho, hs⟩ := ostep_unplug ht h'
      refine ⟨t', ?_, .mach ho, hs⟩
      obtain ⟨μ', e'⟩ := c₁
      change e' = Kf.plug t' at ht'
      rw [ht']
      rfl
  | io hterm hK _ _ =>
      cases hc
      exact (no_io_of_step1 (J := J) (ht.plug Kf) _ _ _ _ hterm hK).elim

/-! ### Finalisers that run to `()` -/

/-- **From the memory `μ`, every run of `D` continues to `()`.** -/
def FinOK (μ : Heap) (D : Expr) : Prop :=
  ∀ μ₁ e₁, Steps (ℍ := ℍ) μ D μ₁ e₁ → ∃ μ', Steps (ℍ := ℍ) μ₁ e₁ μ' Val.unit.1

/-- Along a run of a finaliser that runs to `()`, every term is `()` or steps. -/
theorem FinOK.unit_or_step {μ : Heap} {D : Expr} (h : FinOK (ℍ := ℍ) μ D) {μ₁ : Heap} {t : Expr}
    (hs : Steps (ℍ := ℍ) μ D μ₁ t) : t = Val.unit.1 ∨ ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ₁ t μ₂ t₂ := by
  obtain ⟨μ', hrest⟩ := h μ₁ t hs
  by_cases ht : t = Val.unit.1
  · exact .inl ht
  · obtain ⟨μ₂, t₂, h₁, -⟩ := steps_first hrest (Ne.symm ht)
    exact .inr ⟨μ₂, t₂, h₁⟩

/-! ### Contexts of A's unwinding shape -/

/-- **A context of A's unwinding shape** (`Std`) has no finaliser frame, or an innermost one with no
finaliser frame inside it. -/
theorem std_split {K : (𝕊).Kont} (h : (𝕊).Std K) :
    Kont.NoUnwind K ∨ ∃ (K₁ K₂ : Kont) (N D : Expr),
      K = K₂.comp ((thenK N D).comp K₁) ∧ K₁.NoUnwind ∧ (𝕊).Std K₂ := by
  induction h with
  | clear hK => exact .inl hK
  | @frame K₁ K₂ F hK₁ hF hStd ih =>
      change K₁.NoUnwind at hK₁
      rcases hF with ⟨l, H, rfl⟩ | ⟨N, D, rfl⟩
      · rcases ih with hK₂ | ⟨K₁', K₂', N, D, rfl, hK₁', hStd'⟩
        · left
          exact (noUnwind_comp K₂ _).2 ⟨hK₂, (noUnwind_comp _ K₁).2 ⟨handleK_noUnwind _ _ _ _, hK₁⟩⟩
        · right
          refine ⟨K₁'.comp ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
            (H.2.map Subtype.val)).comp K₁), K₂', N, D, ?_, ?_, hStd'⟩
          · change (K₂'.comp ((thenK N D).comp K₁')).comp ((handleK _ _ _ _).comp K₁) = _
            simp only [Kont.comp_assoc]
          · exact (noUnwind_comp K₁' _).2 ⟨hK₁', (noUnwind_comp _ K₁).2 ⟨handleK_noUnwind _ _ _ _, hK₁⟩⟩
      · exact .inr ⟨K₁, K₂, N, D, rfl, hK₁, hStd⟩

/-- The finalisers of a context split at its innermost finaliser frame. -/
theorem fins_split (K₁ K₂ : Kont) (N D : Expr) (hK₁ : K₁.NoUnwind) :
    (𝕊).fins (K₂.comp ((thenK N D).comp K₁)) = D :: (𝕊).fins K₂ := by
  change List.map finE (K₂.comp ((thenK N D).comp K₁)).fins = D :: List.map finE K₂.fins
  rw [fins_map_comp, fins_map_comp, fins_map_of_noUnwind K₁ hK₁, thenK_fins]
  rfl

/-! ### The raise at a configuration a typed program reaches -/

/-- At a configuration a typed program reaches, a raise at an evaluation position is Core's, at a
value. -/
theorem raise_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr} (hc : (𝕊).Live c) {K : Kont}
    {m : (RF.alg Ξ).Lab} {j : ℕ} {w : OVal} (h : c.2 = K.plug ((𝕊).raise m j w)) :
    ∃ v : Val, (𝕊).raise m j w = raiseE (.val (opPayload (RF.name Ξ m) (UInt32.ofNat j) v)) := by
  rcases raise_cases (ℍ := ℍ) (J := J) m j w with ⟨-, hr⟩ | ⟨-, hr⟩
  · have hv : IsVal w.1 := by
      refine val_of_live hL hc w.2 (K := K.comp (.appR (.prim .raise)
        (.pairR (Val.i32 (RF.name Ξ m)) (.pairR (Val.i32 (UInt32.ofNat j)) .hole)))) ?_
      rw [Kont.plug_comp, h, hr]
      rfl
    exact ⟨⟨w.1, hv⟩, by rw [hr]; rfl⟩
  · exfalso
    have hcl := (hL c hc).1
    rw [h, hr] at hcl
    rw [not_closed_opJunk] at hcl
    exact Bool.false_ne_true hcl

/-! ### The steps of an unwind -/

/-- The finaliser frame `thenK N D` around `X` is Core's `ubind (λx. N, λ_. D↑) X`. -/
theorem thenK_plug (N D X : Expr) :
    (thenK N D).plug X = ubindE (Val.pair (Val.lam N) (Val.lam (D.shift 1 0))) X := rfl

/-- A raise in a context is no value. -/
theorem not_isVal_plug_raise (K : Kont) (p : Val) : ¬ IsVal (K.plug (raiseE (.val p))) :=
  fun h => opE_not_isVal true p (K.isVal_of_plug h)

/-- The label of `[finalise]` at A's finaliser frame: `fire D`. -/
theorem labelOf_thenK (N D : Expr) {e : Expr} (he : ¬ IsVal e) :
    labelOf RF Ξ (ubindE (Val.pair (Val.lam N) (Val.lam (D.shift 1 0))) e) = .fire D := by
  rw [labelOf_fire he]
  exact congrArg _ (finE_shift D)

/-- **The fire step of an unwind**: at a raise its finaliser frame is the innermost to stop,
`[finalise]`, labelled `fire D`. -/
theorem rstep_fire {R : (𝕊).Runner} (s : R.St) (μ : Heap) (K K₁ : Kont) (N D : Expr) {n i : UInt32}
    {v : Val} (hn : n ≠ 0) (hK₁ : K₁.Catches n = false) :
    (𝕊).RStep R ((μ, K.plug ((thenK N D).plug (K₁.plug (raiseE (.val (opPayload n i v)))))), s)
      (.fire D)
      ((μ, K.plug (.seq (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit))
        (raiseE (.val (opPayload n i v))))), s) := by
  have hh := Head.ufin (ℍ := ℍ) μ (Val.lam N) (Val.lam (D.shift 1 0)) n i v K₁ hn hK₁
  have ho := OStep.mach (RF := RF) (Ξ := Ξ) (K := K) hh
  rw [labelOf_thenK N D (not_isVal_plug_raise K₁ _)] at ho
  exact .mach ho

/-- **The fire step is the only step there.** -/
theorem rstep_fire_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K K₁ : Kont} {N D : Expr}
    {n i : UInt32} {v : Val} (hn : n ≠ 0) (hK₁ : K₁.Catches n = false) {ev : (𝕊).Event}
    {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug ((thenK N D).plug (K₁.plug (raiseE (.val (opPayload n i v)))))), s)
      ev c') :
    ev = .fire D ∧
      c' = ((μ, K.plug (.seq (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit))
        (raiseE (.val (opPayload n i v))))), s) := by
  have hh := Head.ufin (ℍ := ℍ) μ (Val.lam N) (Val.lam (D.shift 1 0)) n i v K₁ hn hK₁
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) hh rfl h
  exact ⟨labelOf_thenK N D (not_isVal_plug_raise K₁ _), rfl⟩

/-- A head step that keeps the store and is no finaliser's, under every runner: labelled `tau`,
the only step there, and a step of A's that keeps the store. -/
theorem rstep_quiet_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K : Kont} {a a' : Expr}
    (hh : Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false) (hf : finHead a = false)
    {ev : (𝕊).Event} {c' : (𝕊).RConf R} (h : (𝕊).RStep R ((μ, K.plug a), s) ev c') :
    ev = .tau ∧ c' = ((μ, K.plug a'), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) hh hn h
  exact ⟨labelOf_tau_of hf, rfl⟩

theorem ostep_quiet {μ : Heap} (K : Kont) {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ a')
    (hf : finHead a = false) : OStep (ℍ := ℍ) RF Ξ (μ, K.plug a) .tau (μ, K.plug a') := by
  have ho := OStep.mach (RF := RF) (Ξ := Ξ) (K := K) hh
  rwa [labelOf_tau_of hf] at ho

theorem rstep_quiet {R : (𝕊).Runner} (s : R.St) {μ : Heap} (K : Kont) {a a' : Expr}
    (hh : Head (ℍ := ℍ) μ a μ a') (hf : finHead a = false) :
    (𝕊).RStep R ((μ, K.plug a), s) .tau ((μ, K.plug a'), s) :=
  .mach (ostep_quiet K hh hf)

/-- One quiet step, as a path that keeps the store. -/
theorem purePath_quiet {R : (𝕊).Runner} (s : R.St) {μ : Heap} (K : Kont) {a a' : Expr}
    (hh : Head (ℍ := ℍ) μ a μ a') (hf : finHead a = false) :
    (𝕊).PurePath R ((μ, K.plug a), s) [(.tau, ((μ, K.plug a'), s))] ((μ, K.plug a'), s) :=
  .cons ⟨ostep_quiet K hh hf, rfl⟩ rfl .nil

/-- The first step of a path. -/
theorem rpath_cons_inv {R : (𝕊).Runner} {c c' : (𝕊).RConf R} {ev : (𝕊).Event}
    {q : List ((𝕊).Event × (𝕊).RConf R)} (h : (𝕊).RPath R c ((ev, c') :: q)) :
    (𝕊).RStep R c ev c' ∧ (𝕊).RPath R c' q := by
  cases h with
  | cons h₁ h₂ => exact ⟨h₁, h₂⟩

/-- A reached configuration's step keeps it reached. -/
theorem rreach_tail {R : (𝕊).Runner} {c₀ c c' : (𝕊).RConf R} {ev : (𝕊).Event}
    (h : (𝕊).RReach R c₀ c) (hs : (𝕊).RStep R c ev c') : (𝕊).RReach R c₀ c' :=
  Relation.ReflTransGen.tail h ⟨ev, hs⟩

/-! ### What a path needs to be a trace -/

/-- **What S5's prefix-closed reading appends to a path at our machine**: nothing, or one step
`tau` when the path stops right at a fire step — the step that starts the fired finaliser (at our
machine the β-step of `D ()`).  The trace's fire step goes with its β-step. -/
def FireExt {S : A.EffectSystem} {R : S.Runner} (q q' : List (S.Event × S.RConf R)) : Prop :=
  q' = [] ∨ ∃ D c₁ c₂, q.getLast? = some (.fire D, c₁) ∧ q' = [(.tau, c₂)]

/-- Nothing appended. -/
theorem FireExt.nil {S : A.EffectSystem} {R : S.Runner} (q : List (S.Event × S.RConf R)) :
    FireExt q [] :=
  .inl rfl

/-- A step in front of a path keeps what the path needs. -/
theorem FireExt.cons {S : A.EffectSystem} {R : S.Runner} {q q' : List (S.Event × S.RConf R)}
    (x : S.Event × S.RConf R) (h : FireExt q q') : FireExt (x :: q) q' := by
  rcases h with rfl | ⟨D, c₁, c₂, hl, rfl⟩
  · exact .inl rfl
  · refine .inr ⟨D, c₁, c₂, ?_, rfl⟩
    cases q with
    | nil => simp at hl
    | cons y q => rw [List.getLast?_cons_cons]; exact hl

/-- A path that stops at a fire step needs the step after it. -/
theorem FireExt.fire {S : A.EffectSystem} {R : S.Runner} (D : S.Term) (c₁ c₂ : S.RConf R) :
    FireExt [((.fire D : S.Event), c₁)] [(.tau, c₂)] :=
  .inr ⟨D, c₁, c₂, rfl, rfl⟩

/-! ### The unwind's traces -/

/-- A step of the finaliser, read alone, goes in front of the trace of what follows. -/
theorem pend_cons {R : (𝕊).Runner} {FR : (RF.alg Ξ).Lab → Prop} {K₀ K₂ Kp : (𝕊).Kont}
    {pp : (RF.alg Ξ).Lab × ℕ × OVal} {c c' : (𝕊).RConf R} {t t' : Expr} {ev : (𝕊).Event}
    (h₁ : c.1.2 = ((K₀.comp K₂).comp Kp).plug t) (h₂ : c'.1.2 = ((K₀.comp K₂).comp Kp).plug t')
    (hs : (𝕊).RStep R c ev c') (hs' : (𝕊).RStep R ((c.1.1, t), c.2) ev ((c'.1.1, t'), c'.2))
    {q : List ((𝕊).Event × (𝕊).RConf R)} (h : (𝕊).PendTrace R FR K₀ K₂ Kp pp c' q) :
    (𝕊).PendTrace R FR K₀ K₂ Kp pp c ((ev, c') :: q) := by
  cases h with
  | running ha => exact .running (.cons h₁ h₂ hs hs' ha)
  | returned ha he hpp ht hu =>
      have := A.EffectSystem.PendTrace.returned (.cons h₁ h₂ hs hs' ha) he hpp ht hu
      simpa only [List.cons_append] using this
  | superseded ha ht hK hU hFR hu =>
      have := A.EffectSystem.PendTrace.superseded (p := pp) (.cons h₁ h₂ hs hs' ha) ht hK hU hFR hu
      simpa only [List.cons_append] using this

/-- **The unwind while a fired finaliser runs alone**, given the unwind through the rest of the
context on shorter paths.  The finaliser runs to `()` from the memory it fired at (`FinOK`): while
it has a step, the run is its run alone (`rstep_unplug`); at `()`, `(); raise p` hands the raise on
(`[1↦]`). -/
theorem pend_pfx {R : (𝕊).Runner} {P : Expr} {K₀ K₂ : Kont} {lab : (RF.alg Ξ).Lab} {j : ℕ}
    {w : OVal} {p : Val} (hp : (𝕊).raise lab j w = raiseE (.val p)) {μf : Heap} {D : Expr}
    (hD : FinOK (ℍ := ℍ) μf D) (n : ℕ)
    (ihU : ∀ q : List ((𝕊).Event × (𝕊).RConf R), q.length < n → ∀ c : (𝕊).RConf R,
      (𝕊).RReach R ((𝕊).rinit R P) c → c.1.2 = K₀.plug (K₂.plug ((𝕊).raise lab j w)) →
      (𝕊).RPath R c q → ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ c K₂ (q ++ q')) :
    ∀ (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n → ∀ (c : (𝕊).RConf R) (t : Expr),
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = ((K₀.comp K₂).comp (.seq .hole (raiseE (.val p)))).plug t →
      Steps (ℍ := ℍ) μf D c.1.1 t → (𝕊).RPath R c q →
      ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).PendTrace R (𝕊).noFinRaise K₀ K₂ (.seq .hole (raiseE (.val p))) (lab, j, w) c
          (q ++ q') := by
  intro q
  induction q with
  | nil =>
      intro _ c t _ _ _ _
      exact ⟨[], FireExt.nil _, .nil, .running .nil⟩
  | cons x q₁ ih =>
      intro hlen c t hreach hterm hrun hq
      obtain ⟨ev, c'⟩ := x
      obtain ⟨⟨μc, ec⟩, sc⟩ := c
      change ec = _ at hterm
      change Steps μf D μc t at hrun
      subst hterm
      cases hq with
      | cons hst hq₁ =>
      rcases hD.unit_or_step hrun with rfl | ⟨μ₂, t₂, ht⟩
      · -- the finaliser returned `()`: `(); raise p` hands the raise on
        have he : ((K₀.comp K₂).comp (.seq .hole (raiseE (.val p)))).plug Val.unit.1 =
            (K₀.comp K₂).plug (.seq (.val Val.unit) (raiseE (.val p))) := by
          rw [Kont.plug_comp]; rfl
        have hst' := hst
        rw [he] at hst'
        obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J) (Head.seq (ℍ := ℍ) μc (raiseE (.val p))) rfl
          rfl hst'
        have hterm' : ((K₀.comp K₂).plug (raiseE (.val p))) =
            K₀.plug (K₂.plug ((𝕊).raise lab j w)) := by
          rw [hp, Kont.plug_comp]
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ihU q₁ (by simp at hlen; omega) _
          (rreach_tail hreach hst) hterm' hq₁
        refine ⟨q'', hl''.cons _, .cons hst hpath'', ?_⟩
        have hpp := purePath_quiet (R := R) (J := J) sc (K₀.comp K₂)
          (Head.seq (ℍ := ℍ) μc (raiseE (.val p))) rfl
        rw [← he] at hpp
        have hend : (𝕊).Ended ((K₀.comp K₂).comp (.seq .hole (raiseE (.val p))))
            ((μc, ((K₀.comp K₂).comp (.seq .hole (raiseE (.val p)))).plug Val.unit.1), sc) none :=
          ⟨(𝕊).unitV, rfl⟩
        have := A.EffectSystem.PendTrace.returned (R := R) (FR := (𝕊).noFinRaise) (K₀ := K₀)
          (K₂ := K₂) (p := (lab, j, w)) .nil hend hpp hterm' htr''
        exact this
      · -- the finaliser steps: the run's step is its step alone
        obtain ⟨t', hc', hst', hs'⟩ := rstep_unplug ht hst
        obtain ⟨⟨μ', e'⟩, s'⟩ := c'
        simp only at hc'
        obtain ⟨⟨-, rfl⟩, rfl⟩ := hc'
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ih (by simp at hlen; omega) _ t'
          (rreach_tail hreach hst) rfl (hrun.trans (Steps.one hs')) hq₁
        exact ⟨q'', hl''.cons _, .cons hst hpath'', pend_cons rfl rfl hst hst' htr''⟩

/-- **The unwind's traces.**  At a configuration a typed program reaches, a raise pending under a
context of A's unwinding shape (`Std`) that holds no handler of its label, whose finalisers run to
`()` from every finite memory: every path is an unwind trace once what it needs is appended
(`FireExt`): nothing, or the β-step that starts a fired finaliser when the path stops right after
the fire step. -/
theorem unwind_pfx (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0) {R : (𝕊).Runner}
    (hR : R.Respects) {P : Expr} {C : OCTy} (hP : (𝕊).der [] P C) :
    ∀ (n : ℕ) (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n →
    ∀ (c : (𝕊).RConf R) (K₀ : Kont) (K : (𝕊).Kont) (lab : (RF.alg Ξ).Lab) (j : ℕ) (w : OVal),
      (𝕊).RReach R ((𝕊).rinit R P) c → (𝕊).Std K →
      c.1.2 = K₀.plug (Kont.plug K ((𝕊).raise lab j w)) → Kont.HasHnd (RF.name Ξ lab) K = false →
      (∀ D ∈ (𝕊).fins K, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) → (𝕊).RPath R c q →
      ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ c K (q ++ q') := by
  intro n
  induction n with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ n ih =>
    intro q hlen c K₀ K lab j w hreach hstd hterm hhnd hfin hq
    rcases std_split hstd with hU | ⟨K₁, K₂, N, D, rfl, hK₁, hstd₂⟩
    · refine ⟨[], FireExt.nil _, by simpa using hq, ?_⟩
      rw [List.append_nil]
      exact A.EffectSystem.UnwindTrace.out hterm hhnd hU
    have hlive : (𝕊).Live c.1 := ⟨P, C, R, c.2, hR, hP, hreach⟩
    obtain ⟨v, hr⟩ := raise_live (K := K₀.comp (K₂.comp ((thenK N D).comp K₁))) (m := lab) (j := j)
      (w := w) hL hlive (hterm.trans (Kont.plug_comp K₀ _ _).symm)
    have hH : Kont.HasHnd (RF.name Ξ lab) K₂ = false ∧ Kont.HasHnd (RF.name Ξ lab) K₁ = false := by
      have h := hhnd
      change Kont.HasHnd (RF.name Ξ lab) (K₂.comp ((thenK N D).comp K₁)) = false at h
      rw [hasHnd_comp, hasHnd_comp, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h
      exact ⟨h.1, h.2.2⟩
    have hK₁c : K₁.Catches (RF.name Ξ lab) = false :=
      catches_of_noUnwind _ (hnz lab) K₁ hK₁ hH.2
    have hfins := fins_split (ℍ := ℍ) (Ξ := Ξ) (J := J) K₁ K₂ N D hK₁
    have hD : ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D :=
      hfin D (by rw [hfins]; exact List.mem_cons_self)
    have hfin₂ : ∀ D' ∈ (𝕊).fins K₂, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D' :=
      fun D' h => hfin D' (by rw [hfins]; exact List.mem_cons_of_mem _ h)
    have hfd : FinDom c.1.1 := finDom_reach hreach
    have ihU : ∀ q' : List ((𝕊).Event × (𝕊).RConf R), q'.length < n → ∀ c' : (𝕊).RConf R,
        (𝕊).RReach R ((𝕊).rinit R P) c' → c'.1.2 = K₀.plug (K₂.plug ((𝕊).raise lab j w)) →
        (𝕊).RPath R c' q' → ∃ q'', FireExt q' q'' ∧ (𝕊).RPath R c' (q' ++ q'') ∧
          (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ c' K₂ (q' ++ q'') :=
      fun q' hq' c' hr' ht' hp' => ih q' hq' c' K₀ K₂ lab j w hr' hstd₂ ht' hH.1 hfin₂ hp'
    obtain ⟨⟨μ, e⟩, s⟩ := c
    change e = _ at hterm
    change FinDom μ at hfd
    have he : e = (K₀.comp K₂).plug ((thenK N D).plug (K₁.plug
        (raiseE (.val (opPayload (RF.name Ξ lab) (UInt32.ofNat j) v))))) := by
      refine hterm.trans ?_
      rw [hr, Kont.plug_comp K₂ ((thenK N D).comp K₁), Kont.plug_comp (thenK N D) K₁,
        ← Kont.plug_comp K₀ K₂]
    -- the configurations after the fire step and after the β-step
    let r := raiseE (.val (opPayload (RF.name Ξ lab) (UInt32.ofNat j) v))
    let c₁ : (𝕊).RConf R :=
      ((μ, (K₀.comp K₂).plug (.seq (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit)) r)), s)
    let c₂ : (𝕊).RConf R := ((μ, ((K₀.comp K₂).comp (.seq .hole r)).plug D), s)
    have hb : (K₀.comp K₂).plug (.seq (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit)) r) =
        ((K₀.comp K₂).comp (.seq .hole r)).plug (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit)) :=
      (Kont.plug_comp (K₀.comp K₂) (.seq .hole r) _).symm
    have hsub : (D.shift 1 0).subst 0 Val.unit = D := finE_shift D
    have hβo : OStep (ℍ := ℍ) RF Ξ c₁.1 .tau c₂.1 := by
      have h := ostep_quiet (RF := RF) (Ξ := Ξ) ((K₀.comp K₂).comp (.seq .hole r))
        (Head.beta (ℍ := ℍ) μ (D.shift 1 0) Val.unit) rfl
      rw [hsub, ← hb] at h
      exact h
    have hβ : (𝕊).RStep R c₁ .tau c₂ := .mach hβo
    have hpp : (𝕊).PurePath R c₁ [(.tau, c₂)] c₂ := .cons ⟨hβo, rfl⟩ rfl .nil
    have hβinv : ∀ {ev : (𝕊).Event} {c' : (𝕊).RConf R}, (𝕊).RStep R c₁ ev c' → ev = .tau ∧ c' = c₂ := by
      intro ev c' h
      change (𝕊).RStep R ((μ, (K₀.comp K₂).plug
        (.seq (.app (.val (Val.lam (D.shift 1 0))) (.val Val.unit)) r)), s) ev c' at h
      rw [hb] at h
      obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J) (Head.beta (ℍ := ℍ) μ (D.shift 1 0) Val.unit)
        rfl rfl h
      exact ⟨rfl, by rw [hsub]; rfl⟩
    cases hq with
    | nil => exact ⟨[], FireExt.nil _, .nil, .stop⟩
    | @cons _ ev₁ c₁' q₁ hst₁ hq₁ =>
    have hst₁' := hst₁
    change (𝕊).RStep R ((μ, e), s) ev₁ c₁' at hst₁'
    rw [he] at hst₁'
    obtain ⟨rfl, rfl⟩ := rstep_fire_inv (J := J) (hnz lab) hK₁c hst₁'
    have hreach₂ : (𝕊).RReach R ((𝕊).rinit R P) c₂ :=
      rreach_tail (rreach_tail hreach hst₁) hβ
    have hfire : ∀ q : List ((𝕊).Event × (𝕊).RConf R),
        (𝕊).PendTrace R (𝕊).noFinRaise K₀ K₂ (.seq .hole r) (lab, j, w) c₂ q →
        (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ ((μ, e), s) (K₂.comp ((thenK N D).comp K₁))
          ((.fire D, c₁) :: [(.tau, c₂)] ++ q) := fun q hpend =>
      A.EffectSystem.UnwindTrace.fire (S := 𝕊) (R := R) (FR := (𝕊).noFinRaise)
        (K₀ := K₀) (c := ((μ, e), s)) (c₁ := c₁) (c₂ := c₂) (K := K₂.comp ((thenK N D).comp K₁))
        (K₁ := K₁) (K₂ := K₂) (N := N) (D := D) (Kp := .seq .hole r) (m := lab) (j := j) (w := w)
        (q₀ := [(.tau, c₂)]) (q := q)
        rfl hH.2 hK₁ hterm hst₁ hpp (fun _ => rfl) trivial rfl hpend
    rcases q₁ with _ | ⟨⟨ev₂, c₂'⟩, q₂⟩
    · refine ⟨[(.tau, c₂)], FireExt.fire D c₁ c₂, .cons hst₁ (.cons hβ .nil), ?_⟩
      exact hfire [] (.running .nil)
    · obtain ⟨hst₂, hq₂⟩ := rpath_cons_inv hq₁
      obtain ⟨rfl, rfl⟩ := hβinv hst₂
      obtain ⟨q'', hl'', hpath'', hpend''⟩ :=
        pend_pfx (R := R) (P := P) (K₀ := K₀) (K₂ := K₂) (lab := lab) (j := j) (w := w) hr
          (hD μ hfd) n ihU q₂ (by simp at hlen; omega) c₂ D hreach₂ rfl (.refl _ _) hq₂
      exact ⟨q'', (hl''.cons _).cons _, .cons hst₁ (.cons hst₂ hpath''), hfire _ hpend''⟩

/-! ### The steps of a cancel -/

/-- The cancel-mode finaliser frame. -/
abbrev cfinK (st : Val) : Kont := .appR (.app (.prim .cfin) st.1) .hole

/-- The context around a cancel's raise: the canceller's, `ccatch`, and the region's frames still
to unwind. -/
abbrev cancelK (K₀ : Kont) (Kc : Kont) : Kont :=
  K₀.comp (ccatchK Kc)

theorem cancelK_plug (K₀ : Kont) (Kc : Kont) (x : Expr) :
    (cancelK K₀ Kc).plug x = K₀.plug (ccatchE (Kc.plug x)) := by
  rw [Kont.plug_comp]; rfl

/-- A step of our machine is a machine step, or the driver's at a whole term `drive v`. -/
theorem ostep_step1_or_drive {c c' : Heap × Expr} {ev : A.Ev (RF.alg Ξ).Lab OVal Expr}
    (h : OStep (ℍ := ℍ) RF Ξ c ev c') :
    (∃ μ' t', Step1 (ℍ := ℍ) c.1 c.2 μ' t') ∨ ∃ v : Val, c.2 = driveE (.val v) := by
  cases h with
  | mach hh => exact .inl ⟨_, _, ⟨_, _, _, rfl, rfl, hh⟩⟩
  | again => exact .inr ⟨_, rfl⟩
  | fin => exact .inr ⟨_, rfl⟩

/-- **At a configuration a typed program reaches, a raise stopped by a frame `f x` steps there**:
the configuration goes on (`LiveOK`), the raise is caught (no answer of the runner), it is no
value, and the step is at the stopping frame (`step1_raise`, `innerCatch_unique`). -/
theorem frame_step_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr} (hc : (𝕊).Live c)
    {K Ki : Kont} {f : Expr} {p : Val} {n : UInt32} (hp : payloadName p = some n)
    (hKi : Ki.Catches n = false) (hf : FrameCatches n f)
    (he : c.2 = K.plug (.app f (Ki.plug (raiseE (.val p))))) :
    ∃ μ' a', Head (ℍ := ℍ) c.1 (.app f (Ki.plug (raiseE (.val p)))) μ' a' := by
  have hctx : K.plug (.app f (Ki.plug (raiseE (.val p)))) =
      (K.comp (.appR f Ki)).plug (raiseE (.val p)) := by
    rw [Kont.plug_comp]; rfl
  rw [hctx] at he
  have hIC : InnerCatch n (K.comp (.appR f Ki)) K f Ki := ⟨rfl, hKi, hf⟩
  rcases (hL c hc).2 with ⟨v, hv⟩ | ⟨ev, c', h⟩ | ⟨r, K', p', n', hK', hp', hfree⟩
  · exfalso
    have h1 : IsVal ((K.comp (.appR f Ki)).plug (raiseE (.val p))) := by
      rw [← he, hv]; exact v.2
    exact not_isVal_plug_raise _ p h1
  · rcases ostep_step1_or_drive h with ⟨μ', t', hs⟩ | ⟨v, hv⟩
    · rw [he] at hs
      obtain ⟨Ko', f', Ki', a', hIC', hhead, -⟩ := step1_raise hp hs
      obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
      exact ⟨_, _, hhead⟩
    · exfalso
      rw [he] at hv
      have := plug_eq_drive hv (opE_not_isVal true p)
      rw [this] at hv
      simp [Kont.plug, driveE, driveMark, raiseE] at hv
  · exfalso
    rw [he] at hK'
    obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r := true) (r' := r) hK'
    rw [hp] at hp'
    cases hp'
    have hc' := catches_of_innerCatch (Ko := K) (Ki := Ki) (n := n) (f := f) hf
    simp only [OpFree, if_true] at hfree
    rw [hfree] at hc'
    cases hc'

/-- **At a configuration a typed program reaches, a raise stopped by a finaliser frame `ubind x`
holds a pair of values there**: the configuration steps at the frame (`frame_step_live`), and only
`[finalise]` or `[finalise-cancel]` steps at it (`head_ubind_raise`). -/
theorem ubind_pair_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr} (hc : (𝕊).Live c)
    {K Ki : Kont} {x : Expr} {p : Val} {n : UInt32} (hp : payloadName p = some n)
    (hKi : Ki.Catches n = false)
    (he : c.2 = K.plug (.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p))))) :
    ∃ N D : Val, x = (Val.pair N D).1 := by
  obtain ⟨μ', a', hhead⟩ := frame_step_live hL hc hp hKi
    (by simp [FrameCatches, Kont.Catches]) he
  obtain ⟨-, N, D, hx, -⟩ := head_ubind_raise hhead
  exact ⟨N, D, hx⟩

/-- A running finaliser's `cfin` frame stopping a raise: `[cfin-raise]` at a name other than `0`,
`[cfin-cancel]` at a cancel; its state is a cancel's. -/
theorem head_cfin_raise {μ μ' : Heap} {x : Expr} {Ki : Kont} {p : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.app (.prim .cfin) x) (Ki.plug (raiseE (.val p)))) μ' a') :
    μ' = μ ∧ ∃ err : Option Val, x = (cancelVal err).1 ∧
      ((∃ m j w, m ≠ 0 ∧ p = opPayload m j w ∧
          a' = raiseE (.val (cancelVal (BoCa.BoLo.errNext err m j w)))) ∨
       (∃ err', p = cancelVal err' ∧ a' = raiseE (.val (cancelVal (err.or err'))))) := by
  generalize hX : Expr.app (.app (.prim .cfin) x) (Ki.plug (raiseE (.val p))) = X at h
  cases h with
  | cfret err w =>
      simp only [cfinE, Expr.app.injEq] at hX
      exact absurd hX.2 (plug_raise_ne_val _ _ _)
  | cferr err m j w K hm hK =>
      simp only [cfinE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, err, hx, .inl ⟨m, j, w, hm, rfl, rfl⟩⟩
  | cfcancel err err' K hK =>
      simp only [cfinE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, err, hx, .inr ⟨err', rfl, rfl⟩⟩
  | _ => simp_all [hndE, ccatchE, ubindE]

/-- **At a configuration a typed program reaches, a raise stopped by a running finaliser's `cfin`
frame finds a cancel's state there**: the configuration steps at the frame (`frame_step_live`), and
only `[cfin-raise]` or `[cfin-cancel]` steps at it (`head_cfin_raise`). -/
theorem cfin_state_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr} (hc : (𝕊).Live c)
    {K Ki : Kont} {x : Expr} {p : Val} {n : UInt32} (hp : payloadName p = some n)
    (hKi : Ki.Catches n = false)
    (he : c.2 = K.plug (.app (.app (.prim .cfin) x) (Ki.plug (raiseE (.val p))))) :
    ∃ e : Option Val, x = (cancelVal e).1 := by
  obtain ⟨μ', a', hhead⟩ := frame_step_live hL hc hp hKi
    (by simp [FrameCatches, Kont.Catches]) he
  obtain ⟨-, e, hx, -⟩ := head_cfin_raise hhead
  exact ⟨e, hx⟩

/-- `[finalise-cancel]` at a pair of values, labelled `fire (finE D)`, the only step there. -/
theorem rstep_fireC_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K Ki : Kont} {N D : Val}
    {err : Option Val} (hKi : Ki.Catches 0 = false) {ev : (𝕊).Event}
    {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (cancelVal err)))))), s)
      ev c') :
    ev = .fire (finE D.1) ∧
      c' = ((μ, K.plug (cfinE (cancelVal err) (.app (.val D) (.val Val.unit)))), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) (Head.ufinC (ℍ := ℍ) μ N D err Ki hKi) rfl h
  exact ⟨labelOf_fire (not_isVal_plug_raise Ki _), rfl⟩

/-- `[cfin-ret]`, labelled `finEnd none`, the only step there. -/
theorem rstep_cfret_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K : Kont}
    {err : Option Val} {w : Val} {ev : (𝕊).Event} {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug (cfinE (cancelVal err) (.val w))), s) ev c') :
    ev = .finEnd none ∧ c' = ((μ, K.plug (raiseE (.val (cancelVal err)))), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) (Head.cfret (ℍ := ℍ) μ err w) rfl h
  exact ⟨labelOf_cfret _ _, rfl⟩

theorem rstep_cfret {R : (𝕊).Runner} (s : R.St) (μ : Heap) (K : Kont)
    (err : Option Val) (w : Val) :
    (𝕊).RStep R ((μ, K.plug (cfinE (cancelVal err) (.val w))), s) (.finEnd none)
      ((μ, K.plug (raiseE (.val (cancelVal err)))), s) := by
  have ho := OStep.mach (RF := RF) (Ξ := Ξ) (K := K) (Head.cfret (ℍ := ℍ) μ err w)
  rw [labelOf_cfret] at ho
  exact .mach ho

/-- `[cfin-cancel]`, labelled `finEnd` of the passing cancel's kept error, the only step there. -/
theorem rstep_cfcancel_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K Ki : Kont}
    {e err : Option Val} (hKi : Ki.Catches 0 = false) {ev : (𝕊).Event} {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug (cfinE (cancelVal e) (Ki.plug (raiseE (.val (cancelVal err)))))), s)
      ev c') :
    ev = .finEnd (keptErrOf RF Ξ err) ∧
      c' = ((μ, K.plug (raiseE (.val (cancelVal (e.or err))))), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) (Head.cfcancel (ℍ := ℍ) μ e err Ki hKi) rfl h
  exact ⟨labelOf_cfcancel _ _ _, rfl⟩

/-! ### The region a cancel tears down -/

/-- `K` has no `ccatch` frame: no delimiter of a cancel in progress. -/
def _root_.BoCa.BoLo.Kont.NoCC : Kont → Prop
  | .hole => True
  | .appR f K => f ≠ .prim .ccatch ∧ K.NoCC
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCC

theorem noCC_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoCC ↔ K₁.NoCC ∧ K₂.NoCC := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, Kont.NoCC]
  | appR f K ih => simp only [Kont.comp, Kont.NoCC, ih]; tauto
  | _ => simp_all [Kont.comp, Kont.NoCC]

/-- **A dead region holds no `ccatch` frame**: a cancel delimiter of the region is a frame the
cancel kills. -/
theorem noCC_dead : ∀ K : Kont, K.dead.NoCC
  | .hole => trivial
  | .appR f K => by
      simp only [Kont.dead]
      split
      · exact noCC_dead K
      · rename_i hf
        refine ⟨fun h => ?_, noCC_dead K⟩
        subst h
        simp [Kont.DeadFrame] at hf
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => noCC_dead K

/-- **A dead region meets what the region meets**: the frames a cancel kills are handler frames and
cancel delimiters, at which a cancel acts on nothing. -/
theorem kActs_dead : ∀ K : Kont, kActs RF Ξ K.dead = kActs RF Ξ K
  | .hole => rfl
  | .appR f K => by
      simp only [Kont.dead]
      split
      · rename_i hf
        rw [kActs_dead K]
        simp only [kActs]
        split
        · simp [Kont.DeadFrame] at hf
        · simp [Kont.DeadFrame] at hf
        · simp
      · simp only [kActs, kActs_dead K]
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => by simp only [Kont.dead, kActs, kActs_dead K]

/-- A context that stops no cancel meets nothing. -/
theorem kActs_nil_of_catches : ∀ (K : Kont), K.Catches 0 = false → kActs RF Ξ K = []
  | .hole, _ => rfl
  | .appR f K, h => by
      rw [catches_appR, Bool.or_eq_false_iff] at h
      simp only [kActs, kActs_nil_of_catches K h.2, List.nil_append]
      split
      · simp [Kont.Catches] at h
      · simp [Kont.Catches] at h
      · rfl
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => kActs_nil_of_catches K h

/-- What a cancel meets when its innermost stopping frame is a finaliser frame. -/
theorem kActs_innerUbind {Ko Ki : Kont} {N D : Val} (hKi : Ki.Catches 0 = false) :
    kActs RF Ξ (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)) =
      .fire (finE D.1) :: kActs RF Ξ Ko := by
  rw [kActs_comp]
  simp only [kActs, kActs_nil_of_catches Ki hKi, List.nil_append, Val.pair]
  rfl

/-- What a cancel meets when its innermost stopping frame is a running finaliser's `cfin` frame. -/
theorem kActs_innerCfin {Ko Ki : Kont} {x : Expr} (hKi : Ki.Catches 0 = false) :
    kActs RF Ξ (Ko.comp (.appR (.app (.prim .cfin) x) Ki)) =
      .pend (cfinErrOf RF Ξ x) :: kActs RF Ξ Ko := by
  rw [kActs_comp]
  simp only [kActs, kActs_nil_of_catches Ki hKi, List.nil_append]
  rfl

/-- The finalisers of a context whose innermost stopping frame is a running finaliser's `cfin`
frame: those outside it. -/
theorem fins_innerCfin {Ko Ki : Kont} {x : Expr} (hKi : Ki.Catches 0 = false) :
    (Ko.comp (.appR (.app (.prim .cfin) x) Ki)).fins = Ko.fins := by
  rw [fins_comp]
  simp only [Kont.fins, fins_nil_of_catches Ki hKi, List.nil_append, List.append_nil]

/-- **A stopping frame of `0`, in a context with no handler named `0` and no `ccatch` frame**, is a
finaliser frame or a running finaliser's `cfin` frame. -/
theorem frame_of_cancel {f : Expr} {Ki : Kont} (hf : FrameCatches 0 f)
    (hH : (Kont.appR f Ki).HasHnd 0 = false) (hC : (Kont.appR f Ki).NoCC) :
    (∃ x, f = .app (.prim .ubind) x) ∨ ∃ x, f = .app (.prim .cfin) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  simp only [Kont.HasHnd, Bool.or_eq_false_iff] at hH
  obtain ⟨hc, -⟩ := hC
  split at hf
  · rename_i m r
    simp only [beq_iff_eq] at hf
    subst hf
    simp at hH
  · exact .inl ⟨_, rfl⟩
  · exact absurd rfl hc
  · exact .inr ⟨_, rfl⟩
  · simp at hf

/-! ### Kept errors the labels read -/

/-- A label's name. -/
def LabName (RF : RowForm) (Ξ : EffCtx) (m : UInt32) : Prop := ∃ l, RF.name Ξ l = m

/-- **A kept error the labels read**: none, or the payload of a raise of a label's name. -/
def ErrNamed (RF : RowForm) (Ξ : EffCtx) : Option Val → Prop
  | none => True
  | some E => ∃ m j w, E = opPayload m j w ∧ LabName RF Ξ m

/-- **Every running finaliser's `cfin` frame of `K` holds a kept error the labels read**, at a state
that is a cancel's. -/
def CfinNamed (RF : RowForm) (Ξ : EffCtx) : Kont → Prop
  | .hole => True
  | .appR f K => (∀ e, f = .app (.prim .cfin) (cancelVal e).1 → ErrNamed RF Ξ e) ∧ CfinNamed RF Ξ K
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => CfinNamed RF Ξ K

theorem cfinNamed_comp : ∀ (K₁ K₂ : Kont),
    CfinNamed RF Ξ (K₁.comp K₂) ↔ CfinNamed RF Ξ K₁ ∧ CfinNamed RF Ξ K₂ := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, CfinNamed]
  | appR f K ih => simp only [Kont.comp, CfinNamed, ih]; tauto
  | _ => simp_all [Kont.comp, CfinNamed]

/-- A dead region keeps the region's `cfin` frames. -/
theorem cfinNamed_dead : ∀ {K : Kont}, CfinNamed RF Ξ K → CfinNamed RF Ξ K.dead
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.dead]
      split
      · exact cfinNamed_dead h.2
      · exact ⟨h.1, cfinNamed_dead h.2⟩
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => cfinNamed_dead (K := K) h

theorem errOf_named {m : UInt32} (hm : LabName RF Ξ m) (j : UInt32) (w : Val) :
    ∃ l, errOf RF Ξ m j w = some (l, j.toNat, OVal.ofVal w) ∧ RF.name Ξ l = m := by
  have hm' : ∃ l, RF.name Ξ l = m := hm
  unfold errOf
  rw [dif_pos hm']
  exact ⟨_, rfl, Classical.choose_spec hm'⟩

theorem keptErrOf_payload (m j : UInt32) (w : Val) :
    keptErrOf RF Ξ (some (opPayload m j w)) = errOf RF Ξ m j w := by
  have h : ∃ (m' j' : UInt32) (w' : Val), opPayload m j w = opPayload m' j' w' := ⟨m, j, w, rfl⟩
  simp only [keptErrOf, dif_pos h]
  have key : ∀ m' j' w', opPayload m j w = opPayload m' j' w' →
      errOf RF Ξ m' j' w' = errOf RF Ξ m j w := by
    intro m' j' w' he
    obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj he
    rfl
  exact key _ _ _ (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))

/-- The error a `cfin` frame at a cancel's state holds, read at the labels. -/
theorem cfinErrOf_cancelVal (e : Option Val) : cfinErrOf RF Ξ (cancelVal e).1 = keptErrOf RF Ξ e := by
  unfold cfinErrOf
  have h : ∃ e', (cancelVal e).1 = (cancelVal e').1 := ⟨e, rfl⟩
  rw [dif_pos h]
  rw [← cancelVal_inj (Subtype.ext (Classical.choose_spec h))]

/-- A kept error the labels read is read as an error. -/
theorem keptErrOf_some_ne {E : Val} (h : ErrNamed RF Ξ (some E)) : keptErrOf RF Ξ (some E) ≠ none := by
  obtain ⟨m, j, w, rfl, hm⟩ := h
  obtain ⟨l, hl, -⟩ := errOf_named hm j w
  rw [keptErrOf_payload, hl]
  simp

/-- **The labels read the first error**, when the earlier one is read. -/
theorem keptErrOf_or {e : Option Val} (he : ErrNamed RF Ξ e) (err : Option Val) :
    keptErrOf RF Ξ (e.or err) = (𝕊).keep (keptErrOf RF Ξ e) (keptErrOf RF Ξ err) := by
  cases e with
  | none => rfl
  | some E =>
      simp only [Option.some_or]
      cases h : keptErrOf RF Ξ (some E) with
      | none => exact absurd h (keptErrOf_some_ne he)
      | some x => rfl

theorem errNamed_or {e err : Option Val} (he : ErrNamed RF Ξ e) (herr : ErrNamed RF Ξ err) :
    ErrNamed RF Ξ (e.or err) := by
  cases e with
  | none => exact herr
  | some E => exact he

theorem keep_none_right {S : A.EffectSystem} (x : S.Err) : S.keep x none = x := by
  cases x <;> rfl

/-- **The canceller is answered as the labels read the kept error**: `()` at none, and at a kept
raise of a label's name, that raise. -/
theorem answered_none (K₀ : Kont) :
    (𝕊).Answered K₀ (keptErrOf RF Ξ none) (K₀.plug (.val Val.unit)) := rfl

theorem answered_some (K₀ : Kont) {E : Val} (h : ErrNamed RF Ξ (some E)) :
    ∃ x, keptErrOf RF Ξ (some E) = x ∧ (𝕊).Answered K₀ x (K₀.plug (raiseE (.val E))) := by
  obtain ⟨m, j, w, hE, hm⟩ := h
  obtain ⟨l, hl, hname⟩ := errOf_named hm j w
  refine ⟨some (l, j.toNat, OVal.ofVal w), by rw [hE, keptErrOf_payload, hl], ?_⟩
  show K₀.plug (raiseE (.val E)) = K₀.plug ((𝕊).raise l j.toNat (OVal.ofVal w))
  rw [raise_eq (ℍ := ℍ) (OVal.ofVal w) (UInt32.toNat_lt j), UInt32.ofNat_toNat, hname, hE]
  rfl

/-! ### The cancel's traces -/

/-- `finE` of a term that is no λ: the term applied to `()`. -/
theorem finE_of_not_lam {e : Expr} (h : ∀ b, e ≠ .lam b) : finE e = .app e (.val Val.unit) := by
  unfold finE
  split
  · rename_i b; exact absurd rfl (h b)
  · rfl

/-- A step of the finaliser, read alone, goes in front of the cancel trace of what follows. -/
theorem fin_cons {R : (𝕊).Runner} {FR : (RF.alg Ξ).Lab → Prop} {K₀ Kf : (𝕊).Kont}
    {c c' : (𝕊).RConf R} {t t' : Expr} {ev : (𝕊).Event} {as : List (𝕊).SAct} {err : (𝕊).Err}
    (h₁ : c.1.2 = Kf.plug t) (h₂ : c'.1.2 = Kf.plug t') (hs : (𝕊).RStep R c ev c')
    (hs' : (𝕊).RStep R ((c.1.1, t), c.2) ev ((c'.1.1, t'), c'.2))
    {q : List ((𝕊).Event × (𝕊).RConf R)} (h : (𝕊).FinTrace R FR K₀ Kf c' as err q) :
    (𝕊).FinTrace R FR K₀ Kf c as err ((ev, c') :: q) := by
  cases h with
  | running ha => exact .running (.cons h₁ h₂ hs hs' ha)
  | ended ha hend hFE hst hct =>
      have := A.EffectSystem.FinTrace.ended (.cons h₁ h₂ hs hs' ha) hend hFE hst hct
      simpa only [List.cons_append] using this

/-- **A cancel while a fired finaliser runs alone under `cfin`**, given the cancel through the rest
of the region on shorter paths.  The finaliser runs to `()` from the memory it fired at (`FinOK`):
while it has a step, the run is its run alone; at `()`, `[cfin-ret]` (labelled `finEnd none`) hands
the cancel on, the kept error unchanged. -/
theorem fin_pfx {R : (𝕊).Runner} {P : Expr} {K₀ : Kont} {Ko : Kont} {err : Option Val}
    {μf : Heap} {D : Expr} (hD : FinOK (ℍ := ℍ) μf D) (n : ℕ)
    (ihC : ∀ q : List ((𝕊).Event × (𝕊).RConf R), q.length < n → ∀ c : (𝕊).RConf R,
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = (cancelK K₀ Ko).plug (raiseE (.val (cancelVal err))) → (𝕊).RPath R c q →
      ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).CancelTrace R (𝕊).noFinRaise K₀ c (kActs RF Ξ Ko) (keptErrOf RF Ξ err) (q ++ q')) :
    ∀ (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n → ∀ (c : (𝕊).RConf R) (t : Expr),
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug t →
      Steps (ℍ := ℍ) μf D c.1.1 t → (𝕊).RPath R c q →
      ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).FinTrace R (𝕊).noFinRaise K₀ ((cancelK K₀ Ko).comp (cfinK (cancelVal err)))
          c (kActs RF Ξ Ko) (keptErrOf RF Ξ err) (q ++ q') := by
  intro q
  induction q with
  | nil =>
      intro _ c t _ _ _ _
      exact ⟨[], FireExt.nil _, .nil, .running .nil⟩
  | cons x q₁ ih =>
      intro hlen c t hreach hterm hrun hq
      obtain ⟨ev, c'⟩ := x
      obtain ⟨⟨μc, ec⟩, sc⟩ := c
      change ec = _ at hterm
      change Steps μf D μc t at hrun
      subst hterm
      obtain ⟨hst, hq₁⟩ := rpath_cons_inv hq
      rcases hD.unit_or_step hrun with rfl | ⟨μ₂, t₂, ht⟩
      · -- the finaliser returned `()`: `[cfin-ret]` hands the cancel on
        have he : ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug Val.unit.1 =
            (cancelK K₀ Ko).plug (cfinE (cancelVal err) (.val Val.unit)) :=
          Kont.plug_comp _ _ _
        have hst' := hst
        rw [he] at hst'
        obtain ⟨rfl, rfl⟩ := rstep_cfret_inv (J := J) hst'
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ihC q₁ (by simp at hlen; omega) _
          (rreach_tail hreach hst) rfl hq₁
        refine ⟨q'', hl''.cons _, .cons hst hpath'', ?_⟩
        have hend : (𝕊).Ended ((cancelK K₀ Ko).comp (cfinK (cancelVal err)))
            ((μc, ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug Val.unit.1), sc) none :=
          ⟨(𝕊).unitV, rfl⟩
        rw [← keep_none_right (S := 𝕊) (keptErrOf RF Ξ err)] at htr''
        exact A.EffectSystem.FinTrace.ended (S := 𝕊) (R := R) (FR := (𝕊).noFinRaise)
          (K₀ := K₀) (as := kActs RF Ξ Ko) (err := keptErrOf RF Ξ err) (r := none) .nil hend trivial
          hst htr''
      · -- the finaliser steps: the run's step is its step alone
        obtain ⟨t', hc', hst', hs'⟩ := rstep_unplug ht hst
        obtain ⟨⟨μ', e'⟩, s'⟩ := c'
        simp only at hc'
        obtain ⟨⟨-, rfl⟩, rfl⟩ := hc'
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ih (by simp at hlen; omega) _ t'
          (rreach_tail hreach hst) rfl (hrun.trans (Steps.one hs')) hq₁
        exact ⟨q'', hl''.cons _, .cons hst hpath'', fin_cons rfl rfl hst hst' htr''⟩

/-- **The cancel's traces.**  At a configuration a typed program reaches, a cancel raised under the
region's frames `Kc` still to unwind, inside `ccatch`, holding a kept error the labels read: when
`Kc` holds no `ccatch` and no handler named `0`, its running finalisers' `cfin` frames hold kept
errors the labels read, and its finalisers run to `()` from every finite memory, every path is a
cancel trace of what `Kc` meets once what it needs is appended (`FireExt`): nothing, or the β-step
that starts a fired finaliser that is a λ, when the path stops right after the fire step.  At a
finaliser frame the cancel fires it; at a running finaliser's `cfin` frame `[cfin-cancel]` passes
it, the earlier error first (`pend`). -/
theorem cancel_pfx (hL : LiveOK (ℍ := ℍ) RF Ξ J) {R : (𝕊).Runner} (hR : R.Respects) {P : Expr}
    {C : OCTy} (hP : (𝕊).der [] P C) {K₀ : Kont} :
    ∀ (n : ℕ) (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n →
    ∀ (c : (𝕊).RConf R) (Kc : Kont) (err : Option Val), (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = (cancelK K₀ Kc).plug (raiseE (.val (cancelVal err))) → Kc.NoCC →
      Kc.HasHnd 0 = false → CfinNamed RF Ξ Kc → ErrNamed RF Ξ err →
      (∀ D ∈ (𝕊).fins Kc, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) → (𝕊).RPath R c q →
      ∃ q', FireExt q q' ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).CancelTrace R (𝕊).noFinRaise K₀ c (kActs RF Ξ Kc) (keptErrOf RF Ξ err) (q ++ q') := by
  intro n
  induction n with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ n ih =>
  intro q hlen c Kc err hreach hterm hC hH hN herr hfin hq
  have hfd : FinDom c.1.1 := finDom_reach hreach
  have hlive : (𝕊).Live c.1 := ⟨P, C, R, c.2, hR, hP, hreach⟩
  obtain ⟨⟨μ, e⟩, s⟩ := c
  change e = _ at hterm
  change FinDom μ at hfd
  by_cases hA : Kc.Catches 0 = true
  swap
  · -- no frame is left: `[cancel]` or `[cancel-raise]` answers the canceller
    simp only [Bool.not_eq_true] at hA
    rw [kActs_nil_of_catches Kc hA]
    have he : e = K₀.plug (ccatchE (Kc.plug (raiseE (.val (cancelVal err))))) := by
      rw [hterm, Kont.plug_comp]; rfl
    rcases q with _ | ⟨⟨ev₁, c₁⟩, q₁⟩
    · exact ⟨[], FireExt.nil _, .nil, .stop⟩
    obtain ⟨hst₁, -⟩ := rpath_cons_inv hq
    have hst₁' := hst₁
    change (𝕊).RStep R ((μ, e), s) ev₁ c₁ at hst₁'
    rw [he] at hst₁'
    refine ⟨[], FireExt.nil _, by simpa using hq, ?_⟩
    rw [List.append_nil]
    cases err with
    | none =>
        obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J)
          (Head.cancel (ℍ := ℍ) μ Kc hA) rfl rfl hst₁'
        exact A.EffectSystem.CancelTrace.answer hst₁ (answered_none K₀)
    | some E =>
        obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J)
          (Head.creraise (ℍ := ℍ) μ E Kc hA) rfl rfl hst₁'
        obtain ⟨x, hx, hans⟩ := answered_some (ℍ := ℍ) (J := J) K₀ herr
        rw [hx]
        exact A.EffectSystem.CancelTrace.answer hst₁ hans
  -- the innermost frame that stops the cancel
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists 0 Kc hA
  have hH' : (Kont.appR f Ki).HasHnd 0 = false ∧ Ko.HasHnd 0 = false := by
    rw [hasHnd_comp, Bool.or_eq_false_iff] at hH; exact ⟨hH.2, hH.1⟩
  have hCo := (noCC_comp _ _).1 hC
  have hNo := (cfinNamed_comp _ _).1 hN
  have he₀ : ∀ g : Expr, f = g → e = (cancelK K₀ Ko).plug (.app g
      (Ki.plug (raiseE (.val (cancelVal err))))) := by
    rintro g rfl
    rw [hterm]
    change (K₀.comp (ccatchK (Ko.comp (.appR f Ki)))).plug _ = _
    rw [Kont.plug_comp, Kont.plug_comp]
    change K₀.plug (.app (.prim .ccatch) ((Ko.comp (.appR f Ki)).plug _)) =
      K₀.plug (.app (.prim .ccatch) (Ko.plug _))
    rw [Kont.plug_comp]
    rfl
  rcases frame_of_cancel hf hH'.1 hCo.2 with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · -- a finaliser frame: `[finalise-cancel]` fires it
    obtain ⟨N', D', rfl⟩ := ubind_pair_live (c := (μ, e)) hL hlive (payloadName_cancelVal err)
      hKi (he₀ _ rfl)
    have hfins : (𝕊).fins (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N' D').1) Ki)) =
        finE D'.1 :: (𝕊).fins Ko := by
      change List.map finE (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N' D').1) Ki)).fins = _
      rw [fins_innerUbind hKi]; rfl
    rw [kActs_innerUbind hKi]
    have hD : FinOK (ℍ := ℍ) μ (finE D'.1) :=
      hfin _ (by rw [hfins]; exact List.mem_cons_self) μ hfd
    have hfino : ∀ D ∈ (𝕊).fins Ko, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D :=
      fun D h => hfin D (by rw [hfins]; exact List.mem_cons_of_mem _ h)
    have ihC : ∀ q' : List ((𝕊).Event × (𝕊).RConf R), q'.length < n → ∀ c' : (𝕊).RConf R,
        (𝕊).RReach R ((𝕊).rinit R P) c' →
        c'.1.2 = (cancelK K₀ Ko).plug (raiseE (.val (cancelVal err))) → (𝕊).RPath R c' q' →
        ∃ q'', FireExt q' q'' ∧ (𝕊).RPath R c' (q' ++ q'') ∧
          (𝕊).CancelTrace R (𝕊).noFinRaise K₀ c' (kActs RF Ξ Ko) (keptErrOf RF Ξ err) (q' ++ q'') :=
      fun q' hq' c' hr' ht' hp' => ih q' hq' c' Ko err hr' ht' hCo.1 hH'.2 hNo.1 herr hfino hp'
    have he : e = (cancelK K₀ Ko).plug (ubindE (Val.pair N' D')
        (Ki.plug (raiseE (.val (cancelVal err))))) := he₀ _ rfl
    rcases q with _ | ⟨⟨ev₁, c₁⟩, q₁⟩
    · exact ⟨[], FireExt.nil _, .nil, .stop⟩
    obtain ⟨hst₁, hq₁⟩ := rpath_cons_inv hq
    have hst₁' := hst₁
    change (𝕊).RStep R ((μ, e), s) ev₁ c₁ at hst₁'
    rw [he] at hst₁'
    obtain ⟨rfl, rfl⟩ := rstep_fireC_inv (J := J) hKi hst₁'
    have hreach₁ := rreach_tail hreach hst₁
    -- the finaliser's start: `D ()`, one β-step from `D`'s body when `D` is a λ
    have hc₁ : (cancelK K₀ Ko).plug (cfinE (cancelVal err) (.app (.val D') (.val Val.unit))) =
        ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug (.app (.val D') (.val Val.unit)) :=
      (Kont.plug_comp (cancelK K₀ Ko) (cfinK (cancelVal err)) _).symm
    by_cases hlam : ∃ b, D'.1 = .lam b
    · obtain ⟨b, hb⟩ := hlam
      have hDv : D' = Val.lam b := Subtype.ext hb
      subst hDv
      let c₂ : (𝕊).RConf R :=
        ((μ, ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug (finE (Val.lam b).1)), s)
      have hβo : OStep (ℍ := ℍ) RF Ξ
          (μ, (cancelK K₀ Ko).plug (cfinE (cancelVal err) (.app (.val (Val.lam b)) (.val Val.unit))))
          .tau c₂.1 := by
        have h := ostep_quiet (RF := RF) (Ξ := Ξ) ((cancelK K₀ Ko).comp (cfinK (cancelVal err)))
          (Head.beta (ℍ := ℍ) μ b Val.unit) rfl
        rw [← hc₁] at h
        exact h
      have hpp : (𝕊).PurePath R
          ((μ, (cancelK K₀ Ko).plug (cfinE (cancelVal err) (.app (.val (Val.lam b)) (.val Val.unit)))), s)
          [(.tau, c₂)] c₂ := .cons ⟨hβo, rfl⟩ rfl .nil
      have hfire : ∀ q : List ((𝕊).Event × (𝕊).RConf R),
          (𝕊).FinTrace R (𝕊).noFinRaise K₀ ((cancelK K₀ Ko).comp (cfinK (cancelVal err)))
            c₂ (kActs RF Ξ Ko) (keptErrOf RF Ξ err) q →
          (𝕊).CancelTrace R (𝕊).noFinRaise K₀ ((μ, e), s)
            (.fire (finE (Val.lam b).1) :: kActs RF Ξ Ko) (keptErrOf RF Ξ err)
            ((.fire (finE (Val.lam b).1),
              ((μ, (cancelK K₀ Ko).plug
                (cfinE (cancelVal err) (.app (.val (Val.lam b)) (.val Val.unit)))), s)) ::
              [(.tau, c₂)] ++ q) := fun q hft =>
        A.EffectSystem.CancelTrace.fire hst₁ hpp rfl hft
      rcases q₁ with _ | ⟨⟨ev₂, c₂'⟩, q₂⟩
      · exact ⟨[(.tau, c₂)], FireExt.fire _ _ c₂, .cons hst₁ (.cons (.mach hβo) .nil),
          hfire [] (.running .nil)⟩
      obtain ⟨hst₂, hq₂⟩ := rpath_cons_inv hq₁
      have hst₂' := hst₂
      rw [hc₁] at hst₂'
      obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J) (Head.beta (ℍ := ℍ) μ b Val.unit) rfl rfl hst₂'
      obtain ⟨q'', hl'', hpath'', hft''⟩ :=
        fin_pfx (R := R) (P := P) (K₀ := K₀) (Ko := Ko) (err := err) hD n ihC q₂
          (by simp at hlen; omega) c₂ _ (rreach_tail hreach₁ hst₂) rfl (.refl _ _) hq₂
      exact ⟨q'', (hl''.cons _).cons _, .cons hst₁ (.cons hst₂ hpath''), hfire _ hft''⟩
    · -- `D` is no λ: `D ()` is the finaliser's term already
      have hfe : finE D'.1 = .app (.val D') (.val Val.unit) :=
        finE_of_not_lam (fun b h => hlam ⟨b, h⟩)
      have hc₁' : ((μ, (cancelK K₀ Ko).plug (cfinE (cancelVal err)
          (.app (.val D') (.val Val.unit)))), s).1.2 =
          ((cancelK K₀ Ko).comp (cfinK (cancelVal err))).plug (finE D'.1) := by
        rw [hfe]; exact hc₁
      obtain ⟨q'', hl'', hpath'', hft''⟩ :=
        fin_pfx (R := R) (P := P) (K₀ := K₀) (Ko := Ko) (err := err) hD n ihC q₁
          (by simp at hlen; omega) _ _ hreach₁ hc₁' (.refl _ _) hq₁
      exact ⟨q'', hl''.cons _, .cons hst₁ hpath'',
        A.EffectSystem.CancelTrace.fire (q₀ := []) hst₁ .nil hc₁' hft''⟩
  · -- a running finaliser's `cfin` frame: `[cfin-cancel]` passes it, the earlier error first
    obtain ⟨e', rfl⟩ := cfin_state_live (c := (μ, e)) hL hlive (payloadName_cancelVal err) hKi
      (he₀ _ rfl)
    have he'N : ErrNamed RF Ξ e' := hNo.2.1 e' rfl
    rw [kActs_innerCfin hKi, cfinErrOf_cancelVal]
    have hfins : (𝕊).fins (Ko.comp (.appR (.app (.prim .cfin) (cancelVal e').1) Ki)) = (𝕊).fins Ko := by
      change List.map finE (Ko.comp (.appR (.app (.prim .cfin) (cancelVal e').1) Ki)).fins = _
      rw [fins_innerCfin hKi]; rfl
    have hfino : ∀ D ∈ (𝕊).fins Ko, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D :=
      fun D h => hfin D (by rw [hfins]; exact h)
    have he : e = (cancelK K₀ Ko).plug (cfinE (cancelVal e')
        (Ki.plug (raiseE (.val (cancelVal err))))) := he₀ _ rfl
    rcases q with _ | ⟨⟨ev₁, c₁⟩, q₁⟩
    · exact ⟨[], FireExt.nil _, .nil, .stop⟩
    obtain ⟨hst₁, hq₁⟩ := rpath_cons_inv hq
    have hst₁' := hst₁
    change (𝕊).RStep R ((μ, e), s) ev₁ c₁ at hst₁'
    rw [he] at hst₁'
    obtain ⟨rfl, rfl⟩ := rstep_cfcancel_inv (J := J) hKi hst₁'
    obtain ⟨q'', hl'', hpath'', htr''⟩ := ih q₁ (by simp at hlen; omega) _ Ko (e'.or err)
      (rreach_tail hreach hst₁) rfl hCo.1 hH'.2 hNo.1 (errNamed_or he'N herr) hfino hq₁
    refine ⟨q'', hl''.cons _, .cons hst₁ hpath'', ?_⟩
    rw [keptErrOf_or he'N] at htr''
    exact A.EffectSystem.CancelTrace.pend hst₁ htr''

/-! ### S5 at our instance -/

/-- Steps that keep the store reach, under every runner, at the runner's state. -/
theorem rreach_of_pureSteps {R : (𝕊).Runner} {c₀ : (𝕊).RConf R} {d d' : (𝕊).Conf}
    (h : (𝕊).PureSteps d d') {s : R.St} (h₀ : (𝕊).RReach R c₀ (d, s)) : (𝕊).RReach R c₀ (d', s) := by
  induction h with
  | refl => exact h₀
  | tail _ hst ih =>
      obtain ⟨ev, hst, -⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨ev, .mach hst⟩

/-- Steps of the machine reach, under every runner, at the runner's state. -/
theorem rreach_reach_tail {R : (𝕊).Runner} {c₀ : (𝕊).RConf R} {d d' : (𝕊).Conf}
    (h : (𝕊).Reach d d') {s : R.St} (h₀ : (𝕊).RReach R c₀ (d, s)) : (𝕊).RReach R c₀ (d', s) := by
  induction h with
  | refl => exact h₀
  | tail _ hst ih =>
      obtain ⟨ev, hst⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨ev, .mach hst⟩

/-- **Every cancelled continuation's region holds kept errors the labels read**: at a configuration
a typed program reaches that cancels `capture l H K`, or an affine continuation at its cell, every
running finaliser's `cfin` frame of `K` holds a kept error that is none or a raise of a label's
name.  A `cfin` frame keeps what a finaliser raised (`[cfin-raise]`) or what a cancel passing it
kept (`[cfin-cancel]`), so this is a whole-run fact about the names finalisers raise.  The cancel
bridge's added hypothesis (`noIntercept_of_core`): the cancel's traces read a kept error at the
labels, and an error of a name no label has would be read as none. -/
def CancelsNamed (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    ∀ (c₀ : (ourInst (ℍ := ℍ) RF Ξ J).RConf R) (K₀ : Kont) l H (K : Kont),
      (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) c₀ →
      (c₀.1.2 = K₀.plug ((ourInst (ℍ := ℍ) RF Ξ J).cancel ((ourInst (ℍ := ℍ) RF Ξ J).capture l H K)) ∨
        ∃ ℓ, c₀.1.2 = K₀.plug ((ourInst (ℍ := ℍ) RF Ξ J).cancel
          ((ourInst (ℍ := ℍ) RF Ξ J).captureAt .affine l H K ℓ))) →
      CfinNamed RF Ξ K

/-- **A cancelled continuation's context holds no `ccatch` and no `cfin` frame**, at a cancel of
`capture l H K`.  Before frame deadness (decision D1 of 2026-10-08) it was the cancel bridge's
hypothesis; the cancel's traces now pass a running finaliser's `cfin` frame (`pend`), and a cancel
nested in a cancel puts one there. -/
def CancelsNoCtl (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    ∀ (c₀ : (ourInst (ℍ := ℍ) RF Ξ J).RConf R) (K₀ : Kont) l H (K : Kont),
      (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) c₀ →
      c₀.1.2 = K₀.plug ((ourInst (ℍ := ℍ) RF Ξ J).cancel ((ourInst (ℍ := ℍ) RF Ξ J).capture l H K)) →
      K.NoCtl

/-- **A cancelled continuation's context holds no handler named `0`**: I3.c's `NoInterception` read
on the captured context.  Not read by the cancel bridge: a cancel runs the dead region `K†`, which
holds no handler. -/
def CancelsNZ (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    ∀ (c₀ : (ourInst (ℍ := ℍ) RF Ξ J).RConf R) (K₀ : Kont) l H (K : Kont),
      (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) c₀ →
      c₀.1.2 = K₀.plug ((ourInst (ℍ := ℍ) RF Ξ J).cancel ((ourInst (ℍ := ℍ) RF Ξ J).capture l H K)) →
      K.HasHnd 0 = false

/-- **S5's unwind at our instance** (`unwind_pfx`), given what typing gives about a fired finaliser
that meets the no-interception condition: from every finite memory it runs to `()`. -/
theorem unwindOrder_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) :
    (𝕊).UnwindOrder (𝕊).noFinRaise := by
  intro R hR e ε A _ he c K₀ K m j w q hreach hK hc hm hfin hq
  obtain ⟨q', -, hpath, htr⟩ := unwind_pfx hL hnz hR he (q.length + 1) q (Nat.lt_succ_self _) c
    K₀ K m j w hreach hK hc hm (fun D hD => hF D (hfin D hD)) hq
  exact ⟨q', hpath, htr⟩

/-- **The handler of a cancelled continuation is a value**, at a configuration a typed program
reaches: otherwise the cancel is stuck at `() (inj₂ ())`, against `LiveOK`. -/
theorem hnd_val_of_cancel (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c₀ : Heap × Expr} (hlive : (𝕊).Live c₀)
    {K₀ : Kont} {l : (RF.alg Ξ).Lab} {H : OVal × List OVal} {K : Kont}
    (h₀ : c₀.2 = K₀.plug ((𝕊).cancel ((𝕊).capture l H K)) ∨
      ∃ ℓ, c₀.2 = K₀.plug ((𝕊).cancel ((𝕊).captureAt .affine l H K ℓ))) :
    IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val)) := by
  have hgo := (hL c₀ hlive).2
  obtain ⟨μ₀, e₀⟩ := c₀
  by_contra hnv
  have h₀' : e₀ = Kont.plug K₀ (.app .unit (Val.inj₂ Val.unit).1) := by
    rcases h₀ with h₀ | ⟨ℓ, h₀⟩
    · change e₀ = Kont.plug K₀ (cancelE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
        (H.2.map Subtype.val) K)) at h₀
      rw [captureE_of_not_val K hnv] at h₀
      exact h₀
    · change e₀ = Kont.plug K₀ (cancelE (captureAtE true ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l))
        H.1.1 (H.2.map Subtype.val) K)) at h₀
      have hc : captureAtE true ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
          (H.2.map Subtype.val) K = .unit := by
        unfold captureAtE; rw [dif_neg hnv]
      rw [hc] at h₀
      exact h₀
  rw [h₀'] at hgo
  exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) K₀ μ₀
    (plug_unit_app_ne_drive K₀ _) hgo

/-- **S5's no-interception at our instance** (`cancel_pfx`), given what typing gives about a fired
finaliser that meets the no-interception condition, and that a cancelled continuation's running
finalisers hold kept errors the labels read (`CancelsNamed`).  A cancel of `capture l H K`, or of an
affine continuation at its cell, reaches `cancelOf l H K`; there the region is `K†`, which holds no
handler and no `ccatch` frame (`hasHnd_dead`, `noCC_dead`) and meets what `K` meets (`kActs_dead`,
`fins_dead`). -/
theorem noIntercept_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D)
    (hS : CancelsNamed (ℍ := ℍ) RF Ξ J) :
    (𝕊).NoIntercept (𝕊).noFinRaise := by
  intro R hR e ε A hA he c₀ c K₀ l H K q hreach ⟨hst, hs, hc⟩ hfin hq
  have h₀ : c₀.1.2 = K₀.plug ((𝕊).cancel ((𝕊).capture l H K)) ∨
      ∃ ℓ, c₀.1.2 = K₀.plug ((𝕊).cancel ((𝕊).captureAt .affine l H K ℓ)) := by
    rcases hst with ⟨h, -⟩ | ⟨ℓ, h, -⟩
    · exact .inl h
    · exact .inr ⟨ℓ, h⟩
  have hNK := hS R hR e ε A hA he c₀ K₀ l H K hreach h₀
  have hreachc : (𝕊).RReach R ((𝕊).rinit R e) c := by
    obtain ⟨d, s⟩ := c
    change s = c₀.2 at hs
    subst hs
    rcases hst with ⟨-, hps⟩ | ⟨ℓ, -, hrch⟩
    · exact rreach_of_pureSteps hps hreach
    · exact rreach_reach_tail hrch hreach
  have hlive : (𝕊).Live c₀.1 := ⟨e, _, R, c₀.2, hR, he, hreach⟩
  have hv := hnd_val_of_cancel hL hlive h₀
  obtain ⟨⟨μc, ec⟩, sc⟩ := c
  change ec = Kont.plug K₀ (cancelOfE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
    (H.2.map Subtype.val) K) at hc
  have hterm : ((μc, ec), sc).1.2 =
      (cancelK K₀ K.dead).plug (raiseE (.val (cancelVal none))) := by
    show ec = _
    rw [hc, cancelOfE_of_val K hv]
    exact (cancelK_plug K₀ K.dead _).symm
  have hfK : (𝕊).fins K.dead = (𝕊).fins K :=
    congrArg (List.map finE) (fins_dead K)
  obtain ⟨q', -, hpath, htr⟩ := cancel_pfx hL hR he (q.length + 1) q
    (Nat.lt_succ_self _) ((μc, ec), sc) K.dead none hreachc hterm (noCC_dead K) (hasHnd_dead 0 K)
    (cfinNamed_dead hNK) trivial (fun D hD => hF D (hfin D (hfK ▸ hD))) hq
  rw [kActs_dead K] at htr
  exact ⟨q', hpath, htr⟩

/-- **S5 at our instance.** -/
theorem cancellation_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D)
    (hS : CancelsNamed (ℍ := ℍ) RF Ξ J) :
    (𝕊).Cancellation (𝕊).noFinRaise :=
  ⟨noIntercept_of_core hL hF hS, unwindOrder_of_core hL hnz hF⟩

/-! ### A path that stops right after a fire step -/

/-- A context holding a handler frame of `n` has a handler of `n`. -/
theorem hasHnd_handleK_comp (K₂ K₁ : Kont) (n : UInt32) (qs r : Expr) (cs : List Expr) :
    (K₂.comp ((handleK n qs r cs).comp K₁)).HasHnd n = true := by
  rw [hasHnd_comp, hasHnd_comp]
  simp [handleK, hndValE, Kont.HasHnd]

/-- **A path that stops right after a fire step follows no unwind trace**, at a context that is one
finaliser frame, when the configuration the fire step reaches holds the fired finaliser at no
evaluation position.  `UnwindTrace.fire` reads the fire step's administrative steps whole
(`PurePath c₁ q₀ c₂`, the finaliser at `c₂`), and a trace stops only at `[]`. -/
theorem not_unwindTrace_one {R : (𝕊).Runner} {FR : (RF.alg Ξ).Lab → Prop} {K₀ : (𝕊).Kont}
    {c c₁ : (𝕊).RConf R} {N D : Expr} (hc₁ : ∀ Kf : Kont, c₁.1.2 ≠ Kf.plug D) :
    ¬ (𝕊).UnwindTrace R FR K₀ c (thenK N D) [(.fire D, c₁)] := by
  intro h
  generalize hK : thenK N D = K at h
  generalize hq : [((.fire D : (𝕊).Event), c₁)] = q at h
  cases h with
  | stop => exact List.cons_ne_nil _ _ hq
  | out _ _ hU =>
      subst hK
      exact thenK_not_noUnwind N D hU
  | @caught _ K' K₁ K₂ H m _ _ _ hK' _ _ _ =>
      subst hK'
      have h₁ : Kont.HasHnd (RF.name Ξ m) (thenK N D) = false := rfl
      rw [hK] at h₁
      have h₂ := hasHnd_handleK_comp K₂ K₁ (RF.name Ξ m) (qsOf Ξ (RF.name Ξ m)) H.1.1
        (H.2.map Subtype.val)
      exact absurd (h₂.symm.trans h₁) (by decide)
  | @fire _ c₁' c₂ K' K₁ K₂ N' D' Kp m j w q₀ q' _ _ _ _ _ hpp _ _ hterm₂ _ =>
      obtain ⟨h₁, hnil⟩ := List.cons.inj hq
      obtain ⟨hD, rfl⟩ := Prod.mk.inj h₁
      injection hD with hD
      subst hD
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil.symm
      cases hpp
      exact hc₁ _ hterm₂

end Targets.Inst

end
