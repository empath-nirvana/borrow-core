import Targets.Instance.CellRuns
import Targets.A.CancelPrefix

/-!
# The Instance — S5's traces at our machine

A's S5 (`Cancellation`, `Targets/A/Soundness.lean`) reads every run from the start of a cancel or of
an unwind against a trace: each finaliser fires, runs alone, and hands the cancel or the raise on.
This module builds those traces at our machine, from one fact about each fired finaliser: from the
memory it fires at, every run of it continues to `()` (`FinOK`).  Typing gives that fact
(`Targets/I/S5J1.lean`: a finaliser that meets S5's no-interception condition at option A is a
closed program at the pure row, and runs to `()` from every finite memory).

* **A step of `Kf[t]`, `t` stepping, is `t`'s step under `Kf`**, with its label (`ostep_unplug`,
  `rstep_unplug`).  So while the fired finaliser has a step, the run is the finaliser's run alone.
* **The unwind** (`unwind_pfx`): at a raise under a context of A's shape (`Std`) whose finalisers
  are `FinOK` at every finite memory, the innermost finaliser frame fires (`[finalise]`, labelled
  `fire D`), `D ()` reduces to `D` (a β-step), `D` runs alone to `()`, `(); raise p` hands the raise
  on (`[1↦]`), and the unwind goes on through the rest of the context.
* **The cancel** (`cancel_pfx`): at `ccatch (hnd H K[raise (0, (0, (N, none)))])`, `K` free of
  `ccatch`, `cfin` and handlers named `0`, the innermost finaliser frame fires
  (`[finalise-cancel]`), its finaliser runs alone under `cfin` to `()`, `[cfin-ret]` (labelled
  `finEnd none`) hands the cancel on, and at the end `[cancel]` answers `()`.

**What is proved is S5's traces up to one step.**  A's trace constructors read the configuration
after a fire step's administrative steps (`PurePath c₁ q₀ c₂`, then the finaliser at `c₂`), and a
trace stops only at `[]`, so a path that stops between the fire step and the finaliser's start
follows no trace.  At our machine the fire step leaves `D ()`, one β-step from `D`.  Every path
here is a trace once at most one step of the run is appended: the β-step, when the path stops right
after a fire.  `Targets/I/S5J1.lean` shows the step is needed: S5 as written fails at `J₁`.
`[Core σ=[]]`
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
      (𝕊).RPath R c q → ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ c K₂ (q ++ q')) :
    ∀ (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n → ∀ (c : (𝕊).RConf R) (t : Expr),
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = ((K₀.comp K₂).comp (.seq .hole (raiseE (.val p)))).plug t →
      Steps (ℍ := ℍ) μf D c.1.1 t → (𝕊).RPath R c q →
      ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).PendTrace R (𝕊).noFinRaise K₀ K₂ (.seq .hole (raiseE (.val p))) (lab, j, w) c
          (q ++ q') := by
  intro q
  induction q with
  | nil =>
      intro _ c t _ _ _ _
      exact ⟨[], by simp, .nil, .running .nil⟩
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
        refine ⟨q'', hl'', .cons hst hpath'', ?_⟩
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
        exact ⟨q'', hl'', .cons hst hpath'', pend_cons rfl rfl hst hst' htr''⟩

/-- **The unwind's traces, up to one step of the run.**  At a configuration a typed program reaches,
a raise pending under a context of A's unwinding shape (`Std`) that holds no handler of its label,
whose finalisers run to `()` from every finite memory: every path is an unwind trace once at most
one step is appended.  The step is the β-step that starts a fired finaliser, needed when the path
stops right after the fire step. -/
theorem unwind_pfx (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0) {R : (𝕊).Runner}
    (hR : R.Respects) {P : Expr} {C : OCTy} (hP : (𝕊).der [] P C) :
    ∀ (n : ℕ) (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n →
    ∀ (c : (𝕊).RConf R) (K₀ : Kont) (K : (𝕊).Kont) (lab : (RF.alg Ξ).Lab) (j : ℕ) (w : OVal),
      (𝕊).RReach R ((𝕊).rinit R P) c → (𝕊).Std K →
      c.1.2 = K₀.plug (Kont.plug K ((𝕊).raise lab j w)) → Kont.HasHnd (RF.name Ξ lab) K = false →
      (∀ D ∈ (𝕊).fins K, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) → (𝕊).RPath R c q →
      ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).UnwindTrace R (𝕊).noFinRaise K₀ c K (q ++ q') := by
  intro n
  induction n with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ n ih =>
    intro q hlen c K₀ K lab j w hreach hstd hterm hhnd hfin hq
    rcases std_split hstd with hU | ⟨K₁, K₂, N, D, rfl, hK₁, hstd₂⟩
    · refine ⟨[], by simp, by simpa using hq, ?_⟩
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
        (𝕊).RPath R c' q' → ∃ q'', q''.length ≤ 1 ∧ (𝕊).RPath R c' (q' ++ q'') ∧
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
    | nil => exact ⟨[], by simp, .nil, .stop⟩
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
    · refine ⟨[(.tau, c₂)], by simp, .cons hst₁ (.cons hβ .nil), ?_⟩
      exact hfire [] (.running .nil)
    · obtain ⟨hst₂, hq₂⟩ := rpath_cons_inv hq₁
      obtain ⟨rfl, rfl⟩ := hβinv hst₂
      obtain ⟨q'', hl'', hpath'', hpend''⟩ :=
        pend_pfx (R := R) (P := P) (K₀ := K₀) (K₂ := K₂) (lab := lab) (j := j) (w := w) hr
          (hD μ hfd) n ihU q₂ (by simp at hlen; omega) c₂ D hreach₂ rfl (.refl _ _) hq₂
      exact ⟨q'', hl'', .cons hst₁ (.cons hst₂ hpath''), hfire _ hpend''⟩

/-! ### The steps of a cancel -/

/-- The handler frame of a cancel run's dying handler. -/
abbrev hndK (Hv : Val) : Kont := .appR (.app (.prim .hnd) Hv.1) .hole

/-- The cancel-mode finaliser frame. -/
abbrev cfinK (st : Val) : Kont := .appR (.app (.prim .cfin) st.1) .hole

/-- The context around a cancel's raise: the canceller's, `ccatch`, the dying handler, and the
region's frames still to unwind. -/
abbrev cancelK (K₀ : Kont) (Hv : Val) (Kc : Kont) : Kont :=
  K₀.comp (ccatchK ((hndK Hv).comp Kc))

theorem cancelK_plug (K₀ : Kont) (Hv : Val) (Kc : Kont) (x : Expr) :
    (cancelK K₀ Hv Kc).plug x = K₀.plug (ccatchE (hndE Hv (Kc.plug x))) := by
  rw [Kont.plug_comp]; rfl

/-- A step of our machine is a machine step, or the driver's at a whole term `drive v`. -/
theorem ostep_step1_or_drive {c c' : Heap × Expr} {ev : A.Ev (RF.alg Ξ).Lab OVal Expr}
    (h : OStep (ℍ := ℍ) RF Ξ c ev c') :
    (∃ μ' t', Step1 (ℍ := ℍ) c.1 c.2 μ' t') ∨ ∃ v : Val, c.2 = driveE (.val v) := by
  cases h with
  | mach hh => exact .inl ⟨_, _, ⟨_, _, _, rfl, rfl, hh⟩⟩
  | again => exact .inr ⟨_, rfl⟩
  | fin => exact .inr ⟨_, rfl⟩

/-- **At a configuration a typed program reaches, a raise stopped by a finaliser frame `ubind x`
holds a pair of values there**: otherwise the configuration would not go on (`LiveOK`), since the
raise is caught (no answer of the runner), it is no value, and only `[finalise]` or
`[finalise-cancel]` steps at it (`step1_raise`, `head_ubind_raise`). -/
theorem ubind_pair_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr} (hc : (𝕊).Live c)
    {K Ki : Kont} {x : Expr} {p : Val} {n : UInt32} (hp : payloadName p = some n)
    (hKi : Ki.Catches n = false)
    (he : c.2 = K.plug (.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p))))) :
    ∃ N D : Val, x = (Val.pair N D).1 := by
  have hctx : K.plug (.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p)))) =
      (K.comp (.appR (.app (.prim .ubind) x) Ki)).plug (raiseE (.val p)) := by
    rw [Kont.plug_comp]; rfl
  rw [hctx] at he
  have hIC : InnerCatch n (K.comp (.appR (.app (.prim .ubind) x) Ki)) K (.app (.prim .ubind) x) Ki :=
    ⟨rfl, hKi, by simp [FrameCatches, Kont.Catches]⟩
  rcases (hL c hc).2 with ⟨v, hv⟩ | ⟨ev, c', h⟩ | ⟨r, K', p', n', hK', hp', hfree⟩
  · exfalso
    have h1 : IsVal ((K.comp (.appR (.app (.prim .ubind) x) Ki)).plug (raiseE (.val p))) := by
      rw [← he, hv]; exact v.2
    exact not_isVal_plug_raise _ p h1
  · rcases ostep_step1_or_drive h with ⟨μ', t', hs⟩ | ⟨v, hv⟩
    · rw [he] at hs
      obtain ⟨Ko', f', Ki', a', hIC', hhead, -⟩ := step1_raise hp hs
      obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
      obtain ⟨-, N, D, hx, -⟩ := head_ubind_raise hhead
      exact ⟨N, D, hx⟩
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
    have hc' := catches_of_innerCatch (Ko := K) (Ki := Ki) (n := n) (f := .app (.prim .ubind) x)
      (by simp [FrameCatches, Kont.Catches])
    simp only [OpFree, if_true] at hfree
    rw [hfree] at hc'
    cases hc'

/-- `[finalise-cancel]` at a pair of values, labelled `fire (finE D)`, the only step there. -/
theorem rstep_fireC_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K Ki : Kont} {N D : Val}
    {Ns : List UInt32} {err : Option Val} (hKi : Ki.Catches 0 = false) {ev : (𝕊).Event}
    {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (cancelVal Ns err)))))), s)
      ev c') :
    ev = .fire (finE D.1) ∧
      c' = ((μ, K.plug (cfinE (cancelVal Ns err) (.app (.val D) (.val Val.unit)))), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) (Head.ufinC (ℍ := ℍ) μ N D Ns err Ki hKi) rfl h
  exact ⟨labelOf_fire (not_isVal_plug_raise Ki _), rfl⟩

/-- `[cfin-ret]`, labelled `finEnd none`, the only step there. -/
theorem rstep_cfret_inv {R : (𝕊).Runner} {s : R.St} {μ : Heap} {K : Kont} {Ns : List UInt32}
    {err : Option Val} {w : Val} {ev : (𝕊).Event} {c' : (𝕊).RConf R}
    (h : (𝕊).RStep R ((μ, K.plug (cfinE (cancelVal Ns err) (.val w))), s) ev c') :
    ev = .finEnd none ∧ c' = ((μ, K.plug (raiseE (.val (cancelVal Ns err)))), s) := by
  obtain ⟨rfl, rfl⟩ := rstep_det (J := J) (Head.cfret (ℍ := ℍ) μ Ns err w) rfl h
  exact ⟨labelOf_cfret _ _, rfl⟩

theorem rstep_cfret {R : (𝕊).Runner} (s : R.St) (μ : Heap) (K : Kont) (Ns : List UInt32)
    (err : Option Val) (w : Val) :
    (𝕊).RStep R ((μ, K.plug (cfinE (cancelVal Ns err) (.val w))), s) (.finEnd none)
      ((μ, K.plug (raiseE (.val (cancelVal Ns err)))), s) := by
  have ho := OStep.mach (RF := RF) (Ξ := Ξ) (K := K) (Head.cfret (ℍ := ℍ) μ Ns err w)
  rw [labelOf_cfret] at ho
  exact .mach ho

/-! ### The cancel's traces -/

/-- A handler frame stops a raise of `n` exactly when it is a handler of `n`. -/
theorem catches_hndK (Hv : Val) (n : UInt32) : (hndK Hv).Catches n = (hndK Hv).HasHnd n := by
  simp only [Kont.Catches, Kont.HasHnd, Bool.or_false]
  split <;> simp_all

/-- `finE` of a term that is no λ: the term applied to `()`. -/
theorem finE_of_not_lam {e : Expr} (h : ∀ b, e ≠ .lam b) : finE e = .app e (.val Val.unit) := by
  unfold finE
  split
  · rename_i b; exact absurd rfl (h b)
  · rfl

/-- A step of the finaliser, read alone, goes in front of the cancel trace of what follows. -/
theorem fin_cons {R : (𝕊).Runner} {FR N : (RF.alg Ξ).Lab → Prop} {K₀ Kf : (𝕊).Kont}
    {c c' : (𝕊).RConf R} {t t' : Expr} {ev : (𝕊).Event} {fs : List Expr} {err : (𝕊).Err}
    (h₁ : c.1.2 = Kf.plug t) (h₂ : c'.1.2 = Kf.plug t') (hs : (𝕊).RStep R c ev c')
    (hs' : (𝕊).RStep R ((c.1.1, t), c.2) ev ((c'.1.1, t'), c'.2))
    {q : List ((𝕊).Event × (𝕊).RConf R)} (h : (𝕊).FinTrace R FR N K₀ Kf c' fs err q) :
    (𝕊).FinTrace R FR N K₀ Kf c fs err ((ev, c') :: q) := by
  cases h with
  | running ha => exact .running (.cons h₁ h₂ hs hs' ha)
  | ended ha hend hFE hst hct =>
      have := A.EffectSystem.FinTrace.ended (.cons h₁ h₂ hs hs' ha) hend hFE hst hct
      simpa only [List.cons_append] using this

/-- **A cancel while a fired finaliser runs alone under `cfin`**, given the cancel through the rest
of the region on shorter paths.  The finaliser runs to `()` from the memory it fired at (`FinOK`):
while it has a step, the run is its run alone; at `()`, `[cfin-ret]` (labelled `finEnd none`) hands
the cancel on, with no error kept. -/
theorem fin_pfx {R : (𝕊).Runner} {P : Expr} {N : (RF.alg Ξ).Lab → Prop} {K₀ : Kont} {Hv : Val}
    {Ns : List UInt32} {Ko : Kont} {μf : Heap} {D : Expr} (hD : FinOK (ℍ := ℍ) μf D) (n : ℕ)
    (ihC : ∀ q : List ((𝕊).Event × (𝕊).RConf R), q.length < n → ∀ c : (𝕊).RConf R,
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = (cancelK K₀ Hv Ko).plug (raiseE (.val (cancelVal Ns none))) → (𝕊).RPath R c q →
      ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).CancelTrace R (𝕊).noFinRaise N K₀ c ((𝕊).fins Ko) none (q ++ q')) :
    ∀ (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n → ∀ (c : (𝕊).RConf R) (t : Expr),
      (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug t →
      Steps (ℍ := ℍ) μf D c.1.1 t → (𝕊).RPath R c q →
      ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).FinTrace R (𝕊).noFinRaise N K₀ ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none)))
          c ((𝕊).fins Ko) none (q ++ q') := by
  intro q
  induction q with
  | nil =>
      intro _ c t _ _ _ _
      exact ⟨[], by simp, .nil, .running .nil⟩
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
        have he : ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug Val.unit.1 =
            (cancelK K₀ Hv Ko).plug (cfinE (cancelVal Ns none) (.val Val.unit)) :=
          Kont.plug_comp _ _ _
        have hst' := hst
        rw [he] at hst'
        obtain ⟨rfl, rfl⟩ := rstep_cfret_inv (J := J) hst'
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ihC q₁ (by simp at hlen; omega) _
          (rreach_tail hreach hst) rfl hq₁
        refine ⟨q'', hl'', .cons hst hpath'', ?_⟩
        have hend : (𝕊).Ended ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none)))
            ((μc, ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug Val.unit.1), sc) none :=
          ⟨(𝕊).unitV, rfl⟩
        have := A.EffectSystem.FinTrace.ended (S := 𝕊) (R := R) (FR := (𝕊).noFinRaise) (N := N)
          (K₀ := K₀) (fs := (𝕊).fins Ko) (err := none) (r := none) .nil hend trivial hst htr''
        exact this
      · -- the finaliser steps: the run's step is its step alone
        obtain ⟨t', hc', hst', hs'⟩ := rstep_unplug ht hst
        obtain ⟨⟨μ', e'⟩, s'⟩ := c'
        simp only at hc'
        obtain ⟨⟨-, rfl⟩, rfl⟩ := hc'
        obtain ⟨q'', hl'', hpath'', htr''⟩ := ih (by simp at hlen; omega) _ t'
          (rreach_tail hreach hst) rfl (hrun.trans (Steps.one hs')) hq₁
        exact ⟨q'', hl'', .cons hst hpath'', fin_cons rfl rfl hst hst' htr''⟩

/-- **The cancel's traces, up to one step of the run.**  At a configuration a typed program reaches,
a cancel raised under the dying handler `Hv` and the region's frames `Kc` still to unwind, inside
`ccatch`: when `Kc` holds no `ccatch` and no `cfin` frame, no handler named `0` is in `hnd Hv ∘ Kc`,
and `Kc`'s finalisers run to `()` from every finite memory, every path is a cancel trace, with
nothing kept, once at most one step is appended (the β-step that starts a fired finaliser that is
a λ). -/
theorem cancel_pfx (hL : LiveOK (ℍ := ℍ) RF Ξ J) {R : (𝕊).Runner} (hR : R.Respects) {P : Expr}
    {C : OCTy} (hP : (𝕊).der [] P C) {N : (RF.alg Ξ).Lab → Prop} {K₀ : Kont} {Hv : Val}
    {Ns : List UInt32} :
    ∀ (n : ℕ) (q : List ((𝕊).Event × (𝕊).RConf R)), q.length < n →
    ∀ (c : (𝕊).RConf R) (Kc : Kont), (𝕊).RReach R ((𝕊).rinit R P) c →
      c.1.2 = (cancelK K₀ Hv Kc).plug (raiseE (.val (cancelVal Ns none))) → Kc.NoCtl →
      ((hndK Hv).comp Kc).HasHnd 0 = false →
      (∀ D ∈ (𝕊).fins Kc, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) → (𝕊).RPath R c q →
      ∃ q', q'.length ≤ 1 ∧ (𝕊).RPath R c (q ++ q') ∧
        (𝕊).CancelTrace R (𝕊).noFinRaise N K₀ c ((𝕊).fins Kc) none (q ++ q') := by
  intro n
  induction n with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ n ih =>
  intro q hlen c Kc hreach hterm hC hH hfin hq
  have hfd : FinDom c.1.1 := finDom_reach hreach
  have hlive : (𝕊).Live c.1 := ⟨P, C, R, c.2, hR, hP, hreach⟩
  obtain ⟨⟨μ, e⟩, s⟩ := c
  change e = _ at hterm
  change FinDom μ at hfd
  have hHv : (hndK Hv).HasHnd 0 = false := by
    rw [hasHnd_comp, Bool.or_eq_false_iff] at hH; exact hH.1
  by_cases hA : Kc.Catches 0 = true
  swap
  · -- no finaliser frame is left: `[cancel]` answers the canceller
    simp only [Bool.not_eq_true] at hA
    have hK0 : ((hndK Hv).comp Kc).Catches 0 = false := by
      rw [catches_comp, catches_hndK, hHv, hA]; rfl
    have hfins : (𝕊).fins Kc = [] := by
      change List.map finE Kc.fins = []
      rw [fins_nil_of_catches Kc hA]; rfl
    rw [hfins]
    have he : e = K₀.plug (ccatchE (((hndK Hv).comp Kc).plug (raiseE (.val (cancelVal Ns none))))) := by
      rw [hterm, Kont.plug_comp]; rfl
    rcases q with _ | ⟨⟨ev₁, c₁⟩, q₁⟩
    · exact ⟨[], by simp, .nil, .stop⟩
    obtain ⟨hst₁, -⟩ := rpath_cons_inv hq
    have hst₁' := hst₁
    change (𝕊).RStep R ((μ, e), s) ev₁ c₁ at hst₁'
    rw [he] at hst₁'
    obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J)
      (Head.cancel (ℍ := ℍ) μ Ns ((hndK Hv).comp Kc) hK0) rfl rfl hst₁'
    refine ⟨[], by simp, by simpa using hq, ?_⟩
    rw [List.append_nil]
    have hans : (𝕊).Answered K₀ none (K₀.plug (.val Val.unit)) := rfl
    exact A.EffectSystem.CancelTrace.answer hst₁ hans
  -- the innermost finaliser frame fires: `[finalise-cancel]`
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists 0 Kc hA
  have hH' : (Kont.appR f Ki).HasHnd 0 = false ∧ ((hndK Hv).comp Ko).HasHnd 0 = false := by
    have h := hH
    rw [hasHnd_comp, hasHnd_comp, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h
    refine ⟨h.2.2, ?_⟩
    rw [hasHnd_comp, Bool.or_eq_false_iff]; exact ⟨h.1, h.2.1⟩
  have hCo := (noCtl_comp _ _).1 hC
  obtain ⟨x, rfl⟩ := frame_ubind_of_cancel hf hH'.1 hCo.2
  have he₀ : e = (cancelK K₀ Hv Ko).plug (.app (.app (.prim .ubind) x)
      (Ki.plug (raiseE (.val (cancelVal Ns none))))) := by
    rw [hterm]
    change (K₀.comp (ccatchK ((hndK Hv).comp (Ko.comp (.appR _ Ki))))).plug _ = _
    rw [Kont.plug_comp, Kont.plug_comp]
    change K₀.plug (.app (.prim .ccatch) (((hndK Hv).comp (Ko.comp (.appR _ Ki))).plug _)) =
      K₀.plug (.app (.prim .ccatch) (((hndK Hv).comp Ko).plug _))
    rw [Kont.plug_comp, Kont.plug_comp, Kont.plug_comp]
    rfl
  obtain ⟨N', D', rfl⟩ := ubind_pair_live (c := (μ, e)) hL hlive (payloadName_cancelVal Ns none)
    hKi he₀
  have hfins : (𝕊).fins (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N' D').1) Ki)) =
      finE D'.1 :: (𝕊).fins Ko := by
    change List.map finE (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N' D').1) Ki)).fins = _
    rw [fins_innerUbind hKi]; rfl
  rw [hfins]
  have hD : FinOK (ℍ := ℍ) μ (finE D'.1) :=
    hfin _ (by rw [hfins]; exact List.mem_cons_self) μ hfd
  have hfino : ∀ D ∈ (𝕊).fins Ko, ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D :=
    fun D h => hfin D (by rw [hfins]; exact List.mem_cons_of_mem _ h)
  have ihC : ∀ q' : List ((𝕊).Event × (𝕊).RConf R), q'.length < n → ∀ c' : (𝕊).RConf R,
      (𝕊).RReach R ((𝕊).rinit R P) c' →
      c'.1.2 = (cancelK K₀ Hv Ko).plug (raiseE (.val (cancelVal Ns none))) → (𝕊).RPath R c' q' →
      ∃ q'', q''.length ≤ 1 ∧ (𝕊).RPath R c' (q' ++ q'') ∧
        (𝕊).CancelTrace R (𝕊).noFinRaise N K₀ c' ((𝕊).fins Ko) none (q' ++ q'') :=
    fun q' hq' c' hr' ht' hp' => ih q' hq' c' Ko hr' ht' hCo.1 hH'.2 hfino hp'
  have he : e = (cancelK K₀ Hv Ko).plug (ubindE (Val.pair N' D')
      (Ki.plug (raiseE (.val (cancelVal Ns none))))) := he₀
  rcases q with _ | ⟨⟨ev₁, c₁⟩, q₁⟩
  · exact ⟨[], by simp, .nil, .stop⟩
  obtain ⟨hst₁, hq₁⟩ := rpath_cons_inv hq
  have hst₁' := hst₁
  change (𝕊).RStep R ((μ, e), s) ev₁ c₁ at hst₁'
  rw [he] at hst₁'
  obtain ⟨rfl, rfl⟩ := rstep_fireC_inv (J := J) hKi hst₁'
  have hreach₁ := rreach_tail hreach hst₁
  -- the finaliser's start: `D ()`, one β-step from `D`'s body when `D` is a λ
  have hc₁ : (cancelK K₀ Hv Ko).plug (cfinE (cancelVal Ns none) (.app (.val D') (.val Val.unit))) =
      ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug (.app (.val D') (.val Val.unit)) :=
    (Kont.plug_comp (cancelK K₀ Hv Ko) (cfinK (cancelVal Ns none)) _).symm
  by_cases hlam : ∃ b, D'.1 = .lam b
  · obtain ⟨b, hb⟩ := hlam
    have hDv : D' = Val.lam b := Subtype.ext hb
    subst hDv
    let c₂ : (𝕊).RConf R :=
      ((μ, ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug (finE (Val.lam b).1)), s)
    have hβo : OStep (ℍ := ℍ) RF Ξ
        (μ, (cancelK K₀ Hv Ko).plug (cfinE (cancelVal Ns none) (.app (.val (Val.lam b)) (.val Val.unit))))
        .tau c₂.1 := by
      have h := ostep_quiet (RF := RF) (Ξ := Ξ) ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none)))
        (Head.beta (ℍ := ℍ) μ b Val.unit) rfl
      rw [← hc₁] at h
      exact h
    have hpp : (𝕊).PurePath R
        ((μ, (cancelK K₀ Hv Ko).plug (cfinE (cancelVal Ns none) (.app (.val (Val.lam b)) (.val Val.unit)))), s)
        [(.tau, c₂)] c₂ := .cons ⟨hβo, rfl⟩ rfl .nil
    have hfire : ∀ q : List ((𝕊).Event × (𝕊).RConf R),
        (𝕊).FinTrace R (𝕊).noFinRaise N K₀ ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none)))
          c₂ ((𝕊).fins Ko) none q →
        (𝕊).CancelTrace R (𝕊).noFinRaise N K₀ ((μ, e), s) (finE (Val.lam b).1 :: (𝕊).fins Ko) none
          ((.fire (finE (Val.lam b).1),
            ((μ, (cancelK K₀ Hv Ko).plug
              (cfinE (cancelVal Ns none) (.app (.val (Val.lam b)) (.val Val.unit)))), s)) ::
            [(.tau, c₂)] ++ q) := fun q hft =>
      A.EffectSystem.CancelTrace.fire hst₁ hpp rfl hft
    rcases q₁ with _ | ⟨⟨ev₂, c₂'⟩, q₂⟩
    · exact ⟨[(.tau, c₂)], by simp, .cons hst₁ (.cons (.mach hβo) .nil), hfire [] (.running .nil)⟩
    obtain ⟨hst₂, hq₂⟩ := rpath_cons_inv hq₁
    have hst₂' := hst₂
    rw [hc₁] at hst₂'
    obtain ⟨rfl, rfl⟩ := rstep_quiet_inv (J := J) (Head.beta (ℍ := ℍ) μ b Val.unit) rfl rfl hst₂'
    obtain ⟨q'', hl'', hpath'', hft''⟩ :=
      fin_pfx (R := R) (P := P) (N := N) (K₀ := K₀) (Hv := Hv) (Ns := Ns) (Ko := Ko) hD n ihC q₂
        (by simp at hlen; omega) c₂ _ (rreach_tail hreach₁ hst₂) rfl (.refl _ _) hq₂
    exact ⟨q'', hl'', .cons hst₁ (.cons hst₂ hpath''), hfire _ hft''⟩
  · -- `D` is no λ: `D ()` is the finaliser's term already
    have hfe : finE D'.1 = .app (.val D') (.val Val.unit) :=
      finE_of_not_lam (fun b h => hlam ⟨b, h⟩)
    have hc₁' : ((μ, (cancelK K₀ Hv Ko).plug (cfinE (cancelVal Ns none) (.app (.val D') (.val Val.unit)))), s).1.2 =
        ((cancelK K₀ Hv Ko).comp (cfinK (cancelVal Ns none))).plug (finE D'.1) := by
      rw [hfe]; exact hc₁
    obtain ⟨q'', hl'', hpath'', hft''⟩ :=
      fin_pfx (R := R) (P := P) (N := N) (K₀ := K₀) (Hv := Hv) (Ns := Ns) (Ko := Ko) hD n ihC q₁
        (by simp at hlen; omega) _ _ hreach₁ hc₁' (.refl _ _) hq₁
    exact ⟨q'', hl'', .cons hst₁ hpath'',
      A.EffectSystem.CancelTrace.fire (q₀ := []) hst₁ .nil hc₁' hft''⟩

/-! ### S5 at our instance, prefix-closed -/

/-- Steps that keep the store reach, under every runner, at the runner's state. -/
theorem rreach_of_pureSteps {R : (𝕊).Runner} {c₀ : (𝕊).RConf R} {d d' : (𝕊).Conf}
    (h : (𝕊).PureSteps d d') {s : R.St} (h₀ : (𝕊).RReach R c₀ (d, s)) : (𝕊).RReach R c₀ (d', s) := by
  induction h with
  | refl => exact h₀
  | tail _ hst ih =>
      obtain ⟨ev, hst, -⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨ev, .mach hst⟩

/-- **Every cancelled continuation was captured in a standard context** (the cancel bridge's added
hypothesis): at a configuration a typed program reaches that cancels `capture l H K`, `K` holds no
`ccatch`, no `cfin` and no handler named `0`.  Source: SPEC §19's "its handlers are dying, so they
catch nothing", read at the capture — no operation is caught across a cancel or a cancel-mode
finaliser — with I3.c's `NoInterception` read on the captured context.  Scope: it speaks of the
context a continuation was captured in, not of the cancel run it starts, so it does not assume the
trace. -/
def CancelsStd (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) RF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) RF Ξ J).der [] e ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
    ∀ (c₀ : (ourInst (ℍ := ℍ) RF Ξ J).RConf R) (K₀ : Kont) l H (K : Kont),
      (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R e) c₀ →
      c₀.1.2 = K₀.plug ((ourInst (ℍ := ℍ) RF Ξ J).cancel ((ourInst (ℍ := ℍ) RF Ξ J).capture l H K)) →
      K.NoCtl ∧ K.HasHnd 0 = false

/-- **S5's unwind at our instance, prefix-closed** (`unwind_pfx`), given what typing gives about a
fired finaliser that meets the no-interception condition: from every finite memory it runs to
`()`. -/
theorem unwindOrderPfx_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D) :
    (𝕊).UnwindOrderPfx (𝕊).noFinRaise := by
  intro R hR e ε A _ he c K₀ K m j w q hreach hK hc hm hfin hq
  obtain ⟨q', -, hpath, htr⟩ := unwind_pfx hL hnz hR he (q.length + 1) q (Nat.lt_succ_self _) c
    K₀ K m j w hreach hK hc hm (fun D hD => hF D (hfin D hD)) hq
  exact ⟨q', hpath, htr⟩

/-- **S5's no-interception at our instance, prefix-closed** (`cancel_pfx`), given what typing gives
about a fired finaliser that meets the no-interception condition, and that a cancelled
continuation was captured in a standard context (`CancelsStd`).  A cancel of `capture l H K` reaches
`cancelOf l H K` by three steps that keep the store; there the dying handler's name is a label's,
not `0`. -/
theorem noInterceptPfx_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D)
    (hS : CancelsStd (ℍ := ℍ) RF Ξ J) :
    (𝕊).NoInterceptPfx (𝕊).noFinRaise := by
  intro R hR e ε A hA he c₀ c K₀ l H K q hreach h₀ hps hs hc hfin hq
  obtain ⟨hNC, hK0⟩ := hS R hR e ε A hA he c₀ K₀ l H K hreach h₀
  have hreachc : (𝕊).RReach R ((𝕊).rinit R e) c := by
    obtain ⟨d, s⟩ := c
    change s = c₀.2 at hs
    subst hs
    exact rreach_of_pureSteps hps hreach
  have hlive : (𝕊).Live c₀.1 := ⟨e, _, R, c₀.2, hR, he, hreach⟩
  have hgo := (hL c₀.1 hlive).2
  obtain ⟨⟨μ₀, e₀⟩, s₀⟩ := c₀
  obtain ⟨⟨μc, ec⟩, sc⟩ := c
  set n := RF.name Ξ l
  set qs := qsOf Ξ n
  change e₀ = Kont.plug K₀ (cancelE (captureE n qs H.1.1 (H.2.map Subtype.val) K)) at h₀
  change ec = Kont.plug K₀ (cancelOfE n qs H.1.1 (H.2.map Subtype.val) K) at hc
  -- the handler is a value: otherwise the cancel's start is stuck at `() (inj₂ ())`
  have hv : IsVal (hndValE n qs H.1.1 (H.2.map Subtype.val)) := by
    by_contra hnv
    rw [captureE_of_not_val K hnv] at h₀
    have h₀' : e₀ = Kont.plug K₀ (.app .unit (Val.inj₂ Val.unit).1) := h₀
    rw [h₀'] at hgo
    exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) K₀ μ₀
      (plug_unit_app_ne_drive K₀ _) hgo
  let Hv : Val := ⟨_, hv⟩
  have hterm : ((μc, ec), sc).1.2 =
      (cancelK K₀ Hv K).plug (raiseE (.val (cancelVal (n :: Kont.hndNames K) none))) := by
    show ec = _
    rw [hc, cancelOfE_of_val K hv]
    exact (cancelK_plug K₀ Hv K _).symm
  have hH : ((hndK Hv).comp K).HasHnd 0 = false := by
    have e₁ := hasHnd_comp 0 (hndK Hv) K
    rw [e₁, hK0, Bool.or_false]
    simp only [Kont.HasHnd, Bool.or_false]
    show (n == 0) = false
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact hnz l
  obtain ⟨q', -, hpath, htr⟩ := cancel_pfx (N := (𝕊).Region l K) hL hR he (q.length + 1) q
    (Nat.lt_succ_self _) ((μc, ec), sc) K hreachc hterm hNC hH (fun D hD => hF D (hfin D hD)) hq
  exact ⟨q', hpath, htr⟩

/-- **S5 at our instance, prefix-closed.** -/
theorem cancellationPfx_of_core (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hF : ∀ D, (𝕊).FinRow (𝕊).noFinRaise D → ∀ μ, FinDom μ → FinOK (ℍ := ℍ) μ D)
    (hS : CancelsStd (ℍ := ℍ) RF Ξ J) :
    (𝕊).CancellationPfx (𝕊).noFinRaise :=
  ⟨noInterceptPfx_of_core hL hnz hF hS, unwindOrderPfx_of_core hL hnz hF⟩

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
