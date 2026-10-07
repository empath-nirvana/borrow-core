import Targets.A.Expressiveness

/-!
# System A — non-vacuity, abstractly (RESTRUCTURE §6.1)

Every (E) property fails at a **trivial** instance, and where a decided feature is genuinely needed
it fails at an instance **without that feature**.  Each lemma here is over every instance, and its
proof uses only A's laws, never an instance's typing rules.

* `not_eProps_of_emptyTyping`: an instance that types nothing fails `EProps`;
  `not_eProps_of_noLabels`: so does one with no error label (no effects).
* **Effect polymorphism** (row variables, decision 62): `MonoCallback` says that a context type
  fixes one callback row.  `not_noColouring_of_monoCallback` and its siblings at E2a, E6 and E10:
  no instance meets S0, S1, S3, the let law and the (E) property without effect polymorphism.
* **Divergence** (decision 35): `not_loops_of_total` (an instance in which every typed program
  terminates fails E3; totality is not a goal) and `divInTypes_of_loops` (a pure-row loop that
  diverges has a type that is not data).
* **Effect safety has teeth**: `not_der_unhandled` (an unhandled operation is untypable at the pure
  row), and `c1_of_rowSig` (Def. 5.1 (1) follows from one signature object).

**Builder's additions.**  `not_reconciler_of_monoCallback` takes `LiftExt S` (two distinct labels
compose, and the second's row is below the composite): `timeout`'s schema is `PolyUseOpen`, which
asks the callback at `wait ⊙ ε`, and E10 types the failing callback at `(exn)↑`; `SubClosed` moves
it to `wait ⊙ exn` only if `(exn)↑ < wait ⊙ exn`, which Def. 3.5 does not give (it has no
commutativity).  `divInTypes_of_loops` takes `RowAlgebra S`: its proof runs the loop under `R₀`,
which answers the pure row only if the pure row admits nothing (`RowSig`).  Both hold at our
instance (`Targets/Instance`).
-/

namespace Targets.A

namespace EffectSystem

variable {S : EffectSystem}

/-! ### Runs: paths, last configurations, termination -/

theorem lastC_nil {R : S.Runner} (c : S.RConf R) : S.lastC c [] = c := rfl

theorem lastC_cons {R : S.Runner} (c c' : S.RConf R) (ev : S.Event)
    (q : List (S.Event × S.RConf R)) : S.lastC c ((ev, c') :: q) = S.lastC c' q := by
  unfold lastC cfgAt
  simp only [List.map_cons, List.length_cons]
  rw [List.getElem?_cons_succ, List.getElem?_eq_getElem (by simp)]
  rfl

/-- A run to `c'` is a path whose last configuration is `c'`. -/
theorem path_of_rreach {R : S.Runner} {c c' : S.RConf R} (h : S.RReach R c c') :
    ∃ q, S.RPath R c q ∧ S.lastC c q = c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .nil, rfl⟩
  | head hst _ ih =>
      obtain ⟨ev, hst⟩ := hst
      obtain ⟨q, hq, hl⟩ := ih
      exact ⟨(ev, _) :: q, .cons hst hq, by rw [lastC_cons]; exact hl⟩

/-- A terminating program has a complete run. -/
theorem complete_of_terminates {R : S.Runner} {e : S.Term} (h : S.Terminates R e) :
    ∃ q, S.CompleteFrom R (S.rinit R e) q := by
  obtain ⟨c', hc', hv⟩ := h.1 _ Relation.ReflTransGen.refl
  obtain ⟨q, hq, hl⟩ := path_of_rreach hc'
  exact ⟨q, hq, hl ▸ hv⟩

theorem reach_of_pureSteps {c d : S.Conf} (h : S.PureSteps c d) : S.Reach c d := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
      obtain ⟨ev, hst, -⟩ := hst
      exact Relation.ReflTransGen.tail ih ⟨ev, hst⟩

/-! ### Labels -/

theorem eq_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem eq_three {α : Type} {l : List α} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  match l, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem eq_four {α : Type} {l : List α} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-! ### Effect safety has teeth -/

/-- A closed program at the pure row that reaches a raise no frame of its context stops, by steps
that keep the store, breaks effect safety. -/
theorem not_effSafe_of_stuck (hm : S.MachShape) (hr : S.RowSig) (he : S.EffSafe) {P : S.Term}
    {A : S.Ty} (hP : S.der [] P (S.F S.EA.unit A)) {K : S.Kont} {l : S.EA.Lab} {i : ℕ}
    {v : S.Val} (hK : S.catches K l = false) (hU : S.unwindClear K)
    (hs : S.PureSteps (S.init P) (S.setT (S.init P) (S.plug K (S.raise l i v)))) : False := by
  obtain ⟨⟨-, hterm, -, -⟩, -, -, -, -, ⟨-, hstuck⟩, ⟨-, -, -, -, -, -, -, -, hplug, -⟩, -, -⟩ := hm
  rcases he P S.EA.unit A hP _ (reach_of_pureSteps hs) with hv | ⟨ev, c', hst⟩ | hstop
  · obtain ⟨⟨w, hw⟩, -⟩ := hv
    rw [hterm] at hw
    exact (hplug K l i v w).2 hw
  · exact hstuck _ K l i v (hterm _ _) hK hU ev c' hst
  · obtain ⟨_, _, _, _, _, _, hhas, _, _⟩ := hstop
    exact hr.2.1 _ _ hhas

/-- **Effect safety has teeth**: an operation is untypable at the pure row on its own. -/
theorem not_der_unhandled (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (l : S.EA.Lab) (i : ℕ) (v : S.Val) (A' : S.Ty) :
    ¬ S.der [] (S.perform l i v) (S.F S.EA.unit A') := by
  intro hd
  obtain ⟨⟨hinit, -, -, -⟩, ⟨hhole, -, -, -, -, -, hch, -⟩, -, -, -, ⟨hstuck, -⟩,
    ⟨-, -, -, -, -, -, -, -, hplug, -⟩, -, -⟩ := hm
  rcases he _ S.EA.unit A' hd _ Relation.ReflTransGen.refl with hv | ⟨ev, c', hst⟩ | hstop
  · obtain ⟨⟨w, hw⟩, -⟩ := hv
    rw [hinit, ← hhole (S.perform l i v)] at hw
    exact (hplug S.hole l i v w).1 hw
  · exact hstuck _ S.hole l i v (by rw [hinit, hhole]) (hch l) ev c' hst
  · obtain ⟨_, _, _, _, _, _, hhas, _, _⟩ := hstop
    exact hr.2.2.1.2.1 _ _ hhas

/-- **Def. 5.1 (1) follows from one signature object**: no label's row is below the pure row. -/
theorem c1_of_rowSig (hr : S.RowSig) (L : S.EA.Lab) : ¬ S.EA.Sub (S.EA.lift L) S.EA.unit := by
  rintro ⟨ε, x, hc, he⟩
  obtain ⟨hlift, hunit, hcomp, heqv, -, -, hne⟩ := hr
  have h0 : S.has (S.EA.lift L) L 0 :=
    (hlift L L 0).mpr ⟨rfl, List.length_pos_iff.mpr (hne L)⟩
  exact hunit L 0 ((heqv _ _ L 0 he).mp ((hcomp _ _ _ L 0 hc).mpr (Or.inl h0)))

/-! ### Trivial instances fail every (E) property -/

/-- **An instance that types nothing fails `EProps`.** -/
theorem not_eProps_of_emptyTyping (h : ∀ Γ e C, ¬ S.der Γ e C) : ¬ S.EProps := by
  rintro ⟨⟨⟨ls, hls⟩, hP⟩, -⟩
  obtain ⟨le, lw, rfl⟩ := eq_two hls.1
  obtain ⟨A, -, -, -, h1, -⟩ := hP _ hls le lw rfl
  exact h _ _ _ h1

/-- **An instance with no error label fails `EProps`** (E1's `∃ labels` fails). -/
theorem not_eProps_of_noLabels (h : ∀ l, S.sig l ≠ S.sigExn) : ¬ S.EProps := by
  rintro ⟨⟨⟨ls, hls⟩, -⟩, -⟩
  obtain ⟨le, lw, rfl⟩ := eq_two hls.1
  exact h le (hls.2.2 0 (by simp) (by simp))

/-! ### Effect polymorphism is needed -/

/-- **A context type fixes one callback row** (no effect polymorphism).  At a use that applies a
context variable to a callback with a data answer, a callback accepted at one type of the use is
accepted at every type at which the use accepts some callback with that answer. -/
def MonoCallback (S : EffectSystem) : Prop :=
  ∀ Γ i pre post B, S.DataTy B → ∀ M₁ M₂ ε₁ ε₂ C₁ C₂,
    S.der [] M₁ (S.F ε₁ B) → S.der [] M₂ (S.F ε₂ B) →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₁ :: post)) C₁ →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₂ :: post)) C₂ →
    S.der Γ (S.apps (S.var i) (pre ++ S.lam M₂ :: post)) C₁

theorem dataTy_bool : S.DataTy S.bool := .sum .unit .unit

/-- **E1 needs effect polymorphism.**  The schema accepts `ret tt` at the pure row and
`raise le 0 ()` at `(le)↑`; `MonoCallback` accepts the raise's use at the pure row too; the let law
types the closed program `let f = hof in f (λ_. raise le 0 ())` at the pure row; `CallsThrough`
makes it reach the raise under a context that catches nothing, where `OpStuck` stops it,
`DataInj` says it is no answer, and `RowSig` says the pure row admits nothing: `EffSafe` fails. -/
theorem not_noColouring_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (hl : S.LetLaw) (hmono : MonoCallback S) : ¬ S.NoColouring := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨le, lw, rfl⟩ := eq_two hls.1
  obtain ⟨A, hA, hpoly, hcall, h1, h2, -⟩ := hP _ hls le lw rfl
  have u2 := hmono [A] 0 [] [] S.bool dataTy_bool _ _ _ _ _ _ h1 h2
    (hpoly S.EA.unit _ h1) (hpoly (S.EA.lift le) _ h2)
  have hprog : S.der [] (S.lets [S.hof] (S.call (S.var 0) (S.lam (S.raise le 0 S.unitV))))
      (S.F S.EA.unit S.bool) := hl [] _ _ _ _ hA u2
  obtain ⟨K, hK, hU, hs⟩ := hcall _ _ h2
  exact not_effSafe_of_stuck hm hr.2.2.1 he hprog (hK le trivial) hU hs

/-- **E2 needs effect polymorphism**, at E2a's `twice f`. -/
theorem not_higherOrderPoly_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra)
    (he : S.EffSafe) (hl : S.LetLaw) (hmono : MonoCallback S) : ¬ S.HigherOrderPoly := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨le, lw, ly, llog, rfl⟩ := eq_four hls.1
  obtain ⟨⟨Af, At, hAf, hAt, hpoly, hcall, h1, h2, -⟩, -⟩ := hP _ hls le lw ly llog rfl
  have u2 := hmono [At, Af] 0 [S.var 1] [] S.bool dataTy_bool _ _ _ _ _ _ h1 h2
    (hpoly S.EA.unit _ h1) (hpoly (S.EA.lift le) _ h2)
  have hprog : S.der [] (S.lets [S.twice, S.hof]
      (S.call2 (S.var 0) (S.var 1) (S.lam (S.raise le 0 S.unitV))))
      (S.F S.EA.unit (S.Tensor S.bool S.bool)) := hl [] _ _ _ _ hAf (hl [Af] _ _ _ _ hAt u2)
  obtain ⟨K, hK, hU, hs⟩ := hcall _ _ h2
  exact not_effSafe_of_stuck hm hr.2.2.1 he hprog (hK le trivial) hU hs

/-- **E6 needs effect polymorphism**, at `fwrap`: both callbacks lack `li`, since `li ≠ lo`, and
`fwrap`'s handler does not catch `lo`. -/
theorem not_tunnel_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (hl : S.LetLaw) (hmono : MonoCallback S) : ¬ S.Tunnel := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨li, lo, rfl⟩ := eq_two hls.1
  have hne : li ≠ lo := by simpa using hls.2.1
  obtain ⟨Af, hAf, hpoly, hcall, h1, h2, -⟩ := hP _ hls li lo rfl
  obtain ⟨hlift, hunit, -⟩ := hr.2.2.1
  have hl1 : S.Lacks S.EA.unit li := fun i => hunit li i
  have hl2 : S.Lacks (S.EA.lift lo) li := fun i h => hne ((hlift lo li i).mp h).1
  have u2 := hmono [Af] 0 [] [] S.bool dataTy_bool _ _ _ _ _ _ h1 h2
    (hpoly S.EA.unit _ hl1 h1) (hpoly (S.EA.lift lo) _ hl2 h2)
  have hprog : S.der [] (S.lets [S.fwrap li] (S.call (S.var 0) (S.lam (S.raise lo 0 S.unitV))))
      (S.F S.EA.unit S.bool) := hl [] _ _ _ _ hAf u2
  obtain ⟨K, hK, hU, hs⟩ := hcall _ _ hl2 h2
  exact not_effSafe_of_stuck hm hr.2.2.1 he hprog (hK lo (Ne.symm hne)) hU hs

/-- Two distinct labels compose, and the second's row is below the composite. -/
def LiftExt (S : EffectSystem) : Prop :=
  ∀ l l', l ≠ l' → ∃ ε', S.EA.comp (S.EA.lift l) (S.EA.lift l') = some ε' ∧
    S.EA.Sub (S.EA.lift l') ε'

/-- **E10 needs effect polymorphism**, at `timeout`, whose handler does not catch `le`; the
callbacks are put at `wait ⊙ ε` by `SubClosed`, through the unit laws at the pure row and through
`LiftExt` at `(exn)↑`.  `SubClosed` asks its target row well formed; with labels well formed in the
empty context (`hwf`, as our rows' labels are), so are the targets here (`lift_wf`, `comp_wf`). -/
theorem not_reconciler_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (hl : S.LetLaw) (hmono : MonoCallback S) (hext : LiftExt S) (hwf : ∀ l, S.EA.WFLab [] l) :
    ¬ S.Reconciler := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨lw, le, lk, llog, rfl⟩ := eq_four hls.1
  have hne : lw ≠ le := by
    have := hls.2.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at this
    exact fun h => this.1 (Or.inl h)
  obtain ⟨At, Ar, ε, L, hAt, -, hpoly, hcall, -, h1, h2, -⟩ := hP _ hls lw le lk llog rfl
  obtain ⟨hlaws, -, hrs, hsub⟩ := hr
  have hlift := hrs.1
  have hunit := hrs.2.1
  -- the pure callback, at `wait ⊙ 0`
  obtain ⟨ε₁, hc₁, he₁⟩ := hlaws.unit_r (S.EA.lift lw)
  have h1' : S.der [] (S.ret S.tt) (S.F ε₁ S.bool) := by
    obtain ⟨x, hx, hxe⟩ := hlaws.unit_l ε₁
    exact hsub _ _ _ _ _ h1 ⟨ε₁, x, hx, hxe⟩
      ⟨[], hlaws.comp_wf [] _ _ _ (hlaws.lift_wf [] lw (hwf lw)) (hlaws.unit_wf []) hc₁⟩
  have u1 := hpoly S.EA.unit ε₁ _ (fun i => hunit lw i) hc₁ h1'
  -- the failing callback, at `wait ⊙ (exn)↑`
  obtain ⟨ε₂, hc₂, hs₂⟩ := hext lw le hne
  have hl2 : S.Lacks (S.EA.lift le) lw := fun i h => hne ((hlift le lw i).mp h).1
  have u2 := hpoly (S.EA.lift le) ε₂ _ hl2 hc₂ (hsub _ _ _ _ _ h2 hs₂
    ⟨[], hlaws.comp_wf [] _ _ _ (hlaws.lift_wf [] lw (hwf lw)) (hlaws.lift_wf [] le (hwf le)) hc₂⟩)
  have u2' := hmono [At] 0 [] [] S.bool dataTy_bool _ _ _ _ _ _ h1 h2 u1 u2
  have hprog : S.der [] (S.lets [S.timeoutR lw] (S.call (S.var 0) (S.lam (S.raise le 0 S.unitV))))
      (S.F S.EA.unit S.bool) := hl [] _ _ _ _ hAt u2'
  obtain ⟨K, hK, hU, hs⟩ := hcall _ _ hl2 h2
  exact not_effSafe_of_stuck hm hrs he hprog (hK le (Ne.symm hne)) hU hs

/-! ### Divergence is needed, and appears in types -/

/-- Every typed program terminates. -/
def Total (S : EffectSystem) : Prop :=
  ∀ (R : S.Runner) e ε A, R.Respects → S.Answers R ε → S.der [] e (S.F ε A) → S.Terminates R e

/-- `Rtick` keeps its protocol. -/
theorem rtick_respects {lt : S.EA.Lab} (h : S.sig lt = S.sigTick) : (S.Rtick lt).Respects := by
  intro l i o ha ho
  obtain ⟨rfl, rfl⟩ := ha
  rw [h] at ho
  simp only [sigTick, List.getElem?_cons_zero, Option.some.injEq] at ho
  subst ho
  refine ⟨rfl, .unit, .unit, fun s v _ => ⟨S.unitV, (), ?_, .unit⟩⟩
  simp [Rtick]

/-- `Rtl` keeps its protocol. -/
theorem rtl_respects {lt llog : S.EA.Lab} (ht : S.sig lt = S.sigTick) (hl : S.sig llog = S.sigLog) :
    (S.Rtl lt llog).Respects := by
  intro l i o ha ho
  obtain ⟨hl' | hl', rfl⟩ := ha <;> subst hl'
  · rw [ht] at ho
    simp only [sigTick, List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    refine ⟨rfl, .unit, .unit, fun s v _ => ⟨S.unitV, (), ?_, .unit⟩⟩
    simp [Rtl]
  · rw [hl] at ho
    simp only [sigLog, List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    refine ⟨rfl, .sum .unit .unit, .unit, fun s v _ => ⟨S.unitV, (), ?_, .unit⟩⟩
    simp [Rtl]

/-- `Rrec` keeps its protocol, at two distinct labels. -/
theorem rrec_respects {lk llog : S.EA.Lab} (hk : S.sig lk = S.sigKube) (hl : S.sig llog = S.sigLog)
    (hne : llog ≠ lk) : (S.Rrec lk llog).Respects := by
  intro l i o ha ho
  obtain ⟨hl' | hl', rfl⟩ := ha <;> subst hl'
  · rw [hk] at ho
    simp only [sigKube, List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    refine ⟨rfl, .unit, .sum .unit .unit, fun s v _ => ?_⟩
    change Bool at s
    cases s
    · exact ⟨S.ff, true, by simp [Rrec], .inl .unit⟩
    · exact ⟨S.tt, false, by simp [Rrec], .inr .unit⟩
  · rw [hl] at ho
    simp only [sigLog, List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    refine ⟨rfl, .sum .unit .unit, .unit, fun s v _ => ⟨S.unitV, s, ?_, .unit⟩⟩
    simp [Rrec, hne]

/-- **Totality is not a goal**: an instance in which every typed program terminates fails E3. -/
theorem not_loops_of_total (h : Total S) : ¬ S.Loops := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨lt, llog, rfl⟩ := eq_two hls.1
  obtain ⟨⟨ε, L, hans, hder⟩, hfor, -⟩ := hP _ hls lt llog rfl
  have hresp : (S.Rtick lt).Respects := rtick_respects (hls.2.2 0 (by simp) (by simp))
  obtain ⟨q, hq⟩ := complete_of_terminates (h _ _ _ _ hresp hans hder)
  exact hfor.2.1 q hq

/-- **Divergence appears in types**: a pure-row loop that the driver runs forever is not at a data
answer, since S2 would claim it terminates. -/
theorem divInTypes_of_loops (hr : S.RowAlgebra) (hs : S.Safety) (hd : S.DataDiv) (hl : S.Loops) :
    ∀ L, S.der [] (S.runL S.spinL) (S.F S.EA.unit (S.Sum S.UnitT L)) → ¬ S.DataTy L := by
  intro L hder hL
  obtain ⟨⟨ls, hls⟩, hP⟩ := hl
  obtain ⟨lt, llog, rfl⟩ := eq_two hls.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfor⟩ := hP _ hls lt llog rfl
  have hA : S.DataTy (S.Sum S.UnitT L) := .sum .unit hL
  have hR₀ : S.R₀.Respects := fun _ _ _ h => h.elim
  have hans : S.Answers S.R₀ S.EA.unit := fun l i h => (hr.2.2.1.2.1 l i h).elim
  obtain ⟨-, hterm, -⟩ := (hs S.R₀ hR₀ S.EA.unit hans).1 _ _ hA hder
  obtain ⟨q, hq⟩ := complete_of_terminates (hterm (hd _ hA))
  exact hfor.2.1 q hq

end EffectSystem

end Targets.A
