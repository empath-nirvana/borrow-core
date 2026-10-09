import Targets.I.J1
import Targets.Instance.CellRuns
import Targets.Instance.HandlerCell

/-!
# The interaction — S6 at the capture cell, reduced to the cell's ownership

S6 per capture event (`ContUseEv`, decision S6) at our instance, read through the capture cell
(SPEC §25).  On a run of a typed program, at a configuration it reaches:

* **A capture event hands a cell `κ`** (`catchEv_cell`): at an admissible effect context the
  operation is linear or affine, so the catch is followed by the allocation of a cell at a location
  `ℓ` the memory does not hold and `κ`'s β-step, and the event's `κ` is `kappaC aff ℓ H K`, affine
  exactly at an affine operation.
* **A use of a cell `κ` releases its cell three steps later** (`use_frees_cell`): `κ` applied to a
  data value takes its β-step, its `case` and its `;`, the memory unchanged, and releases `ℓ`, which
  the memory holds; at a linear `κ` the value is `inj₁ ()` — a cancel reaches the cancel branch,
  which has no step.
* **Leak freedom** (`leakFree_of_coreClosed`, `I.leakFreeAt_J₁`): every complete run of a typed
  program at a data answer ends at the empty memory (B2's runs, through the runner's platform).

**S6 from leak freedom and the cell's ownership** (`contUseEv_of_cells`; at `J₁`,
`I.contUseEv_J₁_of`): S6 follows at a typing system with `LiveOK` and leak freedom from two run
properties of the capture cell, stated here and OPEN at `J₁`:

* `OnlyOwnerFrees`: the first release of a capture event's cell after its allocation is three steps
  after a use of the event's `κ` — until `κ` is applied, its location occurs only in copies of `κ`;
* `NoDanglingUse`: a use of `κ` comes after a capture event that handed `κ`, with no release of its
  location since — no use after the cell's release, the location reallocated.

Each event's cell is released by the end, first by a use of its `κ`; each use releases the cell of
the one event whose allocation it follows; so the uses and the events of `κ` are as many, and an
affine `κ`'s cancels are among its uses.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.A.EffectSystem

variable {S : EffectSystem}

theorem cfgAt_cons_succ {R : S.Runner} (c c' : S.RConf R) (ev : S.Event)
    (q : List (S.Event × S.RConf R)) {t : ℕ} (ht : t ≤ q.length) :
    S.cfgAt c ((ev, c') :: q) (t + 1) = S.cfgAt c' q t := by
  unfold cfgAt
  simp only [List.map_cons, List.getElem?_cons_succ]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  rfl

/-- Each step of a path is a step of the runner. -/
theorem rstep_cfgAt {R : S.Runner} : ∀ {c : S.RConf R} {q : List (S.Event × S.RConf R)},
    S.RPath R c q → ∀ t, t < q.length → ∃ ev, S.RStep R (S.cfgAt c q t) ev (S.cfgAt c q (t + 1))
  | _, _, .nil, t, ht => absurd ht (Nat.not_lt_zero _)
  | _, (ev, _) :: _, .cons hs _, 0, _ => ⟨ev, hs⟩
  | c, (ev, c') :: q, .cons _ hp, t + 1, ht => by
      have ht' : t < q.length := by simp at ht; omega
      rw [cfgAt_cons_succ c c' ev q (by omega), cfgAt_cons_succ c c' ev q (by omega)]
      exact rstep_cfgAt hp t ht'

/-- Each configuration of a path is reached from its start. -/
theorem rreach_cfgAt {R : S.Runner} : ∀ {c : S.RConf R} {q : List (S.Event × S.RConf R)},
    S.RPath R c q → ∀ t, t ≤ q.length → S.RReach R c (S.cfgAt c q t)
  | _, _, _, 0, _ => .refl
  | c, q, hp, t + 1, ht => by
      obtain ⟨ev, hs⟩ := rstep_cfgAt hp t (by omega)
      exact (rreach_cfgAt hp t (by omega)).tail ⟨ev, hs⟩

/-- On a complete run a configuration that is not an answer is not the last. -/
theorem lt_length_of_not_isVal {R : S.Runner} {c : S.RConf R} {q : List (S.Event × S.RConf R)}
    (hq : S.CompleteFrom R c q) {t : ℕ} (ht : t ≤ q.length) (hv : ¬ S.IsVal (S.cfgAt c q t).1) :
    t < q.length := by
  rcases Nat.lt_or_eq_of_le ht with h | h
  · exact h
  · subst h; exact absurd hq.2 hv

end Targets.A.EffectSystem

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt capTag kappaAt kappaC kappaCBody kappaCell freeE stuckE)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain StuckAt stuckAt_case stuckAt_seq
  stuckAt_unit_app)

section CellRun
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

/-- A configuration of a run from a typed program is live. -/
theorem live_cfgAt {R : (𝕊).Runner} (hR : R.Respects) {e : Expr} {C : OCTy} (hd : (𝕊).der [] e C)
    {q : List ((𝕊).Event × (𝕊).RConf R)} (hp : (𝕊).RPath R ((𝕊).rinit R e) q) {t : ℕ}
    (ht : t ≤ q.length) : (𝕊).Live ((𝕊).cfgAt ((𝕊).rinit R e) q t).1 :=
  ⟨e, C, R, _, hR, hd, A.EffectSystem.rreach_cfgAt hp t ht⟩

/-- A head step that allocates nothing is the next step of the run. -/
theorem cfg_next_head {R : (𝕊).Runner} {c₀ : (𝕊).RConf R} {q : List ((𝕊).Event × (𝕊).RConf R)}
    (hp : (𝕊).RPath R c₀ q) {t : ℕ} (ht : t < q.length) {μ μ' : Heap} {K : Kont} {a a' : Expr}
    {s : R.St} (hc : (𝕊).cfgAt c₀ q t = ((μ, K.plug a), s)) (hh : Head (ℍ := ℍ) μ a μ' a')
    (hn : a.allocs = false) : (𝕊).cfgAt c₀ q (t + 1) = ((μ', K.plug a'), s) := by
  obtain ⟨ev, hst⟩ := A.EffectSystem.rstep_cfgAt hp t ht
  rw [hc] at hst
  exact (rstep_det hh hn hst).2

/-- A configuration at a head redex is not an answer. -/
theorem not_isVal_head {μ μ' : Heap} {K : Kont} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') :
    ¬ (𝕊).IsVal (μ, K.plug a) := fun hv => hv.2 _ _ (OStep.mach hh)

/-- A release of a location the memory does not hold does not go on. -/
theorem not_goesOn_free {μ : Heap} (K : Kont) {ℓ : Loc} (hμ : μ ℓ = none) :
    ¬ GoesOn (ℍ := ℍ) orowRF Ξ (μ, K.plug (freeE (.val (Val.loc ℓ)))) := by
  have hnv : ¬ IsVal (freeE (.val (Val.loc ℓ))) := by unfold freeE; intro h; cases h
  rintro (⟨v, hv⟩ | ⟨ev, c', h⟩ | ⟨r, K', p, n, he, -, -⟩)
  · exact hnv (K.isVal_of_plug (by rw [show K.plug _ = v.1 from hv]; exact v.2))
  · exact no_ostep_free (J := tier1Open) K hμ h
  · rcases plug_cmp K K' hnv (opE_not_isVal r p) he with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
    · by_cases h0 : K'' = .hole
      · subst h0
        simp only [Kont.plug, freeE, opE_eq_app] at h₁
        cases r <;> simp [Expr.val, Val.prim] at h₁
      · exact opE_not_isVal r p (by
          unfold freeE at h₁
          cases K'' with
          | hole => exact absurd rfl h0
          | appR f K₃ =>
              simp only [Kont.plug, Expr.app.injEq] at h₁
              exact K₃.isVal_of_plug (h₁.2 ▸ IsVal.loc)
          | appL K₃ u =>
              simp only [Kont.plug, Expr.app.injEq] at h₁
              exact K₃.isVal_of_plug (h₁.1 ▸ IsVal.prim)
          | _ => simp [Kont.plug] at h₁)
    · by_cases h0 : K'' = .hole
      · subst h0
        simp only [Kont.plug, freeE, opE_eq_app] at h₁
        cases r <;> simp [Expr.val, Val.prim] at h₁
      · exact hnv (isVal_of_plug_opE h₁.symm h0)

/-- A redex in a context is no drive when the redex is none. -/
theorem plug_ne_drive_of {s : Expr} (hnv : ¬ IsVal s) (hne : ∀ w : Val, s ≠ driveE (.val w))
    (K : Kont) (w : Val) : K.plug s ≠ driveE (.val w) := by
  intro h
  have := plug_eq_drive h hnv
  subst this
  exact hne w h

/-- A live configuration holds no stuck redex at an evaluation position. -/
theorem false_of_stuck_live (hL : LiveOK (ℍ := ℍ) orowRF Ξ J) {μ : Heap} {K : Kont} {s : Expr}
    (hlive : (𝕊).Live (μ, K.plug s)) (hs : StuckAt (ℍ := ℍ) s)
    (hne : ∀ w : Val, s ≠ driveE (.val w)) : False :=
  not_goesOn_stuck hs K μ (plug_ne_drive_of hs.not_val hne K) (hL _ hlive).2

/-- The shapes of a data value at our instance. -/
theorem dataVal_shape : ∀ {T : OVTy} {w : OVal}, (𝕊).DataVal T w →
    w.1 = .unit ∨ (∃ a b : Expr, w.1 = .pair a b ∧ IsVal a ∧ IsVal b) ∨
    (∃ a : Expr, w.1 = .inj₁ a ∧ IsVal a) ∨ (∃ a : Expr, w.1 = .inj₂ a ∧ IsVal a)
  | _, _, .unit => .inl rfl
  | _, _, .pair ha hb => .inr (.inl ⟨_, _, rfl, isVal_of_dataVal ha, isVal_of_dataVal hb⟩)
  | _, _, .inl ha => .inr (.inr (.inl ⟨_, rfl, isVal_of_dataVal ha⟩))
  | _, _, .inr hb => .inr (.inr (.inr ⟨_, rfl, isVal_of_dataVal hb⟩))

/-- **A use of a cell `κ` releases its cell three steps later.**  On a complete run from a typed
program, at a typing system whose reached configurations go on (`LiveOK`): where `κ = kappaC aff ℓ …`
is applied to a data value `w`, the run takes `κ`'s β-step, its `case` and its `;`, and releases `ℓ`,
which the memory holds then; `w` is `inj₁ ()` at a linear `κ` (a cancel reaches the cancel branch,
which has no step). -/
theorem use_frees_cell (hL : LiveOK (ℍ := ℍ) orowRF Ξ J) {R : (𝕊).Runner} (hR : R.Respects)
    {e : Expr} {C : OCTy} (hd : (𝕊).der [] e C) {q : List ((𝕊).Event × (𝕊).RConf R)}
    (hq : (𝕊).CompleteFrom R ((𝕊).rinit R e) q) {t : ℕ} (ht : t ≤ q.length) {K₀ : Kont}
    {w : OVal} {T : OVTy} (hw : (𝕊).DataVal T w) {aff : Bool} {ℓ : Loc} {H : Val} {K : Kont}
    (he : ((𝕊).cfgAt ((𝕊).rinit R e) q t).1.2 = K₀.plug (.app (kappaC aff ℓ H K) w.1)) :
    t + 3 < q.length ∧
      ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 1)).1.1 = ((𝕊).cfgAt ((𝕊).rinit R e) q t).1.1 ∧
      ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 2)).1.1 = ((𝕊).cfgAt ((𝕊).rinit R e) q t).1.1 ∧
      ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 = ((𝕊).cfgAt ((𝕊).rinit R e) q t).1.1 ∧
      (((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 ℓ).isSome ∧
      ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 4)).1.1 ℓ = none ∧ (aff = true ∨ w.1 = .inj₁ .unit) := by
  have hp := hq.1
  have live : ∀ t', t' ≤ q.length → (𝕊).Live ((𝕊).cfgAt ((𝕊).rinit R e) q t').1 :=
    fun t' h => live_cfgAt hR hd hp h
  have hshape := dataVal_shape hw
  obtain ⟨w₁, hw₁⟩ := w
  simp only at he hshape ⊢
  rcases hct : (𝕊).cfgAt ((𝕊).rinit R e) q t with ⟨⟨μ, et⟩, s⟩
  rw [hct] at he
  simp only at he ⊢
  subst he
  unfold kappaC at hct
  have hwv : IsVal w₁ := isVal_of_dataVal hw
  have ht0 : t < q.length := A.EffectSystem.lt_length_of_not_isVal hq ht (by
    rw [hct]; exact not_isVal_head (Head.beta μ _ ⟨w₁, hwv⟩))
  have h1 := cfg_next_head (K := K₀) (s := s) hp ht0 (by rw [hct] <;> rfl)
    (Head.beta μ _ ⟨w₁, hwv⟩) rfl
  -- the release, after the `;` of a branch at `()`
  have release : ∀ (L : Expr), (𝕊).cfgAt ((𝕊).rinit R e) q (t + 3) =
      ((μ, K₀.plug (.seq (freeE (.val (Val.loc ℓ))) L)), s) → t + 2 < q.length →
      t + 3 < q.length ∧ ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 = μ ∧
        (((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 ℓ).isSome ∧
        ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 4)).1.1 ℓ = none := by
    intro L h3 ht2
    have h3' : (𝕊).cfgAt ((𝕊).rinit R e) q (t + 3) =
        ((μ, (K₀.comp (.seq .hole L)).plug (freeE (.val (Val.loc ℓ)))), s) := by
      rw [h3, Kont.plug_comp]; rfl
    cases hμ : μ ℓ with
    | none =>
        exfalso
        have hl := live (t + 3) (by omega)
        rw [h3'] at hl
        exact not_goesOn_free (K₀.comp (.seq .hole L)) hμ (hL _ hl).2
    | some v =>
        have hfree : Head (ℍ := ℍ) μ (freeE (.val (Val.loc ℓ))) (μ.del ℓ) (.val v) :=
          Head.free μ ℓ v hμ
        have ht3 : t + 3 < q.length := A.EffectSystem.lt_length_of_not_isVal hq (by omega) (by
          rw [h3']; exact not_isVal_head hfree)
        have h4 := cfg_next_head hp ht3 h3' hfree rfl
        refine ⟨ht3, by rw [h3'], by rw [h3']; simp [hμ], by rw [h4]; simp⟩
  -- a branch at `a`: `a; free ℓ; …` steps only at `a = ()`
  have branch : ∀ (a : Expr) (ha : IsVal a) (L : Expr), (𝕊).cfgAt ((𝕊).rinit R e) q (t + 2) =
      ((μ, K₀.plug (.seq a (.seq (freeE (.val (Val.loc ℓ))) L))), s) → t + 1 < q.length →
      a = .unit ∧ t + 3 < q.length ∧ ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 = μ ∧
        (((𝕊).cfgAt ((𝕊).rinit R e) q (t + 3)).1.1 ℓ).isSome ∧
        ((𝕊).cfgAt ((𝕊).rinit R e) q (t + 4)).1.1 ℓ = none := by
    intro a ha L h2 ht1
    by_cases hu : a = .unit
    · subst hu
      have ht2 : t + 2 < q.length := A.EffectSystem.lt_length_of_not_isVal hq (by omega)
        (by rw [h2]; exact not_isVal_head (Head.seq μ _))
      have h3 := cfg_next_head (K := K₀) (s := s) hp ht2 (by rw [h2] <;> rfl) (Head.seq μ _) rfl
      exact ⟨rfl, release L h3 ht2⟩
    · exfalso
      have hl := live (t + 2) (by omega)
      rw [h2] at hl
      exact false_of_stuck_live hL hl (stuckAt_seq (w := ⟨a, ha⟩) hu _)
        (fun w h => by simp [driveE, driveMark, Expr.subst, stuckE] at h)
  rcases hshape with rfl | ⟨a, b, rfl, ha, hb⟩ | ⟨a, rfl, ha⟩ | ⟨a, rfl, ha⟩
  · exfalso
    have hl := live (t + 1) (by omega)
    rw [h1] at hl
    exact false_of_stuck_live hL hl (stuckAt_case (v := ⟨.unit, .unit⟩) (fun a => by simp) _ _)
      (fun w h => by simp [driveE, driveMark, Expr.subst, stuckE] at h)
  · exfalso
    have hl := live (t + 1) (by omega)
    rw [h1] at hl
    exact false_of_stuck_live hL hl (stuckAt_case (v := ⟨.pair a b, .pair ha hb⟩)
      (fun a => by simp) _ _) (fun w h => by simp [driveE, driveMark, Expr.subst, stuckE] at h)
  · have ht1 : t + 1 < q.length := A.EffectSystem.lt_length_of_not_isVal hq (by omega) (by
      rw [h1]; exact not_isVal_head (Head.case₁ μ ⟨a, ha⟩ _ _))
    have h2 := cfg_next_head (K := K₀) (s := s) hp ht1 (by rw [h1] <;> rfl)
      (Head.case₁ μ ⟨a, ha⟩ _ _) rfl
    obtain ⟨rfl, hr1, hr3, hr4, hr5⟩ := branch a ha _ h2 ht1
    exact ⟨hr1, by rw [h1], by rw [h2], hr3, hr4, hr5, .inr rfl⟩
  · have ht1 : t + 1 < q.length := A.EffectSystem.lt_length_of_not_isVal hq (by omega) (by
      rw [h1]; exact not_isVal_head (Head.case₂ μ ⟨a, ha⟩ _ _))
    have h2 := cfg_next_head (K := K₀) (s := s) hp ht1 (by rw [h1] <;> rfl)
      (Head.case₂ μ ⟨a, ha⟩ _ _) rfl
    cases aff with
    | false =>
        exfalso
        have hl := live (t + 2) (by omega)
        rw [h2] at hl
        exact false_of_stuck_live hL hl (stuckAt_unit_app Val.unit)
          (fun w h => by simp [driveE, driveMark, Expr.subst, stuckE] at h)
    | true =>
        obtain ⟨-, hr1, hr3, hr4, hr5⟩ := branch a ha _ h2 ht1
        exact ⟨hr1, by rw [h1], by rw [h2], hr3, hr4, hr5, .inl rfl⟩

/-- A cell `κ` before its allocation is no value. -/
theorem not_isVal_kappaCell (aff : Bool) (H : Val) (K : Kont) :
    ¬ IsVal (kappaCell aff H K) := by
  unfold kappaCell; simp [Expr.val, Val.lam]

/-- **A capture event hands a cell `κ`.**  At an admissible effect context, on a run from a typed
program at a typing system whose reached configurations go on: the catch's `[op]` step is followed by
the allocation of the cell at a location `ℓ` the memory does not hold and `κ`'s β-step at `ℓ`, and the
event's `κ` is `kappaC aff ℓ H K`, affine exactly at an affine operation. -/
theorem catchEv_cell (hΞ : AdmEff Ξ) (hL : LiveOK (ℍ := ℍ) orowRF Ξ J) {R : (𝕊).Runner}
    (hR : R.Respects) {e : Expr} {C : OCTy} (hd : (𝕊).der [] e C)
    {q : List ((𝕊).Event × (𝕊).RConf R)} (hp : (𝕊).RPath R ((𝕊).rinit R e) q) {j : ℕ} {κ : OVal}
    {k : A.OpClass} (h : (𝕊).CatchEvAt ((𝕊).rinit R e) q j κ k) :
    ∃ (aff : Bool) (ℓ : Loc) (H : Val) (K : Kont), κ.1 = kappaC aff ℓ H K ∧
      (aff = true ↔ k = .affine) ∧ j + 2 < q.length ∧
      ((𝕊).cfgAt ((𝕊).rinit R e) q (j + 1)).1.1 ℓ = none ∧
      (((𝕊).cfgAt ((𝕊).rinit R e) q (j + 2)).1.1 ℓ).isSome := by
  rcases h with ⟨hj, (K₀ : Kont), l, (r : OVal), (cs : List OVal), (K : Kont), i, (v : OVal), o,
    (cl : OVal), hterm, hK, hsig, hcls, hk, hcl, happ, j', hjj', hj'q, hterm', hfirst⟩
  have hi := idx_lt (J := J) l.2.2.2 hsig
  rw [perform_eq (ℍ := ℍ) (RF := orowRF) (Ξ := Ξ) (J := J) (l := l) v hi] at hterm
  rcases hct : (𝕊).cfgAt ((𝕊).rinit R e) q j with ⟨⟨μ, et⟩, s⟩
  have hlive := live_cfgAt hR hd hp (le_of_lt hj)
  rw [hct] at hterm hlive
  change et = K₀.plug ((handleK (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l)) r.1
    (cs.map Subtype.val)).plug (K.plug (performE (opArgE (orowRF.name Ξ l) (UInt32.ofNat i) v.1))))
    at hterm
  subst hterm
  change K.HasHnd (orowRF.name Ξ l) = false at hK
  obtain ⟨hr, hcs⟩ := hndVal_of_live hL hlive rfl
  have hv : IsVal v.1 := val_of_live hL hlive v.2
    (K := ((K₀.comp (handleK (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l)) r.1
      (cs.map Subtype.val))).comp K).comp
      (.appR (.prim .perform) (.pairR (Val.i32 (orowRF.name Ξ l))
        (.pairR (Val.i32 (UInt32.ofNat i)) .hole))))
    (by rw [Kont.plug_comp, Kont.plug_comp, Kont.plug_comp]; rfl)
  have hcl₀ : cs[i]? = some cl := hcl
  have hcl' : (cs.map Subtype.val)[i]? = some cl.1 := by
    simp [hcl₀]
  have hclv : IsVal cl.1 := isVal_of_mem_clausesE hcs _ (List.mem_of_getElem? hcl')
  have hca : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨cl.1, hclv⟩ := by
    rw [UInt32.toNat_ofNat_of_lt' hi]
    exact clauseAt_clausesE _ i hclv hcl'
  -- the operation is linear or affine
  obtain ⟨p, hpi, hpo⟩ := sig_entry (J := J) hsig
  have hres := resuming_of_cls (hpo ▸ hcls ▸ hk)
  have hplt : i < (Ξ (orowRF.name Ξ l)).length := (List.getElem?_eq_some_iff.1 hpi).1
  have hpe : (Ξ (orowRF.name Ξ l))[i] = p := (List.getElem?_eq_some_iff.1 hpi).2
  have hqu : p.1 ≠ .unr := by
    intro hu
    have hz := hΞ.1 _ p.1 p.2.1 p.2.2 (by rw [← hpe]; exact List.getElem_mem hplt) hu
    rw [hz, hu] at hres
    simp at hres
  have htag : capTag (qsOf Ξ (orowRF.name Ξ l)) (UInt32.ofNat i).toNat = p.1.tag := by
    rw [UInt32.toNat_ofNat_of_lt' hi]
    unfold qsOf
    rw [capTag_qualsVal _ i (by simpa using hplt)]
    simp [hpe]
  obtain ⟨n, hn⟩ : ∃ n, n = orowRF.name Ξ l := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Val, H = hndVal n (qualsVal ((Ξ n).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩ :=
    ⟨_, rfl⟩
  have hkc : kappaAt (capTag (qualsVal ((Ξ n).map Prod.fst)).1 (UInt32.ofNat i).toNat) H K =
      kappaCell (cellAff p.1) H K := by
    have e₁ : capTag (qualsVal ((Ξ n).map Prod.fst)).1 (UInt32.ofNat i).toNat = p.1.tag := by
      rw [hn]; exact htag
    rw [e₁]
    exact kappaAt_cell hqu H K
  have hhop : Head (ℍ := ℍ) μ (hndE H (K.plug (performE (.val (opPayload n (UInt32.ofNat i)
      ⟨v.1, hv⟩))))) μ (.app (.val ⟨cl.1, hclv⟩) (.pair (.val ⟨v.1, hv⟩)
        (kappaCell (cellAff p.1) H K))) := by
    have h0 := Head.hop (ℍ := ℍ) μ n (UInt32.ofNat i) (qualsVal ((Ξ n).map Prod.fst)) ⟨r.1, hr⟩
      ⟨_, hcs⟩ ⟨cl.1, hclv⟩ ⟨v.1, hv⟩ K hca (hn ▸ hK)
    rw [← hH, hkc] at h0
    exact h0
  have h1 := cfg_next_head (K := K₀) (s := s) hp hj (by rw [hct, hH, hn]; rfl) hhop rfl
  -- no hand-off before the third step
  have hval3 : IsVal (Expr.pair v.1 κ.1) := isVal_of_appK_ne happ
  have handoff : ∀ t (μ' : Heap) (x : Expr), (𝕊).cfgAt ((𝕊).rinit R e) q t =
      ((μ', K₀.plug (.app (.val ⟨cl.1, hclv⟩) (.pair (.val ⟨v.1, hv⟩) x))), s) → t = j' →
      x = κ.1 := by
    intro t μ' x ht htj
    subst htj
    have h' := hterm'
    rw [ht] at h'
    change K₀.plug (.app cl.1 (.pair v.1 x)) = K₀.plug ((appK (Expr.pair v.1 κ.1)).plug cl.1) at h'
    rw [plug_appK_of_isVal hval3 K₀] at h'
    have h'' := plug_inj_hole K₀ h'
    simp only [Expr.app.injEq, Expr.pair.injEq, true_and] at h''
    exact h''
  have hj1 : j + 1 ≠ j' := by
    intro hh
    have hx := handoff (j + 1) _ _ h1 hh
    exact not_isVal_kappaCell _ _ _ (hx ▸ hval3.pair_right)
  have hj1q : j + 1 < q.length := by omega
  have h1' : (𝕊).cfgAt ((𝕊).rinit R e) q (j + 1) =
      ((μ, (K₀.comp (.appR (.val ⟨cl.1, hclv⟩) (.pairR ⟨v.1, hv⟩
        (.appR (.val (Val.lam (kappaCBody (cellAff p.1) H K))) .hole)))).plug
          (allocE Val.unit)), s) := by
    rw [h1, Kont.plug_comp]; rfl
  obtain ⟨ev, hst⟩ := A.EffectSystem.rstep_cfgAt hp (j + 1) hj1q
  rw [h1'] at hst
  obtain ⟨ℓ, hℓ, -, h2⟩ := rstep_alloc_inv R _ Val.unit hst
  have hb := Head.beta (ℍ := ℍ) (μ.upd ℓ Val.unit) (kappaCBody (cellAff p.1) H K) (Val.loc ℓ)
  rw [kappaCBody_subst] at hb
  have h2' : (𝕊).cfgAt ((𝕊).rinit R e) q (j + 2) =
      ((μ.upd ℓ Val.unit, (K₀.comp (.appR (.val ⟨cl.1, hclv⟩) (.pairR ⟨v.1, hv⟩ .hole))).plug
        (.app (.val (Val.lam (kappaCBody (cellAff p.1) H K))) (.val (Val.loc ℓ)))), s) := by
    rw [h2, Kont.plug_comp, Kont.plug_comp]; rfl
  have hj2 : j + 2 ≠ j' := by
    intro hh
    have hx := handoff (j + 2) _ _ (by rw [h2, Kont.plug_comp]; rfl) hh
    have h0 : IsVal κ.1 := hval3.pair_right
    rw [← hx] at h0
    simp [Kont.plug, Expr.val, Val.lam] at h0
  have hj2q : j + 2 < q.length := by omega
  have h3 := cfg_next_head hp hj2q h2' hb rfl
  have h3' : (𝕊).cfgAt ((𝕊).rinit R e) q (j + 3) =
      ((μ.upd ℓ Val.unit, K₀.plug (.app (.val ⟨cl.1, hclv⟩) (.pair (.val ⟨v.1, hv⟩)
        (kappaC (cellAff p.1) ℓ H K)))), s) := by
    rw [h3, Kont.plug_comp]; rfl
  -- the hand-off is at the third step
  have hj3 : j' = j + 3 := by
    by_contra hne
    have hlt : j + 3 < j' := by omega
    have hv3 : IsVal (Expr.pair v.1 (kappaC (cellAff p.1) ℓ H K)) :=
      .pair hv (isVal_kappaC _ _ _ _)
    refine hfirst (j + 3) ⟨kappaC (cellAff p.1) ℓ H K, isOVal_of_isVal (isVal_kappaC _ _ _ _)⟩
      (by omega) hlt (by
        show appK (Expr.pair v.1 (kappaC (cellAff p.1) ℓ H K)) ≠ .hole
        unfold appK; rw [dif_pos hv3]; simp) ?_
    rw [h3']
    change K₀.plug (.app cl.1 (.pair v.1 (kappaC (cellAff p.1) ℓ H K))) =
      K₀.plug ((appK (Expr.pair v.1 (kappaC (cellAff p.1) ℓ H K))).plug cl.1)
    rw [plug_appK_of_isVal hv3 K₀]
  -- the hand-off at the third step names `κ`
  have hκ : kappaC (cellAff p.1) ℓ H K = κ.1 := handoff (j + 3) _ _ h3' hj3.symm
  refine ⟨cellAff p.1, ℓ, H, K, hκ.symm, ?_, hj2q, by rw [h1]; exact hℓ, by rw [h2]; simp⟩
  rw [← hcls, hpo]
  rcases hq1 : p.1 with _ | _ | _
  · simp [cellAff, clsOf]
  · rw [hq1] at hres
    simp [cellAff, clsOf, hres]
  · exact absurd hq1 hqu

end CellRun

section Leak
variable {Ξ : EffCtx} {D : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer D)

open Targets (ORow adequateRetAt_core psteps_from_val) in
/-- **Leak freedom at our instance** (B2's runs): at a typing system whose closed programs are
Core's, every complete run of a typed program at a data answer, under a runner that keeps its
protocol and answers the row, ends at the empty memory.  The run is the run under the runner's
platform (`plain_reach`), whose runs end at a final configuration (`adequateRetAt_core`). -/
theorem leakFree_of_coreClosed (hJ : CoreClosed (OurTyping.ofDer D)) {R : (𝕊).Runner}
    (hR : R.Respects) {ε : ORow} (hans : (𝕊).Answers R ε) {e : Expr} {A : OVTy}
    (hA : (𝕊).DataTy A) (hd : (𝕊).der [] e ((𝕊).F ε A)) {q : List ((𝕊).Event × (𝕊).RConf R)}
    (hq : (𝕊).CompleteFrom R ((𝕊).rinit R e) q) :
    ((𝕊).lastC ((𝕊).rinit R e) q).1.1 = Adequacy.emptyMem := by
  obtain ⟨S, A₀, hC, hS, hcases⟩ := der_cases hJ hd
  have hC' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den (fun _ => [])) =
      CTy.effOf S A₀ := hC
  obtain ⟨rfl, rfl⟩ := effOf_inj hC'
  have hdata := data_den_of_dataTy hA (fun _ => [])
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, -, -, he₀, -⟩
  swap
  · rw [he₀] at hdata; exact (not_data_thunkSum hdata).elim
  have hcl := closed_of_der hJ hd
  have hPl := platformOf_respects hR hS
  have hle := rowLe_platformOf hS hans
  obtain ⟨-, hterm⟩ := adequateRetAt_core (platformOf R _) hPl _ _ e hdata hle hcC
  obtain ⟨hpath, ⟨v, hv⟩, -⟩ := hq
  have hx := rreach_of_path hpath
  obtain ⟨hc, -, hps⟩ := plain_reach hR hS hcC hcl hx
  have hv' : ((𝕊).lastC ((𝕊).rinit R e) q).1.2 = v.1 := hv
  have hcv : IsVal ((𝕊).lastC ((𝕊).rinit R e) q).1.2 := isVal_of_closed_oval (hv' ▸ v.2) hc
  obtain ⟨cc', hcc', w, -, -, hμ⟩ := hterm.1 _ hps
  obtain rfl := psteps_from_val (v := ⟨_, hcv⟩) rfl hcc'
  exact hμ

end Leak

/-! ### S6 from leak freedom and the cell's ownership -/

/-- A count over a range is the size of the filtered range. -/
theorem countP_range_eq_card (p : ℕ → Bool) : ∀ n : ℕ,
    (List.range n).countP p = ((Finset.range n).filter (fun j => p j = true)).card
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.countP_append, countP_range_eq_card p n, Finset.range_add_one,
        Finset.filter_insert]
      by_cases h : p n = true
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp [h]
      · rw [if_neg h]
        simp [h]

/-- A cell `κ` names its class and its cell. -/
theorem kappaC_inj {aff aff' : Bool} {ℓ ℓ' : Loc} {H H' : Val} {K K' : Kont}
    (h : kappaC aff ℓ H K = kappaC aff' ℓ' H' K') : aff = aff' ∧ ℓ = ℓ' := by
  cases aff <;> cases aff' <;>
    simp [kappaC, freeE, stuckE, Expr.val, Val.lam, Val.loc, Val.prim, Val.unit] at h ⊢
  · exact h.1
  · exact h.1.1

section Reduction
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

/-- The run releases `ℓ` at its step `t`. -/
def RelLoc {R : (𝕊).Runner} (c₀ : (𝕊).RConf R) (q : List ((𝕊).Event × (𝕊).RConf R)) (t : ℕ)
    (ℓ : Loc) : Prop :=
  t < q.length ∧ (((𝕊).cfgAt c₀ q t).1.1 ℓ).isSome ∧ ((𝕊).cfgAt c₀ q (t + 1)).1.1 ℓ = none

/-- A run whose memory holds `ℓ` and later does not releases it in between. -/
theorem exists_relLoc {R : (𝕊).Runner} {c₀ : (𝕊).RConf R} {q : List ((𝕊).Event × (𝕊).RConf R)}
    {ℓ : Loc} : ∀ (d a : ℕ), a + d + 1 ≤ q.length → (((𝕊).cfgAt c₀ q a).1.1 ℓ).isSome →
      ((𝕊).cfgAt c₀ q (a + d + 1)).1.1 ℓ = none → ∃ r, a ≤ r ∧ r ≤ a + d ∧ RelLoc c₀ q r ℓ
  | 0, a, hb, ha, hb' => ⟨a, le_refl _, by omega, by omega, ha, by simpa using hb'⟩
  | d + 1, a, hb, ha, hb' => by
      by_cases hm : (((𝕊).cfgAt c₀ q (a + d + 1)).1.1 ℓ).isSome
      · refine ⟨a + d + 1, by omega, by omega, by omega, hm, ?_⟩
        rw [show a + d + 1 + 1 = a + (d + 1) + 1 by omega]; exact hb'
      · obtain ⟨r, h₁, h₂, h₃⟩ := exists_relLoc d a (by omega) ha (by simpa using hm)
        exact ⟨r, h₁, by omega, h₃⟩

/-- **Leak freedom at our instance**: every complete run of a typed program at a data answer, under
a runner that keeps its protocol and answers the row, ends at the empty memory. -/
def LeakFreeAt (Ξ : EffCtx) (J : OurTyping orowRF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) orowRF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) orowRF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) orowRF Ξ J).der [] e ((ourInst (ℍ := ℍ) orowRF Ξ J).F ε A) →
    (ourInst (ℍ := ℍ) orowRF Ξ J).DataTy A → ∀ q,
    (ourInst (ℍ := ℍ) orowRF Ξ J).CompleteFrom R ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q →
    ((ourInst (ℍ := ℍ) orowRF Ξ J).lastC ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q).1.1 =
      Adequacy.emptyMem

/-- **Only a capture's `κ` releases its cell** (OPEN at `J₁`): on every complete run of a typed
program at a data answer, the first release of a capture event's cell after its allocation is three
steps after a use of the event's `κ`.  A run invariant: until `κ` is applied, its cell's location
occurs only in copies of `κ`. -/
def OnlyOwnerFrees (Ξ : EffCtx) (J : OurTyping orowRF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) orowRF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) orowRF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) orowRF Ξ J).der [] e ((ourInst (ℍ := ℍ) orowRF Ξ J).F ε A) →
    (ourInst (ℍ := ℍ) orowRF Ξ J).DataTy A → ∀ q,
    (ourInst (ℍ := ℍ) orowRF Ξ J).CompleteFrom R ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q →
    ∀ j (κ : OVal) k aff ℓ H K,
      (ourInst (ℍ := ℍ) orowRF Ξ J).CatchEvAt ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q j κ k →
      κ.1 = kappaC aff ℓ H K →
      ∀ r, j + 1 < r → RelLoc ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q r ℓ →
      (∀ r', j + 1 < r' → r' < r → ¬ RelLoc ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q r' ℓ) →
      ∃ u, u + 3 = r ∧
        (ourInst (ℍ := ℍ) orowRF Ξ J).UseAt ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q u κ

/-- **A cell `κ` is used only while a cell of its own lives** (OPEN at `J₁`): on every complete run
of a typed program at a data answer, a use of `κ = kappaC aff ℓ …` comes after a capture event that
handed `κ`, with no release of `ℓ` since that event's allocation.  It excludes a use of `κ` after
its cell's release, the location reallocated: a use the bump allocator's run of the same program
would have stuck (B5's simulation, `Targets/B/BumpSim.lean`). -/
def NoDanglingUse (Ξ : EffCtx) (J : OurTyping orowRF) : Prop :=
  ∀ R : (ourInst (ℍ := ℍ) orowRF Ξ J).Runner, R.Respects → ∀ e ε A,
    (ourInst (ℍ := ℍ) orowRF Ξ J).Answers R ε →
    (ourInst (ℍ := ℍ) orowRF Ξ J).der [] e ((ourInst (ℍ := ℍ) orowRF Ξ J).F ε A) →
    (ourInst (ℍ := ℍ) orowRF Ξ J).DataTy A → ∀ q,
    (ourInst (ℍ := ℍ) orowRF Ξ J).CompleteFrom R ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q →
    ∀ u (κ : OVal) aff ℓ H K, κ.1 = kappaC aff ℓ H K →
      (ourInst (ℍ := ℍ) orowRF Ξ J).UseAt ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q u κ →
      ∃ j k, (ourInst (ℍ := ℍ) orowRF Ξ J).CatchEvAt ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q j
          κ k ∧ j + 1 < u ∧
        ∀ r, j + 1 < r → r < u → ¬ RelLoc ((ourInst (ℍ := ℍ) orowRF Ξ J).rinit R e) q r ℓ

open Classical in
/-- **S6 from leak freedom and the cell's ownership.**  At an admissible effect context, at a
typing system whose reached configurations go on (`LiveOK`) and whose complete runs end at the
empty memory (`LeakFreeAt`), S6 (`ContUseEv`) follows from the two ownership properties of the
capture cell: only a capture's `κ` releases its cell (`OnlyOwnerFrees`), and a `κ` is used only
while a cell of its own lives (`NoDanglingUse`).  Every capture event handing `κ` allocates `κ`'s
location (`catchEv_cell`); its cell is released by the end (leak freedom), first three steps after a
use of `κ`; a use releases the cell three steps later, the memory unchanged before
(`use_frees_cell`), so it is the use of one event; and a linear `κ`'s cancel reaches the cancel
branch, which has no step. -/
theorem contUseEv_of_cells (hΞ : AdmEff Ξ) (hL : LiveOK (ℍ := ℍ) orowRF Ξ J)
    (hLeak : LeakFreeAt (ℍ := ℍ) Ξ J) (hO : OnlyOwnerFrees (ℍ := ℍ) Ξ J)
    (hN : NoDanglingUse (ℍ := ℍ) Ξ J) : (𝕊).ContUseEv := by
  intro R hR e ε Aty hans hd hA q hq κ ⟨j₀, k₀, hev₀⟩
  have hp := hq.1
  obtain ⟨aff, ℓ, H, K, hκ, -, -, -, -⟩ := catchEv_cell hΞ hL hR hd hp hev₀
  set c₀ := (𝕊).rinit R e with hc₀
  -- every event handing `κ` allocates `ℓ`, at `κ`'s class
  have hev_cell : ∀ j k, (𝕊).CatchEvAt c₀ q j κ k →
      k = (if aff then .affine else .linear) ∧ j + 2 < q.length ∧
      ((𝕊).cfgAt c₀ q (j + 1)).1.1 ℓ = none ∧ (((𝕊).cfgAt c₀ q (j + 2)).1.1 ℓ).isSome := by
    intro j k hev
    obtain ⟨aff', ℓ', H', K', hκ', hk', hjq, h1, h2⟩ := catchEv_cell hΞ hL hR hd hp hev
    obtain ⟨rfl, rfl⟩ := kappaC_inj (hκ.symm.trans hκ')
    have hkab : k ≠ .abortive := by
      obtain ⟨-, _, _, _, _, _, _, _, _, _, -, -, -, -, hk, -⟩ := hev
      exact hk
    refine ⟨?_, hjq, h1, h2⟩
    cases aff <;> cases k <;> simp_all
  -- a use of `κ` applies the cell `κ` to a data value
  have huse : ∀ u, (𝕊).UseAt c₀ q u κ → u < q.length ∧ ∃ (K₀ : Kont) (w : OVal) (T : OVTy),
      (𝕊).DataVal T w ∧ ((𝕊).cfgAt c₀ q u).1.2 = K₀.plug (.app (kappaC aff ℓ H K) w.1) := by
    rintro u ⟨hu, (K₀ : Kont), (w : OVal), (T : OVTy), hw, he⟩
    refine ⟨hu, K₀, w, T, hw, ?_⟩
    have he' : ((𝕊).cfgAt c₀ q u).1.2 = K₀.plug ((appK w.1).plug κ.1) := he
    rw [he', use_app hw, hκ]
  have hfin : ((𝕊).cfgAt c₀ q q.length).1.1 ℓ = none := by
    have h := hLeak R hR e ε Aty hans hd hA q hq
    change ((𝕊).cfgAt c₀ q q.length).1.1 = _ at h
    rw [h]; rfl
  -- the first release of `ℓ` after an event's allocation
  have hrel : ∀ j k, (𝕊).CatchEvAt c₀ q j κ k → ∃ r, j + 1 < r ∧ RelLoc c₀ q r ℓ := by
    intro j k hev
    obtain ⟨-, hjq, -, h2⟩ := hev_cell j k hev
    obtain ⟨r, h₁, -, h₃⟩ := exists_relLoc (q.length - (j + 2) - 1) (j + 2) (by omega) h2 (by
      rw [show j + 2 + (q.length - (j + 2) - 1) + 1 = q.length by omega]; exact hfin)
    exact ⟨r, by omega, h₃⟩
  let rel : ℕ → ℕ := fun j =>
    if h : ∃ r, j + 1 < r ∧ RelLoc c₀ q r ℓ then Nat.find h else 0
  -- a use's release is the first after the allocation of an event before it
  have huse_rel : ∀ u j, (𝕊).UseAt c₀ q u κ → j + 1 < u →
      (∀ r, j + 1 < r → r < u → ¬ RelLoc c₀ q r ℓ) → rel j = u + 3 := by
    intro u j hu hju hnr
    obtain ⟨hul, K₀, w, T, hw, he⟩ := huse u hu
    obtain ⟨h3, hm1, hm2, hm3, hs3, hn4, -⟩ := use_frees_cell hL hR hd hq (le_of_lt hul) hw he
    have hR3 : RelLoc c₀ q (u + 3) ℓ := ⟨h3, hs3, hn4⟩
    have hex : ∃ r, j + 1 < r ∧ RelLoc c₀ q r ℓ := ⟨u + 3, by omega, hR3⟩
    have hconst : ∀ d, d ≤ 3 → ((𝕊).cfgAt c₀ q (u + d)).1.1 = ((𝕊).cfgAt c₀ q u).1.1 := by
      intro d hd
      interval_cases d
      · rfl
      · exact hm1
      · exact hm2
      · exact hm3
    have hmin : ∀ r', r' < u + 3 → ¬ (j + 1 < r' ∧ RelLoc c₀ q r' ℓ) := by
      rintro r' hr' ⟨hjr, hrl⟩
      by_cases hlt : r' < u
      · exact hnr r' hjr hlt hrl
      · obtain ⟨-, hs, hn⟩ := hrl
        obtain ⟨d, rfl⟩ : ∃ d, r' = u + d := ⟨r' - u, by omega⟩
        rw [hconst d (by omega)] at hs
        rw [show u + d + 1 = u + (d + 1) by omega, hconst (d + 1) (by omega)] at hn
        rw [hn] at hs
        simp at hs
    show (if h : ∃ r, j + 1 < r ∧ RelLoc c₀ q r ℓ then Nat.find h else 0) = u + 3
    rw [dif_pos hex]
    refine le_antisymm (Nat.find_min' hex ⟨by omega, hR3⟩) ?_
    by_contra hlt
    push_neg at hlt
    exact hmin _ hlt (Nat.find_spec hex)
  -- an event's first release is three steps after a use of `κ`
  have hev_use : ∀ j k, (𝕊).CatchEvAt c₀ q j κ k → ∃ u, rel j = u + 3 ∧ (𝕊).UseAt c₀ q u κ := by
    intro j k hev
    have hex := hrel j k hev
    obtain ⟨hjr, hrl⟩ := Nat.find_spec hex
    obtain ⟨u, hu, huse'⟩ := hO R hR e ε Aty hans hd hA q hq j κ k aff ℓ H K hev hκ (Nat.find hex)
      hjr hrl (fun r' h₁ h₂ h₃ => Nat.find_min hex h₂ ⟨h₁, h₃⟩)
    refine ⟨u, ?_, huse'⟩
    show (if h : ∃ r, j + 1 < r ∧ RelLoc c₀ q r ℓ then Nat.find h else 0) = u + 3
    rw [dif_pos hex, hu]
  -- two events handing `κ` have distinct first releases
  have hev_inj : ∀ j₁ k₁ j₂ k₂, (𝕊).CatchEvAt c₀ q j₁ κ k₁ → (𝕊).CatchEvAt c₀ q j₂ κ k₂ →
      j₁ < j₂ → rel j₁ < rel j₂ := by
    intro j₁ k₁ j₂ k₂ hev₁ hev₂ hlt
    obtain ⟨-, hj₁q, -, ha₁⟩ := hev_cell j₁ k₁ hev₁
    obtain ⟨-, hj₂q, hn₂, -⟩ := hev_cell j₂ k₂ hev₂
    have hex₁ := hrel j₁ k₁ hev₁
    have hex₂ := hrel j₂ k₂ hev₂
    have e₁ : rel j₁ = Nat.find hex₁ := dif_pos hex₁
    have e₂ : rel j₂ = Nat.find hex₂ := dif_pos hex₂
    rw [e₁, e₂]
    have hgt := (Nat.find_spec hex₂).1
    rcases Nat.lt_or_ge (j₁ + 2) (j₂ + 1) with hlt' | hge
    · obtain ⟨r, h₁, h₂, h₃⟩ := exists_relLoc (j₂ + 1 - (j₁ + 2) - 1) (j₁ + 2) (by omega) ha₁
        (by rw [show j₁ + 2 + (j₂ + 1 - (j₁ + 2) - 1) + 1 = j₂ + 1 by omega]; exact hn₂)
      have := Nat.find_min' hex₁ ⟨by omega, h₃⟩
      omega
    · have he : j₂ + 1 = j₁ + 2 := by omega
      rw [he] at hn₂
      rw [hn₂] at ha₁
      simp at ha₁
  -- the counts
  have hcount : (𝕊).uses c₀ q κ = (𝕊).caughtEv c₀ q κ := by
    have hU : (𝕊).uses c₀ q κ =
        ((Finset.range q.length).filter (fun u => (𝕊).UseAt c₀ q u κ)).card := by
      unfold A.EffectSystem.uses
      rw [countP_range_eq_card]
      congr 1
      ext u
      simp
    have hE : (𝕊).caughtEv c₀ q κ =
        ((Finset.range q.length).filter (fun j => ∃ k, (𝕊).CatchEvAt c₀ q j κ k)).card := by
      unfold A.EffectSystem.caughtEv A.EffectSystem.caughtEvLin A.EffectSystem.caughtEvAff
      rw [countP_range_eq_card, countP_range_eq_card]
      have hcls : ∀ j k, (𝕊).CatchEvAt c₀ q j κ k → k = (if aff then .affine else .linear) :=
        fun j k hev => (hev_cell j k hev).1
      cases aff
      · have h0 : ((Finset.range q.length).filter
            (fun j => decide ((𝕊).CatchEvAt c₀ q j κ .affine) = true)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _ hj
          simp only [decide_eq_true_eq] at hj
          exact absurd (hcls j _ hj) (by simp)
        rw [h0, Nat.add_zero]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hj, hev⟩; exact ⟨hj, _, hev⟩
        · rintro ⟨hj, k, hev⟩
          have := hcls j k hev
          simp at this
          subst this
          exact ⟨hj, hev⟩
      · have h0 : ((Finset.range q.length).filter
            (fun j => decide ((𝕊).CatchEvAt c₀ q j κ .linear) = true)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _ hj
          simp only [decide_eq_true_eq] at hj
          exact absurd (hcls j _ hj) (by simp)
        rw [h0, Nat.zero_add]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hj, hev⟩; exact ⟨hj, _, hev⟩
        · rintro ⟨hj, k, hev⟩
          have := hcls j k hev
          simp at this
          subst this
          exact ⟨hj, hev⟩
    rw [hU, hE]
    apply le_antisymm
    · -- a use, to the event before it
      let g : ℕ → ℕ := fun u =>
        if h : ∃ j, (∃ k, (𝕊).CatchEvAt c₀ q j κ k) ∧ j + 1 < u ∧
            ∀ r, j + 1 < r → r < u → ¬ RelLoc c₀ q r ℓ then h.choose else 0
      have hg : ∀ u, (𝕊).UseAt c₀ q u κ → (∃ k, (𝕊).CatchEvAt c₀ q (g u) κ k) ∧ g u + 1 < u ∧
          ∀ r, g u + 1 < r → r < u → ¬ RelLoc c₀ q r ℓ := by
        intro u hu
        obtain ⟨j, k, hev, hju, hnr⟩ := hN R hR e ε Aty hans hd hA q hq u κ aff ℓ H K hκ hu
        have h : ∃ j, (∃ k, (𝕊).CatchEvAt c₀ q j κ k) ∧ j + 1 < u ∧
            ∀ r, j + 1 < r → r < u → ¬ RelLoc c₀ q r ℓ := ⟨j, ⟨k, hev⟩, hju, hnr⟩
        have hgu : g u = h.choose := dif_pos h
        rw [hgu]
        exact h.choose_spec
      refine Finset.card_le_card_of_injOn g (fun u hu => ?_) (fun u₁ hu₁ u₂ hu₂ heq => ?_)
      · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hu ⊢
        obtain ⟨⟨k, hev⟩, -, -⟩ := hg u hu.2
        exact ⟨hev.1, k, hev⟩
      · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hu₁ hu₂
        obtain ⟨-, hj₁, hn₁⟩ := hg u₁ hu₁.2
        obtain ⟨-, hj₂, hn₂⟩ := hg u₂ hu₂.2
        have e₁ := huse_rel u₁ (g u₁) hu₁.2 hj₁ hn₁
        have e₂ := huse_rel u₂ (g u₂) hu₂.2 hj₂ hn₂
        rw [heq] at e₁
        omega
    · -- an event, to the use before its first release
      refine Finset.card_le_card_of_injOn (fun j => rel j - 3) (fun j hj => ?_)
        (fun j₁ hj₁ j₂ hj₂ heq => ?_)
      · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj ⊢
        obtain ⟨-, k, hev⟩ := hj
        obtain ⟨u, hu, huse'⟩ := hev_use j k hev
        rw [hu, Nat.add_sub_cancel]
        exact ⟨huse'.1, huse'⟩
      · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj₁ hj₂
        obtain ⟨-, k₁, hev₁⟩ := hj₁
        obtain ⟨-, k₂, hev₂⟩ := hj₂
        obtain ⟨u₁, hu₁, -⟩ := hev_use j₁ k₁ hev₁
        obtain ⟨u₂, hu₂, -⟩ := hev_use j₂ k₂ hev₂
        have heq' : rel j₁ = rel j₂ := by simp only at heq; omega
        rcases Nat.lt_trichotomy j₁ j₂ with hlt | hEq | hgt
        · exact absurd heq' (Nat.ne_of_lt (hev_inj j₁ k₁ j₂ k₂ hev₁ hev₂ hlt))
        · exact hEq
        · exact absurd heq'.symm (Nat.ne_of_lt (hev_inj j₂ k₂ j₁ k₁ hev₂ hev₁ hgt))
  refine ⟨hcount, ?_⟩
  have hinr : (𝕊).DataVal ((𝕊).Sum (𝕊).UnitT (𝕊).UnitT) ((𝕊).inr (𝕊).unitV) := .inr .unit
  cases aff
  · -- a linear `κ` is never cancelled
    have h0 : (𝕊).cancels c₀ q κ = 0 := by
      unfold A.EffectSystem.cancels
      refine List.countP_eq_zero.2 fun t _ ht => ?_
      simp only [decide_eq_true_eq] at ht
      obtain ⟨htq, (K₀ : Kont), he⟩ := ht
      have he' : ((𝕊).cfgAt c₀ q t).1.2 =
          K₀.plug (.app (kappaC false ℓ H K) ((𝕊).inr (𝕊).unitV).1) := by
        have h' : ((𝕊).cfgAt c₀ q t).1.2 = K₀.plug (cancelE κ.1) := he
        rw [h', hκ]; rfl
      obtain ⟨-, -, -, -, -, -, h⟩ := use_frees_cell hL hR hd hq (le_of_lt htq) hinr he'
      change false = true ∨ Expr.inj₂ Expr.unit = Expr.inj₁ Expr.unit at h
      simp at h
    rw [h0]; exact Nat.zero_le _
  · -- an affine `κ`'s cancels are among its uses, and its events are affine
    have hle : (𝕊).cancels c₀ q κ ≤ (𝕊).uses c₀ q κ := by
      unfold A.EffectSystem.cancels A.EffectSystem.uses
      refine List.countP_mono_left fun t _ hc => ?_
      simp only [decide_eq_true_eq] at hc ⊢
      obtain ⟨htq, (K₀ : Kont), he⟩ := hc
      refine ⟨htq, K₀, (𝕊).inr (𝕊).unitV, (𝕊).Sum (𝕊).UnitT (𝕊).UnitT, hinr, ?_⟩
      have h' : ((𝕊).cfgAt c₀ q t).1.2 = K₀.plug (cancelE κ.1) := he
      show ((𝕊).cfgAt c₀ q t).1.2 = K₀.plug ((appK (Expr.inj₂ .unit)).plug κ.1)
      rw [h', plug_appK_of_isVal (.inj₂ .unit) K₀]
      rfl
    have hlin : (𝕊).caughtEvLin c₀ q κ = 0 := by
      unfold A.EffectSystem.caughtEvLin
      refine List.countP_eq_zero.2 fun j _ hj => ?_
      simp only [decide_eq_true_eq] at hj
      exact absurd (hev_cell j _ hj).1 (by simp)
    have : (𝕊).caughtEv c₀ q κ = (𝕊).caughtEvAff c₀ q κ := by
      unfold A.EffectSystem.caughtEv; rw [hlin, Nat.zero_add]
    omega

end Reduction

end Targets.Inst

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets.Inst (ourInst J₁ J1Der AdmEff LeakFreeAt OnlyOwnerFrees NoDanglingUse)

/-- **Leak freedom at `J₁`**, at every effect context: its closed programs there are Core's
(`coreClosed_J₁At`), so B2's runs end at the empty memory. -/
theorem leakFreeAt_J₁ {Ξ : EffCtx} : LeakFreeAt (ℍ := ℍ) Ξ J₁ :=
  fun _ hR _ _ _ hans hd hA _ hq =>
    Inst.leakFree_of_coreClosed (D := Inst.J1DerAt Ξ) (Inst.coreClosed_J₁At Ξ) hR hans hA hd hq

/-- **S6 at `J₁`, given the capture cell's ownership** (`OnlyOwnerFrees`, `NoDanglingUse`), at every
admissible effect context: leak freedom (`leakFreeAt_J₁`) and `LiveOK` hold there. -/
theorem contUseEv_J₁_of (hO : ∀ Ξ, AdmEff Ξ → OnlyOwnerFrees (ℍ := ℍ) Ξ J₁)
    (hN : ∀ Ξ, AdmEff Ξ → NoDanglingUse (ℍ := ℍ) Ξ J₁) :
    ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv := fun Ξ hΞ =>
  Inst.contUseEv_of_cells hΞ
    (Inst.liveOK_of_coreClosed (D := Inst.J1DerAt Ξ) (Inst.coreClosed_J₁At Ξ))
    leakFreeAt_J₁ (hO Ξ hΞ) (hN Ξ hΞ)

end Targets.I

end
