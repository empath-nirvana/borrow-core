import Core.Totality
import Core.NuRel
import Targets.B.BoLo
import Targets.Base.Runs

/-!
# System B — adequacy at BoLo under every platform (B2; TIER1-PLAN §3)

`Adequate B.coreB` reads Core's relation at a row `S` that a platform `P` answers: `cC (F_S A)` is
`ewpTS` at `opTable (Row.tab S δ)` (`cC_effOf`).  A run under `P` is machine segments separated by
the platform's answers (`psteps_split`).

* **One segment.**  `ewpTS` unfolds to `wpG` (`ewp_unfold`), whose run, under the allocator that
  replays the given segment, continues it to a value or to a stop (`wpG_seg`, from `steps_replay`
  and `arun_rest_irr`); an infinite segment is an infinite run under `Alloc.ofRun` and passes
  through that end (`wpG_no_infinite`).
* **An answer.**  A stop of `S` is an operation of `P` (`RowLe S P.ops`), linear at data types
  (`P.Respects`); its argument and the platform's answer hold nothing (`vC_data`), so the
  continuation's share `contShare` resumes `K` at the answer, at the post's own resource.
* **The whole run.**  Induction on `ewpTS`'s least fixed point (`ewp_ind`) carries `PlatOK`: from
  every frame that owns nothing, every run continues to a value in the postcondition and none is
  infinite (`platOK_of_ewp`).  The frame accumulates the segments' leftovers `ρ⁺`, which own
  nothing, and the run-end relation from `∅` composes by 6.48 and 6.49 (`seg_frame`), so at a data
  answer `reclaim` empties the memory (`final_of_platEnd`).

**The return conjunct** holds at every platform that keeps its protocol (`adequateRetAt_core`).

**The drive conjunct** reads the relation at `U(Loop_S A B)`, at a positive loop body (decision D2:
`νX. C` is well formed at a positive `C`, `CTy.NuOk`).  Each iteration is in the relation at
`F_S(A ⊕ U(Loop_S A B))` (`cC_nu_iff`, `loopEffBody_instT`), re-established at each `inj₂ l`, and
every finite prefix of the drive is safe (`adequateDriveAt_core`).  At rows with distinct keys that
the platform answers, every loop body is positive (`loopEffBody_nuOk_of_uniq`).  So **B2 holds at
BoLo** (`adequate_core`).  The hypothesis is needed: a row whose shadowed entry has an open type
makes the body not positive without changing what the row's protocol reads, `cC` then holds of
`()` at that loop type, and its drive is stuck (`adequateDrive_needs_nuOk`).

**B3, B4, B4′** at today's unr-free kernel: B3 and B4 from FL and B2 (`sound_tier1NU`); B4′
from the return conjunct (`soundContractsOfFL_ret`, `soundContracts_tier1NU`).  B5 follows from B4′
through the step-for-step simulation (`Targets/B/BumpSim.lean`, `releasedOnceReuse_tier1NU`).

**Effect safety of driven programs** (`EffSafeDrive`, at a positive loop body, its finished drive
observed, decisions D2 and D4) holds at every typing system with FL at BoLo (`effSafeDrive_of_FL`):
each step runs to a value or to a stop of its row (`platStart_seg`), and a step whose loop's row is
below its own is covered (`effSafeDrive_of_rel`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Runs under a platform, split at the platform's answers -/

/-- A step under a platform is a machine step that keeps the platform's state, or the platform's
answer to an operation of its row that no handler catches. -/
theorem pstep_cases {P : Platform} {c c' : Conf P} (h : PStep (ℍ := ℍ) P c c') :
    (Step1 (ℍ := ℍ) c.μ c.e c'.μ c'.e ∧ c'.s = c.s) ∨
    ∃ (K : Kont) (n i : UInt32) (v w : Val) (s' : P.St) (o : OpSig),
      c.e = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
      Row.find P.ops n i = some o ∧ P.co c.s n i v = some (w, s') ∧
      c' = ⟨c.μ, K.plug (.val w), s'⟩ := by
  cases h with
  | mach h => exact Or.inl ⟨h, rfl⟩
  | plat hK hf hco => exact Or.inr ⟨_, _, _, _, _, _, _, rfl, hK, hf, hco, rfl⟩

/-- **A run under a platform splits at its first answer**: it is a machine run that keeps the
platform's state, or a machine run to an operation the platform answers, the answer, and the rest
of the run. -/
theorem psteps_split {P : Platform} {c₀ c : Conf P} (h : PSteps (ℍ := ℍ) P c₀ c) :
    (Steps (ℍ := ℍ) c₀.μ c₀.e c.μ c.e ∧ c.s = c₀.s) ∨
    ∃ (μ₁ : Heap) (K : Kont) (n i : UInt32) (v w : Val) (s₁ : P.St) (o : OpSig),
      Steps (ℍ := ℍ) c₀.μ c₀.e μ₁ (K.plug (performE (.val (opPayload n i v)))) ∧
      K.HasHnd n = false ∧ Row.find P.ops n i = some o ∧ P.co c₀.s n i v = some (w, s₁) ∧
      PSteps (ℍ := ℍ) P ⟨μ₁, K.plug (.val w), s₁⟩ c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl ⟨.refl _ _, rfl⟩
  | head hab hbc ih =>
      rcases pstep_cases hab with ⟨hm, hs⟩ | ⟨K, n, i, v, w, s', o, he, hK, hf, hco, rfl⟩
      · rcases ih with ⟨hst, hcs⟩ | ⟨μ₁, K, n, i, v, w, s₁, o, hst, hK, hf, hco, hrest⟩
        · exact Or.inl ⟨.more hm hst, hcs.trans hs⟩
        · exact Or.inr ⟨μ₁, K, n, i, v, w, s₁, o, .more hm hst, hK, hf, hs ▸ hco, hrest⟩
      · exact Or.inr ⟨_, K, n, i, v, w, s', o, he ▸ .refl _ _, hK, hf, hco, hbc⟩

/-- `ARun.no_infinite` at an end that takes no step: no infinite run under an allocator passes
through a configuration with a run to such an end. -/
theorem arun_no_infinite_irr {Al : Alloc} {k k' : Nat} {μ μ' : Heap} {e t : Expr}
    (hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) Al k' μ' t k₂ μ₂ e₂)
    (hr : ARun (ℍ := ℍ) Al k μ e k' μ' t) :
    ∀ g : ℕ → Nat × Heap × Expr, g 0 = (k, μ, e) →
      (∀ n, AStep1 (ℍ := ℍ) Al (g n).1 (g n).2.1 (g n).2.2 (g (n + 1)).1 (g (n + 1)).2.1
        (g (n + 1)).2.2) → False := by
  induction hr with
  | refl =>
      intro g h0 hg
      have h1 := hg 0
      rw [h0] at h1
      exact hirr _ _ _ h1
  | more s _ ih =>
      intro g h0 hg
      have h1 := hg 0
      rw [h0] at h1
      obtain ⟨hk, hμ, he⟩ := AStep1.deterministic s h1
      exact ih hirr (fun n => g (n + 1)) (by simp only [hk, hμ, he]) (fun n => hg (n + 1))

/-! ### One segment: `wpG` read demonically at an end that takes no step -/

section Segment
variable {ls : List SRec} {e : Expr} {Φ : List SRec → Expr → WProp} {ρ ρf fρ : WRes}
  {ps : List FrameRec} {μ : Heap}

/-- **A segment continues to the end `wpG` gives.**  A machine run from a configuration `wpG`
quantifies over is a prefix of the run `wpG` gives under the allocator that replays it
(`steps_replay`, `Alloc.replay_agree`), which ends at a term that takes no step (`arun_rest_irr`). -/
theorem wpG_seg (hw : wpG (ℍ := ℍ) ls e Φ ρ)
    (hirr : ∀ ls' t ρ', Φ ls' t ρ' → ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂)
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) μ e μ₁ e₁) :
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ' : Heap) (ps' : List FrameRec) (ls' : List SRec),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ Steps (ℍ := ℍ) μ₁ e₁ μ' t ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧ NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Φ ls' t ρ' := by
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ₀, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ⟨k', h₇⟩, h₈, h₉,
    h₁₀, hT', htg', hps, hls, hΦ⟩ := hw ρf fρ ps hf hc hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₄ hμ
  have hirr' : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) (Alloc.replay cs) k' μ' t k₂ μ₂ e₂ :=
    fun _ _ _ hst => hirr _ _ _ hΦ _ _ _ hst.toStep1
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ', ps', ls', h₁, h₂, h₃, h₅, h₆,
    (arun_rest_irr hirr' hrun h₇).toSteps, h₈, h₉, h₁₀, hT', htg', hps, hls, hΦ⟩

/-- **A segment is finite.**  An infinite machine run from a configuration `wpG` quantifies over is
an infinite run under `Alloc.ofRun`, which `wpG`'s run under that allocator passes through to an
end that takes no step. -/
theorem wpG_no_infinite (hw : wpG (ℍ := ℍ) ls e Φ ρ)
    (hirr : ∀ ls' t ρ', Φ ls' t ρ' → ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂)
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) {f : ℕ → Heap × Expr} (h0 : f 0 = (μ, e))
    (hinf : InfRun (ℍ := ℍ) f) : False := by
  obtain ⟨ρ', -, -, -, -, t, μ₀, μ', -, ls', -, -, -, h₄, -, -, ⟨k', h₇⟩, -, -, -, -, -, -, -,
    hΦ⟩ := hw ρf fρ ps hf hc hT htg (Alloc.ofRun hinf) 0
  obtain rfl := ResU.Lower.functional h₄ hμ
  refine arun_no_infinite_irr (fun _ _ _ hst => hirr _ _ _ hΦ _ _ _ hst.toStep1) h₇
    (fun n => (InfRun.cnt hinf n, (f n).1, (f n).2)) ?_ (fun n => InfRun.astep hinf n)
  simp [InfRun.cnt, countTrue, h0]

end Segment

/-- **The frame across a segment.**  At the end of a segment, the frame `ρf` and the segment's
leftover `ρp`, both owning nothing, frame the post `ρ'`; and the run-end relation from `∅` reaches
the new configuration, by 6.48 (`updV_frame`) and 6.49 (`ResU.UpdV.trans`).  `wpG_bind`'s
regrouping of the frame. -/
theorem seg_frame {ρ ρf fρ ρ' ρp fρ' fρ'p π : WRes} (hno : NoOwn ρf)
    (hU : ResU.UpdV PMap.empty fρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (h₂ : ResU.CompS ρf ρ' fρ') (h₃ : ResU.Hash ρp fρ') (h₅ : ResU.CompS fρ' ρp fρ'p)
    (h₈ : ResU.CompS ρ' ρp π) (h₉ : ResU.UpdV ρ π) (h₁₀ : NoOwn ρp) (hv : ResU.Valid fρ'p) :
    ∃ z, NoOwn z ∧ ResU.Hash z ρ' ∧ ResU.CompS z ρ' fρ'p ∧ ResU.UpdV PMap.empty fρ'p := by
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₅
  have hzY : ResU.CompS z ρ' fρ'p := by
    rwa [ResU.CompS.functional hz₀ (ResU.CompS.comm hzp)] at hY
  obtain ⟨bc, hbc, hfbc⟩ := compS_reassoc h₂ h₅
  obtain rfl := ResU.CompS.functional hbc h₈
  have hfπ : ResU.Hash ρf bc := ⟨hfbc.1, fρ'p, hfbc, hv⟩
  exact ⟨z, noOwn_compS hzp h₁₀ hno, hz, hzY, hU.trans (updV_frame hc hfbc hf hfπ h₉)⟩

/-! ### The whole run: induction on `ewpTS`'s least fixed point -/

section Plat
variable (P : Platform) (Q : List SRec → Val → WProp)

/-- **A run under `P` has ended in `Q`**: at a value in `Q`, its resource framed by what owns
nothing, the configuration one `TW` reaches and the memory its lowering, reached from `∅` by the
run-end relation. -/
def PlatEnd (c : Conf P) : Prop :=
  ∃ (v : Val) (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec),
    c.e = .val v ∧ Q ls v ρ ∧ NoOwn ρf ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Lower fρ c.μ ∧ ResU.UpdV PMap.empty fρ

/-- **Every run under `P` from `e` ends in `Q`, and none is infinite**: from every frame that owns
nothing and every platform state. -/
def PlatOK (ls : List SRec) (e : Expr) (ρ : WRes) : Prop :=
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap) (s : P.St),
    NoOwn ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
    ResU.Lower fρ μ → ResU.UpdV PMap.empty fρ →
    (∀ c, PSteps (ℍ := ℍ) P ⟨μ, e, s⟩ c → ∃ c', PSteps (ℍ := ℍ) P c c' ∧ PlatEnd P Q c') ∧
    ¬ ∃ f : ℕ → Conf P, f 0 = ⟨μ, e, s⟩ ∧ ∀ n, PStep (ℍ := ℍ) P (f n) (f (n + 1))

end Plat

section Answer
variable {P : Platform} {Q : List SRec → Val → WProp}

/-- **A stop of a row the platform answers is the platform's operation**: linear, not abortive,
at data types (`P.Respects`), its entry `o.ent δ`. -/
theorem stop_op (hP : P.Respects) {S : Row} (hle : RowLe S P.ops) {δ : LSub} {n i : UInt32}
    {en : OpEnt} (h : Row.tab S δ n i = some en) :
    ∃ o, Row.find P.ops n i = some o ∧ en = o.ent δ ∧ o.q = .lin ∧ o.abort = false ∧
      o.A.Data ∧ o.B.Data := by
  obtain ⟨o, hf, rfl⟩ := Row.tab_some h
  have hfP := hle n i o hf
  have hm := (Row.find_mem hfP).1
  exact ⟨o, hfP, rfl, (hP.lin o hm).1, (hP.lin o hm).2, (hP.data o hm).1, (hP.data o hm).2⟩

/-- An end `wpG`'s post at an operation table allows takes no step: a value, or an operation no
frame of its context catches (`opPlug_no_step`). -/
theorem post_irr {T : OpTab} {Φ : List SRec → Expr → WProp} {ls : List SRec} {t : Expr}
    {ρ : WRes} (h : valPost Q ls t ρ ∨ opTable T ls t Φ ρ) :
    ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂ := by
  intro μ₁ μ₂ e₂ hst
  rcases h with ⟨v, rfl, -⟩ | ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · exact BoCa.BoLo.no_step_val hst
  · obtain ⟨⟨rfl, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK hst
  · obtain ⟨⟨rfl, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    exact opPlug_no_step (r := true) (payloadName_opPayload n i v) hK hst

/-- **No raise stops at a row the platform answers**: the platform's operations resume. -/
theorem not_raise_stop (hP : P.Respects) {S : Row} (hle : RowLe S P.ops) {δ : LSub}
    {Φ : List SRec → Expr → WProp} {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : opTable (Row.tab S δ) ls t Φ ρ) :
    ∃ K n i v en, t = K.plug (performE (.val (opPayload n i v))) ∧
      (⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        Row.tab S δ n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA ls v ⋆ contShare en ls K Φ)) ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · exact ⟨K, n, i, v, en, (pure_sep_iff.mp hp).1.1, hp⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨o, -, rfl, -, hab, -⟩ := stop_op hP hle hT
    exact absurd ha (by rw [show (o.ent δ).abort = o.abort from rfl, hab]; decide)

/-- **The answer at a stop.**  At a stop of a row the platform answers, the operation is the
platform's, its argument is data, and the continuation's share resumes `K` at every answer of the
operation's answer type, at the post's own resource: the argument holds nothing (`vC_data`), and
the answer holds nothing either. -/
theorem answer_at_stop (hP : P.Respects) {S : Row} (hle : RowLe S P.ops) {δ : LSub}
    {Φ : List SRec → Expr → WProp} {ls : List SRec} {K : Kont} {n i : UInt32} {v : Val}
    {ρ : WRes} (h : opTable (Row.tab S δ) ls (K.plug (performE (.val (opPayload n i v)))) Φ ρ) :
    K.HasHnd n = false ∧ ∃ o, Row.find P.ops n i = some o ∧ DataVal o.A v ∧
      ∀ w, DataVal o.B w → Φ ls (K.plug (.val w)) ρ := by
  obtain ⟨K', n', i', v', en, he, hp⟩ := not_raise_stop hP hle h
  obtain ⟨hK', hpay⟩ := plug_perform_inj he
  obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
  subst hK'
  obtain ⟨⟨-, hK, hT, -⟩, ρ₁, ρ₂, hc, hA, hshare⟩ := pure_sep_iff.mp hp
  obtain ⟨o, hfo, rfl, -, -, hdA, hdB⟩ := stop_op hP hle hT
  obtain ⟨rfl, hv⟩ := (vC_data hdA).mp hA
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨hK, o, hfo, hv, fun w hw => ?_⟩
  exact (hshare.2 ls (Ext.refl ls ρ)).1 w PMap.empty ρ ((vC_data hdB).mpr ⟨rfl, hw⟩)
    (ResU.comp_empty_right ρ)

end Answer

/-- **Every run under the platform from a program in the relation ends in its postcondition, and
none is infinite** (B2's runs through answers).  Induction on `ewpTS`'s least fixed point: each
segment continues to `wpG`'s end (`wpG_seg`) and is finite (`wpG_no_infinite`); at a stop the
platform answers, and the answer resumes `K` at a configuration of the induction hypothesis
(`answer_at_stop`), framed by the segment's leftover (`seg_frame`). -/
theorem platOK_of_ewp {P : Platform} {Q : List SRec → Val → WProp} (hP : P.Respects) {S : Row}
    (hle : RowLe S P.ops) {δ : LSub} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS (ℍ := ℍ) ls e (opTable (Row.tab S δ)) Q ρ) : PlatOK (ℍ := ℍ) P Q ls e ρ := by
  refine ewp_ind (PlatOK P Q) ?_ h
  intro ls e ρ hw ρf fρ ps μ s hno hf hc hT htg hμ hU
  have hirr : ∀ ls' t ρ', (valPost Q ls' t ρ' ∨ opTable (Row.tab S δ) ls' t (PlatOK P Q) ρ') →
      ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂ := fun _ _ _ hp => post_irr hp
  -- a segment to its end, with the frame regrouped
  have hseg : ∀ {μ₁ : Heap} {e₁ : Expr}, Steps (ℍ := ℍ) μ e μ₁ e₁ →
      ∃ (t : Expr) (μ' : Heap) (ls' : List SRec) (ρ' z fρ'p : WRes) (ps' : List FrameRec),
        Steps (ℍ := ℍ) μ₁ e₁ μ' t ∧ NoOwn z ∧ ResU.Hash z ρ' ∧ ResU.CompS z ρ' fρ'p ∧
        TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧ ResU.Lower fρ'p μ' ∧
        ResU.UpdV PMap.empty fρ'p ∧
        (valPost Q ls' t ρ' ∨ opTable (Row.tab S δ) ls' t (PlatOK P Q) ρ') := by
    intro μ₁ e₁ hst
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ', ps', ls', -, h₂, h₃, h₅, h₆, h₇, h₈, h₉, h₁₀, hT', htg',
      -, -, hΦ⟩ := wpG_seg hw hirr hf hc hT htg hμ hst
    have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h₆; exact ⟨σ, hσ⟩
    obtain ⟨z, hz, hzh, hzc, hzU⟩ := seg_frame hno hU hf hc h₂ h₃ h₅ h₈ h₉ h₁₀ hv
    exact ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩
  -- a segment that reaches an operation no handler catches ends there
  have hstop : ∀ {μ₁ : Heap} {K : Kont} {n i : UInt32} {v : Val}, K.HasHnd n = false →
      Steps (ℍ := ℍ) μ e μ₁ (K.plug (performE (.val (opPayload n i v)))) →
      ∃ (ls' : List SRec) (ρ' z fρ'p : WRes) (ps' : List FrameRec),
        NoOwn z ∧ ResU.Hash z ρ' ∧ ResU.CompS z ρ' fρ'p ∧ TW fρ'p ps' (rsOf ls') ∧
        Tagged fρ'p ps' ls' ∧ ResU.Lower fρ'p μ₁ ∧ ResU.UpdV PMap.empty fρ'p ∧
        ∃ o, Row.find P.ops n i = some o ∧ DataVal o.A v ∧
          ∀ w, DataVal o.B w → PlatOK P Q ls' (K.plug (.val w)) ρ' := by
    intro μ₁ K n i v hK hst
    obtain ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩ := hseg hst
    cases h₇ with
    | more h _ => exact absurd h (opPlug_no_step (r := false) (payloadName_opPayload n i v) hK)
    | refl =>
        rcases hΦ with ⟨w, hw, -⟩ | hop
        · exact absurd hw (plug_perform_ne_val K _ w)
        · obtain ⟨-, o, hfo, hdA, hres⟩ := answer_at_stop hP hle hop
          exact ⟨ls', ρ', z, fρ'p, ps', hz, hzh, hzc, hT', htg', h₆, hzU, o, hfo, hdA, hres⟩
  refine ⟨fun c hcs => ?_, ?_⟩
  · -- every run continues to an end
    rcases psteps_split hcs with ⟨hst, hss⟩ | ⟨μ₁, K, n, i, v, w, s₁, o, hst, hK, hfo, hco, hrest⟩
    · obtain ⟨cμ, ce, cs⟩ := c
      simp only at hst hss
      rw [hss]
      obtain ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩ := hseg hst
      have hrun : PSteps (ℍ := ℍ) P ⟨cμ, ce, s⟩ ⟨μ', t, s⟩ := psteps_of_steps P s h₇
      rcases hΦ with ⟨w, rfl, hQ⟩ | hop
      · exact ⟨⟨μ', .val w, s⟩, hrun, w, ls', ρ', z, fρ'p, ps', rfl, hQ, hz, hzh, hzc, hT', htg', h₆,
          hzU⟩
      · obtain ⟨K, n, i, v, en, rfl, -⟩ := not_raise_stop hP hle hop
        obtain ⟨hK, o, hfo, hdA, hres⟩ := answer_at_stop hP hle hop
        obtain ⟨w, s₁, hco₀⟩ := hP.total s o v (Row.find_mem hfo).1 hdA
        have hdB : DataVal o.B w := hP.typed s s₁ o v w (Row.find_mem hfo).1 hdA hco₀
        have hco : P.co s n i v = some (w, s₁) := by
          rw [← (Row.find_mem hfo).2.1, ← (Row.find_mem hfo).2.2]; exact hco₀
        obtain ⟨c', hc', hend⟩ := (hres w hdB z fρ'p ps' μ' s₁ hz hzh hzc hT' htg' h₆ hzU).1 _ .refl
        exact ⟨c', hrun.trans (.head (PStep.plat hK hfo hco) hc'), hend⟩
    · obtain ⟨ls', ρ', z, fρ'p, ps', hz, hzh, hzc, hT', htg', h₆, hzU, o', hfo', hdA, hres⟩ :=
        hstop hK hst
      obtain rfl : o' = o := Option.some.inj (hfo'.symm.trans hfo)
      have hdB : DataVal o'.B w := hP.typed s s₁ o' v w (Row.find_mem hfo').1 hdA
        (by rw [(Row.find_mem hfo').2.1, (Row.find_mem hfo').2.2]; exact hco)
      exact (hres w hdB z fρ'p ps' μ₁ s₁ hz hzh hzc hT' htg' h₆ hzU).1 c hrest
  · -- no run is infinite
    rintro ⟨f, hf0, hfs⟩
    by_cases hall : ∀ n, Step1 (ℍ := ℍ) (f n).μ (f n).e (f (n + 1)).μ (f (n + 1)).e ∧
        (f (n + 1)).s = (f n).s
    · exact wpG_no_infinite hw hirr hf hc hT htg hμ (f := fun n => ((f n).μ, (f n).e))
        (by simp only [hf0]) (fun n => (hall n).1)
    · classical
      have hex := not_forall.mp hall
      have hlt : ∀ k, k < Nat.find hex → Step1 (ℍ := ℍ) (f k).μ (f k).e (f (k + 1)).μ (f (k + 1)).e ∧
          (f (k + 1)).s = (f k).s := fun k hk => not_not.mp (Nat.find_min hex hk)
      have hpre : ∀ k, k ≤ Nat.find hex → Steps (ℍ := ℍ) μ e (f k).μ (f k).e ∧ (f k).s = s := by
        intro k hk
        induction k with
        | zero => rw [hf0]; exact ⟨.refl _ _, rfl⟩
        | succ k ih =>
            obtain ⟨hs, hss⟩ := ih (by omega)
            obtain ⟨h1, h2⟩ := hlt k (by omega)
            exact ⟨hs.trans (.more h1 (.refl _ _)), h2.trans hss⟩
      rcases pstep_cases (hfs (Nat.find hex)) with hmach | ⟨K, n, i, v, w, s', o, he, hK, hfo, hco, hnext⟩
      · exact Nat.find_spec hex hmach
      · obtain ⟨hst, hss⟩ := hpre _ le_rfl
        rw [he] at hst
        obtain ⟨ls', ρ', z, fρ'p, ps', hz, hzh, hzc, hT', htg', h₆, hzU, o', hfo', hdA, hres⟩ :=
          hstop hK hst
        obtain rfl : o' = o := Option.some.inj (hfo'.symm.trans hfo)
        rw [hss] at hco
        have hdB : DataVal o'.B w := hP.typed s s' o' v w (Row.find_mem hfo').1 hdA
          (by rw [(Row.find_mem hfo').2.1, (Row.find_mem hfo').2.2]; exact hco)
        refine (hres w hdB z fρ'p ps' _ s' hz hzh hzc hT' htg' h₆ hzU).2
          ⟨fun k => f (Nat.find hex + 1 + k), by simp only [Nat.add_zero, hnext], fun k => ?_⟩
        have := hfs (Nat.find hex + 1 + k)
        rwa [show Nat.find hex + 1 + k + 1 = Nat.find hex + 1 + (k + 1) by omega] at this

/-! ### The return conjunct -/

/-- **At a data answer the memory is empty**: the answer holds nothing (`vC_data`), the frame owns
nothing, and what the run-end relation reaches from `∅` and owns nothing is `∅` (`reclaim`). -/
theorem final_of_platEnd {P : Platform} {A : VTy} (hA : A.Data) {δ : LSub} {c : Conf P}
    (h : PlatEnd P (fun ls v => vCE (ℍ := ℍ) none true A ls δ v) c) : Final P A c := by
  obtain ⟨v, ls, ρ, ρf, fρ, ps, he, hQ, hno, -, hc, -, -, hμ, hU⟩ := h
  obtain ⟨rfl, hv⟩ := (vC_data hA).mp hQ
  obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hc)
  obtain rfl := reclaim _ hU hno
  exact ⟨v, he, hv, ResU.Lower.functional hμ Fig16.BoLo.lower_empty⟩

/-- A configuration at a value takes no step under a platform. -/
theorem no_pstep_of_val {P : Platform} {c c' : Conf P} {v : Val} (he : c.e = .val v) :
    ¬ PStep (ℍ := ℍ) P c c' := by
  intro h
  rcases pstep_cases h with ⟨hs, -⟩ | ⟨K, n, i, u, w, s', o, he', -⟩
  · rw [he] at hs; exact BoCa.BoLo.no_step_val hs
  · exact plug_perform_ne_val K _ v (he'.symm.trans he)

/-- A run from a value under a platform is empty. -/
theorem psteps_from_val {P : Platform} {c c' : Conf P} {v : Val} (he : c.e = .val v)
    (h : PSteps (ℍ := ℍ) P c c') : c' = c := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, h₁, -⟩
  · rfl
  · exact (no_pstep_of_val he h₁).elim

/-- The empty configuration: nothing owned, nothing reached but `TW.empty`, the empty memory. -/
theorem platOK_init {P : Platform} {Q : List SRec → Val → WProp} {e : Expr}
    (h : PlatOK (ℍ := ℍ) P Q [] e PMap.empty) :
    (∀ c, PSteps (ℍ := ℍ) P (init P e) c → ∃ c', PSteps (ℍ := ℍ) P c c' ∧ PlatEnd P Q c') ∧
    ¬ ∃ f : ℕ → Conf P, f 0 = init P e ∧ ∀ n, PStep (ℍ := ℍ) P (f n) (f (n + 1)) :=
  h PMap.empty PMap.empty [] Adequacy.emptyMem P.s₀ noOwn_empty Fig16.LogRel.hash_empty
    (ResU.comp_empty_right _) TW.empty (fun x hx => absurd hx (by simp)) Fig16.BoLo.lower_empty
    ((ResU.updV_self_iff _).mpr Fig16.LogRel.valid_empty)

/-- **B2's return conjunct at BoLo, at every platform that keeps its protocol**: a program in
Core's relation at `F_S A`, `A` data and `S` answered by the platform, has every run safe, and
every run continues to a data answer with the memory empty and none is infinite. -/
theorem adequateRetAt_core (P : Platform) (hP : P.Respects) :
    AdequateRetAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) P := by
  intro S A e hd hle h
  obtain ⟨hcont, hinf⟩ :=
    platOK_init (platOK_of_ewp hP hle ((cC_effOf S A [] LSub.empty e PMap.empty).mp h))
  refine ⟨fun c hc => ?_, fun c hc => ?_, hinf⟩
  · obtain ⟨c', hc', hend⟩ := hcont c hc
    rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
    · exact Or.inl (final_of_platEnd hd hend)
    · exact Or.inr ⟨c₁, h₁⟩
  · obtain ⟨c', hc', hend⟩ := hcont c hc
    exact ⟨c', hc', final_of_platEnd hd hend⟩

/-! ### The drive conjunct at a positive loop body -/

/-- **A loop's step is in the relation at `F_S(A ⊕ U(Loop_S A B))`**, at a positive body: the
relation at `U(νX. C)` is at `νX. C`'s unrolling (`cC_nu_iff`), whose first observation is
`F_S(A ⊕ U(Loop_S A B))` (`loopEffBody_instT`), read through the row's protocol (`cC_effOf`). -/
theorem ewp_next_of_loop {S : Row} {A B : VTy} (hC : (CTy.loopEffBody S A B).NuOk)
    {ls : List SRec} {δ : LSub} {l : Val} {ρ : WRes}
    (h : vCE (ℍ := ℍ) none true (.thunk (CTy.loopEff S A B)) ls δ l ρ) :
    ewpTS (ℍ := ℍ) ls (nextE l) (opTable (Row.tab S δ))
      (fun ls v => vCE (ℍ := ℍ) none true (.sum A (.thunk (CTy.loopEff S A B))) ls δ v) ρ := by
  have h₁ := (cC_nu_iff hC ls δ _ ρ).mp (h ls (Ext.refl ls ρ))
  rw [CTy.unroll, CTy.loopEffBody_instT] at h₁
  exact (cC_effOf S _ ls δ _ ρ).mp h₁.1

section Drive
variable {P : Platform} {S : Row} {A B : VTy}

/-- The post of the main program of a drive: a loop. -/
abbrev QLoop (S : Row) (A B : VTy) : List SRec → Val → WProp :=
  fun ls v => vCE (ℍ := ℍ) none true (.thunk (CTy.loopEff S A B)) ls LSub.empty v

/-- The post of a loop's step: done at `A`, or the rest of the loop. -/
abbrev QStep (S : Row) (A B : VTy) : List SRec → Val → WProp :=
  fun ls v => vCE (ℍ := ℍ) none true (.sum A (.thunk (CTy.loopEff S A B))) ls LSub.empty v

/-- A configuration from which a run of `S`'s protocol starts, in `Q`: what `PlatOK` reads. -/
def PlatStart (P : Platform) (S : Row) (Q : List SRec → Val → WProp) (c : Conf P) : Prop :=
  ∃ (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec),
    NoOwn ρf ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧
    ResU.Lower fρ c.μ ∧ ResU.UpdV PMap.empty fρ ∧
    ewpTS (ℍ := ℍ) ls c.e (opTable (Row.tab S LSub.empty)) Q ρ

/-- From a start, every run continues to an end in `Q` (`platOK_of_ewp`). -/
theorem platStart_cont (hP : P.Respects) (hle : RowLe S P.ops) {Q : List SRec → Val → WProp}
    {c₀ c : Conf P} (h₀ : PlatStart P S Q c₀) (hc : PSteps (ℍ := ℍ) P c₀ c) :
    ∃ c', PSteps (ℍ := ℍ) P c c' ∧ PlatEnd P Q c' := by
  obtain ⟨ls, ρ, ρf, fρ, ps, hno, hf, hcm, hT, htg, hμ, hU, hw⟩ := h₀
  exact ((platOK_of_ewp hP hle hw) ρf fρ ps c₀.μ c₀.s hno hf hcm hT htg hμ hU).1 c hc

/-- The end of a run whose post is a loop starts the loop's step. -/
theorem platStart_next (hC : (CTy.loopEffBody S A B).NuOk) {c : Conf P} {l : Val}
    (he : c.e = .val l) (h : PlatEnd P (QLoop S A B) c) :
    PlatStart P S (QStep S A B) ⟨c.μ, nextE l, c.s⟩ := by
  obtain ⟨v, ls, ρ, ρf, fρ, ps, he', hQ, hno, hf, hcm, hT, htg, hμ, hU⟩ := h
  obtain rfl : v = l := Subtype.ext (he'.symm.trans he)
  exact ⟨ls, ρ, ρf, fρ, ps, hno, hf, hcm, hT, htg, hμ, hU, ewp_next_of_loop hC hQ⟩

/-- At the end of a loop's step, `inr l` is the rest of the loop, whose step starts there. -/
theorem platStart_inr (hC : (CTy.loopEffBody S A B).NuOk) {c : Conf P} {l : Val}
    (he : c.e = .val (Val.inj₂ l)) (h : PlatEnd P (QStep S A B) c) :
    PlatStart P S (QStep S A B) ⟨c.μ, nextE l, c.s⟩ := by
  obtain ⟨v, ls, ρ, ρf, fρ, ps, he', hQ, hno, hf, hcm, hT, htg, hμ, hU⟩ := h
  obtain rfl : v = Val.inj₂ l := Subtype.ext (he'.symm.trans he)
  rcases hQ with ⟨v₁, hp⟩ | ⟨v₂, hp⟩
  · obtain ⟨hv, -⟩ := pure_sep_iff.mp hp
    exact absurd (congrArg Subtype.val hv) (by simp [Val.inj₁, Val.inj₂])
  · obtain ⟨hv, hQ'⟩ := pure_sep_iff.mp hp
    obtain rfl : l = v₂ := Val.inj₂_inj' hv
    exact ⟨ls, ρ, ρf, fρ, ps, hno, hf, hcm, hT, htg, hμ, hU, ewp_next_of_loop hC hQ'⟩

/-- At the end of a loop's step, `inl a` is a finished drive: `a` is data and the memory is
empty (`reclaim`). -/
theorem finalDrive_of_inl (hA : A.Data) {c : Conf P} {a : Val} (he : c.e = .val (Val.inj₁ a))
    (h : PlatEnd P (QStep S A B) c) : FinalDrive P A (c, .drive) := by
  obtain ⟨v, ls, ρ, ρf, fρ, ps, he', hQ, hno, -, hcm, -, -, hμ, hU⟩ := h
  obtain rfl : v = Val.inj₁ a := Subtype.ext (he'.symm.trans he)
  rcases hQ with ⟨v₁, hp⟩ | ⟨v₂, hp⟩
  · obtain ⟨hv, hQ'⟩ := pure_sep_iff.mp hp
    obtain rfl : a = v₁ := Val.inj₁_inj' hv
    obtain ⟨rfl, hd⟩ := (vC_data hA).mp hQ'
    obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hcm)
    obtain rfl := reclaim _ hU hno
    exact ⟨a, he, hd, ResU.Lower.functional hμ Fig16.BoLo.lower_empty⟩
  · obtain ⟨hv, -⟩ := pure_sep_iff.mp hp
    exact absurd (congrArg Subtype.val hv) (by simp [Val.inj₁, Val.inj₂])

/-- **The drive's invariant**: in the main phase, the configuration is reached from a start of the
main program; in the drive phase, from a start of a loop's step. -/
def DriveInv (P : Platform) (S : Row) (A B : VTy) (rc : Conf P × Phase) : Prop :=
  (rc.2 = .main ∧ ∃ c₀, PlatStart P S (QLoop S A B) c₀ ∧ PSteps (ℍ := ℍ) P c₀ rc.1) ∨
  (rc.2 = .drive ∧ ∃ c₀, PlatStart P S (QStep S A B) c₀ ∧ PSteps (ℍ := ℍ) P c₀ rc.1)

/-- **The invariant is kept by every step of the drive.**  A machine or platform step extends the
segment's run; `start` and `again` act at a value, which ends its run (`psteps_from_val`), and
start the loop's step there (`platStart_next`, `platEnd_inr`). -/
theorem driveInv_step (hP : P.Respects) (hle : RowLe S P.ops) (hC : (CTy.loopEffBody S A B).NuOk)
    {rc rc' : Conf P × Phase} (h : DriveInv P S A B rc) (hs : RStep (ℍ := ℍ) P rc rc') :
    DriveInv P S A B rc' := by
  cases hs with
  | run hp =>
      rcases h with ⟨hph, c₀, h₀, hr⟩ | ⟨hph, c₀, h₀, hr⟩
      · exact Or.inl ⟨hph, c₀, h₀, hr.tail hp⟩
      · exact Or.inr ⟨hph, c₀, h₀, hr.tail hp⟩
  | @start μ s l =>
      rcases h with ⟨-, c₀, h₀, hr⟩ | ⟨hph, -⟩
      · obtain ⟨c', hc', hend⟩ := platStart_cont hP hle h₀ hr
        obtain rfl := psteps_from_val (c := ⟨μ, .val l, s⟩) rfl hc'
        exact Or.inr ⟨rfl, _, platStart_next hC rfl hend, .refl⟩
      · cases hph
  | @again μ s l =>
      rcases h with ⟨hph, -⟩ | ⟨-, c₀, h₀, hr⟩
      · cases hph
      · obtain ⟨c', hc', hend⟩ := platStart_cont hP hle h₀ hr
        obtain rfl := psteps_from_val (c := ⟨μ, .val (Val.inj₂ l), s⟩) rfl hc'
        exact Or.inr ⟨rfl, _, platStart_inr hC rfl hend, .refl⟩

/-- **The invariant gives a step or a finished drive.** -/
theorem driveInv_safe (hP : P.Respects) (hle : RowLe S P.ops) (hA : A.Data)
    {rc : Conf P × Phase} (h : DriveInv P S A B rc) :
    FinalDrive P A rc ∨ ∃ rc', RStep (ℍ := ℍ) P rc rc' := by
  obtain ⟨⟨μ, e, s⟩, ph⟩ := rc
  rcases h with ⟨hph, c₀, h₀, hr⟩ | ⟨hph, c₀, h₀, hr⟩
  · obtain ⟨c', hc', hend⟩ := platStart_cont hP hle h₀ hr
    simp only at hph
    subst hph
    rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
    · obtain ⟨v, -, -, -, -, -, he, -⟩ := hend
      simp only at he
      subst he
      exact Or.inr ⟨_, .start⟩
    · exact Or.inr ⟨(c₁, .main), .run h₁⟩
  · obtain ⟨c', hc', hend⟩ := platStart_cont hP hle h₀ hr
    simp only at hph
    subst hph
    rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
    · obtain ⟨v, ls, ρ, -, -, -, he, hQ, -⟩ := id hend
      simp only at he
      subst he
      rcases hQ with ⟨a, hp⟩ | ⟨l, hp⟩
      · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
        exact Or.inl (finalDrive_of_inl hA rfl hend)
      · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
        exact Or.inr ⟨_, .again⟩
    · exact Or.inr ⟨(c₁, .drive), .run h₁⟩

/-- **B2's drive conjunct at a positive loop body**: every finite prefix of the drive of a program
in Core's relation at `F_S(U(Loop_S A B))` is safe, when `Loop_S A B`'s body is positive. -/
theorem safeDrive_of_nuOk (hP : P.Respects) (hle : RowLe S P.ops) (hA : A.Data)
    (hC : (CTy.loopEffBody S A B).NuOk) {e : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.thunk (CTy.loopEff S A B))) [] LSub.empty e PMap.empty) :
    SafeDrive (ℍ := ℍ) P A e := by
  have h₀ : DriveInv P S A B (init P e, .main) :=
    Or.inl ⟨rfl, init P e, ⟨[], PMap.empty, PMap.empty, PMap.empty, [], noOwn_empty,
      Fig16.LogRel.hash_empty, ResU.comp_empty_right _, TW.empty, fun x hx => absurd hx (by simp),
      Fig16.BoLo.lower_empty, (ResU.updV_self_iff _).mpr Fig16.LogRel.valid_empty,
      (cC_effOf S _ [] LSub.empty e PMap.empty).mp h⟩, .refl⟩
  intro rc hrc
  have hinv : DriveInv P S A B rc := by
    induction hrc with
    | refl => exact h₀
    | tail _ hs ih => exact driveInv_step hP hle hC ih hs
  exact driveInv_safe hP hle hA hinv

end Drive

/-- **B2's drive conjunct at BoLo, at every platform that keeps its protocol**: at a positive loop
body (decision D2), every finite prefix of the drive of a program in Core's relation at
`F_S(U(Loop_S A B))` is safe. -/
theorem adequateDriveAt_core (P : Platform) (hP : P.Respects) :
    AdequateDriveAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) P :=
  fun _ _ _ _ hA hle hC h => safeDrive_of_nuOk hP hle hA hC h

/-- A row whose operations have distinct keys and which a platform answers has closed operation
types, so its loop bodies are positive. -/
theorem loopEffBody_nuOk_of_uniq {P : Platform} (hP : P.Respects) {S : Row} (hU : S.Uniq)
    (hle : RowLe S P.ops) (A B : VTy) : (CTy.loopEffBody S A B).NuOk :=
  CTy.loopEffBody_nuOk (fun o ho => by
    have hm := (Row.find_mem (hle o.n o.i o (Row.find_of_mem hU ho))).1
    exact ⟨dataB_cl (hP.data o hm).1, dataB_cl (hP.data o hm).2⟩) A B

/-- **B2's drive conjunct at BoLo at the rows whose operations have distinct keys**: there the
positivity hypothesis holds (`loopEffBody_nuOk_of_uniq`). -/
theorem adequateDriveAt_core_uniq (P : Platform) (hP : P.Respects) (S : Row) (hU : S.Uniq)
    (A B : VTy) (e : Expr) (hA : A.Data) (hle : RowLe S P.ops)
    (h : cC (ℍ := ℍ) (CTy.effOf S (.thunk (CTy.loopEff S A B))) [] LSub.empty e PMap.empty) :
    SafeDrive (ℍ := ℍ) P A e :=
  safeDrive_of_nuOk hP hle hA (loopEffBody_nuOk_of_uniq hP hU hle A B) h

/-- **B2 at BoLo**: adequacy at every platform that keeps its protocol, the return conjunct through
the platform's answers and the drive conjunct at positive loop bodies. -/
theorem adequate_core : Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) :=
  fun P hP => ⟨adequateRetAt_core P hP, adequateDriveAt_core P hP⟩

/-- **B2 at the platform with no operation.** -/
theorem adequateAt_core_none : AdequateAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) Platform.none :=
  adequate_core Platform.none platformNone_respects

/-! ### The drive conjunct needs its positivity hypothesis -/

/-- The shadow of an operation: its key, linear, at the open argument type `tvar 0`, answering `1`.
Behind the operation in a row, `Row.find` never finds it. -/
def shadowOp (o : OpSig) : OpSig := ⟨o.n, o.i, .lin, .tvar 0, .unit⟩

/-- `[o, shadowOp o]` reads as `[o]`: the shadow is never found. -/
theorem find_shadow (o : OpSig) {n i : UInt32} {x : OpSig}
    (h : Row.find [o, shadowOp o] n i = some x) : n = o.n ∧ i = o.i ∧ x = o := by
  unfold Row.find at h
  simp only [List.find?_cons, shadowOp, List.find?_nil] at h
  by_cases hk : n = o.n ∧ i = o.i
  · rw [decide_eq_true hk] at h
    exact ⟨hk.1, hk.2, (Option.some.inj h).symm⟩
  · rw [decide_eq_false hk] at h
    simp at h

/-- **The loop body at `[o, shadowOp o]` is not positive**: the shadowed entry's argument type is
open (`CTy.EffLeaf` asks every layer's types closed). -/
theorem not_nuOk_shadow (o : OpSig) (A B : VTy) :
    ¬ (CTy.loopEffBody [o, shadowOp o] A B).NuOk :=
  fun h => absurd h.1.2.2.1 (Nat.lt_irrefl 0)

/-- **At a loop type whose body is not positive, `()` is in the relation**: `cC` at `νX. C` holds
of every term when `C` is not positive. -/
theorem cC_loop_unit_of_not_nuOk {S : Row} {A B : VTy} (hC : ¬ (CTy.loopEffBody S A B).NuOk) :
    cC (ℍ := ℍ) (CTy.effOf S (.thunk (CTy.loopEff S A B))) [] LSub.empty (.val Val.unit)
      PMap.empty :=
  (cC_effOf S _ [] LSub.empty _ PMap.empty).mpr
    (ewp_val (opTable_mono _) (fun _ _ hN => absurd hN hC))

/-- A step of the drive: a step under the platform in either phase, `start` at a value of the main
phase, or `again` at `inr l` in the drive phase. -/
theorem rstep_cases {P : Platform} {rc rc' : Conf P × Phase} (h : RStep (ℍ := ℍ) P rc rc') :
    (PStep (ℍ := ℍ) P rc.1 rc'.1 ∧ rc'.2 = rc.2) ∨
    (rc.2 = .main ∧ ∃ l : Val, rc.1.e = .val l ∧ rc' = (⟨rc.1.μ, nextE l, rc.1.s⟩, .drive)) ∨
    (rc.2 = .drive ∧ ∃ l : Val, rc.1.e = .val (Val.inj₂ l) ∧
      rc' = (⟨rc.1.μ, nextE l, rc.1.s⟩, .drive)) := by
  cases h with
  | run hp => exact Or.inl ⟨hp, rfl⟩
  | start => exact Or.inr (Or.inl ⟨rfl, _, rfl, rfl⟩)
  | again => exact Or.inr (Or.inr ⟨rfl, _, rfl, rfl⟩)

/-- **The drive of `()` is stuck** at `nextE ()`, which is no value and takes no step
(`stuckAt_unit_app`). -/
theorem not_safeDrive_unit (P : Platform) (A : VTy) : ¬ SafeDrive (ℍ := ℍ) P A (.val Val.unit) := by
  intro h
  rcases h _ (.single .start) with ⟨a, ha, -⟩ | ⟨rc', hs⟩
  · simp [nextE, Val.val_inj₁] at ha
  · rcases rstep_cases hs with ⟨hp, -⟩ | ⟨hph, -⟩ | ⟨-, l, he, -⟩
    · rcases pstep_cases hp with ⟨hst, -⟩ | ⟨K, n, i, v, w, s', o, he, -⟩
      · exact stuck_no_step (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole hst
      · exact stuck_ne_op (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole K false _ he
    · cases hph
    · simp [nextE, Val.val_inj₂] at he

/-- **The drive conjunct needs its positivity hypothesis** (its scope, decision D2).  At every
platform with an operation `o`, the row `[o, shadowOp o]` reads as `[o]`, which the platform
answers; its loop body is not positive, so `()` is in Core's relation at `F_S(U(Loop_S 1 1))`
(`cC_loop_unit_of_not_nuOk`), and its drive is stuck at `nextE ()`.  The configurations are the
empty world's (`TW.empty`). -/
theorem adequateDrive_needs_nuOk {P : Platform} (hP : P.Respects) {o : OpSig} (ho : o ∈ P.ops) :
    RowLe [o, shadowOp o] P.ops ∧ ¬ (CTy.loopEffBody [o, shadowOp o] .unit .unit).NuOk ∧
      cC (ℍ := ℍ) (CTy.effOf [o, shadowOp o] (.thunk (CTy.loopEff [o, shadowOp o] .unit .unit))) []
        LSub.empty (.val Val.unit) PMap.empty ∧
      ¬ SafeDrive (ℍ := ℍ) P .unit (.val Val.unit) := by
  refine ⟨?_, not_nuOk_shadow o _ _, cC_loop_unit_of_not_nuOk (not_nuOk_shadow o _ _),
    not_safeDrive_unit P .unit⟩
  intro n i x hx
  obtain ⟨rfl, rfl, rfl⟩ := find_shadow o hx
  exact Row.find_of_mem hP.uniq ho

/-- The platform with one operation, `1.0 : 1 ↠ 1`, linear, answering `()`. -/
def Platform.one : Platform :=
  ⟨[⟨1, 0, .lin, .unit, .unit⟩], Unit, (), fun _ _ _ _ => some (Val.unit, ())⟩

theorem platformOne_respects : Platform.one.Respects where
  uniq := List.pairwise_singleton _ _
  nz := by
    intro o ho
    simp only [Platform.one, List.mem_singleton] at ho
    subst ho
    decide
  lin := by
    intro o ho
    simp only [Platform.one, List.mem_singleton] at ho
    subst ho
    exact ⟨rfl, rfl⟩
  data := by
    intro o ho
    simp only [Platform.one, List.mem_singleton] at ho
    subst ho
    exact ⟨.unit 0, .unit 0⟩
  total := fun _ _ _ _ _ => ⟨Val.unit, (), rfl⟩
  typed := by
    intro s s' o v w ho _ hco
    simp only [Platform.one, List.mem_singleton] at ho
    subst ho
    simp only [Platform.one, Option.some.injEq] at hco
    obtain ⟨rfl, -⟩ := hco
    exact .unit

/-! ### B3, B4 and B4′ -/

/-- **B4′ from FL and B2's return conjunct**: `soundContractsOfFL` reads adequacy only at its
return conjunct. -/
theorem soundContractsOfFL_ret {M : B.BWorld} {J : TypingJ} (hFL : FL M J)
    (hAd : ∀ P : Platform, P.Respects → AdequateRetAt (ℍ := ℍ) M P) :
    B.SoundContracts (ℍ := ℍ) J M :=
  fun P hP _ γ S A e hd hle h hγ =>
    hAd P hP S A (substAll γ e) hd hle
      (semWC_of_FL hFL h LSub.empty γ ([], M.nil) PMap.empty Adequacy.models_empty hγ)

/-- **B3 and B4's return conjunct at today's unr-free kernel, at every platform.** -/
theorem soundRetAt_tier1NU (P : Platform) (hP : P.Respects) : SoundRetAt (ℍ := ℍ) tier1NU P :=
  soundRetAt_of_FL fl_core_tier1NU (adequateRetAt_core P hP)

/-- **B3 and B4's drive conjunct at today's unr-free kernel, at every platform** (positive loop
bodies). -/
theorem soundDriveAt_tier1NU (P : Platform) (hP : P.Respects) : SoundDriveAt (ℍ := ℍ) tier1NU P :=
  soundDriveAt_of_FL fl_core_tier1NU (adequateDriveAt_core P hP)

/-- **B3 and B4 at today's unr-free kernel**: from FL and B2. -/
theorem sound_tier1NU : Sound (ℍ := ℍ) tier1NU :=
  soundnessOfFL _ _ fl_core_tier1NU adequate_core

/-- **B4′ at today's unr-free kernel and BoLo.** -/
theorem soundContracts_tier1NU : B.SoundContracts (ℍ := ℍ) tier1NU (B.coreB (ℍ := ℍ)) :=
  soundContractsOfFL_ret fl_core_tier1NU adequateRetAt_core

/-! ### Effect safety of driven programs -/

section DriveStop
variable {P : Platform} {S : Row} {A B : VTy}

/-- **From a start, a machine run continues to an end in `Q` or to a stop of `S`** (no platform
answers): `ewpTS` unfolds once (`ewp_unfold`), and the segment continues to `wpG`'s end
(`wpG_seg`), a value or a stop the row's protocol allows (`Row.tab_some`). -/
theorem platStart_seg {Q : List SRec → Val → WProp} {c₀ : Conf P} {μ₁ : Heap} {e₁ : Expr}
    (h₀ : PlatStart P S Q c₀) (hs : Steps (ℍ := ℍ) c₀.μ c₀.e μ₁ e₁) :
    ∃ μ' t, Steps (ℍ := ℍ) μ₁ e₁ μ' t ∧
      (PlatEnd P Q ⟨μ', t, c₀.s⟩ ∨ StopsIn S t) := by
  obtain ⟨ls, ρ, ρf, fρ, ps, hno, hf, hc, hT, htg, hμ, hU, hw⟩ := h₀
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ', ps', ls', -, h₂, h₃, h₅, h₆, h₇, h₈, h₉, h₁₀, hT', htg',
    -, -, hΦ⟩ := wpG_seg (ewp_unfold (opTable_mono _) hw) (fun _ _ _ hp => post_irr hp) hf hc hT
      htg hμ hs
  refine ⟨μ', t, h₇, ?_⟩
  rcases hΦ with ⟨v, rfl, hQ⟩ | hop
  · have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h₆; exact ⟨σ, hσ⟩
    obtain ⟨z, hz, hzh, hzc, hzU⟩ := seg_frame hno hU hf hc h₂ h₃ h₅ h₈ h₉ h₁₀ hv
    exact Or.inl ⟨v, ls', ρ', z, fρ'p, ps', rfl, hQ, hz, hzh, hzc, hT', htg', h₆, hzU⟩
  · right
    rcases hop with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
    · obtain ⟨⟨rfl, hK, hT0, ha⟩, -⟩ := pure_sep_iff.mp hp
      obtain ⟨o, hfo, rfl⟩ := Row.tab_some hT0
      exact Or.inl ⟨K, n, i, v, o, rfl, hK, hfo, ha⟩
    · obtain ⟨⟨rfl, hK, hT0, ha⟩, -⟩ := pure_sep_iff.mp hp
      obtain ⟨o, hfo, rfl⟩ := Row.tab_some hT0
      exact Or.inr ⟨K, n, i, v, o, rfl, hK, hfo, ha⟩

end DriveStop

/-- A stop of a row is a stop of every larger row. -/
theorem stopsIn_mono {T S : Row} (hle : RowLe T S) {e : Expr} (h : StopsIn T e) : StopsIn S e := by
  rcases h with ⟨K, n, i, v, o, he, hK, hf, ha⟩ | ⟨K, n, i, v, o, he, hK, hf, ha⟩
  · exact Or.inl ⟨K, n, i, v, o, he, hK, hle n i o hf, ha⟩
  · exact Or.inr ⟨K, n, i, v, o, he, hK, hle n i o hf, ha⟩

/-- The start of a program in Core's relation at the empty configuration. -/
theorem platStart_init {P : Platform} {T : Row} {Q : List SRec → Val → WProp} {e : Expr}
    (h : ewpTS (ℍ := ℍ) [] e (opTable (Row.tab T LSub.empty)) Q PMap.empty) :
    PlatStart P T Q (init P e) :=
  ⟨[], PMap.empty, PMap.empty, PMap.empty, [], noOwn_empty, Fig16.LogRel.hash_empty,
    ResU.comp_empty_right _, TW.empty, fun x hx => absurd hx (by simp), Fig16.BoLo.lower_empty,
    (ResU.updV_self_iff _).mpr Fig16.LogRel.valid_empty, h⟩

/-- **Effect safety of a drive from its first step, at Core's relation.**  The drive phase from `M`,
in Core's relation at `F_S(A ⊕ U(Loop_{S₀} A 1))`, the loop's row `S₀` below the step's row `S`
and its body positive, reaches only a finished drive, a configuration that steps, or a stop of `S`.
The invariant at the platform with no operation: the configuration is reached by machine steps
from a start of a step at a row below `S` (`platStart_seg`); `again` starts the next step, at the
loop's row (`platStart_inr`). -/
theorem effSafeDrive_of_rel {S S₀ : Row} {A : VTy} (hle : RowLe S₀ S)
    (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty) :
    ∀ rc, Relation.ReflTransGen (RStep (ℍ := ℍ) Platform.none) (init _ M, .drive) rc →
      DoneDrive Platform.none rc ∨ (∃ rc', RStep (ℍ := ℍ) Platform.none rc rc') ∨
        StopsIn S rc.1.e := by
  let Inv : Conf Platform.none × Phase → Prop := fun rc =>
    rc.2 = .drive ∧ ∃ (T : Row) (c₀ : Conf Platform.none), RowLe T S ∧
      PlatStart Platform.none T (QStep S₀ A .unit) c₀ ∧ Steps (ℍ := ℍ) c₀.μ c₀.e rc.1.μ rc.1.e
  have h₀ : Inv (init _ M, .drive) :=
    ⟨rfl, S, init _ M, fun _ _ _ hf => hf,
      platStart_init ((cC_effOf S _ [] LSub.empty M PMap.empty).mp h), .refl _ _⟩
  have hstep : ∀ rc rc', Inv rc → RStep (ℍ := ℍ) Platform.none rc rc' → Inv rc' := by
    rintro rc rc' ⟨hph, T, c₀, hT, hs₀, hr⟩ hs
    rcases rstep_cases hs with ⟨hp, hph'⟩ | ⟨hph', -⟩ | ⟨-, l, he, rfl⟩
    · exact ⟨hph'.trans hph, T, c₀, hT, hs₀, hr.trans (.more (pstep_none hp) (.refl _ _))⟩
    · rw [hph] at hph'; cases hph'
    · obtain ⟨μ', t, hst, hend | hstop⟩ := platStart_seg hs₀ hr
      · rw [he] at hst
        cases hst with
        | more h _ => exact absurd h BoCa.BoLo.no_step_val
        | refl => exact ⟨rfl, S₀, _, hle, platStart_inr hC rfl hend, .refl _ _⟩
      · rw [he] at hst
        cases hst with
        | more h _ => exact absurd h BoCa.BoLo.no_step_val
        | refl =>
            rcases hstop with ⟨K, n, i, v, o, hK, -⟩ | ⟨K, n, i, v, o, hK, -⟩
            · exact absurd hK.symm (plug_perform_ne_val K _ _)
            · exact absurd hK.symm (plug_raise_ne_val K _ _)
  intro rc hrc
  have hinv : Inv rc := by
    induction hrc with
    | refl => exact h₀
    | tail _ hs ih => exact hstep _ _ ih hs
  obtain ⟨hph, T, c₀, hT, hs₀, hr⟩ := hinv
  obtain ⟨⟨μ, e, ⟨⟩⟩, ph⟩ := rc
  obtain ⟨μ₀, e₀, ⟨⟩⟩ := c₀
  simp only at hph hr
  subst hph
  obtain ⟨μ', t, hst, hend | hstop⟩ := platStart_seg hs₀ hr
  · cases hst with
    | more h _ => exact Or.inr (Or.inl ⟨_, .run (.mach h)⟩)
    | refl =>
        obtain ⟨v, ls, ρ, -, -, -, he, hQ, -⟩ := id hend
        simp only at he
        subst he
        rcases hQ with ⟨a, hp⟩ | ⟨l, hp⟩
        · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
          exact Or.inl ⟨a, rfl⟩
        · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
          exact Or.inr (Or.inl ⟨_, .again⟩)
  · cases hst with
    | more h _ => exact Or.inr (Or.inl ⟨_, .run (.mach h)⟩)
    | refl => exact Or.inr (Or.inr (stopsIn_mono hT hstop))

/-- **Effect safety of driven programs from FL at BoLo** (decision D2's positive loop body; decision
D4's observed end). -/
theorem effSafeDrive_of_FL {J : TypingJ} (hFL : FL (B.coreB (ℍ := ℍ)) J) :
    EffSafeDrive (ℍ := ℍ) J :=
  fun _ _ _ _ hC hJ => effSafeDrive_of_rel (fun _ _ _ hf => hf) hC (comp_of_FL hFL hJ)

/-- **Effect safety of driven programs at today's unr-free kernel.** -/
theorem effSafeDrive_tier1NU : EffSafeDrive (ℍ := ℍ) tier1NU :=
  effSafeDrive_of_FL fl_core_tier1NU

end Targets

end
