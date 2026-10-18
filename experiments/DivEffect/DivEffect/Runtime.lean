import DivEffect.Residual
import Core.Alloc
import Core.Stale
import Core.EffMachine

/-!
# DivEffect — the runtime's clause  (§4.1, unknown 1, item 3)

The runtime drives `main` as the outermost handler of `Div`: its clause resumes every tick with
*next*.

    H_rt = (d, (lin, (λv. v, (λ((), κ). κ next, ()))))

`runtime_every_run`: a closed `M` at `F_{Div} A`, under `hnd_d H_rt`, from the empty memory: no
prefix of any run is stuck.  The run is infinite in general, so no `wp` covers it; the proof is
an invariant of configurations, closed under every step (`rt_step`), each of which steps or is a
value (`rt_safe`):

* `seg`: `hnd H_rt x₁`, `x₁` on a run of a segment `x` of `cwp` from a configuration the
  segment's `wp` holds at (`Good`).  The segment's `wp`, taken under the allocator that replays
  the run (`seg_demonic`, as Core's `wpTS_demonic`), continues `x₁` to a term with no step: an
  answer (then `[ret]`) or a tick (then `[op]`);
* the handler's steps after a tick, each its configuration's only step (Core's `catch_step`,
  `kappaCell_beta`, `kappaC_beta`, `kappaC_case₁`, `free_step1Only`, `kResume_beta`), but the
  cell's allocation, which takes any free location.  They end at `hnd H_rt K[next]`, which is
  `seg` again: the tick's continuation is in `cwp`, at the resources the segment's `wp` left
  (`next_good`);
* the answer's steps after `[ret]`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaCBody kappaAt clauseAt capTag freeE Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The runtime's handler -/

/-- `h_ret = λv. v`. -/
def rtR : Val := .lam (.var 0)

/-- The tick's clause `λ((), κ). κ next`. -/
def rtC : Val := .lam (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV)))

/-- The runtime's handler value. -/
def rtH (d : UInt32) : Val := hndVal d (qualsVal [.lin]) rtR (Val.pair rtC .unit)

/-! ### A run of a segment continues to its stop -/

/-- **Prefix**, at an end that takes no step: Core's `ARun.rest`, whose end there is a value. -/
theorem ARun.rest_final {A : Alloc} {i j j₁ : Nat} {μ μ' μ₁ : Heap} {e e₁ t : Expr}
    (hf : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ' t μ₂ t₂)
    (h' : ARun (ℍ := ℍ) A i μ e j₁ μ₁ e₁) :
    ARun (ℍ := ℍ) A i μ e j μ' t → ARun (ℍ := ℍ) A j₁ μ₁ e₁ j μ' t := by
  induction h' with
  | refl => exact id
  | more s' _ ih =>
      intro h
      cases h with
      | refl => exact (hf _ _ s'.toStep1).elim
      | more s t =>
          obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s'
          exact ih t

section
variable (d : UInt32) (Q : List SRec → Val → WProp)

/-- A configuration a segment's `wp` holds at: `x` in `cwp`, its frame, world and memory. -/
def Good (μ : Heap) (x : Expr) : Prop :=
  ∃ (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec), cwp LSub.empty d T0 Q ls x ρ ∧
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Lower fρ μ

/-- The configuration a segment's `wp` stops at: its post-configuration, at a term that is an
answer at `Q` or a tick owing `cwp`. -/
def PostD (μ : Heap) (t : Expr) : Prop :=
  ∃ (ls' : List SRec) (ρ' ρf ρp fρ' fρ'p : WRes) (ps' : List FrameRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.CompS fρ' ρp fρ'p ∧
    ResU.Lower fρ'p μ ∧ NoOwn ρp ∧ TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    (valPost Q ls' t ρ' ∨
      divTab LSub.empty d T0 Q (cwp LSub.empty d T0 Q) ls' t
        (fun ls e => ewpTS ls e (divTab LSub.empty d T0 Q (cwp LSub.empty d T0 Q)) Q) ρ')

/-- A stop of a segment takes no step. -/
theorem post_final {μ : Heap} {t : Expr} (h : PostD d Q μ t) :
    ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ t μ₂ t₂ := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, ht⟩ := h
  rcases ht with ⟨v, rfl, -⟩ | ht | ht
  · exact fun _ _ => BoCa.BoLo.no_step_val
  · exact (opTable_empty (by simp only [T0, rowTab_nil] at ht; exact ht)).elim
  · obtain ⟨K, n, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK, hT, -⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
    exact fun _ _ h => opPlug_no_step (r := false) (payloadName_opPayload n 0 v) hK h

/-- **Every run of a segment continues to its stop**, under the allocator that replays it. -/
theorem seg_demonic {μ₀ μ₁ : Heap} {x x₁ : Expr} (hg : Good d Q μ₀ x)
    (hs : Steps (ℍ := ℍ) μ₀ x μ₁ x₁) :
    ∃ μt t, Steps (ℍ := ℍ) μ₁ x₁ μt t ∧ PostD d Q μt t := by
  obtain ⟨ls, ρ, ρf, fρ, ps, hc, hf, hcf, hT, htg, hμ⟩ := hg
  have hw := ewp_unfold (divTab_mono _ _ _ _ _) (cwp_out ls x ρ hc)
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, -, -, hB,
    hT', htg', -, -, hC⟩ := hw ρf fρ ps hf hcf hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₅ hμ
  have hpost : PostD d Q μ' t := ⟨ls', ρ', ρf, ρp, fρ', fρ'p, ps', h₁, h₂, h₃, h₆, h₇, hB, hT',
    htg', hC⟩
  exact ⟨μ', t, (ARun.rest_final (post_final d Q hpost) hrun h₈).toSteps, hpost⟩

/-- **A segment's stop**: an answer, or a tick whose continuation at *next* is `Good`, at the
stop's resources, the garbage joining the frame. -/
theorem post_cases {μ : Heap} {t : Expr} (h : PostD d Q μ t) :
    (∃ v : Val, t = .val v) ∨
      ∃ K₁ : Kont, t = K₁.plug (tickE d) ∧ K₁.HasHnd d = false ∧ Good d Q μ (K₁.plug (.val nextV)) := by
  obtain ⟨ls', ρ', ρf, ρp, fρ', fρ'p, ps', h₁, h₂, h₃, h₆, h₇, hB, hT', htg', hC⟩ := h
  rcases hC with ⟨w, rfl, -⟩ | ht | ht
  · exact .inl ⟨w, rfl⟩
  · exact (opTable_empty (by simp only [T0, rowTab_nil] at ht; exact ht)).elim
  obtain ⟨K, n, i, v, en, hp⟩ := ht
  obtain ⟨⟨rfl, hK, hT, -⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
  obtain ⟨rfl, rfl⟩ := hA
  refine .inr ⟨K, rfl, hK, ?_⟩
  rw [eq_of_compS_empty_left hcak] at h₁ h₂
  have hk : cwp LSub.empty n T0 Q ls' (K.plug (.val nextV)) ρk :=
    ((hcont ls' (Ext.refl ls' ρk)).1 nextV PMap.empty ρk
      (Or.inl ⟨.unit, ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩)
      (ResU.comp_empty_right ρk)).1
  -- the garbage joins the frame (`wpG_bind`'s regrouping)
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρk).mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρk fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  exact ⟨ls', ρk, z, fρ'p, ps', hk, hz, hzY, hT', htg', h₇⟩

end


/-! ### The handler's steps after a tick -/

section chain
variable (d : UInt32) (K₁ : Kont) (ℓ : Loc)

/-- `κ` at its cell. -/
abbrev kap : Val := kapV ℓ (rtH d) K₁

/-- The resume frame `[·] next`. -/
abbrev nK : Kont := .appL .hole nextV

def c1 : Expr := .app (.val rtC) (.pair (.val .unit) (kappaCell false (rtH d) K₁))
def c2 : Expr := .app (.val rtC) (.pair (.val .unit)
  (.app (.val (Val.lam (kappaCBody false (rtH d) K₁))) (.val (Val.loc ℓ))))
def c3 : Expr := .app (.val rtC) (.val (Val.pair .unit (kap d K₁ ℓ)))
def c4 : Expr := .letpair (.val (Val.pair .unit (kap d K₁ ℓ)))
  (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV))
def c5 : Expr := (nK).plug (.app (kappaC false ℓ (rtH d) K₁) (.val (Val.inj₁ .unit)))
def c6 : Expr := (nK).plug (.case (.val (Val.inj₁ .unit))
  (Expr.subst 1 ((Val.inj₁ Val.unit).shift 1 0) (BoCa.Fig16.LogRel.Core.kResBr ℓ (rtH d) K₁))
  (Expr.subst 1 ((Val.inj₁ Val.unit).shift 1 0) (BoCa.Fig16.LogRel.Core.kCanBr false ℓ K₁)))
def c7 : Expr := (nK).plug (.seq (.val .unit) (.seq (freeE (.val (Val.loc ℓ)))
  (BoCa.Fig16.LogRel.Core.kResume (rtH d) K₁).1))
def c8 : Expr := (nK).plug (.seq (freeE (.val (Val.loc ℓ))) (BoCa.Fig16.LogRel.Core.kResume (rtH d) K₁).1)
def c9 : Expr := (nK).plug (.seq (.val .unit) (BoCa.Fig16.LogRel.Core.kResume (rtH d) K₁).1)
def c10 : Expr := .app (.val (BoCa.Fig16.LogRel.Core.kResume (rtH d) K₁)) (.val nextV)

theorem c3_c4 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c3 d K₁ ℓ) μ (c4 d K₁ ℓ) :=
  step1Only_plug (Head.beta μ _ _) rfl .hole

theorem c4_c5 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c4 d K₁ ℓ) μ (c5 d K₁ ℓ) := by
  have h := step1Only_plug (ℍ := ℍ) (Head.letpair μ .unit (kap d K₁ ℓ)
    (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV))) rfl .hole
  have e : (Expr.subst 0 Val.unit (Expr.subst 0 (Val.shift 1 0 (kap d K₁ ℓ))
      (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV)))) = c5 d K₁ ℓ := by
    simp [c5, kap, kapV, nextV, subst_shift_succ, Kont.plug]
  simp only [Kont.plug] at h
  rw [e] at h
  exact h

theorem c5_c6 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c5 d K₁ ℓ) μ (c6 d K₁ ℓ) :=
  kappaC_beta μ false ℓ (rtH d) K₁ (Val.inj₁ .unit) nK

theorem c6_c7 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c6 d K₁ ℓ) μ (c7 d K₁ ℓ) :=
  kappaC_case₁ μ false ℓ (rtH d) K₁ _ .unit nK

theorem c7_c8 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c7 d K₁ ℓ) μ (c8 d K₁ ℓ) :=
  step1Only_plug (Head.seq μ _) rfl nK

theorem c8_c9 {μ : Heap} (hℓ : μ ℓ = some Val.unit) :
    Step1Only (ℍ := ℍ) μ (c8 d K₁ ℓ) (μ.del ℓ) (c9 d K₁) := by
  have h := free_step1Only (ℍ := ℍ) hℓ (nK.comp (.seq .hole (BoCa.Fig16.LogRel.Core.kResume (rtH d) K₁).1))
  rw [Kont.plug_comp, Kont.plug_comp] at h
  exact h

theorem c9_c10 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c9 d K₁) μ (c10 d K₁) :=
  step1Only_plug (Head.seq μ _) rfl nK

theorem c10_end (μ : Heap) :
    Step1Only (ℍ := ℍ) μ (c10 d K₁) μ (hndE (rtH d) (K₁.plug (.val nextV))) :=
  step1Only_plug (BoCa.Fig16.LogRel.Core.kResume_beta μ (rtH d) K₁ nextV) rfl .hole

theorem c2_c3 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c2 d K₁ ℓ) μ (c3 d K₁ ℓ) :=
  kappaCell_beta μ .hole rtC .unit false ℓ (rtH d) K₁

theorem c1_steps {μ μ' : Heap} {e : Expr} :
    Step1 (ℍ := ℍ) μ (c1 d K₁) μ' e ↔ ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ Val.unit ∧ e = c2 d K₁ ℓ := by
  have e₁ := plug_kappaCell .hole rtC .unit false (rtH d) K₁
  simp only [Kont.plug] at e₁
  rw [c1, e₁, step1_alloc_iff]
  constructor
  · rintro ⟨ℓ, hℓ, rfl, rfl⟩
    exact ⟨ℓ, hℓ, rfl, by rw [plug_kappaCellLoc]; rfl⟩
  · rintro ⟨ℓ, hℓ, rfl, rfl⟩
    exact ⟨ℓ, hℓ, rfl, by rw [plug_kappaCellLoc]; rfl⟩

end chain

/-! ### The invariant -/

section inv
variable (d : UInt32) (Q : List SRec → Val → WProp)

/-- The handler's configurations after a tick of `K₁` at the memory `μt`. -/
def HS (K₁ : Kont) (μt μ : Heap) (e : Expr) : Prop :=
  (μ = μt ∧ e = c1 d K₁) ∨
  ∃ ℓ, μt ℓ = none ∧
    ((μ = μt.upd ℓ Val.unit ∧ (e = c2 d K₁ ℓ ∨ e = c3 d K₁ ℓ ∨ e = c4 d K₁ ℓ ∨ e = c5 d K₁ ℓ ∨
        e = c6 d K₁ ℓ ∨ e = c7 d K₁ ℓ ∨ e = c8 d K₁ ℓ)) ∨
      (μ = μt ∧ (e = c9 d K₁ ∨ e = c10 d K₁)))

/-- **The invariant** of a run under the runtime's handler. -/
inductive RT : Heap → Expr → Prop
  | seg {μ₀ μ : Heap} {x x₁ : Expr} : Good d Q μ₀ x → Steps (ℍ := ℍ) μ₀ x μ x₁ →
      RT μ (hndE (rtH d) x₁)
  | ret {μ : Heap} {v : Val} : RT μ (.app (.val rtR) (.val v))
  | val {μ : Heap} {v : Val} : RT μ (.val v)
  | hs {μt μ : Heap} {K₁ : Kont} {e : Expr} : Good d Q μt (K₁.plug (.val nextV)) →
      HS d K₁ μt μ e → RT μ e

theorem good_finDom {μ : Heap} {x : Expr} (h : Good d Q μ x) : Fig16.FinDom μ := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hμ⟩ := h
  exact lower_finDom hμ

/-- At a configuration of a segment with no step, the segment has stopped. -/
theorem seg_stopped {μ₀ μ : Heap} {x x₁ : Expr} (hg : Good d Q μ₀ x)
    (hs : Steps (ℍ := ℍ) μ₀ x μ x₁) (hno : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ x₁ μ₂ t₂) :
    PostD d Q μ x₁ := by
  obtain ⟨μt, t, hst, hp⟩ := seg_demonic d Q hg hs
  cases hst with
  | refl => exact hp
  | more h _ => exact (hno _ _ h).elim

theorem rt_safe {μ : Heap} {e : Expr} (h : RT (ℍ := ℍ) d Q μ e) :
    IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
  cases h with
  | @seg μ₀ _ x x₁ hg hs =>
      by_cases hx : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ x₁ μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hx
        exact .inr ⟨μ₂, _, h₂.plug (hndK (rtH d))⟩
      · simp only [not_exists] at hx
        rcases post_cases d Q (seg_stopped d Q hg hs hx) with ⟨v, rfl⟩ | ⟨K₁, rfl, hK, -⟩
        · exact .inr ⟨_, _, (catch_ret μ d _ _ _ v .hole).1⟩
        · exact .inr ⟨_, _, (catch_step μ (qs := qualsVal [.lin]) (hr := rtR) .unit (clauseAt_one rtC) hK .hole).1⟩
  | ret => exact .inr ⟨_, _, Step1.head (Head.beta μ _ _)⟩
  | @val _ v => exact .inl v.2
  | @hs μt _ K₁ e hg hh =>
      rcases hh with ⟨rfl, rfl⟩ | ⟨ℓ, hℓ, ⟨rfl, he⟩ | ⟨rfl, he⟩⟩
      · obtain ⟨ℓ, hℓ⟩ := BoCa.BoLo.finDom_block (good_finDom d Q hg)
        exact .inr ⟨_, _, (c1_steps d K₁).2 ⟨ℓ, by simpa using hℓ 0, rfl, rfl⟩⟩
      · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inr ⟨_, _, (c2_c3 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c3_c4 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c4_c5 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c5_c6 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c6_c7 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c7_c8 d K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c8_c9 d K₁ ℓ (by simp [BoCa.BoLo.Heap.upd])).1⟩
      · rcases he with rfl | rfl
        · exact .inr ⟨_, _, (c9_c10 d K₁ _).1⟩
        · exact .inr ⟨_, _, (c10_end d K₁ _).1⟩

theorem rt_step {μ μ' : Heap} {e e' : Expr} (h : RT (ℍ := ℍ) d Q μ e)
    (hs : Step1 (ℍ := ℍ) μ e μ' e') : RT (ℍ := ℍ) d Q μ' e' := by
  cases h with
  | @seg μ₀ _ x x₁ hg hx₁ =>
      by_cases hx : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ x₁ μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hx
        obtain ⟨x', rfl, h'⟩ := step1_plug_of_step (hndK (rtH d)) h₂ hs
        exact .seg hg (hx₁.trans (.one h'))
      · simp only [not_exists] at hx
        rcases post_cases d Q (seg_stopped d Q hg hx₁ hx) with ⟨v, rfl⟩ | ⟨K₁, rfl, hK, hg'⟩
        · obtain ⟨rfl, rfl⟩ := (catch_ret μ d _ _ _ v .hole).2 _ _ hs
          exact .ret
        · obtain ⟨rfl, rfl⟩ := (catch_step μ (qs := qualsVal [.lin]) (hr := rtR) .unit
            (clauseAt_one rtC) hK .hole).2 _ _ hs
          refine .hs hg' (.inl ⟨rfl, ?_⟩)
          simp only [Kont.plug]
          rw [kappaAt_lin]; rfl
  | ret =>
      obtain ⟨rfl, rfl⟩ := (step1Only_plug (ℍ := ℍ) (Head.beta μ _ _) rfl .hole).2 _ _ hs
      exact .val (v := _)
  | val => exact (BoCa.BoLo.no_step_val hs).elim
  | @hs μt _ K₁ e hg hh =>
      rcases hh with ⟨rfl, rfl⟩ | ⟨ℓ, hℓ, ⟨rfl, he⟩ | ⟨rfl, he⟩⟩
      · obtain ⟨ℓ, hℓ, rfl, rfl⟩ := (c1_steps d K₁).1 hs
        exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inl rfl⟩⟩)
      · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨rfl, rfl⟩ := (c2_c3 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inl rfl)⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c3_c4 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inl rfl))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c4_c5 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inl rfl)))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c5_c6 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inl rfl))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c6_c7 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inr (.inl rfl)))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c7_c8 d K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inr (.inr rfl)))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c8_c9 d K₁ ℓ (by simp [BoCa.BoLo.Heap.upd])).2 _ _ hs
          refine .hs hg (.inr ⟨ℓ, hℓ, .inr ⟨upd_del_of_none hℓ, .inl rfl⟩⟩)
      · rcases he with rfl | rfl
        · obtain ⟨rfl, rfl⟩ := (c9_c10 d K₁ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inr ⟨rfl, .inr rfl⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c10_end d K₁ _).2 _ _ hs
          exact .seg hg (.refl _ _)

end inv

/-- **Every prefix of every run under the runtime's clause** (§4.1 unknown 1 item 3): a closed
`M` at `F_{Div} A`, under `hnd_d H_rt`, from the empty memory: every configuration a run reaches
is an answer or takes a step. -/
theorem runtime_every_run {M : Expr} {d : UInt32} {A : VTy}
    (h : SemD LifeCtx.empty [] M d [] A) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (hndE (rtH d) M) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have hc := h LSub.empty [] [] PMap.empty (models_empty_any _) (gDenC_nil _ _)
  rw [show substAll [] M = M from Adequacy.psub_nil 0 M] at hc
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hg : Good d (fun ls v => vC true A ls LSub.empty v) Adequacy.emptyMem M :=
    ⟨[], PMap.empty, PMap.empty, PMap.empty, [], hc, Fig16.LogRel.hash_empty,
      ResU.comp_empty_right _, TW.empty, htg, Fig16.BoLo.lower_empty⟩
  have hrt : RT (ℍ := ℍ) d (fun ls v => vC true A ls LSub.empty v) Adequacy.emptyMem
      (hndE (rtH d) M) := .seg hg (.refl _ _)
  suffices ∀ {μ e μ' e'}, Steps (ℍ := ℍ) μ e μ' e' →
      RT (ℍ := ℍ) d (fun ls v => vC true A ls LSub.empty v) μ e →
      RT (ℍ := ℍ) d (fun ls v => vC true A ls LSub.empty v) μ' e' from
    rt_safe d _ (this hs hrt)
  intro μ e μ' e' hs' hr
  induction hs' with
  | refl => exact hr
  | more h₁ _ ih => exact ih (rt_step d _ hr h₁)

end BoCa.Fig16.LogRel.Core.DivEffect

end
