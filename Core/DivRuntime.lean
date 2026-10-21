import Core.DivPrograms
import Core.Alloc
import Core.Stale
import Core.EffMachine
import Core.Stdio

/-!
# Core — `Div`: the runtime's clause  `[spec §14]`

The runtime drives `main` as the outermost handler of `Div`: its clause resumes every tick with
*next*.

    H_rt = (divEff, (lin, (λv. v, (λ((), κ). κ next, ()))))

`runtime_every_run`: a closed `M` typed at `F_{Div} A`, under `hnd_Div H_rt`, from the empty
memory: no prefix of any run is stuck.  The run is infinite in general, so no `wp` covers it; the
proof is an invariant of configurations, closed under every step (`rt_step`), each of which steps
or is a value (`rt_safe`):

* `seg`: `hnd H_rt x₁`, `x₁` on a run of a segment `x` of `cwp` from a configuration the
  segment's `wp` holds at (`Good`).  The segment's `wp`, taken under the allocator that replays
  the run (`seg_demonic`, as `wpTS_demonic`), continues `x₁` to a term with no step: an answer
  (then `[ret]`) or a tick (then `[op]`);
* the handler's steps after a tick, each its configuration's only step (`catch_step`,
  `kappaCell_beta`, `kappaC_beta`, `kappaC_case₁`, `free_step1Only`, `kResume_beta`), but the
  cell's allocation, which takes any free location.  They end at `hnd H_rt K[next]`, which is
  `seg` again: the tick's continuation is in `cwp`, at the resources the segment's `wp` left;
* the answer's steps after `[ret]`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaCBody kappaAt clauseAt capTag freeE Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

namespace DivRuntime

/-! ### The runtime's handler -/

/-- `h_ret = λv. v`. -/
def rtR : Val := .lam (.var 0)

/-- The tick's clause `λ((), κ). κ next`. -/
def rtC : Val := .lam (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV)))

/-- The runtime's handler value. -/
def rtH : Val := hndVal divEff (qualsVal [.lin]) rtR (Val.pair rtC .unit)

/-- The table of the row of `Div` alone, at the grade `c`. -/
abbrev T0 (c : Bool) : OpTab := Row.tab [tickSigG c] LSub.empty

theorem T0_erase0 (c : Bool) : (T0 c).erase0 = OpTab.empty := by
  funext n i
  simp only [OpTab.erase0]
  split
  · rfl
  · rename_i h
    show Row.tab [tickSigG c] LSub.empty n i = _
    rw [Row.tab_tickG_ne c [] LSub.empty h]
    simp [Row.tab, Row.find, OpTab.empty]

theorem T0_divOK (c : Bool) : (T0 c).DivOK := Row.divOK_of_divB (Row.divB_tickG c []) LSub.empty

/-! ### A run of a segment continues to its stop -/

/-- **Prefix**, at an end that takes no step: `ARun.rest`, whose end there is a value. -/
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
variable (c : Bool) (Q : List SRec → Val → WProp)

/-- A configuration a segment's `wp` holds at: `x` in `cwp`, its frame, world and memory. -/
def Good (μ : Heap) (x : Expr) : Prop :=
  ∃ (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec), cwp (T0 c) Q ls x ρ ∧
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Lower fρ μ

/-- The configuration a segment's `wp` stops at: its post-configuration, at a term that is an
answer at `Q` or a tick owing `cwp`. -/
def PostD (μ : Heap) (t : Expr) : Prop :=
  ∃ (ls' : List SRec) (ρ' ρf ρp fρ' fρ'p : WRes) (ps' : List FrameRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.CompS fρ' ρp fρ'p ∧
    ResU.Lower fρ'p μ ∧ NoOwn ρp ∧ TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    (valPost Q ls' t ρ' ∨
      divTab (T0 c) Q (cwp (T0 c) Q) ls' t (fun ls e => ewpTS ls e (divTab (T0 c) Q (cwp (T0 c) Q)) Q) ρ')

/-- A stop of a segment takes no step. -/
theorem post_final {μ : Heap} {t : Expr} (h : PostD c Q μ t) :
    ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ t μ₂ t₂ := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, ht⟩ := h
  rcases ht with ⟨v, rfl, -⟩ | ht | ht
  · exact fun _ _ => BoCa.BoLo.no_step_val
  · exact (opTable_empty (by rw [T0_erase0 c] at ht; exact ht)).elim
  · obtain ⟨K, -, rfl, hK, -⟩ := tickStop_inv (T0_divOK c) ht
    exact fun _ _ h => opPlug_no_step (r := false) (p := opPayload divEff 0 .unit)
      (payloadName_opPayload divEff 0 .unit) hK h

/-- **Every run of a segment continues to its stop**, under the allocator that replays it. -/
theorem seg_demonic {μ₀ μ₁ : Heap} {x x₁ : Expr} (hg : Good c Q μ₀ x)
    (hs : Steps (ℍ := ℍ) μ₀ x μ₁ x₁) :
    ∃ μt t, Steps (ℍ := ℍ) μ₁ x₁ μt t ∧ PostD c Q μt t := by
  obtain ⟨ls, ρ, ρf, fρ, ps, hc, hf, hcf, hT, htg, hμ⟩ := hg
  have hw := ewp_unfold (divTab_mono _ _ _) (cwp_out hc)
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, -, -, hB,
    hT', htg', -, -, hC⟩ := hw ρf fρ ps hf hcf hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₅ hμ
  have hpost : PostD c Q μ' t := ⟨ls', ρ', ρf, ρp, fρ', fρ'p, ps', h₁, h₂, h₃, h₆, h₇, hB, hT',
    htg', hC⟩
  exact ⟨μ', t, (ARun.rest_final (post_final c Q hpost) hrun h₈).toSteps, hpost⟩

/-- **A segment's stop**: an answer, or a tick whose continuation at *next* is `Good`, at the
stop's resources, the garbage joining the frame. -/
theorem post_cases {μ : Heap} {t : Expr} (h : PostD c Q μ t) :
    (∃ v : Val, t = .val v ∧ ∃ ls ρ, Q ls v ρ) ∨
      ∃ K₁ : Kont, t = K₁.plug tickE ∧ K₁.HasHnd divEff = false ∧
        Good c Q μ (K₁.plug (.val nextV)) := by
  obtain ⟨ls', ρ', ρf, ρp, fρ', fρ'p, ps', h₁, h₂, h₃, h₆, h₇, hB, hT', htg', hC⟩ := h
  rcases hC with ⟨w, rfl, hw⟩ | ht | ht
  · exact .inl ⟨w, rfl, ls', ρ', hw⟩
  · exact (opTable_empty (by rw [T0_erase0 c] at ht; exact ht)).elim
  obtain ⟨K, en, rfl, hK, -, -, hcont⟩ := tickStop_inv (T0_divOK c) ht
  refine .inr ⟨K, rfl, hK, ?_⟩
  have hk : cwp (T0 c) Q ls' (K.plug (.val nextV)) ρ' :=
    (hcont ls' (Owed.refl _ ls' ρ') nextV (Or.inl rfl)).1
  -- the garbage joins the frame (`wpG_bind`'s regrouping)
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  exact ⟨ls', ρ', z, fρ'p, ps', hk, hz, hzY, hT', htg', h₇⟩

end

/-! ### The handler's steps after a tick -/

section chain
variable (K₁ : Kont) (ℓ : Loc)

/-- `κ` at its cell. -/
abbrev kap : Val := kapV ℓ rtH K₁

/-- The resume frame `[·] next`. -/
abbrev nK : Kont := .appL .hole nextV

def c1 : Expr := .app (.val rtC) (.pair (.val .unit) (kappaCell false rtH K₁))
def c2 : Expr := .app (.val rtC) (.pair (.val .unit)
  (.app (.val (Val.lam (kappaCBody false rtH K₁))) (.val (Val.loc ℓ))))
def c3 : Expr := .app (.val rtC) (.val (Val.pair .unit (kap K₁ ℓ)))
def c4 : Expr := .letpair (.val (Val.pair .unit (kap K₁ ℓ)))
  (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV))
def c5 : Expr := (nK).plug (.app (kappaC false ℓ rtH K₁) (.val (Val.inj₁ .unit)))
def c6 : Expr := (nK).plug (.case (.val (Val.inj₁ .unit))
  (Expr.subst 1 ((Val.inj₁ Val.unit).shift 1 0) (kResBr ℓ rtH K₁))
  (Expr.subst 1 ((Val.inj₁ Val.unit).shift 1 0) (kCanBr false ℓ K₁)))
def c7 : Expr := (nK).plug (.seq (.val .unit) (.seq (freeE (.val (Val.loc ℓ)))
  (kResume rtH K₁).1))
def c8 : Expr := (nK).plug (.seq (freeE (.val (Val.loc ℓ))) (kResume rtH K₁).1)
def c9 : Expr := (nK).plug (.seq (.val .unit) (kResume rtH K₁).1)
def c10 : Expr := .app (.val (kResume rtH K₁)) (.val nextV)

theorem c3_c4 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c3 K₁ ℓ) μ (c4 K₁ ℓ) :=
  step1Only_plug (Head.beta μ _ _) rfl .hole

theorem c4_c5 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c4 K₁ ℓ) μ (c5 K₁ ℓ) := by
  have h := step1Only_plug (ℍ := ℍ) (Head.letpair μ .unit (kap K₁ ℓ)
    (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV))) rfl .hole
  have e : (Expr.subst 0 Val.unit (Expr.subst 0 (Val.shift 1 0 (kap K₁ ℓ))
      (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val nextV)))) = c5 K₁ ℓ := by
    simp [c5, kap, kapV, nextV, subst_shift_succ, Kont.plug]
  simp only [Kont.plug] at h
  rw [e] at h
  exact h

theorem c5_c6 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c5 K₁ ℓ) μ (c6 K₁ ℓ) :=
  kappaC_beta μ false ℓ rtH K₁ (Val.inj₁ .unit) nK

theorem c6_c7 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c6 K₁ ℓ) μ (c7 K₁ ℓ) :=
  kappaC_case₁ μ false ℓ rtH K₁ _ .unit nK

theorem c7_c8 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c7 K₁ ℓ) μ (c8 K₁ ℓ) :=
  step1Only_plug (Head.seq μ _) rfl nK

theorem c8_c9 {μ : Heap} (hℓ : μ ℓ = some Val.unit) :
    Step1Only (ℍ := ℍ) μ (c8 K₁ ℓ) (μ.del ℓ) (c9 K₁) := by
  have h := free_step1Only (ℍ := ℍ) hℓ (nK.comp (.seq .hole (kResume rtH K₁).1))
  rw [Kont.plug_comp, Kont.plug_comp] at h
  exact h

theorem c9_c10 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c9 K₁) μ (c10 K₁) :=
  step1Only_plug (Head.seq μ _) rfl nK

theorem c10_end (μ : Heap) :
    Step1Only (ℍ := ℍ) μ (c10 K₁) μ (hndE rtH (K₁.plug (.val nextV))) :=
  step1Only_plug (kResume_beta μ rtH K₁ nextV) rfl .hole

theorem c2_c3 (μ : Heap) : Step1Only (ℍ := ℍ) μ (c2 K₁ ℓ) μ (c3 K₁ ℓ) :=
  kappaCell_beta μ .hole rtC .unit false ℓ rtH K₁

theorem c1_steps {μ μ' : Heap} {e : Expr} :
    Step1 (ℍ := ℍ) μ (c1 K₁) μ' e ↔ ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ Val.unit ∧ e = c2 K₁ ℓ := by
  have e₁ := plug_kappaCell .hole rtC .unit false rtH K₁
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
variable (c : Bool) (Q : List SRec → Val → WProp)

/-- The handler's configurations after a tick of `K₁` at the memory `μt`. -/
def HS (K₁ : Kont) (μt μ : Heap) (e : Expr) : Prop :=
  (μ = μt ∧ e = c1 K₁) ∨
  ∃ ℓ, μt ℓ = none ∧
    ((μ = μt.upd ℓ Val.unit ∧ (e = c2 K₁ ℓ ∨ e = c3 K₁ ℓ ∨ e = c4 K₁ ℓ ∨ e = c5 K₁ ℓ ∨
        e = c6 K₁ ℓ ∨ e = c7 K₁ ℓ ∨ e = c8 K₁ ℓ)) ∨
      (μ = μt ∧ (e = c9 K₁ ∨ e = c10 K₁)))

/-- **The invariant** of a run under the runtime's handler. -/
inductive RT : Heap → Expr → Prop
  | seg {μ₀ μ : Heap} {x x₁ : Expr} : Good c Q μ₀ x → Steps (ℍ := ℍ) μ₀ x μ x₁ →
      RT μ (hndE rtH x₁)
  | ret {μ : Heap} {v : Val} : (∃ ls ρ, Q ls v ρ) → RT μ (.app (.val rtR) (.val v))
  | val {μ : Heap} {v : Val} : (∃ ls ρ, Q ls v ρ) → RT μ (.val v)
  | hs {μt μ : Heap} {K₁ : Kont} {e : Expr} : Good c Q μt (K₁.plug (.val nextV)) →
      HS K₁ μt μ e → RT μ e

theorem good_finDom {μ : Heap} {x : Expr} (h : Good c Q μ x) : Fig16.FinDom μ := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hμ⟩ := h
  exact lower_finDom hμ

/-- At a configuration of a segment with no step, the segment has stopped. -/
theorem seg_stopped {μ₀ μ : Heap} {x x₁ : Expr} (hg : Good c Q μ₀ x)
    (hs : Steps (ℍ := ℍ) μ₀ x μ x₁) (hno : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ x₁ μ₂ t₂) :
    PostD c Q μ x₁ := by
  obtain ⟨μt, t, hst, hp⟩ := seg_demonic c Q hg hs
  cases hst with
  | refl => exact hp
  | more h _ => exact (hno _ _ h).elim

theorem rt_safe {μ : Heap} {e : Expr} (h : RT (ℍ := ℍ) c Q μ e) :
    IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
  cases h with
  | @seg μ₀ _ x x₁ hg hs =>
      by_cases hx : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ x₁ μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hx
        exact .inr ⟨μ₂, _, h₂.plug (hndK rtH)⟩
      · simp only [not_exists] at hx
        rcases post_cases c Q (seg_stopped c Q hg hs hx) with ⟨v, rfl, -⟩ | ⟨K₁, rfl, hK, -⟩
        · exact .inr ⟨_, _, (catch_ret μ divEff _ _ _ v .hole).1⟩
        · exact .inr ⟨_, _, (catch_step μ (qs := qualsVal [.lin]) (hr := rtR) .unit
            (clauseAt_one rtC) hK .hole).1⟩
  | ret _ => exact .inr ⟨_, _, Step1.head (Head.beta μ _ _)⟩
  | @val _ v _ => exact .inl v.2
  | @hs μt _ K₁ e hg hh =>
      rcases hh with ⟨rfl, rfl⟩ | ⟨ℓ, hℓ, ⟨rfl, he⟩ | ⟨rfl, he⟩⟩
      · obtain ⟨ℓ, hℓ⟩ := BoCa.BoLo.finDom_block (good_finDom c Q hg)
        exact .inr ⟨_, _, (c1_steps K₁).2 ⟨ℓ, by simpa using hℓ 0, rfl, rfl⟩⟩
      · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact .inr ⟨_, _, (c2_c3 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c3_c4 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c4_c5 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c5_c6 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c6_c7 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c7_c8 K₁ ℓ _).1⟩
        · exact .inr ⟨_, _, (c8_c9 K₁ ℓ (by simp [BoCa.BoLo.Heap.upd])).1⟩
      · rcases he with rfl | rfl
        · exact .inr ⟨_, _, (c9_c10 K₁ _).1⟩
        · exact .inr ⟨_, _, (c10_end K₁ _).1⟩

theorem rt_step {μ μ' : Heap} {e e' : Expr} (h : RT (ℍ := ℍ) c Q μ e)
    (hs : Step1 (ℍ := ℍ) μ e μ' e') : RT (ℍ := ℍ) c Q μ' e' := by
  cases h with
  | @seg μ₀ _ x x₁ hg hx₁ =>
      by_cases hx : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ x₁ μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hx
        obtain ⟨x', rfl, h'⟩ := step1_plug_of_step (hndK rtH) h₂ hs
        exact .seg hg (hx₁.trans (.one h'))
      · simp only [not_exists] at hx
        rcases post_cases c Q (seg_stopped c Q hg hx₁ hx) with ⟨v, rfl, hq⟩ | ⟨K₁, rfl, hK, hg'⟩
        · obtain ⟨rfl, rfl⟩ := (catch_ret μ divEff _ _ _ v .hole).2 _ _ hs
          exact .ret hq
        · obtain ⟨rfl, rfl⟩ := (catch_step μ (qs := qualsVal [.lin]) (hr := rtR) .unit
            (clauseAt_one rtC) hK .hole).2 _ _ hs
          refine .hs hg' (.inl ⟨rfl, ?_⟩)
          simp only [Kont.plug]
          rw [kappaAt_lin]; rfl
  | ret hq =>
      obtain ⟨rfl, rfl⟩ := (step1Only_plug (ℍ := ℍ) (Head.beta μ _ _) rfl .hole).2 _ _ hs
      exact .val (v := _) (by simpa [rtR, Expr.subst] using hq)
  | val _ => exact (BoCa.BoLo.no_step_val hs).elim
  | @hs μt _ K₁ e hg hh =>
      rcases hh with ⟨rfl, rfl⟩ | ⟨ℓ, hℓ, ⟨rfl, he⟩ | ⟨rfl, he⟩⟩
      · obtain ⟨ℓ, hℓ, rfl, rfl⟩ := (c1_steps K₁).1 hs
        exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inl rfl⟩⟩)
      · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨rfl, rfl⟩ := (c2_c3 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inl rfl)⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c3_c4 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inl rfl))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c4_c5 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inl rfl)))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c5_c6 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inl rfl))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c6_c7 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inr (.inl rfl)))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c7_c8 K₁ ℓ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inl ⟨rfl, .inr (.inr (.inr (.inr (.inr (.inr rfl)))))⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c8_c9 K₁ ℓ (by simp [BoCa.BoLo.Heap.upd])).2 _ _ hs
          refine .hs hg (.inr ⟨ℓ, hℓ, .inr ⟨upd_del_of_none hℓ, .inl rfl⟩⟩)
      · rcases he with rfl | rfl
        · obtain ⟨rfl, rfl⟩ := (c9_c10 K₁ _).2 _ _ hs
          exact .hs hg (.inr ⟨ℓ, hℓ, .inr ⟨rfl, .inr rfl⟩⟩)
        · obtain ⟨rfl, rfl⟩ := (c10_end K₁ _).2 _ _ hs
          exact .seg hg (.refl _ _)

/-- A value the invariant reaches is an answer. -/
theorem rt_val {μ : Heap} {e : Expr} {v : Val} (h : RT (ℍ := ℍ) c Q μ e) (hv : e = v.1) :
    ∃ ls ρ, Q ls v ρ := by
  have hve : IsVal e := hv ▸ v.2
  cases h with
  | seg => simp [hndE] at hve
  | ret => simp [rtR] at hve
  | @val _ w hq => exact (Subtype.ext hv : w = v) ▸ hq
  | @hs μt _ K₁ e hg hh =>
      exfalso
      rcases hh with ⟨-, rfl⟩ | ⟨ℓ, -, ⟨-, he⟩ | ⟨-, he⟩⟩
      · simp [c1, rtC] at hve
      · rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [c2, c3, c4, c5, c6, c7, c8, rtC, Kont.plug] at hve
      · rcases he with rfl | rfl <;> simp [c9, c10, kResume, Kont.plug] at hve

end inv

end DivRuntime

open DivRuntime in
/-- **Every prefix of every run under the runtime's clause, from `cwp`**: a computation in `cwp`
at the table of `Div` alone, at either grade, at the empty resource and list, under
`hnd_Div H_rt`, from the empty memory: every configuration a run reaches is an answer or takes a
step.  `[spec §14, §48]` -/
theorem runtime_every_run_cwp (c : Bool) {M : Expr} {Q : List SRec → Val → WProp}
    (hc : cwp (T0 c) Q [] M PMap.empty) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (hndE rtH M) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hg : DivRuntime.Good c Q Adequacy.emptyMem M :=
    ⟨[], PMap.empty, PMap.empty, PMap.empty, [], hc, Fig16.LogRel.hash_empty,
      ResU.comp_empty_right _, TW.empty, htg, Fig16.BoLo.lower_empty⟩
  have hrt : DivRuntime.RT (ℍ := ℍ) c Q Adequacy.emptyMem (hndE rtH M) := .seg hg (.refl _ _)
  suffices ∀ {μ e μ' e'}, Steps (ℍ := ℍ) μ e μ' e' →
      DivRuntime.RT (ℍ := ℍ) c Q μ e → DivRuntime.RT (ℍ := ℍ) c Q μ' e' from
    DivRuntime.rt_safe c _ (this hs hrt)
  intro μ e μ' e' hs' hr
  induction hs' with
  | refl => exact hr
  | more h₁ _ ih => exact ih (DivRuntime.rt_step c _ hr h₁)

open DivRuntime in
/-- **Every prefix of every run under the runtime's clause**: a closed `M` typed at `F_{Div} A`,
`tick` at either grade, under `hnd_Div H_rt`, from the empty memory: every configuration a run
reaches is an answer or takes a step.  The relation at `M`'s row is `cwp` (`effWp`), by the
Fundamental Property.  `[spec §14, §48]` -/
theorem runtime_every_run (c : Bool) {M : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty [] M (.comp (CTy.effOf [tickSigG c] A))) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (hndE rtH M) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have hwp := fundamentalC (ℍ := ℍ) h LSub.empty [] [] PMap.empty Adequacy.models_empty
    (gDenC_nil _ _)
  rw [show substAll [] M = M from Adequacy.psub_nil 0 M] at hwp
  have hc := (cC_effOf_wp [tickSigG c] A [] LSub.empty M PMap.empty).mp hwp
  rw [Row.divB_tickG] at hc
  exact runtime_every_run_cwp c hc hs

namespace DivRuntime

/-! ### `main`'s answer read off

The runtime's clause never answers a tick *close*, so a `main` of `F_{Div}(A ⊕ B)` it drives
answers `inj₁ a`; the run reads `a` off with `λx. case x {inj₁ a. a | inj₂ _. Ω}`. -/

/-- `Ω = (λx. x x)(λx. x x)`, whose only step is to itself. -/
def omegaE : Expr := .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

/-- `case x {inj₁ a. a | inj₂ _. Ω}`, `x` the variable `0`. -/
def ansBody : Expr := .case (.var 0) (.var 0) omegaE

/-- `main` under the runtime's clause, its answer read off: `(λx. ansBody) (hnd_Div H_rt M)`.
`[spec §48]` -/
def rtMain (M : Expr) : Expr := .app (.lam ansBody) (hndE rtH M)

theorem omega_only (μ : Heap) : Step1Only (ℍ := ℍ) μ omegaE μ omegaE := by
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ (.app (.var 0) (.var 0))
    (Val.lam (.app (.var 0) (.var 0)))) rfl .hole
  simpa [omegaE, Expr.subst, Kont.plug] using h

theorem ans_beta (μ : Heap) (v : Val) :
    Step1Only (ℍ := ℍ) μ (.app (.lam ansBody) (.val v)) μ (.case (.val v) (.var 0) omegaE) := by
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ ansBody v) rfl .hole
  simpa [ansBody, omegaE, Expr.subst, Kont.plug] using h

theorem ans_case₁ (μ : Heap) (a : Val) :
    Step1Only (ℍ := ℍ) μ (.case (.val (Val.inj₁ a)) (.var 0) omegaE) μ (.val a) := by
  have h := step1Only_plug (ℍ := ℍ) (Head.case₁ μ a (.var 0) omegaE) rfl .hole
  simpa [Expr.subst, Kont.plug] using h

theorem ans_case₂ (μ : Heap) (b : Val) :
    Step1Only (ℍ := ℍ) μ (.case (.val (Val.inj₂ b)) (.var 0) omegaE) μ omegaE := by
  have h := step1Only_plug (ℍ := ℍ) (Head.case₂ μ b (.var 0) omegaE) rfl .hole
  simpa [omegaE, Expr.subst, Kont.plug] using h

section wrap
variable (c : Bool) (Q : List SRec → Val → WProp)

/-- The invariant of a run of `rtMain M`: under the reading-off, `RT`; the reading-off of an
answer; a value; `Ω`. -/
inductive RTW : Heap → Expr → Prop
  | inner {μ : Heap} {x : Expr} : RT (ℍ := ℍ) c Q μ x → RTW μ (.app (.lam ansBody) x)
  | ans {μ : Heap} {v : Val} : (∃ ls ρ, Q ls v ρ) → RTW μ (.case (.val v) (.var 0) omegaE)
  | done {μ : Heap} {v : Val} : RTW μ (.val v)
  | omega {μ : Heap} : RTW μ omegaE

variable (hQ : ∀ ls v ρ, Q ls v ρ → (∃ a, v = Val.inj₁ a) ∨ (∃ b, v = Val.inj₂ b))
include hQ

theorem rtw_safe {μ : Heap} {e : Expr} (h : RTW (ℍ := ℍ) c Q μ e) :
    IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
  cases h with
  | @inner x hx =>
      rcases rt_safe c Q hx with hv | ⟨μ', x', hs⟩
      · exact .inr ⟨_, _, (ans_beta μ ⟨x, hv⟩).1⟩
      · exact .inr ⟨μ', _, hs.plug (.appR (.lam ansBody) .hole)⟩
  | @ans v hv =>
      obtain ⟨ls, ρ, hq⟩ := hv
      rcases hQ ls v ρ hq with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact .inr ⟨_, _, (ans_case₁ μ a).1⟩
      · exact .inr ⟨_, _, (ans_case₂ μ b).1⟩
  | @done v => exact .inl v.2
  | omega => exact .inr ⟨_, _, (omega_only μ).1⟩

theorem rtw_step {μ μ' : Heap} {e e' : Expr} (h : RTW (ℍ := ℍ) c Q μ e)
    (hs : Step1 (ℍ := ℍ) μ e μ' e') : RTW (ℍ := ℍ) c Q μ' e' := by
  cases h with
  | @inner x hx =>
      by_cases hv : IsVal x
      · obtain ⟨rfl, rfl⟩ := (ans_beta μ ⟨x, hv⟩).2 _ _ hs
        exact .ans (rt_val c Q hx (v := ⟨x, hv⟩) rfl)
      · obtain ⟨x', rfl, hx'⟩ := step1_plug_inv (.appR (.lam ansBody) .hole) rfl hv hs
        exact .inner (rt_step c Q hx hx')
  | @ans v hv =>
      obtain ⟨ls, ρ, hq⟩ := hv
      rcases hQ ls v ρ hq with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · obtain ⟨rfl, rfl⟩ := (ans_case₁ μ a).2 _ _ hs
        exact .done
      · obtain ⟨rfl, rfl⟩ := (ans_case₂ μ b).2 _ _ hs
        exact .omega
  | done => exact (BoCa.BoLo.no_step_val hs).elim
  | omega =>
      obtain ⟨rfl, rfl⟩ := (omega_only μ).2 _ _ hs
      exact .omega

end wrap

end DivRuntime

open DivRuntime in
/-- **Every prefix of every run of `main` under the runtime's clause, its answer read off**:
a computation in `cwp` at the table of `Div` alone, at either grade, whose answers are
injections: every configuration a run of `rtMain M` from the empty memory reaches is a value or
takes a step.  `[spec §14, §48]` -/
theorem runtime_main_every_run_cwp (c : Bool) {M : Expr} {Q : List SRec → Val → WProp}
    (hQ : ∀ ls v ρ, Q ls v ρ → (∃ a, v = Val.inj₁ a) ∨ (∃ b, v = Val.inj₂ b))
    (hc : cwp (T0 c) Q [] M PMap.empty) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (rtMain M) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hg : DivRuntime.Good c Q Adequacy.emptyMem M :=
    ⟨[], PMap.empty, PMap.empty, PMap.empty, [], hc, Fig16.LogRel.hash_empty,
      ResU.comp_empty_right _, TW.empty, htg, Fig16.BoLo.lower_empty⟩
  have hrt : DivRuntime.RTW (ℍ := ℍ) c Q Adequacy.emptyMem (rtMain M) :=
    .inner (.seg hg (.refl _ _))
  suffices ∀ {μ e μ' e'}, Steps (ℍ := ℍ) μ e μ' e' →
      DivRuntime.RTW (ℍ := ℍ) c Q μ e → DivRuntime.RTW (ℍ := ℍ) c Q μ' e' from
    DivRuntime.rtw_safe c Q hQ (this hs hrt)
  intro μ e μ' e' hs' hr
  induction hs' with
  | refl => exact hr
  | more h₁ _ ih => exact ih (DivRuntime.rtw_step c Q hQ hr h₁)

open DivRuntime in
/-- **Every prefix of every run of a closed `main` under the runtime's clause, its answer read
off**: a closed `M` typed at `F_{Div}(A ⊕ B)`, `tick` at either grade: every configuration a run
of `rtMain M` from the empty memory reaches is a value or takes a step.  `[spec §14, §48]` -/
theorem runtime_main_every_run (c : Bool) {M : Expr} {A B : VTy}
    (h : CDerives LifeCtx.empty [] M (.comp (CTy.effOf [tickSigG c] (.sum A B))))
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (rtMain M) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have hwp := fundamentalC (ℍ := ℍ) h LSub.empty [] [] PMap.empty Adequacy.models_empty
    (gDenC_nil _ _)
  rw [show substAll [] M = M from Adequacy.psub_nil 0 M] at hwp
  have hc := (cC_effOf_wp [tickSigG c] (.sum A B) [] LSub.empty M PMap.empty).mp hwp
  rw [Row.divB_tickG] at hc
  refine runtime_main_every_run_cwp c (fun ls v ρ hv => ?_) hc hs
  rcases hv with ⟨a, -, -, -, ⟨-, rfl⟩, -⟩ | ⟨b, -, -, -, ⟨-, rfl⟩, -⟩
  · exact .inl ⟨a, rfl⟩
  · exact .inr ⟨b, rfl⟩

open DivRuntime in
/-- **The IO run under the runtime's clause**: `run_io : Bytes ⊸ F_{Div}(R ⊕ R′)`, `tick` at
either grade, checked at a context of externs that meet their contracts (`ExternsMeet`): for
every input byte list, every configuration a run of `rtMain (run_io[γ] inp)` from the empty
memory reaches is a value or takes a step.  `[spec §11, §14, §48]` -/
theorem io_rt_every_run (c : Bool) {Γ : Ctx VTy} {e : Expr} {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ e
      (.comp (.arr bytesTy (CTy.effOf [tickSigG c] (.sum R R')))))
    {γ : List Val} (hγ : ExternsMeet Γ γ) {inp : Val} (hin : BytesV inp)
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (rtMain (.app (substAll γ e) (.val inp))) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂ := by
  have hsem := fundamentalC (ℍ := ℍ) h LSub.empty γ [] PMap.empty Adequacy.models_empty
    (gDenC_of_meets hγ [] LSub.empty)
  have hwp := hsem inp PMap.empty PMap.empty (vC_bytes_iff.mpr ⟨rfl, hin⟩)
    (ResU.comp_empty_right _)
  have hc := (cC_effOf_wp [tickSigG c] (.sum R R') [] LSub.empty _ PMap.empty).mp hwp
  rw [Row.divB_tickG] at hc
  refine runtime_main_every_run_cwp c (fun ls v ρ hv => ?_) hc hs
  rcases hv with ⟨a, -, -, -, ⟨-, rfl⟩, -⟩ | ⟨b, -, -, -, ⟨-, rfl⟩, -⟩
  · exact .inl ⟨a, rfl⟩
  · exact .inr ⟨b, rfl⟩

end BoCa.Fig16.LogRel.Core

end
