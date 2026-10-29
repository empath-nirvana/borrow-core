import Core.EffFin
import Core.Nu
import Core.Arrays

/-!
# Core — `iterate`  `[spec §14]`

    iterate : !U(!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R) ⊗ S ⊸ F_Σ(B ⊕ R))        Σ holds Div

    iterate (f, s) ↦ (f s).1 to r. case r { inl b → inl b
                                          | inr s′ → tick () to n. case n { inl _ → iterate (f, s′)
                                                                          | inr _ → inr ((f s′).2) } }

One machine step, `Head.iterate` (`Support/Dynamics/Iterate.lean`).  `f` is the step: one turn
(`.1`, *next*) or the residual (`.2`, *close*).  `iterate` ticks at each back edge, so every
iteration is guarded, whoever wrote the step.

`cwp_iterate` is its compatibility, by coinduction: the candidate holds `iterate (f, s)` and the
point after a *next*, at every state of the step's relation, and the frame of the turn around
every computation of `cwp`.  `Closing` needs no induction: answered *close*, the tick after a turn
runs `(f s′).2`, a computation of `cwp`, so of `Closing`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The steps -/

/-- `iterate (f, s)`. -/
abbrev iterE (f s : Val) : Expr := .app (.val (.prim .iterate)) (.val (Val.pair f s))

/-- The turn's observation `(f s).1`. -/
def obsN (f s : Val) : Expr := .app (.app (.val f) (.val s)) (.val nextV)

/-- The close observation `(f s).2`. -/
def obsC (f s : Val) : Expr := .app (.app (.val f) (.val s)) (.val closeV)

/-- The frame of a turn: `[·] to r. case r { inl b → inl b | inr s′ → tick () to n. … }`. -/
def iterK (f : Val) : Kont := .case .hole (.inj₁ (.var 0)) (.app (.val (.lam (iterTurn f))) tickE)

/-- The frame of the tick, the state `s′` in it. -/
def turnK (f s' : Val) : Kont := .appR (.val (.lam ((iterTurn f).subst 1 (s'.shift 1 0)))) .hole

theorem tickE_closed : closedAt 0 tickE = true := rfl

theorem tickE_eq : tickE = performE (.val (opPayload divEff 0 .unit)) := rfl

theorem iter_step (f s : Val) : PureSteps (iterE f s) ((iterK f).plug (obsN f s)) :=
  PureSteps.head (fun μ => Head.iterate μ f s) rfl

theorem iterK_inl (f b : Val) :
    PureSteps ((iterK f).plug (.val (Val.inj₁ b))) (.val (Val.inj₁ b)) := by
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp
  exact .refl

theorem iterK_inr (f s' : Val) :
    PureSteps ((iterK f).plug (.val (Val.inj₂ s'))) ((turnK f s').plug tickE) := by
  refine (PureSteps.head (fun μ => Head.case₂ μ s' _ _) rfl).trans ?_
  simp [Kont.plug, turnK, subst_closedAt _ s' tickE_closed]
  exact .refl

theorem turnK_next (f s' : Val) : PureSteps ((turnK f s').plug (.val nextV)) (iterE f s') := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  simp [subst_shift_succ, nextV, iterE, Val.pair]
  exact .refl

theorem turnK_close (f s' : Val) :
    PureSteps ((turnK f s').plug (.val closeV)) (.app (.val inrV) (obsC f s')) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  simp [subst_shift_succ, closeV, inrV, obsC]
  exact .refl

theorem inrV_steps (r : Val) : PureSteps (.app (.val inrV) (.val r)) (.val (Val.inj₂ r)) := by
  refine (PureSteps.beta _ _).trans ?_
  simp
  exact .refl

/-! ### Steps and ticks at `cwp` -/

theorem cwp_pureSteps {T : OpTab} {Q : List SRec → Val → WProp} {e e' : Expr}
    (h : PureSteps e e') {ls : List SRec} {ρ : WRes} (h' : cwp T Q ls e' ρ) : cwp T Q ls e ρ :=
  cwp_roll (ewp_pureSteps (divTab_mono _ _ _) h _ _ ρ (cwp_out h'))

/-- `ewp_frame_plain`'s frame conditions at the empty frame, from `PlainCancel`. -/
theorem emp_conds {T : OpTab} (hPC : T.PlainCancel) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) :
    (∀ n i en, T n i = some en → en.abort = true → ∀ (ls : List SRec) ρ,
      (fun _ => emp : List SRec → WProp) ls ρ → NoOwn ρ) ∧
    (∀ n i en, T n i = some en → en.q = .unr → ∀ (ls : List SRec) ρ,
      (fun _ => emp : List SRec → WProp) ls ρ → ρ = PMap.empty) ∧
    (∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → (fun _ => emp : List SRec → WProp) ls σ →
        ResU.CompS ρ σ ρ' → cancelOK en ls (K.comp K₁) ρ') := by
  refine ⟨fun _ _ _ _ _ _ ρ h => h.1 ▸ noOwn_empty, fun _ _ _ _ _ _ ρ h => h.1, ?_⟩
  intro n i en hT ha hq ls K₁ ρ σ ρ' hcan hσ hc
  obtain ⟨rfl, -⟩ := hσ
  rw [compS_empty_eq hc]
  exact hPC n i en hT ha hq K hH (hC 0) ls K₁ ρ hcan

/-- **A tick in a frame `K`**, one segment: the stop owes `K` at each answer to `owe Y`. -/
theorem cwpF_tickK {T : OpTab} {en : OpEnt} (hT0 : T divEff 0 = some en) (ht : en.IsTick)
    {Q : List SRec → Val → WProp} {Y : List SRec → Expr → WProp}
    (K : Kont) (hK : K.HasHnd divEff = false) {ls : List SRec} {ρ : WRes}
    (h : ∀ ls', Owed en ls ls' ρ → ∀ w : Val, w = nextV ∨ w = closeV →
      owe T Q Y ls' (K.plug (.val w)) ρ) :
    cwpF T Q Y ls (K.plug tickE) ρ :=
  ewp_fold (divTab_mono _ _ _) (wpG_here _ _ _ _ (Or.inr (Or.inr (tickStop_mk hT0 ht K hK h))))

/-- **A tick in a frame `K`**, closing: the stop owes `K` at *close*. -/
theorem closing_tickK {T : OpTab} {en : OpEnt} (hT0 : T divEff 0 = some en) (ht : en.IsTick)
    {Q : List SRec → Val → WProp} (K : Kont) (hK : K.HasHnd divEff = false) {ls : List SRec}
    {ρ : WRes} (h : ∀ ls', Owed en ls ls' ρ → Closing T Q ls' (K.plug (.val closeV)) ρ) :
    Closing T Q ls (K.plug tickE) ρ := by
  have hcs : contShare en.closeOnly ls K (fun ls e => Closing T Q ls e) ρ := by
    refine ⟨fun h => ?_, fun ls' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun h => absurd ht.1 h⟩⟩
    · have h' : en.q = .unr := h; rw [ht.1] at h'; cases h'
    · obtain ⟨⟨-, rfl⟩, rfl⟩ := And.intro ((ht.2.2.2 ls' w τ₁).mp hB.1) hB.2
      rw [compS_empty_eq hc]
      exact h ls' he
  refine ewp_fold (opTable_mono _) (wpG_here _ _ _ _ (Or.inr (Or.inl
    ⟨K, divEff, 0, .unit, en.closeOnly, pure_sep_mk ⟨rfl, hK, by rw [OpTab.closeAt_key, hT0]; rfl,
      ht.2.1⟩ ⟨PMap.empty, ρ, compS_empty_left ρ, (ht.2.2.1 ls .unit _).mpr ⟨rfl, rfl⟩, hcs⟩⟩)))

/-! ### Compatibility -/

theorem iterK_plain (f : Val) :
    (∀ n, (iterK f).HasHnd n = false) ∧ (∀ n, (iterK f).Catches n = false) :=
  ⟨fun n => by simp [iterK, Kont.HasHnd], fun n => by simp [iterK, Kont.Catches]⟩

theorem turnK_hasHnd (f s : Val) (n : UInt32) : (turnK f s).HasHnd n = false := by
  simp [turnK, Kont.HasHnd]

theorem inrK_plain : (∀ n, (Kont.appR (.val inrV) .hole).HasHnd n = false) ∧
    (∀ n, (Kont.appR (.val inrV) .hole).Catches n = false) :=
  ⟨fun n => by simp [Kont.HasHnd, inrV], fun n => by simp [Kont.Catches, inrV]⟩

/-- What a turn answers: the result `inl b`, or the next state `inr s`. -/
def stepPost (QB VS : List SRec → Val → WProp) : List SRec → Val → WProp := fun ls v ρ =>
  (∃ b, v = Val.inj₁ b ∧ QB ls b ρ) ∨ (∃ s, v = Val.inj₂ s ∧ VS ls s ρ)

section
variable {T : OpTab} (hT : T.DivOK) {en : OpEnt} (hT0 : T divEff 0 = some en)
  (hPC : T.PlainCancel) (f : Val) (QB QR VS : List SRec → Val → WProp)

include hT hPC in
/-- The close path: `inr ((f s).2)`. -/
theorem cwp_closePath {ls : List SRec} {s : Val} {ρ : WRes} (h : cwp T QR ls (obsC f s) ρ) :
    cwp T (stepPost QB QR) ls (.app (.val inrV) (obsC f s)) ρ := by
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ inrK_plain.1 inrK_plain.2
  exact cwp_bind hT (.appR (.val inrV) .hole) inrK_plain.1 inrK_plain.2 (fun _ => emp)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hW hU hK QR _
    (fun ls v σ hσ => cwp_pureSteps (inrV_steps v)
      (cwp_of_ewp hT.keyNA (ewp_val (opTable_mono T) (Or.inr ⟨v, rfl, sep_emp_elim hσ⟩)))) h
    ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)

include hT hT0 hPC in
/-- **`iterate (f, s)` is in `Closing`**: answered *close*, the tick after a turn runs the close
path once. -/
theorem closing_iterate
    (hstep : ∀ ls s ρ, VS ls s ρ →
      cwp T (stepPost QB VS) ls (obsN f s) ρ ∧ cwp T QR ls (obsC f s) ρ)
    (hVS : ∀ ls ls' s ρ, Ext ls ls' ρ → VS ls s ρ → VS ls' s ρ)
    {ls : List SRec} {s : Val} {ρ : WRes} (hs : VS ls s ρ) :
    Closing T (stepPost QB QR) ls (iterE f s) ρ := by
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ (iterK_plain f).1 (iterK_plain f).2
  refine ewp_pureSteps (opTable_mono _) (iter_step f s) _ _ ρ ?_
  refine closing_frame (OpTab.Le.refl _) (iterK f) (iterK_plain f).1 (iterK_plain f).2 (fun _ => emp)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hW hU hK (stepPost QB VS) _ ?_
    (closing_of_cwp (hstep ls s ρ hs).1) (ρ₂ := PMap.empty) ⟨rfl, trivial⟩
    (ResU.comp_empty_right ρ)
  intro ls' v σ hσ
  rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
  · exact ewp_pureSteps (opTable_mono _) (iterK_inl f b) _ _ σ
      (ewp_val (opTable_mono _) (Or.inl ⟨b, rfl, hb⟩))
  · refine ewp_pureSteps (opTable_mono _) (iterK_inr f s') _ _ σ
      (closing_tickK hT0 (hT en hT0) _ (turnK_hasHnd f s' divEff) fun ls'' he => ?_)
    exact ewp_pureSteps (opTable_mono _) (turnK_close f s') _ _ σ (closing_of_cwp
      (cwp_closePath hT hPC f QB QR (hstep ls'' s' σ (hVS _ _ _ _ he.ext hs')).2))

include hT hT0 hPC in
/-- **`iterate`'s compatibility**, by coinduction up to `cwp`.  The candidate: `iterate (f, s)`
and the point after a *next*, at every state of `VS`; and the frame of a turn around every
computation of `cwp`.  A turn is `cwpF_frame`; its answer `inl b` finishes; its answer `inr s′`
ticks, and the tick owes the point after a *next* (in the candidate) and the close path (in
`cwp`, `cwp_closePath`), each in `Closing` (`closing_iterate`).  `[spec §14]` -/
theorem cwp_iterate
    (hstep : ∀ ls s ρ, VS ls s ρ →
      cwp T (stepPost QB VS) ls (obsN f s) ρ ∧ cwp T QR ls (obsC f s) ρ)
    (hVS : ∀ ls ls' s ρ, Ext ls ls' ρ → VS ls s ρ → VS ls' s ρ)
    {ls : List SRec} {s : Val} {ρ : WRes} (hs : VS ls s ρ) :
    cwp T (stepPost QB QR) ls (iterE f s) ρ := by
  have ht := hT en hT0
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ (iterK_plain f).1 (iterK_plain f).2
  let W₁ : List SRec → Expr → WProp := fun ls x ρ => ∃ s,
    (x = iterE f s ∨ x = (turnK f s).plug (.val nextV)) ∧ VS ls s ρ
  let W₂ : List SRec → Expr → WProp := fun ls x ρ => ∃ e, x = (iterK f).plug e ∧
    cwp T (stepPost QB VS) ls e ρ
  let W : List SRec → Expr → WProp := fun ls x ρ => W₁ ls x ρ ∨ W₂ ls x ρ
  let Y : List SRec → Expr → WProp := fun ls x ρ => W ls x ρ ∨ cwp T (stepPost QB QR) ls x ρ
  -- the frame of a turn, one segment
  have h₂ : ∀ ls e ρ, cwp T (stepPost QB VS) ls e ρ →
      cwpF T (stepPost QB QR) Y ls ((iterK f).plug e) ρ := by
    intro ls e ρ he
    refine cwpF_frame hT hT (OpTab.Le.refl T) (iterK f) (iterK_plain f).1 (iterK_plain f).2 (fun _ => emp)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hW hU hK (stepPost QB VS) _ Y ?_ ?_ ?_ he
      (ρ₂ := PMap.empty) ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
    · intro ls e ρ ρ₂ ρ' he hF hc
      obtain ⟨rfl, -⟩ := hF
      rw [compS_empty_eq hc]
      exact Or.inl (Or.inr ⟨e, rfl, he⟩)
    · intro ls' v σ hσ
      rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
      · exact ewp_pureSteps (divTab_mono _ _ _) (iterK_inl f b) _ _ σ
          (ewp_val (divTab_mono _ _ _) (Or.inl ⟨b, rfl, hb⟩))
      · refine ewp_pureSteps (divTab_mono _ _ _) (iterK_inr f s') _ _ σ
          (cwpF_tickK hT0 ht _ (turnK_hasHnd f s' divEff) fun ls'' he w hw => ?_)
        have hs'' := hVS _ _ _ _ he.ext hs'
        rcases hw with rfl | rfl
        · exact ⟨Or.inl (Or.inl ⟨s', Or.inr rfl, hs''⟩),
            ewp_pureSteps (opTable_mono _) (turnK_next f s') _ _ σ
              (closing_iterate hT hT0 hPC f QB QR VS hstep hVS hs'')⟩
        · have hc := cwp_pureSteps (turnK_close f s')
            (cwp_closePath hT hPC f QB QR (hstep ls'' s' σ hs'').2)
          exact ⟨Or.inr hc, closing_of_cwp hc⟩
    · intro ls' v σ hσ
      rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
      · exact ewp_pureSteps (opTable_mono _) (iterK_inl f b) _ _ σ
          (ewp_val (opTable_mono _) (Or.inl ⟨b, rfl, hb⟩))
      · refine ewp_pureSteps (opTable_mono _) (iterK_inr f s') _ _ σ
          (closing_tickK hT0 ht _ (turnK_hasHnd f s' divEff) fun ls'' he => ?_)
        exact ewp_pureSteps (opTable_mono _) (turnK_close f s') _ _ σ (closing_of_cwp
          (cwp_closePath hT hPC f QB QR (hstep ls'' s' σ (hVS _ _ _ _ he.ext hs')).2))
  have hW' : ∀ ls x ρ, W ls x ρ → cwpF T (stepPost QB QR) Y ls x ρ := by
    rintro ls x ρ (⟨s, hx, hs⟩ | ⟨e, rfl, he⟩)
    · have h := ewp_pureSteps (divTab_mono _ _ _) (iter_step f s) _ _ ρ
        (h₂ ls _ ρ (hstep ls s ρ hs).1)
      rcases hx with rfl | rfl
      · exact h
      · exact ewp_pureSteps (divTab_mono _ _ _) (turnK_next f s) _ _ ρ h
    · exact h₂ ls e ρ he
  exact cwp_coind_up hW' (Or.inl ⟨s, Or.inl rfl, hs⟩)

end

/-! ### The constant -/

/-- The step's type, `!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R)`.  `[spec §14]` -/
abbrev iterStepTy (Sg : Row) (St B R : VTy) : VTy :=
  .bang (.thunk (.arr St (.amp (CTy.effOf Sg (.sum B St)) (CTy.effOf Sg R))))

/-- `iterate : !U(!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R) ⊗ S ⊸ F_Σ(B ⊕ R))`.  `[spec §14]` -/
abbrev iterTy (Sg : Row) (St B R : VTy) : VTy :=
  .bang (.thunk (.arr (.tensor (iterStepTy Sg St B R) St) (CTy.effOf Sg (.sum B R))))

/-- `𝒱⟦A ⊕ B⟧` as a turn's answer. -/
theorem vC_sum_stepPost {A B : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vC true (.sum A B) ls δ v ρ ↔
      stepPost (fun ls v => vC true A ls δ v) (fun ls v => vC true B ls δ v) ls v ρ := by
  constructor
  · rintro (⟨v₁, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, h⟩ | ⟨v₂, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, h⟩)
    · exact Or.inl ⟨v₁, rfl, by rw [eq_of_compS_empty_left hc]; exact h⟩
    · exact Or.inr ⟨v₂, rfl, by rw [eq_of_compS_empty_left hc]; exact h⟩
  · rintro (⟨b, rfl, h⟩ | ⟨s, rfl, h⟩)
    · exact Or.inl ⟨b, PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩, h⟩
    · exact Or.inr ⟨s, PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩, h⟩

/-- **`iterate` is sound**, at a row holding `Div`.  `[spec §14]` -/
theorem iterate_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {Sg : Row} {St B R : VTy}
    (hS : Row.divB Sg = true) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .iterate)) (iterTy Sg St B R) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨f, s, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, hs⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  have hT := Row.divOK_of_divB hS δ
  obtain ⟨o, hfo, -⟩ := Row.divB_find hS
  have hT0 : Row.tab Sg δ divEff 0 = some (o.ent δ) := Row.tab_find hfo
  refine (cC_effOf_wp Sg _ ls' δ _ σ₂).mpr ?_
  rw [hS]
  refine cwp_post (fun ls v ρ h => vC_sum_stepPost.mpr h) ?_
  refine cwp_iterate hT hT0 (Row.tab_plainCancel Sg δ) f (fun ls v => vC true B ls δ v)
    (fun ls v => vC true R ls δ v) (fun ls v => vC true St ls δ v) ?_
    (fun _ _ _ _ he h => vC_local true St he h) hs
  intro ls₁ s₁ ρ₁ hs₁
  have hfs := hf.2 ls₁ (ext_empty' _ ls₁) s₁ ρ₁ ρ₁ hs₁ (compS_empty_left ρ₁)
  refine ⟨?_, ?_⟩
  · have h₁ := (cC_effOf_wp Sg _ ls₁ δ _ ρ₁).mp hfs.1
    rw [hS] at h₁
    exact cwp_post (fun ls v ρ h => vC_sum_stepPost.mp h) h₁
  · have h₂ := (cC_effOf_wp Sg _ ls₁ δ _ ρ₁).mp hfs.2
    rw [hS] at h₂
    exact h₂

end BoCa.Fig16.LogRel.Core

end
