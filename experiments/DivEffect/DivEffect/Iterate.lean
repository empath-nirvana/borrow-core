import DivEffect.Rules
import Core.FoldImm
import Core.Nu

/-!
# DivEffect — `iterate`  (§4.1, unknown 1, item 2)

    iterate (f, s) ↦ (f s).1 to r. case r { inl b → return (inl b)
                                          | inr s' → tick () to n. case n { inl _ → iterate (f, s')
                                                                          | inr _ → (f s').2 to q. return (inr q) } }

`f : !U(S ⊸ F_Σ(B ⊕ S) & F_Σ R)` is the step: one turn (`.1`, *next*) or the residual (`.2`,
*close*).  `iterate` ticks at each back edge, so every iteration is guarded, whoever wrote the
step.

The term here is the Z combinator over BoCa's untyped `λ` (`Core/Fix.lean`): no new machine step.
B1 makes it one constant with one machine step (`docs/pipeline-architecture.md` §3.2); the
semantics is the same unrolling.

`cwp_iterate` is its compatibility, by coinduction: the candidate holds `iterate (f, s)` and the
point after a *next*, at every state of the step's relation, and the frame of the turn around
every computation of `cwp`.  `Closing` needs no induction: answered *close*, the tick after a turn
runs `(f s').2`, a computation of `cwp`, so of `Closing`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The term -/

/-- `λq. inr q`. -/
def inrV : Val := .lam (.inj₂ (.var 0))

/-- After the tick, the answer `n` at `0`, the state `s'` at `1`, the step `f` at `3` and the
loop itself at `5`: `case n { inl _ → self (f, s') | inr _ → (λq. inr q) ((f s').2) }`. -/
def turnB : Expr :=
  .case (.var 0)
    (.app (.var 6) (.pair (.var 4) (.var 2)))
    (.app (.val inrV) (.app (.app (.var 4) (.var 2)) (.val closeV)))

/-- The body under the loop (`1`) and its argument `(f, s)` (`0`). -/
def iterB (d : UInt32) : Expr :=
  .letpair (.var 0)
    (.case (.app (.app (.var 1) (.var 0)) (.val nextV))
      (.inj₁ (.var 0))
      (.app (.val (.lam turnB)) (tickE d)))

/-- **`iterate`**, a closed value. -/
def iterV (d : UInt32) : Val := selfV (iterB d)

theorem iterB_closed (d : UInt32) : closedAt 2 (iterB d) = true := by
  simp [iterB, turnB, tickE, closedAt, inrV, nextV, closeV, BoCa.BoLo.performE,
    BoCa.BoLo.opPayload, Val.pair, Val.i32]

/-! ### Its unrolling -/

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- The turn's observation `(f s).1`. -/
def obsN (f s : Val) : Expr := .app (.app (.val f) (.val s)) (.val nextV)

/-- The close observation `(f s).2`. -/
def obsC (f s : Val) : Expr := .app (.app (.val f) (.val s)) (.val closeV)

/-- `iterate (f, s)`. -/
def iterE (d : UInt32) (f s : Val) : Expr := .app (.val (iterV d)) (.val (Val.pair f s))

/-- After the tick: `case n { inl _ → iterate (f, s') | inr _ → inr ((f s').2) }`, `s'` at `1`
and `n` at `0`. -/
def turnF (d : UInt32) (f : Val) : Expr :=
  .case (.var 0) (.app (.val (iterV d)) (.pair (f.1.shift 3 0) (.var 2)))
    (.app (.lam (.inj₂ (.var 0))) (.app (.app (f.1.shift 3 0) (.var 2)) (.inj₂ .unit)))

/-- The frame of a turn: `[·] to r. case r { inl b → inl b | inr s' → tick () to n. … }`. -/
def iterK (d : UInt32) (f : Val) : Kont :=
  .case .hole (.inj₁ (.var 0)) (.app (.lam (turnF d f)) (tickE d))

/-- The frame of the tick, the state `s'` in it. -/
def turnK (d : UInt32) (f s' : Val) : Kont :=
  .appR (.lam ((turnF d f).subst 1 (s'.shift 1 0))) .hole

theorem iter_unfold (d : UInt32) (f s : Val) :
    PureSteps (iterE d f s) ((iterK d f).plug (obsN f s)) := by
  refine (selfV_steps_in (iterB_closed d) .hole (Val.pair f s)).trans ?_
  rw [fixV_eq (iterB_closed d)]
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ f s _) rfl).trans ?_
  have hc : closedAt 0 (selfV (iterB d)).1 = true := selfV_closed (iterB_closed d)
  simp only [iterK, turnF, iterV]
  generalize selfV (iterB d) = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, subst_shift_succ, tickE, turnB, nextV, closeV,
    BoCa.BoLo.performE, BoCa.BoLo.opPayload, Val.i32, obsN, Kont.plug]
  exact .refl

theorem iterK_inl (d : UInt32) (f b : Val) :
    PureSteps ((iterK d f).plug (.val (Val.inj₁ b))) (.val (Val.inj₁ b)) := by
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp [Kont.plug, iterK]
  exact .refl

theorem iterK_inr (d : UInt32) (f s' : Val) :
    PureSteps ((iterK d f).plug (.val (Val.inj₂ s'))) ((turnK d f s').plug (tickE d)) := by
  refine (PureSteps.head (fun μ => Head.case₂ μ s' _ _) rfl).trans ?_
  have hc : closedAt 0 (tickE d) = true := rfl
  simp [Kont.plug, iterK, turnK, subst_closedAt _ s' hc]
  exact .refl

theorem turnK_next (d : UInt32) (f s' : Val) :
    PureSteps ((turnK d f s').plug (.val nextV)) (iterE d f s') := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (iterV d).1 = true := selfV_closed (iterB_closed d)
  simp only [turnF, iterE]
  generalize iterV d = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, subst_shift_succ, nextV]
  exact .refl

theorem turnK_close (d : UInt32) (f s' : Val) :
    PureSteps ((turnK d f s').plug (.val closeV)) (.app (.val inrV) (obsC f s')) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (iterV d).1 = true := selfV_closed (iterB_closed d)
  simp only [turnF, obsC]
  generalize iterV d = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, subst_shift_succ, closeV, inrV]
  exact .refl

theorem inrV_steps (r : Val) : PureSteps (.app (.val inrV) (.val r)) (.val (Val.inj₂ r)) := by
  refine (PureSteps.beta _ _).trans ?_
  simp
  exact .refl

/-! ### Steps, ticks and empty frames -/

theorem cwp_pureSteps {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {e e' : Expr} (h : PureSteps e e') {ls : List SRec} {ρ : WRes}
    (h' : cwp δ d T Q ls e' ρ) : cwp δ d T Q ls e ρ :=
  cwp_roll ls e ρ (ewp_pureSteps (divTab_mono δ d T Q _) h _ _ ρ (cwp_out ls e' ρ h'))

theorem compS_empty_eq {ρ ρ' : WRes} (h : ResU.CompS ρ PMap.empty ρ') : ρ' = ρ :=
  ResU.CompS.functional h (ResU.comp_empty_right ρ)

theorem sep_emp_elim {P : WProp} {ρ : WRes} (h : (P ⋆ emp) ρ) : P ρ := by
  obtain ⟨σ₁, σ₂, hc, hp, ⟨rfl, -⟩⟩ := h
  rw [compS_empty_eq hc]; exact hp

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
theorem cwpF_tickK {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp} {Y : CPred}
    (K : Kont) (hK : K.HasHnd d = false) {ls : List SRec} {ρ : WRes}
    (h : ∀ ls', Ext ls ls' ρ → ∀ w : Val, w = nextV ∨ w = closeV →
      owe δ d T Q Y ls' (K.plug (.val w)) ρ) :
    cwpF δ d T Q Y ls (K.plug (tickE d)) ρ := by
  refine ewp_fold (divTab_mono δ d T Q _) (wpG_here _ _ _ _ (Or.inr (Or.inr
    ⟨K, d, 0, .unit, tickEnt δ d, pure_sep_mk ⟨rfl, hK, by simp [tickT, OpTab.ext], rfl⟩
      ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩, And.intro (fun h => nomatch h)
        (fun ls' he => And.intro (fun w τ₁ τ₂ hB hc => ?_) (fun h => absurd rfl h))⟩⟩)))
  obtain ⟨hw, rfl⟩ := vC_next hB
  rw [compS_empty_eq hc]
  exact h ls' he w hw

/-- **A tick in a frame `K`**, closing: the stop owes `K` at *close*. -/
theorem closing_tickK {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    (K : Kont) (hK : K.HasHnd d = false) {ls : List SRec} {ρ : WRes}
    (h : ∀ ls', Ext ls ls' ρ → Closing δ d T Q ls' (K.plug (.val closeV)) ρ) :
    Closing δ d T Q ls (K.plug (tickE d)) ρ := by
  refine ewp_fold (opTable_mono _) (wpG_here _ _ _ _ (Or.inr (Or.inl
    ⟨K, d, 0, .unit, closeEnt δ d, pure_sep_mk ⟨rfl, hK, by simp [OpTab.ext], rfl⟩
      ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩, And.intro (fun h => nomatch h)
        (fun ls' he => And.intro (fun w τ₁ τ₂ hB hc => ?_) (fun h => absurd rfl h))⟩⟩)))
  obtain ⟨rfl, rfl⟩ := vC_close.mp hB
  rw [compS_empty_eq hc]
  exact h ls' he

/-! ### Compatibility -/

theorem iterK_plain (d : UInt32) (f : Val) :
    (∀ n, (iterK d f).HasHnd n = false) ∧ (∀ n, (iterK d f).Catches n = false) :=
  ⟨fun n => by simp [iterK, Kont.HasHnd], fun n => by simp [iterK, Kont.Catches]⟩

theorem turnK_hasHnd (d : UInt32) (f s : Val) (n : UInt32) : (turnK d f s).HasHnd n = false := by
  simp [turnK, Kont.HasHnd]

theorem inrK_plain : (∀ n, (Kont.appR (.val inrV) .hole).HasHnd n = false) ∧
    (∀ n, (Kont.appR (.val inrV) .hole).Catches n = false) :=
  ⟨fun n => by simp [Kont.HasHnd, inrV], fun n => by simp [Kont.Catches, inrV]⟩

section
variable {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none) (hPC : T.PlainCancel)
  (f : Val) (QB QR VS : List SRec → Val → WProp)

/-- What a turn answers: the result `inl b`, or the next state `inr s`. -/
def stepPost (QB VS : List SRec → Val → WProp) : List SRec → Val → WProp := fun ls v ρ =>
  (∃ b, v = Val.inj₁ b ∧ QB ls b ρ) ∨ (∃ s, v = Val.inj₂ s ∧ VS ls s ρ)

include hTd hPC in
/-- The close path: `inr ((f s).2)`. -/
theorem cwp_closePath {ls : List SRec} {s : Val} {ρ : WRes} (h : cwp δ d T QR ls (obsC f s) ρ) :
    cwp δ d T (stepPost QB QR) ls (.app (.val inrV) (obsC f s)) ρ := by
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ inrK_plain.1 inrK_plain.2
  exact cwp_bind hTd (.appR (.val inrV) .hole) inrK_plain.1 inrK_plain.2 (fun _ => emp)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hW hU hK QR _
    (fun ls v σ hσ => cwp_pureSteps (inrV_steps v)
      (cwp_of_ewp (ewp_val (opTable_mono T) (Or.inr ⟨v, rfl, sep_emp_elim hσ⟩)))) h
    ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)

include hTd hPC in
/-- **`iterate (f, s)` is in `Closing`**: answered *close*, the tick after a turn runs the close
path once. -/
theorem closing_iterate
    (hstep : ∀ ls s ρ, VS ls s ρ →
      cwp δ d T (stepPost QB VS) ls (obsN f s) ρ ∧ cwp δ d T QR ls (obsC f s) ρ)
    (hVS : ∀ ls ls' s ρ, Ext ls ls' ρ → VS ls s ρ → VS ls' s ρ)
    {ls : List SRec} {s : Val} {ρ : WRes} (hs : VS ls s ρ) :
    Closing δ d T (stepPost QB QR) ls (iterE d f s) ρ := by
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ (iterK_plain d f).1 (iterK_plain d f).2
  obtain ⟨hWc, hUc, hKc⟩ := frame_conds_ext (en₀ := closeEnt δ d) (d := d) rfl rfl _ _ hW hU hK
  refine ewp_pureSteps (opTable_mono _) (iter_unfold d f s) _ _ ρ ?_
  refine ewp_frame_plain _ (iterK d f) (iterK_plain d f).1 (iterK_plain d f).2 (fun _ => emp)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hWc hUc hKc (stepPost QB VS) _ ?_
    (closing_of_cwp hTd (hstep ls s ρ hs).1) (ρ₂ := PMap.empty) ⟨rfl, trivial⟩
    (ResU.comp_empty_right ρ)
  intro ls' v σ hσ
  rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
  · exact ewp_pureSteps (opTable_mono _) (iterK_inl d f b) _ _ σ
      (ewp_val (opTable_mono _) (Or.inl ⟨b, rfl, hb⟩))
  · refine ewp_pureSteps (opTable_mono _) (iterK_inr d f s') _ _ σ
      (closing_tickK _ (turnK_hasHnd d f s' d) fun ls'' he => ?_)
    exact ewp_pureSteps (opTable_mono _) (turnK_close d f s') _ _ σ (closing_of_cwp hTd
      (cwp_closePath hTd hPC f QB QR (hstep ls'' s' σ (hVS _ _ _ _ he hs')).2))

include hTd hPC in
/-- **`iterate`'s compatibility** (§4.1 unknown 1 item 2), by coinduction up to `cwp`.  The
candidate: `iterate (f, s)` and the point after a *next*, at every state of `VS`; and the frame of
a turn around every computation of `cwp`.  A turn is `cwpF_frame`; its answer `inl b` finishes; its
answer `inr s'` ticks, and the tick owes the point after a *next* (in the candidate) and the close
path (in `cwp`, `cwp_closePath`), each in `Closing` (`closing_iterate`). -/
theorem cwp_iterate
    (hstep : ∀ ls s ρ, VS ls s ρ →
      cwp δ d T (stepPost QB VS) ls (obsN f s) ρ ∧ cwp δ d T QR ls (obsC f s) ρ)
    (hVS : ∀ ls ls' s ρ, Ext ls ls' ρ → VS ls s ρ → VS ls' s ρ)
    {ls : List SRec} {s : Val} {ρ : WRes} (hs : VS ls s ρ) :
    cwp δ d T (stepPost QB QR) ls (iterE d f s) ρ := by
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ (iterK_plain d f).1 (iterK_plain d f).2
  let W₁ : CPred := fun ls x ρ => ∃ s, (x = iterE d f s ∨ x = (turnK d f s).plug (.val nextV)) ∧
    VS ls s ρ
  let W₂ : CPred := fun ls x ρ => ∃ e, x = (iterK d f).plug e ∧ cwp δ d T (stepPost QB VS) ls e ρ
  let W : CPred := fun ls x ρ => W₁ ls x ρ ∨ W₂ ls x ρ
  let Y : CPred := fun ls x ρ => W ls x ρ ∨ cwp δ d T (stepPost QB QR) ls x ρ
  -- the frame of a turn, one segment
  have h₂ : ∀ ls e ρ, cwp δ d T (stepPost QB VS) ls e ρ →
      cwpF δ d T (stepPost QB QR) Y ls ((iterK d f).plug e) ρ := by
    intro ls e ρ he
    refine cwpF_frame hTd (iterK d f) (iterK_plain d f).1 (iterK_plain d f).2 (fun _ => emp)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hW hU hK (stepPost QB VS) _ Y ?_ ?_ ?_ he
      (ρ₂ := PMap.empty) ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
    · intro ls e ρ ρ₂ ρ' he hF hc
      obtain ⟨rfl, -⟩ := hF
      rw [compS_empty_eq hc]
      exact Or.inl (Or.inr ⟨e, rfl, he⟩)
    · intro ls' v σ hσ
      rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
      · exact ewp_pureSteps (divTab_mono δ d T _ _) (iterK_inl d f b) _ _ σ
          (ewp_val (divTab_mono δ d T _ _) (Or.inl ⟨b, rfl, hb⟩))
      · refine ewp_pureSteps (divTab_mono δ d T _ _) (iterK_inr d f s') _ _ σ
          (cwpF_tickK _ (turnK_hasHnd d f s' d) fun ls'' he w hw => ?_)
        have hs'' := hVS _ _ _ _ he hs'
        rcases hw with rfl | rfl
        · exact ⟨Or.inl (Or.inl ⟨s', Or.inr rfl, hs''⟩),
            ewp_pureSteps (opTable_mono _) (turnK_next d f s') _ _ σ
              (closing_iterate hTd hPC f QB QR VS hstep hVS hs'')⟩
        · have hc := cwp_pureSteps (turnK_close d f s')
            (cwp_closePath hTd hPC f QB QR (hstep ls'' s' σ hs'').2)
          exact ⟨Or.inr hc, closing_of_cwp hTd hc⟩
    · intro ls' v σ hσ
      rcases sep_emp_elim hσ with ⟨b, rfl, hb⟩ | ⟨s', rfl, hs'⟩
      · exact ewp_pureSteps (opTable_mono _) (iterK_inl d f b) _ _ σ
          (ewp_val (opTable_mono _) (Or.inl ⟨b, rfl, hb⟩))
      · refine ewp_pureSteps (opTable_mono _) (iterK_inr d f s') _ _ σ
          (closing_tickK _ (turnK_hasHnd d f s' d) fun ls'' he => ?_)
        exact ewp_pureSteps (opTable_mono _) (turnK_close d f s') _ _ σ (closing_of_cwp hTd
          (cwp_closePath hTd hPC f QB QR (hstep ls'' s' σ (hVS _ _ _ _ he hs')).2))
  have hW' : W.Le (cwpF δ d T (stepPost QB QR) Y) := by
    rintro ls x ρ (⟨s, hx, hs⟩ | ⟨e, rfl, he⟩)
    · have h := ewp_pureSteps (divTab_mono δ d T _ _) (iter_unfold d f s) _ _ ρ
        (h₂ ls _ ρ (hstep ls s ρ hs).1)
      rcases hx with rfl | rfl
      · exact h
      · exact ewp_pureSteps (divTab_mono δ d T _ _) (turnK_next d f s) _ _ ρ h
    · exact h₂ ls e ρ he
  exact cwp_coind_up hW' ls _ ρ (Or.inl ⟨s, Or.inl rfl, hs⟩)

end

end BoCa.Fig16.LogRel.Core.DivEffect

end
