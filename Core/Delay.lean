import Core.FoldImm

/-!
# Core — guarded recursion on the delay type  `[spec §7]`

`D A = νX. F(A ⊕ U X) & F 1` (`cC`'s `delay` clause, `DelayRel.lean`): forcing a delayed
computation with `next` (`π₁`) returns `now a` (`inj₁ a`) or `later t` (`inj₂ t`, `t` the rest,
a thunk of `D A`); `close` (`π₂`) disposes of an unfinished computation.

**The rule.** `fixD : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`.  `fixD step` is the fixed point

    f = λs. ⟨step s π₁ to x. case x {inj₁ a. now a | inj₂ s′. later (f s′)}, step s π₂⟩

(`etaD_next`, `etaD_close`, `nextKS_now`, `nextKS_later`): the recursive handle `f` occurs only
under `later`, applied to the next state.  `▷` is the shape of the step's type: the step's `next` returns, under `F`, either a
result or a state `S` — never a `D A` — so it cannot observe the recursive computation before a
`later` has been emitted.  The recursion itself is the rule's: the Z combinator
(`Fix.lean`) over `fBD`.

**Soundness** (`fixD_compatX`) is coinduction at the greatest fixed point, with the candidate
`{fixD step s | s ∈ 𝒱⟦S⟧}` (`candD`, `candD_post`).  It uses no approximation of `D A` and no
index.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types -/

/-- The step's type, `S ⊸ F(A ⊕ S) & F 1`. -/
abbrev stepDC (A S : VTy) : CTy := .arr S (.amp (.ret (.sum A S)) (.ret .unit))

/-- `fixD`'s type, `!U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`. -/
abbrev fixDTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepDC A S))) (.bang (.thunk (.arr S (.delay A))))

/-! ### The term -/

/-- `x to …`: the continuation of `next`, under the binders `x, u, o, s, g, self`:
`case x {inj₁ a. inj₁ a | inj₂ s′. inj₂ (λo′. self g s′ o′)}`. -/
def nextK : Expr :=
  .case (.var 0) (.inj₁ (.var 0))
    (.inj₂ (.val (.lam (.app (.app (.app (.var 7) (.var 6)) (.var 1)) (.var 0)))))

/-- The body of `fixD = Z (λself. λg. λs. λo. case o {inj₁ _. (g s π₁) to x. nextK |
inj₂ _. g s π₂})`. -/
def fBD : Expr :=
  .val (.lam (.val (.lam (.case (.var 0)
    (bindE (.app (.app (.var 3) (.var 2)) (.val (.inj₁ .unit))) nextK)
    (.app (.app (.var 3) (.var 2)) (.val (.inj₂ .unit)))))))

theorem fBD_closed : closedAt 2 fBD = true := rfl

/-- The recursive handle. -/
abbrev selfD : Val := selfV fBD

theorem selfD_closed : closedAt 0 selfD.1 = true := selfV_closed fBD_closed

/-- `λo. self g s o`: the delayed computation `fixD step s`, at `g = step`. -/
def etaD (g s : Val) : Val :=
  .lam (.app (.app (.app (.val selfD) (.val (g.shift 1 0))) (.val (s.shift 1 0))) (.var 0))

/-- `λs. λo. self g s o`: `fixD step`, at `g = step`. -/
def hD (g : Val) : Val :=
  .lam (.val (.lam (.app (.app (.app (.val selfD) (.val (g.shift 2 0))) (.var 1)) (.var 0))))

/-- **`fixD = λg. λs. λo. self g s o`**, a closed value. -/
def fixDV : Val :=
  .lam (.val (.lam (.val (.lam (.app (.app (.app (.val selfD) (.var 2)) (.var 1)) (.var 0))))))

theorem fixDV_closed : closedAt 0 fixDV.1 = true := by
  simp [fixDV, closedAt, closedAt_mono _ selfD_closed (Nat.zero_le _)]

/-! ### Reduction -/

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem fixDV_subst (g : Val) :
    Expr.subst 0 g (.val (.lam (.val (.lam (.app (.app (.app (.val selfD) (.var 2)) (.var 1))
      (.var 0)))))) = .val (hD g) := by
  simp [hD, closed_subst selfD_closed]

theorem hD_subst (g s : Val) :
    Expr.subst 0 s (.val (.lam (.app (.app (.app (.val selfD) (.val (g.shift 2 0))) (.var 1))
      (.var 0)))) = .val (etaD g s) := by
  simp [etaD, closed_subst selfD_closed, subst_shift_succ]

/-- `nextK` with `self`, `g`, `s` and `u` substituted: under the binder `x`,
`case x {inj₁ a. inj₁ a | inj₂ s′. inj₂ (λo′. self g s′ o′)}`. -/
def nextKS (g : Val) : Expr :=
  .case (.var 0) (.inj₁ (.var 0))
    (.inj₂ (.val (.lam (.app (.app (.app (.val selfD) (.val (g.shift 3 0))) (.var 1)) (.var 0)))))

/-- An observation `o` of `etaD g s` unrolls the Z combinator and reaches `fBD`'s body at
`g` and `s`. -/
theorem etaD_obs (g s o : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appL (Kont.appL .hole s) o).plug ((fBD.subst 1 selfD).subst 0 g)) Q)
      (wpTS ls (.app (.val (etaD g s)) (.val o)) Q) := by
  intro ρ h
  refine wpTS_lolli ls _ o Q ρ ?_
  have e₁ : Expr.subst 0 o (.app (.app (.app (.val selfD) (.val (g.shift 1 0)))
      (.val (s.shift 1 0))) (.var 0))
      = (Kont.appL (Kont.appL .hole s) o).plug (.app (.val selfD) (.val g)) := by
    simp [Kont.plug, closed_subst selfD_closed, subst_shift_succ]
  rw [e₁]
  refine wpTS_selfV_in fBD_closed _ g ls Q ρ ?_
  rw [fixV_eq fBD_closed]
  exact wpTS_beta_in _ _ g ls Q ρ h

/-- **`next`** of `fixD step s` runs the step's `next` at `s`, then `nextKS`. -/
theorem etaD_next (g s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (bindE (.app (.app (.val g) (.val s)) (.val (.inj₁ .unit))) (nextKS g)) Q)
      (wpTS ls (.app (.val (etaD g s)) (.val (.inj₁ .unit))) Q) := by
  intro ρ h
  refine etaD_obs g s _ ls Q ρ ?_
  simp only [fBD, Kont.plug]
  refine wpTS_beta_in (.appL .hole _) _ s ls Q ρ ?_
  refine wpTS_lolli ls _ _ Q ρ ?_
  refine wpTS_sum₁ ls _ _ _ Q ρ ?_
  simp [nextK, nextKS, bindE, closed_subst selfD_closed, closed_shift selfD_closed, subst_shift_succ] at h ⊢
  exact h

/-- **`close`** of `fixD step s` runs the step's `close` at `s`. -/
theorem etaD_close (g s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.app (.val g) (.val s)) (.val (.inj₂ .unit))) Q)
      (wpTS ls (.app (.val (etaD g s)) (.val (.inj₂ .unit))) Q) := by
  intro ρ h
  refine etaD_obs g s _ ls Q ρ ?_
  simp only [fBD, Kont.plug]
  refine wpTS_beta_in (.appL .hole _) _ s ls Q ρ ?_
  refine wpTS_lolli ls _ _ Q ρ ?_
  refine wpTS_sum₂ ls _ _ _ Q ρ ?_
  simp [subst_shift_succ] at h ⊢
  exact h

/-- The step returned `inj₁ a`: `now a`. -/
theorem nextKS_now (g a : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (Q ls (.inj₁ a)) (wpTS ls ((nextKS g).subst 0 (.inj₁ a)) Q) := by
  intro ρ h
  simp only [nextKS, Expr.subst]
  refine wpTS_sum₁ ls a _ _ Q ρ ?_
  simp only [Expr.subst]
  exact wpTS_val ls (.inj₁ a) Q ρ h

/-- The step returned `inj₂ s′`: `later (fixD step s′)`. -/
theorem nextKS_later (g s' : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (Q ls (.inj₂ (etaD g s'))) (wpTS ls ((nextKS g).subst 0 (.inj₂ s')) Q) := by
  intro ρ h
  simp only [nextKS, Expr.subst]
  refine wpTS_sum₂ ls s' _ _ Q ρ ?_
  convert wpTS_val ls _ Q ρ h using 2
  simp [etaD, closed_subst selfD_closed, subst_shift_succ]

/-! ### Soundness -/

/-- The candidate: the delayed computations `fixD step s` at a state `s ∈ 𝒱⟦S⟧`. -/
def candD (g : Val) (S : VTy) (δ : LSub) : CPred := fun ls e ρ =>
  ∃ s, e = .val (etaD g s) ∧ vC true S ls δ s ρ

/-- The candidate is a post-fixed point of `D A`'s functor: `next` runs one step and returns
`now a` or `later (fixD step s′)` with `s′ ∈ 𝒱⟦S⟧`, back in the candidate; `close` runs the
step's `close`. -/
theorem candD_post {A S : VTy} {δ : LSub} {g : Val}
    (hg : ∀ ls, vC true (.bang (.thunk (stepDC A S))) ls δ g PMap.empty) :
    (candD g S δ).Le (delayF (fun ls v => vC true A ls δ v) (candD g S δ)) := by
  rintro ls e ρ ⟨s, rfl, hs⟩
  obtain ⟨-, hthunk⟩ := hg ls
  obtain ⟨h₁, h₂⟩ := hthunk ls (Ext.refl _ _) s ρ ρ hs (ResU.CompS.comm (ResU.comp_empty_right ρ))
  refine ⟨etaD_next g s ls _ ρ ?_, etaD_close g s ls _ ρ h₂⟩
  refine wpTS_bind (.appR (.val (.lam (nextKS g))) .hole) _ ls _ ρ ?_
  refine wpTS_mono (fun ls' w σ hw => ?_) ρ h₁
  show wpTS ls' (.app (.val (.lam (nextKS g))) (.val w)) _ σ
  refine wpTS_lolli ls' _ w _ σ ?_
  rcases hw with ⟨a, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, ha⟩ | ⟨s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, hs'⟩
  · exact nextKS_now g a ls' _ σ (Or.inl ⟨a, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, ha⟩)
  · refine nextKS_later g s' ls' _ σ (Or.inr ⟨etaD g s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, ?_⟩)
    exact fun ls'' hk => ⟨s', rfl, vC_local true S hk hs'⟩

/-- **`fixD` is sound**: `fixD : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)` at every `A` and `S`.  `[spec §7]` -/
theorem fixD_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (A S : VTy) (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ (.val fixDV) (fixDTy A S) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_dead hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed fixDV_closed]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (.bang (.thunk (stepDC A S))) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [fixDV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ s ρ₂ τ hs hc
  rw [eq_of_compS_empty_left hc]
  refine cC_head (.delay A) (fun μ => Head.beta μ _ s) ls₂ δ ρ₂ ?_
  rw [hD_subst]
  exact delayRel_coind (candD_post hg) ls₂ _ ρ₂ ⟨s, rfl, hs⟩

/-! ### `D A` and its unrolling -/

/-- `delayIn`: a computation of `F(A ⊕ U(D A)) & F 1` is one of `D A`. -/
theorem delayIn_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemC Δ Γ e (delayUnroll A)) : SemC Δ Γ e (.delay A) :=
  fun δ γ ls ρ hδ hΓ => (cC_delay_iff A ls δ _ ρ).mpr (h δ γ ls ρ hδ hΓ)

/-- `delayOut`: a computation of `D A` is one of `F(A ⊕ U(D A)) & F 1`. -/
theorem delayOut_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemC Δ Γ e (.delay A)) : SemC Δ Γ e (delayUnroll A) :=
  fun δ γ ls ρ hδ hΓ => (cC_delay_iff A ls δ _ ρ).mp (h δ γ ls ρ hδ hΓ)

end BoCa.Fig16.LogRel.Core

end
