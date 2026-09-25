import Core.Delay

/-!
# Core — coiteration on the stream type  `[spec §7]`

`Stream A = νX. F(A ⊗ U X) & F 1` (`cC`'s `stream` clause, `StreamRel.lean`): `next` (`π₁`)
returns a value and the rest of the stream, a thunk of `Stream A`; `close` (`π₂`) disposes of
the stream.

**The rule.** `unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`.  `unfoldS step` is the fixed
point

    f = λs. ⟨step s π₁ to p. let (a, s′) = p in (a, f s′), step s π₂⟩

(`etaS_next`, `etaS_close`, `nextKSS_pair`): the recursive handle `f` occurs only in the rest of
the stream, applied to the next state.  The step returns a state, never a `Stream A`.  The
recursion is the rule's: the Z combinator (`Fix.lean`) over `fBS`.

**Soundness** (`unfoldS_compatX`) is coinduction at the greatest fixed point, with the candidate
`{unfoldS step s | s ∈ 𝒱⟦S⟧}` (`candS`, `candS_post`), as for `fixD` (`Delay.lean`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types -/

/-- The step's type, `S ⊸ F(A ⊗ S) & F 1`. -/
abbrev stepSC (A S : VTy) : CTy := .arr S (.amp (.ret (.tensor A S)) (.ret .unit))

/-- `unfoldS`'s type, `!U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`. -/
abbrev unfoldSTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepSC A S))) (.bang (.thunk (.arr S (.stream A))))

/-! ### The term -/

/-- `p to …`: the continuation of `next`, under the binders `p, u, o, s, g, self`:
`let (a, s′) = p in (a, λo′. self g s′ o′)`. -/
def nextKStream : Expr :=
  .letpair (.var 0)
    (.pair (.var 1) (.val (.lam (.app (.app (.app (.var 8) (.var 7)) (.var 1)) (.var 0)))))

/-- The body of `unfoldS = Z (λself. λg. λs. λo. case o {inj₁ _. (g s π₁) to p. nextKStream |
inj₂ _. g s π₂})`. -/
def fBS : Expr :=
  .val (.lam (.val (.lam (.case (.var 0)
    (bindE (.app (.app (.var 3) (.var 2)) (.val (.inj₁ .unit))) nextKStream)
    (.app (.app (.var 3) (.var 2)) (.val (.inj₂ .unit)))))))

theorem fBS_closed : closedAt 2 fBS = true := rfl

/-- The recursive handle. -/
abbrev selfS : Val := selfV fBS

theorem selfS_closed : closedAt 0 selfS.1 = true := selfV_closed fBS_closed

/-- `λo. self g s o`: the stream `unfoldS step s`, at `g = step`. -/
def etaS (g s : Val) : Val :=
  .lam (.app (.app (.app (.val selfS) (.val (g.shift 1 0))) (.val (s.shift 1 0))) (.var 0))

/-- `λs. λo. self g s o`: `unfoldS step`, at `g = step`. -/
def hS (g : Val) : Val :=
  .lam (.val (.lam (.app (.app (.app (.val selfS) (.val (g.shift 2 0))) (.var 1)) (.var 0))))

/-- **`unfoldS = λg. λs. λo. self g s o`**, a closed value. -/
def unfoldSV : Val :=
  .lam (.val (.lam (.val (.lam (.app (.app (.app (.val selfS) (.var 2)) (.var 1)) (.var 0))))))

theorem unfoldSV_closed : closedAt 0 unfoldSV.1 = true := by
  simp [unfoldSV, closedAt, closedAt_mono _ selfS_closed (Nat.zero_le _)]

/-! ### Reduction -/

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem unfoldSV_subst (g : Val) :
    Expr.subst 0 g (.val (.lam (.val (.lam (.app (.app (.app (.val selfS) (.var 2)) (.var 1))
      (.var 0)))))) = .val (hS g) := by
  simp [hS, closed_subst selfS_closed]

theorem hS_subst (g s : Val) :
    Expr.subst 0 s (.val (.lam (.app (.app (.app (.val selfS) (.val (g.shift 2 0))) (.var 1))
      (.var 0)))) = .val (etaS g s) := by
  simp [etaS, closed_subst selfS_closed, subst_shift_succ]

/-- `nextKStream` with `self`, `g`, `s` and `u` substituted: under the binder `p`,
`let (a, s′) = p in (a, λo′. self g s′ o′)`. -/
def nextKSS (g : Val) : Expr :=
  .letpair (.var 0)
    (.pair (.var 1) (.val (.lam (.app (.app (.app (.val selfS) (.val (g.shift 4 0))) (.var 1))
      (.var 0)))))

/-- An observation `o` of `etaS g s` unrolls the Z combinator and reaches `fBS`'s body at
`g` and `s`. -/
theorem etaS_obs (g s o : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appL (Kont.appL .hole s) o).plug ((fBS.subst 1 selfS).subst 0 g)) Q)
      (wpTS ls (.app (.val (etaS g s)) (.val o)) Q) := by
  intro ρ h
  refine wpTS_lolli ls _ o Q ρ ?_
  have e₁ : Expr.subst 0 o (.app (.app (.app (.val selfS) (.val (g.shift 1 0)))
      (.val (s.shift 1 0))) (.var 0))
      = (Kont.appL (Kont.appL .hole s) o).plug (.app (.val selfS) (.val g)) := by
    simp [Kont.plug, closed_subst selfS_closed, subst_shift_succ]
  rw [e₁]
  refine wpTS_selfV_in fBS_closed _ g ls Q ρ ?_
  rw [fixV_eq fBS_closed]
  exact wpTS_beta_in _ _ g ls Q ρ h

/-- **`next`** of `unfoldS step s` runs the step's `next` at `s`, then `nextKSS`. -/
theorem etaS_next (g s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (bindE (.app (.app (.val g) (.val s)) (.val (.inj₁ .unit))) (nextKSS g)) Q)
      (wpTS ls (.app (.val (etaS g s)) (.val (.inj₁ .unit))) Q) := by
  intro ρ h
  refine etaS_obs g s _ ls Q ρ ?_
  simp only [fBS, Kont.plug]
  refine wpTS_beta_in (.appL .hole _) _ s ls Q ρ ?_
  refine wpTS_lolli ls _ _ Q ρ ?_
  refine wpTS_sum₁ ls _ _ _ Q ρ ?_
  simp [nextKStream, nextKSS, bindE, closed_subst selfS_closed, closed_shift selfS_closed,
    subst_shift_succ] at h ⊢
  exact h

/-- **`close`** of `unfoldS step s` runs the step's `close` at `s`. -/
theorem etaS_close (g s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.app (.val g) (.val s)) (.val (.inj₂ .unit))) Q)
      (wpTS ls (.app (.val (etaS g s)) (.val (.inj₂ .unit))) Q) := by
  intro ρ h
  refine etaS_obs g s _ ls Q ρ ?_
  simp only [fBS, Kont.plug]
  refine wpTS_beta_in (.appL .hole _) _ s ls Q ρ ?_
  refine wpTS_lolli ls _ _ Q ρ ?_
  refine wpTS_sum₂ ls _ _ _ Q ρ ?_
  simp [subst_shift_succ] at h ⊢
  exact h

/-- The step returned `(a, s′)`: the value `a` and the stream `unfoldS step s′`. -/
theorem nextKSS_pair (g a s' : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (Q ls (.pair a (etaS g s'))) (wpTS ls ((nextKSS g).subst 0 (.pair a s')) Q) := by
  intro ρ h
  simp only [nextKSS, Expr.subst]
  refine wpTS_tensor ls a s' _ Q ρ ?_
  convert wpTS_val ls _ Q ρ h using 2
  simp [etaS, closed_subst selfS_closed, subst_shift_succ]

/-! ### Soundness -/

/-- The candidate: the streams `unfoldS step s` at a state `s ∈ 𝒱⟦S⟧`. -/
def candS (g : Val) (S : VTy) (δ : LSub) : CPred := fun ls e ρ =>
  ∃ s, e = .val (etaS g s) ∧ vC true S ls δ s ρ

/-- The candidate is a post-fixed point of `Stream A`'s functor: `next` runs one step and returns
`(a, unfoldS step s′)` with `s′ ∈ 𝒱⟦S⟧`, back in the candidate; `close` runs the step's
`close`. -/
theorem candS_post {A S : VTy} {δ : LSub} {g : Val}
    (hg : ∀ ls, vC true (.bang (.thunk (stepSC A S))) ls δ g PMap.empty) :
    (candS g S δ).Le (streamF (fun ls v => vC true A ls δ v) (candS g S δ)) := by
  rintro ls e ρ ⟨s, rfl, hs⟩
  obtain ⟨-, hthunk⟩ := hg ls
  obtain ⟨h₁, h₂⟩ := hthunk ls (Ext.refl _ _) s ρ ρ hs (ResU.CompS.comm (ResU.comp_empty_right ρ))
  refine ⟨etaS_next g s ls _ ρ ?_, etaS_close g s ls _ ρ h₂⟩
  refine wpTS_bind (.appR (.val (.lam (nextKSS g))) .hole) _ ls _ ρ ?_
  refine wpTS_mono (fun ls' w σ hw => ?_) ρ h₁
  show wpTS ls' (.app (.val (.lam (nextKSS g))) (.val w)) _ σ
  refine wpTS_lolli ls' _ w _ σ ?_
  obtain ⟨a, s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', ha, hs'⟩ := hw
  refine nextKSS_pair g a s' ls' _ σ ⟨a, etaS g s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', ha, ?_⟩
  exact fun ls'' hk => ⟨s', rfl, vC_local true S hk hs'⟩

/-- **`unfoldS` is sound**: `unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)` at every `A`
and `S`.  `[spec §7]` -/
theorem unfoldS_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (A S : VTy) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val unfoldSV) (unfoldSTy A S) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed unfoldSV_closed]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (.bang (.thunk (stepSC A S))) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [unfoldSV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ s ρ₂ τ hs hc
  rw [eq_of_compS_empty_left hc]
  refine cC_head (.stream A) (fun μ => Head.beta μ _ s) ls₂ δ ρ₂ ?_
  rw [hS_subst]
  exact streamRel_coind (candS_post hg) ls₂ _ ρ₂ ⟨s, rfl, hs⟩

/-! ### `Stream A` and its unrolling -/

/-- `streamIn`: a computation of `F(A ⊗ U(Stream A)) & F 1` is one of `Stream A`. -/
theorem streamIn_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemC Δ Γ e (streamUnroll A)) : SemC Δ Γ e (.stream A) :=
  fun δ γ ls ρ hδ hΓ => (cC_stream_iff A ls δ _ ρ).mpr (h δ γ ls ρ hδ hΓ)

/-- `streamOut`: a computation of `Stream A` is one of `F(A ⊗ U(Stream A)) & F 1`. -/
theorem streamOut_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemC Δ Γ e (.stream A)) : SemC Δ Γ e (streamUnroll A) :=
  fun δ γ ls ρ hδ hΓ => (cC_stream_iff A ls δ _ ρ).mp (h δ γ ls ρ hδ hΓ)

end BoCa.Fig16.LogRel.Core

end
