import CBPVMu.DelayRel

/-!
# CBPVMu — the delay type by its finite approximations

`approx VA n` is `D A` observed correctly `n` times: `approx 0 = ⊤`,
`approx (n+1) = delayF VA (approx n)`.  The greatest fixed point `delayRel` lies below every
approximation (`delayRel_le_approx`), so below their intersection `approxLim`.

The converse — `approxLim ⊆ delayRel`, "the intersection is the greatest fixed point" — is
reduced here to one property of `wpTS` (`WpChainCommutes`): `wpTS` commutes with the
intersection of a decreasing chain of postconditions (`approxLim_le_delayRel`,
`delayRel_iff_approxLim`).  In `delayF` every other connective commutes with the intersection:
the `⌜w = injᵢ v⌝ ⋆ _` splits are forced (the pure half is empty), the disjunction is decided by
the returned value, and `thunkR` is a `∀` (`delayQ_lim`).  What is left is the `∃` in `wpTS`'s
definition (`World.lean`), over the post-state witness
`(ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls')`: each approximation may choose its own ghost world
`ρ'`, frame part `ρp` and record list `ls'`, and the intersection needs one choice that works for
every `n`.

`exists_forall_of_finite` shows a decreasing chain of properties over a finite witness type does
commute with the `∃`; `not_exists_forall` shows that over `ℕ` it need not.  `wpTS`'s witness
ranges over worlds, whose `imm` and `mut` cells carry lifetimes in `ℕᵒᵈ`, and record lists, so
the finite case does not apply.  The branching of the delay functor itself (`π₁`/`π₂`,
`inj₁`/`inj₂`) is finite but is not where the `∃` is.  I have not derived `WpChainCommutes` and
have not verified that any obstruction to it is real.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The top candidate. -/
def topP : CPred := fun _ _ _ => True

/-- `D A` observed correctly `n` times. -/
def approx (VA : List SRec → Val → WProp) : ℕ → CPred
  | 0 => topP
  | n + 1 => delayF VA (approx VA n)

/-- `⋂ₙ approx n`. -/
def approxLim (VA : List SRec → Val → WProp) : CPred := fun ls e ρ => ∀ n, approx VA n ls e ρ

/-- The approximations decrease. -/
theorem approx_succ_le (VA : List SRec → Val → WProp) :
    ∀ n, (approx VA (n + 1)).Le (approx VA n)
  | 0 => fun _ _ _ _ => trivial
  | n + 1 => delayF_mono VA (approx_succ_le VA n)

theorem approx_le_of_le (VA : List SRec → Val → WProp) {m n : ℕ} (h : m ≤ n) :
    (approx VA n).Le (approx VA m) := by
  induction h with
  | refl => exact fun _ _ _ hx => hx
  | step _ ih => exact fun ls e ρ hx => ih ls e ρ (approx_succ_le VA _ ls e ρ hx)

/-- The greatest fixed point lies below every approximation. -/
theorem delayRel_le_approx (VA : List SRec → Val → WProp) :
    ∀ n, (delayRel VA).Le (approx VA n)
  | 0 => fun _ _ _ _ => trivial
  | n + 1 => fun ls e ρ h =>
      delayF_mono VA (delayRel_le_approx VA n) ls e ρ (delayRel_out VA ls e ρ h)

theorem delayRel_le_approxLim (VA : List SRec → Val → WProp) :
    (delayRel VA).Le (approxLim VA) :=
  fun ls e ρ h n => delayRel_le_approx VA n ls e ρ h

/-- `wpTS` commutes with the intersection of a decreasing chain of postconditions. -/
def WpChainCommutes : Prop :=
  ∀ (ls : List SRec) (e : Expr) (Q : ℕ → List SRec → Val → WProp),
    (∀ n ls' v, Entails (Q (n + 1) ls' v) (Q n ls' v)) →
    ∀ ρ, (∀ n, wpTS ls e (Q n) ρ) → wpTS ls e (fun ls' v σ => ∀ n, Q n ls' v σ) ρ

/-- Inside `delayF`, the intersection commutes with everything but `wpTS`. -/
theorem delayQ_lim (VA : List SRec → Val → WProp) (ls : List SRec) (w : Val) :
    Entails (fun σ => ∀ n, delayQ VA (approx VA n) ls w σ) (delayQ VA (approxLim VA) ls w) := by
  intro σ h
  rcases h 0 with hn | ⟨v₂, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, -⟩
  · exact Or.inl hn
  · refine Or.inr ⟨v₂, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, fun ls' hk n => ?_⟩
    rcases h n with ⟨v₁, τ₀, τ₃, -, ⟨-, he⟩, -⟩ | ⟨v₂', τ₀, τ₃, hc', ⟨hτ₀, he⟩, ht⟩
    · cases he
    · have hv : v₂ = v₂' := Val.ext (Expr.inj₂.inj (congrArg Subtype.val he))
      subst hv hσ₀ hτ₀
      have e₁ := eq_of_compS_empty_left hc
      have e₂ := eq_of_compS_empty_left hc'
      subst e₁
      rw [← e₂] at ht
      exact ht ls' hk

/-- **The reduction.**  If `wpTS` commutes with decreasing intersections, the intersection of
the approximations is a post-fixed point, so it lies below the greatest fixed point. -/
theorem approxLim_le_delayRel (hc : WpChainCommutes) (VA : List SRec → Val → WProp) :
    (approxLim VA).Le (delayRel VA) := by
  refine delayRel_coind (fun ls e ρ h => ⟨?_, (h 1).2⟩)
  refine wpTS_mono (fun ls' w => delayQ_lim VA ls' w) ρ ?_
  exact hc ls _ (fun n => delayQ VA (approx VA n))
    (fun n ls' w => delayQ_mono (approx_succ_le VA n) ls' w) ρ (fun n => (h (n + 1)).1)

/-- Under `WpChainCommutes`, `⟦D A⟧ = ⋂ₙ approx n`. -/
theorem delayRel_iff_approxLim (hc : WpChainCommutes) (VA : List SRec → Val → WProp)
    (ls : List SRec) (e : Expr) (ρ : WRes) : delayRel VA ls e ρ ↔ approxLim VA ls e ρ :=
  ⟨delayRel_le_approxLim VA ls e ρ, approxLim_le_delayRel hc VA ls e ρ⟩

/-! ### The `∃` over a chain -/

/-- A decreasing chain of properties over a finite witness type: some witness satisfies every
member. -/
theorem exists_forall_of_finite {W : Type} [Finite W] (P : ℕ → W → Prop)
    (hP : ∀ n w, P (n + 1) w → P n w) (h : ∀ n, ∃ w, P n w) : ∃ w, ∀ n, P n w := by
  classical
  have hle : ∀ w m n, m ≤ n → P n w → P m w := by
    intro w m n hmn
    induction hmn with
    | refl => exact id
    | step _ ih => exact fun hx => ih (hP _ w hx)
  by_contra hno
  simp only [not_exists, not_forall] at hno
  choose f hf using hno
  have := Fintype.ofFinite W
  obtain ⟨w, hw⟩ := h (Finset.univ.sup f)
  exact hf w (hle w (f w) _ (Finset.le_sup (Finset.mem_univ w)) hw)

/-- Over `ℕ` the `∃` does not commute with the intersection: `n ≤ w`. -/
theorem not_exists_forall :
    ∃ P : ℕ → ℕ → Prop, (∀ n w, P (n + 1) w → P n w) ∧ (∀ n, ∃ w, P n w) ∧
      ¬ ∃ w, ∀ n, P n w :=
  ⟨fun n w => n ≤ w, fun _ _ h => Nat.le_of_succ_le h, fun n => ⟨n, le_rfl⟩,
    fun ⟨w, hw⟩ => Nat.not_succ_le_self w (hw (w + 1))⟩

end BoCa.Fig16.LogRel.CBPVMu

end
