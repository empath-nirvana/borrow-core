import CoeffectsStrict.Fold

/-!
# Codata: `unfold` is the unique coalgebra homomorphism into `Loop A B`, on runs

The final-coalgebra laws, stated about machine runs, at the loop
`Loop A B = νX. F(A ⊕ U X) & F B` (SPEC §7).  A value of `U(Loop A B)` is observed by applying
it to `inj₁ ()` (`next`) or `inj₂ ()` (`close`); `out` (`nuOut`) is the identity on terms.

The functor is `G X = F(A ⊕ U X) & F B` on computation types.  Its observations are `F`
computations, so the step `g : S → G S` may run effects: the β law puts the step's
computation in an evaluation context and maps its result, whatever the step does to the heap.

* **β (computation law)** `out ∘ unfold g = G(unfold g) ∘ g`: `unfold_next` and
  `unfold_close` — observing `unfold g s` reaches the same observation of `g s`, followed by
  the functor's action `mapV` with `unfold g` at the `U X` position.  `next_result_*` show
  the action: `inj₁ a ↦ inj₁ a`, `inj₂ s′ ↦ inj₂ (unfold g s′)`.
* **Uniqueness (coinduction)**: `unfold_unique` — two coalgebra homomorphisms from the same
  step (`IsCoHom`) agree on every finite sequence of observations (`Agree n`), when the step is
  pure and total.  `unfold_isCoHom` shows `unfold g` is one.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CoeffectsStrict
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head Kont)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- `next`, the first observation. -/
abbrev nextO : Val := .inj₁ .unit

/-- `close`, the second observation. -/
abbrev closeO : Val := .inj₂ .unit

/-- `x ← [·]; map_A wr x`: the functor's action on an observation's result. -/
def mapK (A : VTy) (wr : Val) : Kont :=
  .appR (.val (.lam (.app (.app (.val (mapV A)) (.val (wr.shift 1 0))) (.var 0)))) .hole

theorem mapK_plug_val (A : VTy) (wr r : Val) :
    PureSteps (ℍ := ℍ) ((mapK A wr).plug (.val r)) (.app (.app (.val (mapV A)) (.val wr)) (.val r)) := by
  refine (PureSteps.beta _ r).trans ?_
  simp [closed_subst (mapV_closed A), subst_shift_succ]
  exact .refl

/-- The value type of `next`'s result, `A ⊕ X`. -/
abbrev nextTy (A : VTy) : VTy := .sum (A.rename Nat.succ) (.tvar 0)

/-- **β at `next`**: `next (unfold g s)` reaches `x ← next (g s); map_{A ⊕ X} (unfold g) x`. -/
theorem unfold_next (A B : VTy) (g s : Val) :
    PureSteps (ℍ := ℍ) (.app (.val (etaN (CTy.loopBody A B) g s)) (.val nextO))
      ((mapK (nextTy A) (hN (CTy.loopBody A B) g)).plug
        (.app (.app (.val g) (.val s)) (.val nextO))) := by
  refine (etaN_obs _ g s _).trans ?_
  refine (nodeV_amp₁_steps _ _ _ _).trans ?_
  refine (nodeV_ret_steps _ _ _).trans ?_
  refine (PureSteps.plug (mapK (nextTy A) (hN (CTy.loopBody A B) g)) (childV_steps _ _ rfl)).trans ?_
  exact PureSteps.plug (mapK (nextTy A) (hN (CTy.loopBody A B) g))
    (PureSteps.plug (.appL .hole nextO) (rootV_steps g s))

/-- **β at `close`**: `close (unfold g s)` reaches `x ← close (g s); map_B (unfold g) x`. -/
theorem unfold_close (A B : VTy) (g s : Val) :
    PureSteps (ℍ := ℍ) (.app (.val (etaN (CTy.loopBody A B) g s)) (.val closeO))
      ((mapK (B.rename Nat.succ) (hN (CTy.loopBody A B) g)).plug
        (.app (.app (.val g) (.val s)) (.val closeO))) := by
  refine (etaN_obs _ g s _).trans ?_
  refine (nodeV_amp₂_steps _ _ _ _).trans ?_
  refine (nodeV_ret_steps _ _ _).trans ?_
  refine (PureSteps.plug (mapK (B.rename Nat.succ) (hN (CTy.loopBody A B) g))
    (childV_steps _ _ rfl)).trans ?_
  exact PureSteps.plug (mapK (B.rename Nat.succ) (hN (CTy.loopBody A B) g))
    (PureSteps.plug (.appL .hole closeO) (rootV_steps g s))

/-- The action at a finished `next`: `inj₁ a ↦ inj₁ a` (at an `A` with no `X`, whose `mapV` is
the identity). -/
theorem next_result_done {A : VTy} (hA : mapV (A.rename Nat.succ) = .lam (.val (.lam (.var 0))))
    (wr a : Val) :
    Evals (ℍ := ℍ) (.app (.app (.val (mapV (nextTy A))) (.val wr)) (.val (.inj₁ a))) (.inj₁ a) :=
  (mapV_sum₁_steps _ _ wr a).trans (inj₁_steps (mapV_id_steps hA wr a))

/-- The action at an unfinished `next`: `inj₂ s′ ↦ inj₂ (wr s′)`. -/
theorem next_result_more (A : VTy) (wr s' l : Val)
    (hl : Evals (ℍ := ℍ) (.app (.val wr) (.val s')) l) :
    Evals (ℍ := ℍ) (.app (.app (.val (mapV (nextTy A))) (.val wr)) (.val (.inj₂ s'))) (.inj₂ l) :=
  (mapV_sum₂_steps _ _ wr s').trans (inj₂_steps ((mapV_var_steps wr s').trans hl))

/-! ### Uniqueness -/

/-- `h : S → U(Loop A B)` is a coalgebra homomorphism from the step `g`, as a reduction:
`h s` reaches a codata value `c s`, and each observation of `c s` reaches the functor's action
with `h` on the same observation's result of `g s`. -/
def IsCoHom (A B : VTy) (g h : Val) (c : Val → Val) : Prop :=
  ∀ s, Evals (ℍ := ℍ) (.app (.val h) (.val s)) (c s) ∧
    (∀ r, Evals (ℍ := ℍ) (.app (.app (.val g) (.val s)) (.val nextO)) r →
      PureSteps (ℍ := ℍ) (.app (.val (c s)) (.val nextO)) (.app (.app (.val (mapV (nextTy A))) (.val h)) (.val r))) ∧
    (∀ r, Evals (ℍ := ℍ) (.app (.app (.val g) (.val s)) (.val closeO)) r →
      PureSteps (ℍ := ℍ) (.app (.val (c s)) (.val closeO)) (.app (.app (.val (mapV (B.rename Nat.succ))) (.val h)) (.val r)))

/-- `unfold g` is a coalgebra homomorphism from `g`, with `c s = unfold g s`. -/
theorem unfold_isCoHom (A B : VTy) (g : Val) :
    IsCoHom (ℍ := ℍ) A B g (hN (CTy.loopBody A B) g) (etaN (CTy.loopBody A B) g) := by
  intro s
  refine ⟨hN_steps _ g s, fun r hr => ?_, fun r hr => ?_⟩
  · exact (unfold_next A B g s).trans ((PureSteps.plug _ hr).trans (mapK_plug_val _ _ r))
  · exact (unfold_close A B g s).trans ((PureSteps.plug _ hr).trans (mapK_plug_val _ _ r))

/-- Two codata values give the same answers to every sequence of at most `n` observations:
`close` reaches one common value, and `next` finishes at one common value or goes on to two
rests that agree for `n - 1` more. -/
def Agree : Nat → Val → Val → Prop
  | 0, _, _ => True
  | n + 1, l₁, l₂ =>
      (∃ b, Evals (ℍ := ℍ) (.app (.val l₁) (.val closeO)) b ∧ Evals (ℍ := ℍ) (.app (.val l₂) (.val closeO)) b) ∧
      ((∃ a, Evals (ℍ := ℍ) (.app (.val l₁) (.val nextO)) (.inj₁ a) ∧
          Evals (ℍ := ℍ) (.app (.val l₂) (.val nextO)) (.inj₁ a)) ∨
       (∃ l₁' l₂', Evals (ℍ := ℍ) (.app (.val l₁) (.val nextO)) (.inj₂ l₁') ∧
          Evals (ℍ := ℍ) (.app (.val l₂) (.val nextO)) (.inj₂ l₂') ∧ Agree n l₁' l₂'))

/-- The step is pure and total: both observations of `g s` reach a value, and `next`'s is a
sum. -/
def StepTotal (g : Val) : Prop :=
  ∀ s, (∃ r, Evals (ℍ := ℍ) (.app (.app (.val g) (.val s)) (.val nextO)) r ∧
          ((∃ a, r = .inj₁ a) ∨ (∃ s', r = .inj₂ s'))) ∧
       (∃ b, Evals (ℍ := ℍ) (.app (.app (.val g) (.val s)) (.val closeO)) b)

/-- **Uniqueness of the unfold**, on finite observation sequences: two coalgebra homomorphisms
from one pure, total step agree on every `n` observations, at every state. -/
theorem coHoms_agree {A B : VTy} (hA : mapV (A.rename Nat.succ) = .lam (.val (.lam (.var 0))))
    (hB : mapV (B.rename Nat.succ) = .lam (.val (.lam (.var 0))))
    {g h₁ h₂ : Val} {c₁ c₂ : Val → Val} (hg : StepTotal (ℍ := ℍ) g)
    (e₁ : IsCoHom (ℍ := ℍ) A B g h₁ c₁) (e₂ : IsCoHom (ℍ := ℍ) A B g h₂ c₂) :
    ∀ n s, Agree (ℍ := ℍ) n (c₁ s) (c₂ s) := by
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
      intro s
      obtain ⟨⟨r, hr, hsum⟩, ⟨b, hb⟩⟩ := hg s
      obtain ⟨_, n₁, k₁⟩ := e₁ s
      obtain ⟨_, n₂, k₂⟩ := e₂ s
      refine ⟨⟨b, (k₁ b hb).trans (mapV_id_steps hB _ _), (k₂ b hb).trans (mapV_id_steps hB _ _)⟩, ?_⟩
      rcases hsum with ⟨a, rfl⟩ | ⟨s', rfl⟩
      · exact .inl ⟨a, (n₁ _ hr).trans (next_result_done hA _ _),
          (n₂ _ hr).trans (next_result_done hA _ _)⟩
      · exact .inr ⟨c₁ s', c₂ s', (n₁ _ hr).trans (next_result_more A _ _ _ (e₁ s').1),
          (n₂ _ hr).trans (next_result_more A _ _ _ (e₂ s').1), ih s'⟩

/-- **Uniqueness**, against `unfold g`: every coalgebra homomorphism from a pure, total step
agrees with `unfold g` on every finite sequence of observations. -/
theorem unfold_unique {A B : VTy} (hA : mapV (A.rename Nat.succ) = .lam (.val (.lam (.var 0))))
    (hB : mapV (B.rename Nat.succ) = .lam (.val (.lam (.var 0))))
    {g h : Val} {c : Val → Val} (hg : StepTotal (ℍ := ℍ) g) (eh : IsCoHom (ℍ := ℍ) A B g h c)
    (n : Nat) (s : Val) : Agree (ℍ := ℍ) n (c s) (etaN (CTy.loopBody A B) g s) :=
  coHoms_agree hA hB hg eh (unfold_isCoHom A B g) n s

end BoCa.Fig16.LogRel.Core.CoeffectsStrict

end
