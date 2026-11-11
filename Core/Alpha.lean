import Core.RelationFacts
import Core.Persistent

/-!
# Core — α-equivalence of types  `[spec §3]`

`VTy.alphaB`/`CTy.alphaB` (`Core/Types.lean`) decide that two types are equal up to the names of
their lifetime binders.  This file proves the decision sound for `TyEq`/`CTyEq` at one
substitution (`VTy.alphaB_sound`, `CTy.alphaB_sound`), so the relation reads two α-equivalent
types alike (`vC_alpha`, `cC_alpha`).  That is the compatibility lemma of the conversion rule
`CDerives.alpha`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `δ` and `δ'` agree on the variables the binder pairs `ρ` relate. -/
def AlphaAgree (ρ : List (LifeVar × LifeVar)) (δ δ' : LSub) : Prop :=
  ∀ x y, varAlphaB ρ x y = true → δ.find? x = δ'.find? y

theorem alphaAgree_nil (δ : LSub) : AlphaAgree [] δ δ := by
  intro x y h
  simp only [varAlphaB, beq_iff_eq] at h
  rw [h]

/-- Passing a pair of binders, both sides extended at one lifetime. -/
theorem AlphaAgree.extend {ρ : List (LifeVar × LifeVar)} {δ δ' : LSub} (h : AlphaAgree ρ δ δ')
    (x x' : LifeVar) (α : Life) : AlphaAgree ((x, x') :: ρ) (δ.extend x α) (δ'.extend x' α) := by
  intro y y' hy
  simp only [varAlphaB] at hy
  by_cases hyx : y = x
  · subst hyx
    simp only [if_true, beq_iff_eq] at hy
    subst hy
    rw [find?_extend_self, find?_extend_self]
  · rw [if_neg hyx] at hy
    by_cases hy'x : y' = x'
    · rw [if_pos hy'x] at hy; cases hy
    · rw [if_neg hy'x] at hy
      rw [find?_extend_ne δ α (Ne.symm hyx), find?_extend_ne δ' α (Ne.symm hy'x)]
      exact h y y' hy

theorem lifeAlphaB_sound {ρ : List (LifeVar × LifeVar)} {δ δ' : LSub} (h : AlphaAgree ρ δ δ') :
    ∀ (a a' : Lifetime.Life), lifeAlphaB ρ a a' = true → a.interp δ = a'.interp δ'
  | .var x, .var y, hα => h x y hα
  | .top, .top, _ => rfl
  | .join a b, .join a' b', hα => by
      simp only [lifeAlphaB, Bool.and_eq_true] at hα
      simp only [Lifetime.Life.interp, lifeAlphaB_sound h a a' hα.1, lifeAlphaB_sound h b b' hα.2]
  | .meet a b, .meet a' b', hα => by
      simp only [lifeAlphaB, Bool.and_eq_true] at hα
      simp only [Lifetime.Life.interp, lifeAlphaB_sound h a a' hα.1, lifeAlphaB_sound h b b' hα.2]
  | .var _, .top, hα | .var _, .join _ _, hα | .var _, .meet _ _, hα
  | .top, .var _, hα | .top, .join _ _, hα | .top, .meet _ _, hα
  | .join _ _, .var _, hα | .join _ _, .top, hα | .join _ _, .meet _ _, hα
  | .meet _ _, .var _, hα | .meet _ _, .top, hα | .meet _ _, .join _ _, hα => by
      simp [lifeAlphaB] at hα

mutual
/-- **α-equivalent value types are one type** (`TyEq`) at substitutions agreeing on the binder
pairs.  `[spec §3]` -/
theorem VTy.alphaB_sound : ∀ {ρ : List (LifeVar × LifeVar)} {δ δ' : LSub} (A A' : VTy),
    AlphaAgree ρ δ δ' → VTy.alphaB ρ A A' = true → TyEq A δ A' δ'
  | _, _, _, .unit, A', _, hα | _, _, _, .zero, A', _, hα | _, _, _, .unk, A', _, hα
  | _, _, _, .int _, A', _, hα | _, _, _, .opq _, A', _, hα | _, _, _, .tvar _, A', _, hα => by
      cases A' <;> simp_all [VTy.alphaB, TyEq]
  | _, _, _, .tensor A B, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨VTy.alphaB_sound A _ h hα.1, VTy.alphaB_sound B _ h hα.2⟩
  | _, _, _, .sum A B, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨VTy.alphaB_sound A _ h hα.1, VTy.alphaB_sound B _ h hα.2⟩
  | _, _, _, .thunk C, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at hα
      exact CTy.alphaB_sound C _ h hα
  | _, _, _, .code _ E C, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at hα
      exact ⟨hα.1.1, VTy.alphaB_sound E _ h hα.1.2, CTy.alphaB_sound C _ h hα.2⟩
  | _, _, _, .ref A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at hα
      exact VTy.alphaB_sound A _ h hα
  | _, _, _, .bang A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at hα
      exact VTy.alphaB_sound A _ h hα
  | _, _, _, .fam A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at hα
      exact VTy.alphaB_sound A _ h hα
  | _, _, _, .mu A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at hα
      exact VTy.alphaB_sound A _ h hα
  | _, _, _, .imm a A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨lifeAlphaB_sound h _ _ hα.1, VTy.alphaB_sound A _ h hα.2⟩
  | _, _, _, .mut a A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨lifeAlphaB_sound h _ _ hα.1, VTy.alphaB_sound A _ h hα.2⟩
  | _, _, _, .box a A, A', h, hα => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨lifeAlphaB_sound h _ _ hα.1, VTy.alphaB_sound A _ h hα.2⟩
/-- **α-equivalent computation types are one type** (`CTyEq`) at substitutions agreeing on the
binder pairs.  `[spec §3]` -/
theorem CTy.alphaB_sound : ∀ {ρ : List (LifeVar × LifeVar)} {δ δ' : LSub} (C C' : CTy),
    AlphaAgree ρ δ δ' → CTy.alphaB ρ C C' = true → CTyEq C δ C' δ'
  | _, _, _, .top, C', _, hα => by cases C' <;> simp_all [CTy.alphaB, CTyEq]
  | _, _, _, .ret A, C', h, hα => by
      cases C' <;> simp only [CTy.alphaB, reduceCtorEq] at hα
      exact VTy.alphaB_sound A _ h hα
  | _, _, _, .arr A C, C', h, hα => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨VTy.alphaB_sound A _ h hα.1, CTy.alphaB_sound C _ h hα.2⟩
  | _, _, _, .amp C D, C', h, hα => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact ⟨CTy.alphaB_sound C _ h hα.1, CTy.alphaB_sound D _ h hα.2⟩
  | _, _, _, .nuSys _ _ C, C', h, hα => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at hα
      exact CTy.alphaB_sound C _ h hα.2
  | _, _, _, .all x b C, C', h, hα => by
      cases C' with
      | all x' b' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at hα
          exact ⟨lifeAlphaB_sound h _ _ hα.1, fun α => CTy.alphaB_sound C C' (h.extend x x' α) hα.2⟩
      | _ => simp [CTy.alphaB] at hα
  | _, _, _, .eff n i q A B fin rc C, C', h, hα => by
      cases C' with
      | eff n' i' q' A' B' fin' rc' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hα
          obtain ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, -⟩, hA⟩, hB⟩, hf⟩, hC⟩ := hα
          exact ⟨hn, hi, hq, VTy.alphaB_sound A A' h hA, VTy.alphaB_sound B B' h hB,
            CTy.alphaB_sound fin fin' h hf, CTy.alphaB_sound C C' h hC⟩
      | _ => simp [CTy.alphaB] at hα
end

/-! ### α-equivalence is an equivalence

At no binder pairs `alphaB` is reflexive, symmetric and transitive.  Under binders the pairs are a
diagonal (reflexivity), swapped (symmetry), or composed (transitivity). -/

/-- Binder pairs that pair each binder with itself. -/
def AlphaDiag (ρ : List (LifeVar × LifeVar)) : Prop := ∀ p ∈ ρ, p.1 = p.2

theorem AlphaDiag.cons {ρ : List (LifeVar × LifeVar)} (h : AlphaDiag ρ) (x : LifeVar) :
    AlphaDiag ((x, x) :: ρ) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  · exact h p hp

theorem varAlphaB_diag : ∀ {ρ : List (LifeVar × LifeVar)}, AlphaDiag ρ → ∀ x, varAlphaB ρ x x = true
  | [], _, x => by simp [varAlphaB]
  | (a, b) :: ρ, h, x => by
      have hab : a = b := h (a, b) (by simp)
      subst hab
      have h' : AlphaDiag ρ := fun p hp => h p (by simp [hp])
      simp only [varAlphaB]
      by_cases hx : x = a
      · simp [hx]
      · simp [hx, varAlphaB_diag h' x]

theorem lifeAlphaB_diag {ρ : List (LifeVar × LifeVar)} (h : AlphaDiag ρ) :
    ∀ a : Lifetime.Life, lifeAlphaB ρ a a = true
  | .var x => varAlphaB_diag h x
  | .top => rfl
  | .join a b => by simp [lifeAlphaB, lifeAlphaB_diag h a, lifeAlphaB_diag h b]
  | .meet a b => by simp [lifeAlphaB, lifeAlphaB_diag h a, lifeAlphaB_diag h b]

mutual
theorem VTy.alphaB_diag : ∀ {ρ : List (LifeVar × LifeVar)}, AlphaDiag ρ → ∀ A : VTy,
    VTy.alphaB ρ A A = true
  | _, _, .unit | _, _, .zero | _, _, .unk | _, _, .int _ | _, _, .opq _ | _, _, .tvar _ => by
      simp [VTy.alphaB]
  | _, h, .tensor A B | _, h, .sum A B => by
      simp [VTy.alphaB, VTy.alphaB_diag h A, VTy.alphaB_diag h B]
  | _, h, .thunk C => by simp [VTy.alphaB, CTy.alphaB_diag h C]
  | _, h, .code _ E C => by simp [VTy.alphaB, VTy.alphaB_diag h E, CTy.alphaB_diag h C]
  | _, h, .ref A | _, h, .bang A | _, h, .fam A | _, h, .mu A => by
      simp [VTy.alphaB, VTy.alphaB_diag h A]
  | _, h, .imm a A | _, h, .mut a A | _, h, .box a A => by
      simp [VTy.alphaB, VTy.alphaB_diag h A, lifeAlphaB_diag h a]
theorem CTy.alphaB_diag : ∀ {ρ : List (LifeVar × LifeVar)}, AlphaDiag ρ → ∀ C : CTy,
    CTy.alphaB ρ C C = true
  | _, _, .top => rfl
  | _, h, .ret A => by simp [CTy.alphaB, VTy.alphaB_diag h A]
  | _, h, .arr A C => by simp [CTy.alphaB, VTy.alphaB_diag h A, CTy.alphaB_diag h C]
  | _, h, .amp C D => by simp [CTy.alphaB, CTy.alphaB_diag h C, CTy.alphaB_diag h D]
  | _, h, .nuSys _ _ C => by simp [CTy.alphaB, CTy.alphaB_diag h C]
  | _, h, .all x b C => by
      simp [CTy.alphaB, lifeAlphaB_diag h b, CTy.alphaB_diag (h.cons x) C]
  | _, h, .eff n i q A B fin rc C => by
      simp [CTy.alphaB, VTy.alphaB_diag h A, VTy.alphaB_diag h B, CTy.alphaB_diag h fin,
        CTy.alphaB_diag h C]
end

theorem VTy.alphaB_refl (A : VTy) : VTy.alphaB [] A A = true :=
  VTy.alphaB_diag (fun _ h => absurd h List.not_mem_nil) A

theorem CTy.alphaB_refl (C : CTy) : CTy.alphaB [] C C = true :=
  CTy.alphaB_diag (fun _ h => absurd h List.not_mem_nil) C

/-- `[α]` is reflexive at `Code⟨N; E⟩ C`: the code is equal, `E` and `C` are reflexive.
`[spec §68]` -/
theorem VTy.alphaB_refl_code (N : Expr) (E : VTy) (C : CTy) :
    VTy.alphaB [] (.code N E C) (.code N E C) = true := VTy.alphaB_refl _

/-- The binder pairs read the other way. -/
def alphaSwap (ρ : List (LifeVar × LifeVar)) : List (LifeVar × LifeVar) := ρ.map Prod.swap

theorem varAlphaB_swap : ∀ (ρ : List (LifeVar × LifeVar)) (x y : LifeVar),
    varAlphaB (alphaSwap ρ) y x = varAlphaB ρ x y
  | [], x, y => by simp [alphaSwap, varAlphaB, eq_comm]
  | (a, b) :: ρ, x, y => by
      have ih := varAlphaB_swap ρ x y
      simp only [alphaSwap, List.map_cons, Prod.swap_prod_mk] at ih ⊢
      simp only [varAlphaB]
      by_cases hx : x = a <;> by_cases hy : y = b <;> simp_all

theorem lifeAlphaB_swap (ρ : List (LifeVar × LifeVar)) :
    ∀ a a' : Lifetime.Life, lifeAlphaB (alphaSwap ρ) a' a = lifeAlphaB ρ a a'
  | .var x, .var y => varAlphaB_swap ρ x y
  | .top, .top => rfl
  | .join a b, .join a' b' => by simp [lifeAlphaB, lifeAlphaB_swap ρ a a', lifeAlphaB_swap ρ b b']
  | .meet a b, .meet a' b' => by simp [lifeAlphaB, lifeAlphaB_swap ρ a a', lifeAlphaB_swap ρ b b']
  | .var _, .top | .var _, .join _ _ | .var _, .meet _ _
  | .top, .var _ | .top, .join _ _ | .top, .meet _ _
  | .join _ _, .var _ | .join _ _, .top | .join _ _, .meet _ _
  | .meet _ _, .var _ | .meet _ _, .top | .meet _ _, .join _ _ => rfl

mutual
theorem VTy.alphaB_swap : ∀ (ρ : List (LifeVar × LifeVar)) (A A' : VTy),
    VTy.alphaB ρ A A' = true → VTy.alphaB (alphaSwap ρ) A' A = true
  | _, .unit, A', h | _, .zero, A', h | _, .unk, A', h | _, .int _, A', h | _, .opq _, A', h
  | _, .tvar _, A', h => by
      cases A' <;> simp only [VTy.alphaB, decide_eq_true_eq, beq_iff_eq, reduceCtorEq] at h ⊢ <;>
        exact h.symm
  | ρ, .tensor A B, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨VTy.alphaB_swap ρ A _ h.1, VTy.alphaB_swap ρ B _ h.2⟩
  | ρ, .sum A B, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨VTy.alphaB_swap ρ A _ h.1, VTy.alphaB_swap ρ B _ h.2⟩
  | ρ, .thunk C, A', h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at h ⊢
      exact CTy.alphaB_swap ρ C _ h
  | ρ, .code _ E C, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h ⊢
      exact ⟨⟨h.1.1.symm, VTy.alphaB_swap ρ E _ h.1.2⟩, CTy.alphaB_swap ρ C _ h.2⟩
  | ρ, .ref A, A', h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at h ⊢; exact VTy.alphaB_swap ρ A _ h
  | ρ, .bang A, A', h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at h ⊢; exact VTy.alphaB_swap ρ A _ h
  | ρ, .fam A, A', h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at h ⊢; exact VTy.alphaB_swap ρ A _ h
  | ρ, .mu A, A', h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq] at h ⊢; exact VTy.alphaB_swap ρ A _ h
  | ρ, .imm a A, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨(lifeAlphaB_swap ρ _ _).trans h.1, VTy.alphaB_swap ρ A _ h.2⟩
  | ρ, .mut a A, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨(lifeAlphaB_swap ρ _ _).trans h.1, VTy.alphaB_swap ρ A _ h.2⟩
  | ρ, .box a A, A', h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨(lifeAlphaB_swap ρ _ _).trans h.1, VTy.alphaB_swap ρ A _ h.2⟩
theorem CTy.alphaB_swap : ∀ (ρ : List (LifeVar × LifeVar)) (C C' : CTy),
    CTy.alphaB ρ C C' = true → CTy.alphaB (alphaSwap ρ) C' C = true
  | _, .top, C', h => by cases C' <;> simp_all [CTy.alphaB]
  | ρ, .ret A, C', h => by
      cases C' <;> simp only [CTy.alphaB, reduceCtorEq] at h ⊢; exact VTy.alphaB_swap ρ A _ h
  | ρ, .arr A C, C', h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨VTy.alphaB_swap ρ A _ h.1, CTy.alphaB_swap ρ C _ h.2⟩
  | ρ, .amp C D, C', h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h ⊢
      exact ⟨CTy.alphaB_swap ρ C _ h.1, CTy.alphaB_swap ρ D _ h.2⟩
  | ρ, .nuSys _ _ C, C', h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at h ⊢
      exact ⟨⟨h.1.1.symm, h.1.2.symm⟩, CTy.alphaB_swap ρ C _ h.2⟩
  | ρ, .all x b C, C', h => by
      cases C' with
      | all x' b' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h ⊢
          exact ⟨(lifeAlphaB_swap ρ _ _).trans h.1, CTy.alphaB_swap ((x, x') :: ρ) C C' h.2⟩
      | _ => simp [CTy.alphaB] at h
  | ρ, .eff n i q A B fin rc C, C', h => by
      cases C' with
      | eff n' i' q' A' B' fin' rc' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
          obtain ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, hr⟩, hA'⟩, hB'⟩, hf'⟩, hC⟩ := h
          exact ⟨⟨⟨⟨⟨⟨⟨hn.symm, hi.symm⟩, hq.symm⟩, hr.symm⟩,
            VTy.alphaB_swap ρ A A' hA'⟩, VTy.alphaB_swap ρ B B' hB'⟩,
            CTy.alphaB_swap ρ fin fin' hf'⟩, CTy.alphaB_swap ρ C C' hC⟩
      | _ => simp [CTy.alphaB] at h
end

theorem VTy.alphaB_symm {A A' : VTy} (h : VTy.alphaB [] A A' = true) : VTy.alphaB [] A' A = true :=
  VTy.alphaB_swap [] A A' h

theorem CTy.alphaB_symm {C C' : CTy} (h : CTy.alphaB [] C C' = true) : CTy.alphaB [] C' C = true :=
  CTy.alphaB_swap [] C C' h

/-- Two lists of binder pairs composed, the right of the first being the left of the second. -/
def alphaComp : List (LifeVar × LifeVar) → List (LifeVar × LifeVar) → List (LifeVar × LifeVar)
  | (a, _) :: ρ₁, (_, c) :: ρ₂ => (a, c) :: alphaComp ρ₁ ρ₂
  | _, _ => []

/-- `ρ₁`'s right binders are `ρ₂`'s left ones. -/
def AlphaMatch : List (LifeVar × LifeVar) → List (LifeVar × LifeVar) → Prop
  | [], [] => True
  | (_, b) :: ρ₁, (b', _) :: ρ₂ => b = b' ∧ AlphaMatch ρ₁ ρ₂
  | _, _ => False

theorem varAlphaB_trans : ∀ {ρ₁ ρ₂ : List (LifeVar × LifeVar)}, AlphaMatch ρ₁ ρ₂ →
    ∀ {x y z : LifeVar}, varAlphaB ρ₁ x y = true → varAlphaB ρ₂ y z = true →
      varAlphaB (alphaComp ρ₁ ρ₂) x z = true
  | [], [], _, x, y, z, h₁, h₂ => by
      simp only [alphaComp, varAlphaB, beq_iff_eq] at h₁ h₂ ⊢; exact h₁.trans h₂
  | (a, b) :: ρ₁, (b', c) :: ρ₂, hm, x, y, z, h₁, h₂ => by
      obtain ⟨rfl, hm⟩ := hm
      simp only [alphaComp, varAlphaB] at h₁ h₂ ⊢
      by_cases hx : x = a
      · simp only [hx, if_true, beq_iff_eq] at h₁ ⊢
        subst h₁
        simpa using h₂
      · simp only [hx, if_false] at h₁ ⊢
        by_cases hy : y = b
        · simp [hy] at h₁
        · simp only [hy, if_false] at h₁ h₂
          by_cases hz : z = c
          · simp [hz] at h₂
          · simp only [hz, if_false] at h₂ ⊢
            exact varAlphaB_trans hm h₁ h₂
  | [], _ :: _, hm, _, _, _, _, _ | _ :: _, [], hm, _, _, _, _, _ => hm.elim

theorem lifeAlphaB_trans {ρ₁ ρ₂ : List (LifeVar × LifeVar)} (hm : AlphaMatch ρ₁ ρ₂) :
    ∀ (a b c : Lifetime.Life), lifeAlphaB ρ₁ a b = true → lifeAlphaB ρ₂ b c = true →
      lifeAlphaB (alphaComp ρ₁ ρ₂) a c = true := by
  intro a
  induction a with
  | var x =>
      intro b c h₁ h₂
      cases b <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true] at h₁
      cases c <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true] at h₂ ⊢
      exact varAlphaB_trans hm h₁ h₂
  | top =>
      intro b c h₁ h₂
      cases b <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true] at h₁
      cases c <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true] at h₂ ⊢
  | join a₁ a₂ ih₁ ih₂ =>
      intro b c h₁ h₂
      cases b <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true, Bool.and_eq_true] at h₁
      cases c <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true, Bool.and_eq_true] at h₂ ⊢
      exact ⟨ih₁ _ _ h₁.1 h₂.1, ih₂ _ _ h₁.2 h₂.2⟩
  | meet a₁ a₂ ih₁ ih₂ =>
      intro b c h₁ h₂
      cases b <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true, Bool.and_eq_true] at h₁
      cases c <;> simp only [lifeAlphaB, reduceCtorEq, Bool.false_eq_true, Bool.and_eq_true] at h₂ ⊢
      exact ⟨ih₁ _ _ h₁.1 h₂.1, ih₂ _ _ h₁.2 h₂.2⟩

mutual
theorem VTy.alphaB_trans : ∀ {ρ₁ ρ₂ : List (LifeVar × LifeVar)}, AlphaMatch ρ₁ ρ₂ →
    ∀ (A B C : VTy), VTy.alphaB ρ₁ A B = true → VTy.alphaB ρ₂ B C = true →
      VTy.alphaB (alphaComp ρ₁ ρ₂) A C = true
  | _, _, _, .unit, B, C, h₁, h₂ | _, _, _, .zero, B, C, h₁, h₂ | _, _, _, .unk, B, C, h₁, h₂
  | _, _, _, .int _, B, C, h₁, h₂ | _, _, _, .opq _, B, C, h₁, h₂
  | _, _, _, .tvar _, B, C, h₁, h₂ => by
      cases B <;> simp [VTy.alphaB] at h₁ <;> cases C <;> simp_all [VTy.alphaB]
  | _, _, hm, .tensor A₁ A₂, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨VTy.alphaB_trans hm _ _ _ h₁.1 h₂.1, VTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .sum A₁ A₂, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨VTy.alphaB_trans hm _ _ _ h₁.1 h₂.1, VTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .thunk D, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact CTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .code _ E D, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h₂ ⊢
      exact ⟨⟨h₁.1.1.trans h₂.1.1, VTy.alphaB_trans hm _ _ _ h₁.1.2 h₂.1.2⟩,
        CTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .ref A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact VTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .bang A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact VTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .fam A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact VTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .mu A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact VTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .imm a A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨lifeAlphaB_trans hm _ _ _ h₁.1 h₂.1, VTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .mut a A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨lifeAlphaB_trans hm _ _ _ h₁.1 h₂.1, VTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .box a A, B, C, h₁, h₂ => by
      cases B <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases C <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨lifeAlphaB_trans hm _ _ _ h₁.1 h₂.1, VTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
theorem CTy.alphaB_trans : ∀ {ρ₁ ρ₂ : List (LifeVar × LifeVar)}, AlphaMatch ρ₁ ρ₂ →
    ∀ (C D E : CTy), CTy.alphaB ρ₁ C D = true → CTy.alphaB ρ₂ D E = true →
      CTy.alphaB (alphaComp ρ₁ ρ₂) C E = true
  | _, _, _, .top, D, E, h₁, h₂ => by
      cases D <;> simp [CTy.alphaB] at h₁ <;> cases E <;> simp_all [CTy.alphaB]
  | _, _, hm, .ret A, D, E, h₁, h₂ => by
      cases D <;> simp only [CTy.alphaB, reduceCtorEq] at h₁
      cases E <;> simp only [CTy.alphaB, reduceCtorEq] at h₂ ⊢
      exact VTy.alphaB_trans hm _ _ _ h₁ h₂
  | _, _, hm, .arr A C, D, E, h₁, h₂ => by
      cases D <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases E <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨VTy.alphaB_trans hm _ _ _ h₁.1 h₂.1, CTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .amp C C', D, E, h₁, h₂ => by
      cases D <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₁
      cases E <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq] at h₂ ⊢
      exact ⟨CTy.alphaB_trans hm _ _ _ h₁.1 h₂.1, CTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | _, _, hm, .nuSys _ _ C, D, E, h₁, h₂ => by
      cases D <;> simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at h₁
      cases E <;> simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at h₂ ⊢
      exact ⟨⟨h₁.1.1.trans h₂.1.1, h₁.1.2.trans h₂.1.2⟩, CTy.alphaB_trans hm _ _ _ h₁.2 h₂.2⟩
  | ρ₁, ρ₂, hm, .all x b C, D, E, h₁, h₂ => by
      cases D with
      | all y b' D =>
          cases E with
          | all z b'' E =>
              simp only [CTy.alphaB, Bool.and_eq_true] at h₁ h₂ ⊢
              exact ⟨lifeAlphaB_trans hm _ _ _ h₁.1 h₂.1,
                CTy.alphaB_trans (ρ₁ := (x, y) :: ρ₁) (ρ₂ := (y, z) :: ρ₂) ⟨rfl, hm⟩ _ _ _
                  h₁.2 h₂.2⟩
          | _ => simp [CTy.alphaB] at h₂
      | _ => simp [CTy.alphaB] at h₁
  | _, _, hm, .eff n i q A B fin rc C, D, E, h₁, h₂ => by
      cases D with
      | eff n' i' q' A' B' fin' rc' D =>
          cases E with
          | eff n'' i'' q'' A'' B'' fin'' rc'' E =>
              simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h₁ h₂ ⊢
              obtain ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, hr⟩, hA'⟩, hB'⟩, hf'⟩, hC⟩ := h₁
              obtain ⟨⟨⟨⟨⟨⟨⟨gn, gi⟩, gq⟩, gr⟩, gA'⟩, gB'⟩, gf'⟩, gC⟩ := h₂
              exact ⟨⟨⟨⟨⟨⟨⟨hn.trans gn, hi.trans gi⟩, hq.trans gq⟩, hr.trans gr⟩,
                VTy.alphaB_trans hm _ _ _ hA' gA'⟩,
                VTy.alphaB_trans hm _ _ _ hB' gB'⟩, CTy.alphaB_trans hm _ _ _ hf' gf'⟩,
                CTy.alphaB_trans hm _ _ _ hC gC⟩
          | _ => simp [CTy.alphaB] at h₂
      | _ => simp [CTy.alphaB] at h₁
end

theorem VTy.alphaB_trans' {A B C : VTy} (h₁ : VTy.alphaB [] A B = true)
    (h₂ : VTy.alphaB [] B C = true) : VTy.alphaB [] A C = true :=
  VTy.alphaB_trans (ρ₁ := []) (ρ₂ := []) trivial A B C h₁ h₂

theorem CTy.alphaB_trans' {C D E : CTy} (h₁ : CTy.alphaB [] C D = true)
    (h₂ : CTy.alphaB [] D E = true) : CTy.alphaB [] C E = true :=
  CTy.alphaB_trans (ρ₁ := []) (ρ₂ := []) trivial C D E h₁ h₂

/-! ### What α-equivalence keeps

The value-type formers and their order, and so persistence; and `μ`'s substitution, which never
reaches under a `U`, so under no lifetime binder. -/

theorem VTy.alphaB_persistent {ρ : List (LifeVar × LifeVar)} (A : VTy) :
    ∀ {A' : VTy}, VTy.alphaB ρ A A' = true → A.persistent = A'.persistent := by
  induction A using VTy.recV with
  | unit | zero | unk | int _ | opq _ | tvar _ | thunk _ | code _ _ _ _ =>
      intro A' h; cases A' <;> simp_all [VTy.alphaB, VTy.persistent]
  | tensor A B ihA ihB | sum A B ihA ihB =>
      intro A' h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.persistent, ihA h.1, ihB h.2]
  | ref A _ | fam A _ =>
      intro A' h; cases A' <;> simp_all [VTy.alphaB, VTy.persistent]
  | bang A _ =>
      intro A' h; cases A' <;> simp_all [VTy.alphaB, VTy.persistent]
  | mu A ih =>
      intro A' h
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.persistent, ih h]
  | imm a A _ | «mut» a A _ =>
      intro A' h; cases A' <;> simp_all [VTy.alphaB, VTy.persistent]
  | box a A ih =>
      intro A' h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.persistent, ih h.2]

theorem VTy.alphaB_rename {ρ : List (LifeVar × LifeVar)} (A : VTy) :
    ∀ {A' : VTy} (r : Nat → Nat), VTy.alphaB ρ A A' = true →
      VTy.alphaB ρ (A.rename r) (A'.rename r) = true := by
  induction A using VTy.recV with
  | unit | zero | unk | int _ | opq _ | thunk _ | code _ _ _ _ =>
      intro A' r h; cases A' <;> simp_all [VTy.alphaB, VTy.rename]
  | tvar n =>
      intro A' r h; cases A' <;> simp_all [VTy.alphaB, VTy.rename]
  | tensor A B ihA ihB | sum A B ihA ihB =>
      intro A' r h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.rename, VTy.alphaB, ihA r h.1, ihB r h.2, Bool.and_self]
  | ref A ih | fam A ih | bang A ih =>
      intro A' r h
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.rename, VTy.alphaB, ih r h]
  | mu A ih =>
      intro A' r h
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.rename, VTy.alphaB, ih _ h]
  | imm a A ih | «mut» a A ih | box a A ih =>
      intro A' r h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.rename, VTy.alphaB, h.1, ih r h.2, Bool.and_self]

theorem VTy.alphaB_subst {ρ : List (LifeVar × LifeVar)} (A : VTy) :
    ∀ {A' : VTy} {σ σ' : Nat → VTy}, (∀ n, VTy.alphaB ρ (σ n) (σ' n) = true) →
      VTy.alphaB ρ A A' = true → VTy.alphaB ρ (A.subst σ) (A'.subst σ') = true := by
  induction A using VTy.recV with
  | unit | zero | unk | int _ | opq _ | thunk _ | code _ _ _ _ =>
      intro A' σ σ' _ h; cases A' <;> simp_all [VTy.alphaB, VTy.subst]
  | tvar n =>
      intro A' σ σ' hσ h
      cases A' <;> simp only [VTy.alphaB, beq_iff_eq, reduceCtorEq, Bool.false_eq_true] at h
      subst h; exact hσ n
  | tensor A B ihA ihB | sum A B ihA ihB =>
      intro A' σ σ' hσ h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.subst, VTy.alphaB, ihA hσ h.1, ihB hσ h.2, Bool.and_self]
  | ref A ih | fam A ih | bang A ih =>
      intro A' σ σ' hσ h
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.subst, VTy.alphaB, ih hσ h]
  | mu A ih =>
      intro A' σ σ' hσ h
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      refine ih (fun n => ?_) h
      cases n with
      | zero => simp [VTy.upS, VTy.scons, VTy.alphaB]
      | succ n => exact VTy.alphaB_rename _ _ (hσ n)
  | imm a A ih | «mut» a A ih | box a A ih =>
      intro A' σ σ' hσ h
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h
      simp only [VTy.subst, VTy.alphaB, h.1, ih hσ h.2, Bool.and_self]

/-- `μ`'s unrolling respects α-equivalence. -/
theorem VTy.alphaB_inst {ρ : List (LifeVar × LifeVar)} {S S' A A' : VTy}
    (hS : VTy.alphaB ρ S S' = true) (hA : VTy.alphaB ρ A A' = true) :
    VTy.alphaB ρ (VTy.inst S A) (VTy.inst S' A') = true :=
  VTy.alphaB_subst A (fun n => by cases n <;> simp [VTy.scons, VTy.alphaB, hS]) hA

/-! ### Binder pairs that no free variable meets

Pairs `ρ₀` may be inserted below the binders `ρ₁` when every variable of the two sides that
meets a pair of `ρ₀` is bound by `ρ₁`.  So a type under no binder is read alike under binders
none of whose names is free in it (`VTy.alphaB_lift`), which is what unrolling `νX. C` under a
`∀` leaf needs (`CTy.alphaB_unroll`). -/

theorem varAlphaB_pass (ρ₀ ρ : List (LifeVar × LifeVar)) {y y' : LifeVar}
    (h : ∀ p ∈ ρ₀, y ≠ p.1 ∧ y' ≠ p.2) : varAlphaB (ρ₀ ++ ρ) y y' = varAlphaB ρ y y' := by
  induction ρ₀ with
  | nil => rfl
  | cons p ρ₀ ih =>
      obtain ⟨a, b⟩ := p
      have h₁ := h (a, b) (by simp)
      simp only [List.cons_append, varAlphaB, if_neg h₁.1, if_neg h₁.2]
      exact ih (fun p hp => h p (by simp [hp]))

/-- `ρ₀` is met, past the binders `ρ₁`, only by variables `ρ₁` binds: on the left at `P`, on the
right at `P'`. -/
def AlphaAvoid (ρ₀ ρ₁ : List (LifeVar × LifeVar)) (P P' : LifeVar → Prop) : Prop :=
  ∀ p ∈ ρ₀, (P p.1 → p.1 ∈ ρ₁.map Prod.fst) ∧ (P' p.2 → p.2 ∈ ρ₁.map Prod.snd)

theorem AlphaAvoid.mono {ρ₀ ρ₁ : List (LifeVar × LifeVar)} {P P' Q Q' : LifeVar → Prop}
    (h : AlphaAvoid ρ₀ ρ₁ P P') (hQ : ∀ x, Q x → P x) (hQ' : ∀ x, Q' x → P' x) :
    AlphaAvoid ρ₀ ρ₁ Q Q' :=
  fun p hp => ⟨fun q => (h p hp).1 (hQ _ q), fun q => (h p hp).2 (hQ' _ q)⟩

/-- Past one more binder pair, a variable free in the body is that binder or free outside. -/
theorem AlphaAvoid.under {ρ₀ ρ₁ : List (LifeVar × LifeVar)} {P P' Q Q' : LifeVar → Prop}
    {x x' : LifeVar} (h : AlphaAvoid ρ₀ ρ₁ P P') (hQ : ∀ y, Q y → y ≠ x → P y)
    (hQ' : ∀ y, Q' y → y ≠ x' → P' y) : AlphaAvoid ρ₀ ((x, x') :: ρ₁) Q Q' := by
  intro p hp
  refine ⟨fun q => ?_, fun q => ?_⟩
  · by_cases e : p.1 = x
    · simp [e]
    · exact List.mem_cons_of_mem _ ((h p hp).1 (hQ _ q e))
  · by_cases e : p.2 = x'
    · simp [e]
    · exact List.mem_cons_of_mem _ ((h p hp).2 (hQ' _ q e))

theorem varAlphaB_insert (ρ₀ ρ : List (LifeVar × LifeVar)) :
    ∀ (ρ₁ : List (LifeVar × LifeVar)) {y y' : LifeVar},
      AlphaAvoid ρ₀ ρ₁ (· = y) (· = y') →
        varAlphaB (ρ₁ ++ ρ₀ ++ ρ) y y' = varAlphaB (ρ₁ ++ ρ) y y'
  | [], y, y', h => by
      simp only [List.nil_append]
      exact varAlphaB_pass ρ₀ ρ (fun p hp =>
        ⟨fun e => by simpa using (h p hp).1 e.symm, fun e => by simpa using (h p hp).2 e.symm⟩)
  | (a, b) :: ρ₁, y, y', h => by
      simp only [List.cons_append, varAlphaB]
      by_cases hya : y = a
      · simp [hya]
      · by_cases hyb : y' = b
        · simp [hya, hyb]
        · simp only [if_neg hya, if_neg hyb]
          refine varAlphaB_insert ρ₀ ρ ρ₁ (fun p hp => ⟨fun e => ?_, fun e => ?_⟩)
          · have := (h p hp).1 e
            subst e
            exact (List.mem_cons.mp this).resolve_left hya
          · have := (h p hp).2 e
            subst e
            exact (List.mem_cons.mp this).resolve_left hyb

theorem lifeAlphaB_insert (ρ₀ ρ ρ₁ : List (LifeVar × LifeVar)) :
    ∀ (a a' : Lifetime.Life), AlphaAvoid ρ₀ ρ₁ (a.mentions · = true) (a'.mentions · = true) →
      lifeAlphaB (ρ₁ ++ ρ) a a' = true → lifeAlphaB (ρ₁ ++ ρ₀ ++ ρ) a a' = true := by
  intro a
  induction a with
  | var y =>
      intro a' hv h
      cases a' with
      | var y' =>
          simp only [lifeAlphaB] at h ⊢
          rw [varAlphaB_insert ρ₀ ρ ρ₁ (hv.mono (fun z hz => by
            simp [Lifetime.Life.mentions, hz]) (fun z hz => by simp [Lifetime.Life.mentions, hz]))]
          exact h
      | _ => simp [lifeAlphaB] at h
  | top => intro a' _ h; cases a' <;> simp_all [lifeAlphaB]
  | join a b iha ihb =>
      intro a' hv h
      cases a' <;> simp only [lifeAlphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨iha _ (hv.mono (fun z hz => by simp [Lifetime.Life.mentions, hz])
          (fun z hz => by simp [Lifetime.Life.mentions, hz])) h.1,
        ihb _ (hv.mono (fun z hz => by simp [Lifetime.Life.mentions, hz])
          (fun z hz => by simp [Lifetime.Life.mentions, hz])) h.2⟩
  | meet a b iha ihb =>
      intro a' hv h
      cases a' <;> simp only [lifeAlphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨iha _ (hv.mono (fun z hz => by simp [Lifetime.Life.mentions, hz])
          (fun z hz => by simp [Lifetime.Life.mentions, hz])) h.1,
        ihb _ (hv.mono (fun z hz => by simp [Lifetime.Life.mentions, hz])
          (fun z hz => by simp [Lifetime.Life.mentions, hz])) h.2⟩

/-- `AlphaAvoid` at a part of a type: its free variables are the whole's. -/
macro "avoid_part" h:ident : tactic =>
  `(tactic| exact AlphaAvoid.mono $h (fun _ hz => by simp only [VFree, CFree] at *; tauto)
    (fun _ hz => by simp only [VFree, CFree] at *; tauto))

mutual
theorem VTy.alphaB_insert (ρ₀ ρ : List (LifeVar × LifeVar)) :
    ∀ (ρ₁ : List (LifeVar × LifeVar)) (A A' : VTy), AlphaAvoid ρ₀ ρ₁ (VFree · A) (VFree · A') →
      VTy.alphaB (ρ₁ ++ ρ) A A' = true → VTy.alphaB (ρ₁ ++ ρ₀ ++ ρ) A A' = true
  | _, .unit, A', _, h | _, .zero, A', _, h | _, .unk, A', _, h | _, .int _, A', _, h
  | _, .opq _, A', _, h | _, .tvar _, A', _, h => by cases A' <;> simp_all [VTy.alphaB]
  | ρ₁, .tensor A B, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.1,
        VTy.alphaB_insert ρ₀ ρ ρ₁ B _ (by avoid_part hv) h.2⟩
  | ρ₁, .sum A B, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.1,
        VTy.alphaB_insert ρ₀ ρ ρ₁ B _ (by avoid_part hv) h.2⟩
  | ρ₁, .thunk C, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) h
  | ρ₁, .code _ E C, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨⟨h.1.1, VTy.alphaB_insert ρ₀ ρ ρ₁ E _ (by avoid_part hv) h.1.2⟩,
        CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) h.2⟩
  | ρ₁, .ref A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h
  | ρ₁, .bang A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h
  | ρ₁, .fam A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h
  | ρ₁, .mu A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h
  | ρ₁, .imm a A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨lifeAlphaB_insert ρ₀ ρ ρ₁ _ _ (by avoid_part hv) h.1,
        VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.2⟩
  | ρ₁, .mut a A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨lifeAlphaB_insert ρ₀ ρ ρ₁ _ _ (by avoid_part hv) h.1,
        VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.2⟩
  | ρ₁, .box a A, A', hv, h => by
      cases A' <;> simp only [VTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨lifeAlphaB_insert ρ₀ ρ ρ₁ _ _ (by avoid_part hv) h.1,
        VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.2⟩
theorem CTy.alphaB_insert (ρ₀ ρ : List (LifeVar × LifeVar)) :
    ∀ (ρ₁ : List (LifeVar × LifeVar)) (C C' : CTy), AlphaAvoid ρ₀ ρ₁ (CFree · C) (CFree · C') →
      CTy.alphaB (ρ₁ ++ ρ) C C' = true → CTy.alphaB (ρ₁ ++ ρ₀ ++ ρ) C C' = true
  | _, .top, C', _, h => by cases C' <;> simp_all [CTy.alphaB]
  | ρ₁, .ret A, C', hv, h => by
      cases C' <;> simp only [CTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h
  | ρ₁, .arr A C, C', hv, h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) h.1,
        CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) h.2⟩
  | ρ₁, .amp C D, C', hv, h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) h.1,
        CTy.alphaB_insert ρ₀ ρ ρ₁ D _ (by avoid_part hv) h.2⟩
  | ρ₁, .nuSys _ _ C, C', hv, h => by
      cases C' <;> simp only [CTy.alphaB, Bool.and_eq_true, reduceCtorEq, Bool.false_eq_true] at h ⊢
      exact ⟨h.1, CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) h.2⟩
  | ρ₁, .all x b C, C', hv, h => by
      cases C' with
      | all x' b' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h ⊢
          refine ⟨lifeAlphaB_insert ρ₀ ρ ρ₁ _ _ (by avoid_part hv) h.1, ?_⟩
          exact CTy.alphaB_insert ρ₀ ρ ((x, x') :: ρ₁) C C'
            (hv.under (fun y hy e => by simp only [CFree]; exact .inr ⟨e, hy⟩)
              (fun y hy e => by simp only [CFree]; exact .inr ⟨e, hy⟩)) h.2
      | _ => simp [CTy.alphaB] at h
  | ρ₁, .eff n i q A B fin rc C, C', hv, h => by
      cases C' with
      | eff n' i' q' A' B' fin' rc' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h ⊢
          obtain ⟨⟨⟨⟨h₀, hA⟩, hB⟩, hf⟩, hC⟩ := h
          exact ⟨⟨⟨⟨h₀, VTy.alphaB_insert ρ₀ ρ ρ₁ A _ (by avoid_part hv) hA⟩,
            VTy.alphaB_insert ρ₀ ρ ρ₁ B _ (by avoid_part hv) hB⟩,
            CTy.alphaB_insert ρ₀ ρ ρ₁ fin _ (by avoid_part hv) hf⟩,
            CTy.alphaB_insert ρ₀ ρ ρ₁ C _ (by avoid_part hv) hC⟩
      | _ => simp [CTy.alphaB] at h
end

/-- **A type is read alike under binders none of whose names is free in it.** -/
theorem VTy.alphaB_lift {S S' : VTy} (ρ₀ : List (LifeVar × LifeVar))
    (hS : VTy.alphaB [] S S' = true) (hv : ∀ p ∈ ρ₀, ¬ VFree p.1 S ∧ ¬ VFree p.2 S') :
    VTy.alphaB ρ₀ S S' = true := by
  have := VTy.alphaB_insert ρ₀ [] [] S S'
    (fun p hp => ⟨fun h => ((hv p hp).1 h).elim, fun h => ((hv p hp).2 h).elim⟩) hS
  simpa using this

/-- `'x` is bound by a `∀` that `instT` passes under. -/
def CTy.InstBinds (x : LifeVar) : CTy → Prop
  | .amp C D => CTy.InstBinds x C ∨ CTy.InstBinds x D
  | .arr _ D | .eff _ _ _ _ _ _ _ D => CTy.InstBinds x D
  | .all y _ D => y = x ∨ CTy.InstBinds x D
  | _ => False

theorem CTy.not_instBinds_of_effLeaf {x : LifeVar} : ∀ {D : CTy}, D.EffLeaf → ¬ D.InstBinds x
  | .ret _, _, h => h
  | .eff _ _ _ _ _ _ _ D, hD, h => CTy.not_instBinds_of_effLeaf (D := D) hD.2.2 h

theorem CTy.leafBinds_of_instBinds {x : LifeVar} : ∀ {D : CTy}, D.NuLeaf → D.InstBinds x →
    D.LeafBinds x
  | .amp C D, hD, h => h.elim (fun h => .inl (CTy.leafBinds_of_instBinds hD.1 h))
      (fun h => .inr (CTy.leafBinds_of_instBinds hD.2 h))
  | .arr _ D, hD, h => CTy.leafBinds_of_instBinds (D := D) hD.2 h
  | .all y _ D, hD, h => h.elim .inl (fun h => .inr (CTy.leafBinds_of_instBinds (D := D) hD h))
  | .eff n i q A B fin rc D, hD, h => (CTy.not_instBinds_of_effLeaf (D := .eff n i q A B fin rc D) hD h).elim

theorem CTy.alphaB_instT {S S' : VTy} (hS : VTy.alphaB [] S S' = true) :
    ∀ (ρ₁ : List (LifeVar × LifeVar)) (C C' : CTy), (∀ p ∈ ρ₁, ¬ VFree p.1 S ∧ ¬ VFree p.2 S') →
      (∀ x, C.InstBinds x → ¬ VFree x S) → (∀ x', C'.InstBinds x' → ¬ VFree x' S') →
      CTy.alphaB ρ₁ C C' = true → CTy.alphaB ρ₁ (C.instT S) (C'.instT S') = true
  | ρ₁, .ret A, C', hρ, _, _, h => by
      cases C' <;> simp only [CTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      exact VTy.alphaB_inst (VTy.alphaB_lift ρ₁ hS hρ) h
  | ρ₁, .amp C D, C', hρ, hb, hb', h => by
      cases C' with
      | amp C' D' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h
          simp only [CTy.instT, CTy.alphaB, Bool.and_eq_true]
          exact ⟨CTy.alphaB_instT hS ρ₁ C C' hρ (fun x h => hb x (.inl h))
              (fun x h => hb' x (.inl h)) h.1,
            CTy.alphaB_instT hS ρ₁ D D' hρ (fun x h => hb x (.inr h))
              (fun x h => hb' x (.inr h)) h.2⟩
      | _ => simp [CTy.alphaB] at h
  | ρ₁, .arr A C, C', hρ, hb, hb', h => by
      cases C' with
      | arr A' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h
          simp only [CTy.instT, CTy.alphaB, Bool.and_eq_true]
          exact ⟨h.1, CTy.alphaB_instT hS ρ₁ C C' hρ hb hb' h.2⟩
      | _ => simp [CTy.alphaB] at h
  | ρ₁, .all x b C, C', hρ, hb, hb', h => by
      cases C' with
      | all x' b' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h
          simp only [CTy.instT, CTy.alphaB, Bool.and_eq_true]
          refine ⟨h.1, CTy.alphaB_instT hS ((x, x') :: ρ₁) C C' ?_ (fun y h => hb y (.inr h))
            (fun y h => hb' y (.inr h)) h.2⟩
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨hb x (.inl rfl), hb' x' (.inl rfl)⟩
          · exact hρ p hp
      | _ => simp [CTy.alphaB] at h
  | ρ₁, .eff n i q A B fin rc C, C', hρ, hb, hb', h => by
      cases C' with
      | eff n' i' q' A' B' fin' rc' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true] at h
          simp only [CTy.instT, CTy.alphaB, Bool.and_eq_true]
          exact ⟨h.1, CTy.alphaB_instT hS ρ₁ C C' hρ hb hb' h.2⟩
      | _ => simp [CTy.alphaB] at h
  | ρ₁, .top, C', _, _, _, h => by cases C' <;> simp_all [CTy.alphaB, CTy.instT]
  | ρ₁, .nuSys _ _ C, C', _, _, _, h => by
      cases C' <;> simp only [CTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      simpa [CTy.instT, CTy.alphaB] using h

/-- **One unfolding respects α-equivalence** at two positive bodies: their `∀` leaves' binders
are free in neither (`NuOk`), so `U(νX. C)` is read alike under them. -/
theorem CTy.alphaB_unroll {C C' : CTy} (h : CTy.alphaB [] C C' = true) (hC : C.NuOk)
    (hC' : C'.NuOk) : CTy.alphaB [] C.unroll C'.unroll = true := by
  have hfresh : ∀ {D : CTy}, D.NuOk → ∀ x, D.InstBinds x → ¬ VFree x (.thunk (.nu D)) := by
    intro D hD x hx
    obtain ⟨hS, hf⟩ := hD
    cases D with
    | amp D₁ D₂ =>
        have hl : (CTy.amp D₁ D₂).LeafBinds x := hx.elim
          (fun h => .inl (CTy.leafBinds_of_instBinds hS.1 h))
          (fun h => .inr (CTy.leafBinds_of_instBinds hS.2 h))
        simpa [VFree, CFree] using hf x hl
    | _ => simp [CTy.NuShape] at hS
  exact CTy.alphaB_instT (S := .thunk (.nu C)) (S' := .thunk (.nu C')) h [] C C'
    (fun _ hp => absurd hp List.not_mem_nil) (hfresh hC) (hfresh hC') h

/-! ### Rows up to α -/

/-- Two operations up to α: the same key, qualifier and mark, their argument, answer and cancel
row α-equivalent. -/
def OpSig.AlphaEq (o o' : OpSig) : Prop :=
  o.n = o'.n ∧ o.i = o'.i ∧ o.q = o'.q ∧ o.rc = o'.rc ∧ VTy.alphaB [] o.A o'.A = true ∧
    VTy.alphaB [] o.B o'.B = true ∧ CTy.alphaB [] o.fin o'.fin = true

/-- Two rows up to α, operation by operation. -/
abbrev RowAlpha : List OpSig → List OpSig → Prop := List.Forall₂ OpSig.AlphaEq

theorem OpSig.AlphaEq.refl (o : OpSig) : o.AlphaEq o :=
  ⟨rfl, rfl, rfl, rfl, VTy.alphaB_refl _, VTy.alphaB_refl _, CTy.alphaB_refl _⟩

theorem OpSig.AlphaEq.symm {o o' : OpSig} (h : o.AlphaEq o') : o'.AlphaEq o :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, VTy.alphaB_symm h.2.2.2.2.1,
    VTy.alphaB_symm h.2.2.2.2.2.1, CTy.alphaB_symm h.2.2.2.2.2.2⟩

theorem OpSig.AlphaEq.trans {o o' o'' : OpSig} (h : o.AlphaEq o') (h' : o'.AlphaEq o'') :
    o.AlphaEq o'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.1.trans h'.2.2.2.1,
    VTy.alphaB_trans' h.2.2.2.2.1 h'.2.2.2.2.1, VTy.alphaB_trans' h.2.2.2.2.2.1 h'.2.2.2.2.2.1,
    CTy.alphaB_trans' h.2.2.2.2.2.2 h'.2.2.2.2.2.2⟩

theorem OpSig.AlphaEq.isZero_eq {o o' : OpSig} (h : o.AlphaEq o') : o.B.isZero = o'.B.isZero := by
  have hB := h.2.2.2.2.2.1
  cases hb : o.B <;> cases hb' : o'.B <;> rw [hb, hb'] at hB <;>
    simp_all [VTy.alphaB, VTy.isZero]

theorem RowAlpha.refl : ∀ S : List OpSig, RowAlpha S S
  | [] => .nil
  | o :: S => .cons (OpSig.AlphaEq.refl o) (RowAlpha.refl S)

theorem RowAlpha.symm {S S' : List OpSig} (h : RowAlpha S S') : RowAlpha S' S := by
  induction h with
  | nil => exact .nil
  | cons ho _ ih => exact .cons ho.symm ih

theorem RowAlpha.trans {S S' S'' : List OpSig} (h : RowAlpha S S') (h' : RowAlpha S' S'') :
    RowAlpha S S'' := by
  induction h generalizing S'' with
  | nil => cases h'; exact .nil
  | cons ho _ ih => cases h' with | cons ho' h' => exact .cons (ho.trans ho') (ih h')

/-- An α-equivalent of a row's type is a row's type: the row up to α, at an α-equivalent answer. -/
theorem CTy.alphaB_effOf : ∀ (S : List OpSig) {Y : VTy} {D : CTy},
    CTy.alphaB [] (CTy.effOf S Y) D = true →
      ∃ S' Y', D = CTy.effOf S' Y' ∧ RowAlpha S S' ∧ VTy.alphaB [] Y Y' = true
  | [], Y, D, h => by
      cases D <;> simp only [CTy.effOf, CTy.alphaB, reduceCtorEq, Bool.false_eq_true] at h
      exact ⟨[], _, rfl, .nil, h⟩
  | o :: S, Y, D, h => by
      cases D with
      | eff n i q A B fin rc D =>
          simp only [CTy.effOf, CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, hr⟩, hA⟩, hB⟩, hf⟩, hC⟩ := h
          obtain ⟨S', Y', rfl, hS, hY⟩ := CTy.alphaB_effOf S hC
          exact ⟨⟨n, i, q, A, B, fin, rc⟩ :: S', Y', rfl, .cons ⟨hn, hi, hq, hr, hA, hB, hf⟩ hS, hY⟩
      | _ => simp [CTy.effOf, CTy.alphaB] at h

/-- A row's type at α-equivalent rows and answers. -/
theorem CTy.alphaB_effOf_of : ∀ {S S' : List OpSig} {Y Y' : VTy}, RowAlpha S S' →
    VTy.alphaB [] Y Y' = true → CTy.alphaB [] (CTy.effOf S Y) (CTy.effOf S' Y') = true
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons ho hS, h => by
      obtain ⟨hn, hi, hq, hr, hA, hB, hf⟩ := ho
      simp only [CTy.effOf, CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, hr⟩, hA⟩, hB⟩, hf⟩, CTy.alphaB_effOf_of hS h⟩

/-- A row's type at α-equivalent answers. -/
theorem CTy.alphaB_effOf_congr (S : List OpSig) {Y Y' : VTy} (h : VTy.alphaB [] Y Y' = true) :
    CTy.alphaB [] (CTy.effOf S Y) (CTy.effOf S Y') = true :=
  CTy.alphaB_effOf_of (RowAlpha.refl S) h

/-- An α-equivalent cancel row: `⊤` alike, and its operations up to α. -/
theorem CTy.alphaB_rowOf : ∀ {F F' : CTy}, CTy.alphaB [] F F' = true →
    F.isTop = F'.isTop ∧ RowAlpha F.rowOf F'.rowOf
  | .eff n i q A B fin rc C, F', h => by
      cases F' with
      | eff n' i' q' A' B' fin' rc' C' =>
          simp only [CTy.alphaB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨⟨hn, hi⟩, hq⟩, hr⟩, hA⟩, hB⟩, hf⟩, hC⟩ := h
          exact ⟨rfl, .cons ⟨hn, hi, hq, hr, hA, hB, hf⟩ (CTy.alphaB_rowOf hC).2⟩
      | _ => simp [CTy.alphaB] at h
  | .top, F', h => by cases F' <;> simp_all [CTy.alphaB, CTy.isTop, CTy.rowOf]
  | .ret _, F', h | .arr _ _, F', h | .amp _ _, F', h | .all _ _ _, F', h | .nuSys _ _ _, F', h => by
      cases F' <;> simp_all [CTy.alphaB, CTy.isTop, CTy.rowOf]

/-- `𝒱⟦A⟧ = 𝒱⟦A'⟧` at α-equivalent value types. -/
theorem vC_alpha {A A' : VTy} (hα : VTy.alphaB [] A A' = true) (b : Bool) (ls : List SRec)
    (δ : LSub) : vC b A ls δ = vC b A' ls δ :=
  vC_tyEq (VTy.alphaB_sound A A' (alphaAgree_nil δ) hα) b ls

/-- `𝒞⟦C⟧ = 𝒞⟦C'⟧` at α-equivalent computation types. -/
theorem cC_alpha {C C' : CTy} (hα : CTy.alphaB [] C C' = true) (ls : List SRec) (δ : LSub) :
    cC C ls δ = cC C' ls δ :=
  cC_tyEq (CTy.alphaB_sound C C' (alphaAgree_nil δ) hα) ls

/-- **The conversion rule's compatibility lemma**: a computation semantically at `C` is at every
α-equivalent `C'`.  `[spec §3]` -/
theorem alpha_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C C' : CTy}
    (hα : CTy.alphaB [] C C' = true) (h : SemC Δ Γ e C) : SemC Δ Γ e C' := by
  intro δ γ ls ρ hδ hg
  rw [← cC_alpha hα ls δ]
  exact h δ γ ls ρ hδ hg

end BoCa.Fig16.LogRel.Core
