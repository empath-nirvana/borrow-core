import FnMut.Core.CountFold

/-!
# Core — the fuelled fixed point  `[spec §20]`

`bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`, the primitive
`boundedFix`, at every computation type `C` (a row `F_Σ B` among them). From `(s, (k, a))` it runs
the step `s` on `(self, a)`, where `self = inj₂ (λx. bounded_fix (s, (k − 1, x)))` is the fixed
point with one less unit of budget, or `inj₁ ()` at `k = 0`: the budget is spent, and the step
decides what to do (`Head.boundedFix`, `boundedFixNext`, `fixSelf`). The budget is the machine's, read unsigned and counted
down by the machine, as `count`'s counter is counted up, so the recursion is total at every host:
its depth is at most `k`, and each level runs one call of `s`.

`fixSelf_valid` is the induction on the budget: the self-reference is valid at
`1 ⊕ !U(A ⊸ C)`, `inj₁ ()` at `k = 0`, and at `k = j + 1` a function whose call is one
`boundedFix` step to `s` on the self-reference at `j`, valid by the induction hypothesis and
`s`'s validity. `boundedFix_compatX` is the constant. The
relation is unchanged: `𝒞⟦C⟧` at a row is §19's `ewpTS`, total correctness, and nothing here
reads it beyond its closure under a pure step in front (`cC_head`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The self-reference's type, `1 ⊕ !U(A ⊸ C)`: `inj₁ ()` once the budget is spent.
`[spec §20]` -/
abbrev fixSelfTy (A : VTy) (C : CTy) : VTy := .sum .unit (.bang (.thunk (.arr A C)))

/-- The step's type, `!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C)`.  `[spec §20]` -/
abbrev fixStepTy (A : VTy) (C : CTy) : VTy := .bang (.thunk (.arr (.tensor (fixSelfTy A C) A) C))

/-- `bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`.  `[spec §20]` -/
abbrev boundedFixTy (A : VTy) (C : CTy) : VTy :=
  .bang (.thunk (.arr (.tensor (fixStepTy A C) (.tensor (.int .w32) A)) C))

/-- The redex `bounded_fix (s, (k, a))`. -/
abbrev boundedFixE (s : Val) (k : UInt32) (a : Val) : Expr :=
  .app (.val (.prim .boundedFix)) (.val (Val.pair s (Val.pair (Val.i32 k) a)))

/-- The `boundedFix` step.  `[spec §20]` -/
theorem cC_boundedFix (C : CTy) (s : Val) (k : UInt32) (a : Val) (ls : List SRec) (δ : LSub) :
    Entails (cC C ls δ (boundedFixNext s k a)) (cC C ls δ (boundedFixE s k a)) :=
  cC_head C (fun μ => Head.boundedFix μ s k a) rfl ls δ

/-- **The self-reference.** With the step valid at `ls₀`, the self-reference at every budget `k`
is valid at `1 ⊕ !U(A ⊸ C)` at every list `Ext`-above `ls₀`: `inj₁ ()` at `k = 0`, and at
`k = j + 1` a function whose call is one `boundedFix` step to the step on the self-reference at
`j`. By induction on `k`.  `[spec §20]` -/
theorem fixSelf_valid {A : VTy} {C : CTy} {δ : LSub} {ls₀ : List SRec} (s : Val)
    (hs : vP (fixStepTy A C) ls₀ δ s PMap.empty) :
    ∀ (n : Nat) (k : UInt32) (ls : List SRec), k.toNat = n → Ext ls₀ ls PMap.empty →
      vP (fixSelfTy A C) ls δ (fixSelf s k) PMap.empty := by
  intro n
  induction n with
  | zero =>
      intro k ls hk _
      have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      unfold fixSelf
      rw [if_pos hk0]
      exact Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩
  | succ j ih =>
      intro k ls hk hext
      have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
      have hkj : (k - 1).toNat = j := by
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      unfold fixSelf
      rw [if_neg hk0]
      refine Or.inr ⟨_, pure_sep_mk rfl ⟨rfl, fun ls' hext' x ρ₁ ρ₂ hx hc => ?_⟩⟩
      obtain rfl := eq_of_compS_empty_left hc
      refine cC_head C (fun μ => Head.beta μ _ x) rfl ls' δ _ ?_
      rw [fixSelf_body_subst]
      refine cC_boundedFix C s (k - 1) x ls' δ _ ?_
      exact hs.2 ls' (hext.trans hext') (Val.pair (fixSelf s (k - 1)) x) _ _
        ⟨fixSelf s (k - 1), x, pure_sep_mk rfl
          ⟨PMap.empty, _, compS_empty_left _, ih (k - 1) ls' hkj (hext.trans hext'), hx⟩⟩
        (compS_empty_left _)

/-- **`bounded_fix` is sound**, at every host and every computation type.  `[spec §20]` -/
theorem boundedFix_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {C : CTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .boundedFix)) (boundedFixTy A C) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  show cC C ls' δ (.app (.val (Val.prim .boundedFix)) (.val v)) _
  obtain ⟨s, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hs, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hs.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  obtain ⟨vk, a, hk₂⟩ := h₂
  obtain ⟨rfl, ρk, ρa, hc₂, ⟨ek, k, rfl⟩, ha⟩ := pure_sep_iff.mp hk₂
  subst ek
  rw [eq_of_compS_empty_left hc₂]
  refine cC_boundedFix C s k a ls' δ _ ?_
  exact hs.2 ls' (Ext.refl _ _) (Val.pair (fixSelf s k) a) ρa ρa
    ⟨fixSelf s k, a, pure_sep_mk rfl
      ⟨PMap.empty, ρa, compS_empty_left ρa,
        fixSelf_valid s hs _ k ls' rfl (Ext.refl _ _), ha⟩⟩ (compS_empty_left ρa)

end BoCa.Fig16.LogRel.Core
