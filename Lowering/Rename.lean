import Lowering.Low

/-!
# Lowering — renaming the variables of a term  `[spec §54]`

An explicit copy binds two new variables in front of the node whose parts both use a value, and
each part then reads its own copy: the parts' terms are renamed (`ren`). A renaming `ρ` sends a
free variable `i` to `ρ i`, and is lifted under each binder it passes (`liftR`, `liftN`).

**A renaming that keeps every value keeps the substituted term** (`psub_ren`): when the closing
substitution `γ'` holds at `ρ i` what `γ` holds at `i`, and a variable past `γ` stays as far past
`γ'` (`RenOK`), `γ'` applied to the renamed term is `γ` applied to the term. The copies are pure
steps from the node's term to its renamed term at the extended substitution, so a node in the
relation stays there with its copies made explicit (`Lowering/OwnSem.lean`).
-/

namespace Lowering
open BoCa

/-! ### Renamings -/

/-- `ρ` under one binder: the bound variable stays, every other moves by `ρ` past it. -/
def liftR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- `ρ` under `n` binders. -/
def liftN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftR (liftN n ρ)

/-- Rename the free variables of `e` by `ρ`. -/
def ren (ρ : Nat → Nat) : Expr → Expr
  | .var i => .var (ρ i)
  | .unit => .unit
  | .pair a b => .pair (ren ρ a) (ren ρ b)
  | .inj₁ a => .inj₁ (ren ρ a)
  | .inj₂ a => .inj₂ (ren ρ a)
  | .lam b => .lam (ren (liftR ρ) b)
  | .loc ℓ => .loc ℓ
  | .prim p => .prim p
  | .seq a b => .seq (ren ρ a) (ren ρ b)
  | .letpair a b => .letpair (ren ρ a) (ren (liftR (liftR ρ)) b)
  | .case s a b => .case (ren ρ s) (ren (liftR ρ) a) (ren (liftR ρ) b)
  | .app f a => .app (ren ρ f) (ren ρ a)

theorem liftN_apply : ∀ (c : Nat) (ρ : Nat → Nat) (i : Nat),
    liftN c ρ i = if i < c then i else ρ (i - c) + c
  | 0, ρ, i => by simp [liftN]
  | c + 1, ρ, 0 => by simp [liftN, liftR]
  | c + 1, ρ, i + 1 => by
      simp only [liftN, liftR]
      rw [liftN_apply c ρ i]
      by_cases h : i < c
      · simp [h]
      · have h' : ¬ (i + 1 < c + 1) := by omega
        simp only [h, h', if_false]
        have : i + 1 - (c + 1) = i - c := by omega
        rw [this]; omega

theorem liftR_id : liftR id = id := by
  funext i; cases i <;> rfl

theorem liftN_id : ∀ c : Nat, liftN c id = id
  | 0 => rfl
  | c + 1 => by simp only [liftN, liftN_id c, liftR_id]

/-- The identity renaming changes nothing. -/
theorem ren_id : ∀ (e : Expr), ren id e = e
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by simp only [ren, ren_id a, ren_id b]
  | .inj₁ a => by simp only [ren, ren_id a]
  | .inj₂ a => by simp only [ren, ren_id a]
  | .lam b => by simp only [ren, liftR_id, ren_id b]
  | .loc _ => rfl
  | .prim _ => rfl
  | .seq a b => by simp only [ren, ren_id a, ren_id b]
  | .letpair a b => by simp only [ren, liftR_id, ren_id a, ren_id b]
  | .case s a b => by simp only [ren, liftR_id, ren_id s, ren_id a, ren_id b]
  | .app f a => by simp only [ren, ren_id f, ren_id a]

theorem liftR_comp (ρ σ : Nat → Nat) : liftR (ρ ∘ σ) = liftR ρ ∘ liftR σ := by
  funext i; cases i <;> rfl

/-- Renaming twice is renaming by the composite. -/
theorem ren_ren : ∀ (ρ σ : Nat → Nat) (e : Expr), ren ρ (ren σ e) = ren (ρ ∘ σ) e
  | _, _, .var _ => rfl
  | _, _, .unit => rfl
  | ρ, σ, .pair a b => by simp only [ren, ren_ren ρ σ a, ren_ren ρ σ b]
  | ρ, σ, .inj₁ a => by simp only [ren, ren_ren ρ σ a]
  | ρ, σ, .inj₂ a => by simp only [ren, ren_ren ρ σ a]
  | ρ, σ, .lam b => by simp only [ren, ren_ren (liftR ρ) (liftR σ) b, liftR_comp]
  | _, _, .loc _ => rfl
  | _, _, .prim _ => rfl
  | ρ, σ, .seq a b => by simp only [ren, ren_ren ρ σ a, ren_ren ρ σ b]
  | ρ, σ, .letpair a b => by
      simp only [ren, ren_ren ρ σ a, ren_ren (liftR (liftR ρ)) (liftR (liftR σ)) b, liftR_comp]
  | ρ, σ, .case s a b => by
      simp only [ren, ren_ren ρ σ s, ren_ren (liftR ρ) (liftR σ) a,
        ren_ren (liftR ρ) (liftR σ) b, liftR_comp]
  | ρ, σ, .app f a => by simp only [ren, ren_ren ρ σ f, ren_ren ρ σ a]

/-! ### Renamings that keep a substitution -/

/-- `ρ` carries `γ` to `γ'`: `γ'` holds at `ρ i` what `γ` holds at `i`, and a variable past `γ`
is as far past `γ'` after the renaming. -/
def RenOK (ρ : Nat → Nat) (γ' γ : List Val) : Prop :=
  ∀ i, γ'[ρ i]? = γ[i]? ∧ (γ.length ≤ i → ρ i - γ'.length = i - γ.length)

theorem RenOK.id (γ : List Val) : RenOK id γ γ := fun _ => ⟨rfl, fun _ => rfl⟩

/-- Two renamings that keep substitutions compose. -/
theorem RenOK.comp {ρ σ : Nat → Nat} {γ'' γ' γ : List Val} (h₁ : RenOK ρ γ'' γ')
    (h₂ : RenOK σ γ' γ) : RenOK (ρ ∘ σ) γ'' γ := by
  intro i
  refine ⟨(h₁ (σ i)).1.trans (h₂ i).1, fun hi => ?_⟩
  have hn : γ[i]? = none := List.getElem?_eq_none hi
  have hσ : γ'.length ≤ σ i := by
    have := (h₂ i).1; rw [hn] at this; exact List.getElem?_eq_none_iff.mp this
  rw [Function.comp_apply, (h₁ (σ i)).2 hσ, (h₂ i).2 hi]

/-- **A renaming that keeps the substitution keeps the substituted term.** -/
theorem psub_ren {ρ : Nat → Nat} {γ' γ : List Val} (h : RenOK ρ γ' γ) :
    ∀ (e : Expr) (c : Nat), Expr.psub c γ' (ren (liftN c ρ) e) = Expr.psub c γ e
  | .var i, c => by
      simp only [ren, liftN_apply]
      by_cases hi : i < c
      · simp [Expr.psub, hi]
      · have hge : ¬ (ρ (i - c) + c < c) := by omega
        simp only [hi, if_false, Expr.psub, hge, Nat.add_sub_cancel]
        have h1 := (h (i - c)).1
        rw [h1]
        cases hg : γ[i - c]? with
        | some v => rfl
        | none =>
            have hlen : γ.length ≤ i - c := List.getElem?_eq_none_iff.mp hg
            have hlen' : γ'.length ≤ ρ (i - c) := by
              rw [hg] at h1; exact List.getElem?_eq_none_iff.mp h1
            have h2 := (h (i - c)).2 hlen
            show Expr.var (ρ (i - c) + c - γ'.length) = Expr.var (i - γ.length)
            congr 1; omega
  | .unit, _ => rfl
  | .pair a b, c => by simp only [ren, Expr.psub, psub_ren h a c, psub_ren h b c]
  | .inj₁ a, c => by simp only [ren, Expr.psub, psub_ren h a c]
  | .inj₂ a, c => by simp only [ren, Expr.psub, psub_ren h a c]
  | .lam b, c => by
      simp only [ren, Expr.psub]
      exact congrArg Expr.lam (psub_ren h b (c + 1))
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, c => by simp only [ren, Expr.psub, psub_ren h a c, psub_ren h b c]
  | .letpair a b, c => by
      simp only [ren, Expr.psub, psub_ren h a c]
      exact congrArg _ (psub_ren h b (c + 2))
  | .case s a b, c => by
      simp only [ren, Expr.psub, psub_ren h s c]
      exact congrArg₂ _ (psub_ren h a (c + 1)) (psub_ren h b (c + 1))
  | .app f a, c => by simp only [ren, Expr.psub, psub_ren h f c, psub_ren h a c]

/-- `psub_ren` at no binder. -/
theorem psub_ren0 {ρ : Nat → Nat} {γ' γ : List Val} (h : RenOK ρ γ' γ) (e : Expr) :
    Expr.psub 0 γ' (ren ρ e) = Expr.psub 0 γ e :=
  psub_ren h e 0

/-- `psub_ren` under one binder. -/
theorem psub_ren1 {ρ : Nat → Nat} {γ' γ : List Val} (h : RenOK ρ γ' γ) (e : Expr) :
    Expr.psub 1 γ' (ren (liftR ρ) e) = Expr.psub 1 γ e :=
  psub_ren h e 1

/-- `psub_ren` under two binders. -/
theorem psub_ren2 {ρ : Nat → Nat} {γ' γ : List Val} (h : RenOK ρ γ' γ) (e : Expr) :
    Expr.psub 2 γ' (ren (liftR (liftR ρ)) e) = Expr.psub 2 γ e :=
  psub_ren h e 2

end Lowering
