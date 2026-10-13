import Core.InsertDead

/-!
# Core — a function copied at each use is `[let-poly]`'s premise  `[spec §18, §24]`

`[let-poly]` types `let x = λy. b in N` from `N` with the λ-value at each occurrence of `x`, `x`'s
slot dead (`CDerives.letPoly`).  A term with a closed λ-value at some of its places, as a function
is copied at each of its uses (a `def` re-checked at each use, §18's copies, decision 45), is that
premise term for the let that binds the λ-value once:

* `e.unfill b k`: `e` with each occurrence of `λb` replaced by the variable `k` it is bound to,
  and every other variable from `k` up moved past it.  Filling the result with `λb` gives `e` back
  (`subst_unfill`), so `e.unfill b 0` is a body whose filling is `e`.  It compares terms by
  `Expr`'s `DecidableEq`, derived here (the checker decides its side conditions with it too).
* `CDerives.letPoly_of_fill`: a derivation of the copy `N.subst 0 (λb)` at `Γ` is, with the bound
  slot dead and inserted (`CDerives.insert_dead`), a derivation of `[let-poly]`'s premise, so the
  let has one.  `CDerives.letPoly_copy` is the instance at `N = e.unfill b 0`: any derivation of a
  term gives the let of any closed λ-value typed at the empty context.
* `CDerivesAt.letPoly_of_fill` and `CDerivesAt.letPoly_copy`: the same for tied derivations.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa

deriving instance DecidableEq for Expr

end BoCa

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LifeCtx)

/-- **The body of a let of `λb`**: `e` with each occurrence of `λb` replaced by the variable `k`
(the let's variable under `k` binders), every other variable from `k` up moved one past it.
`[spec §24]` -/
def _root_.BoCa.Expr.unfill : Expr → Expr → Nat → Expr
  | .var i, _, k => if i < k then .var i else .var (i + 1)
  | .unit, _, _ => .unit
  | .pair e₁ e₂, b, k => .pair (e₁.unfill b k) (e₂.unfill b k)
  | .inj₁ e, b, k => .inj₁ (e.unfill b k)
  | .inj₂ e, b, k => .inj₂ (e.unfill b k)
  | .lam e, b, k => if e = b then .var k else .lam (e.unfill b (k + 1))
  | .loc ℓ, _, _ => .loc ℓ
  | .prim p, _, _ => .prim p
  | .seq e₁ e₂, b, k => .seq (e₁.unfill b k) (e₂.unfill b k)
  | .letpair e₁ e₂, b, k => .letpair (e₁.unfill b k) (e₂.unfill b (k + 2))
  | .case e e₁ e₂, b, k => .case (e.unfill b k) (e₁.unfill b (k + 1)) (e₂.unfill b (k + 1))
  | .app f a, b, k => .app (f.unfill b k) (a.unfill b k)

/-- **Filling the body with the λ-value gives the term back**: `λb` closed, the copy `e` is
`(e.unfill b k)` with `λb` for the variable `k`.  `[spec §24]` -/
theorem subst_unfill {b : Expr} (hcl : closedAt 0 (Val.lam b).1 = true) :
    ∀ (e : Expr) (k : Nat), (e.unfill b k).subst k (Val.lam b) = e
  | .var i, k => by
      by_cases h : i < k
      · have h₁ : ¬ (i = k) := by omega
        have h₂ : ¬ (i > k) := by omega
        simp only [Expr.unfill, if_pos h, Expr.subst, if_neg h₁, if_neg h₂]
      · have h₁ : ¬ (i + 1 = k) := by omega
        have h₂ : i + 1 > k := by omega
        simp only [Expr.unfill, if_neg h, Expr.subst, if_neg h₁, if_pos h₂, Nat.add_sub_cancel]
  | .unit, _ => rfl
  | .pair a c, k => by
      simp only [Expr.unfill, Expr.subst, subst_unfill hcl a k, subst_unfill hcl c k]
  | .inj₁ a, k => by simp only [Expr.unfill, Expr.subst, subst_unfill hcl a k]
  | .inj₂ a, k => by simp only [Expr.unfill, Expr.subst, subst_unfill hcl a k]
  | .lam e, k => by
      by_cases h : e = b
      · subst h
        simp only [Expr.unfill, if_pos trivial, Expr.subst]
        rfl
      · simp only [Expr.unfill, if_neg h, Expr.subst, val_shift_closed hcl,
          subst_unfill hcl e (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a c, k => by
      simp only [Expr.unfill, Expr.subst, subst_unfill hcl a k, subst_unfill hcl c k]
  | .letpair a c, k => by
      simp only [Expr.unfill, Expr.subst, val_shift_closed hcl, subst_unfill hcl a k,
        subst_unfill hcl c (k + 2)]
  | .case a c d, k => by
      simp only [Expr.unfill, Expr.subst, val_shift_closed hcl, subst_unfill hcl a k,
        subst_unfill hcl c (k + 1), subst_unfill hcl d (k + 1)]
  | .app f a, k => by
      simp only [Expr.unfill, Expr.subst, subst_unfill hcl f k, subst_unfill hcl a k]

/-! ### The let from the copy -/

/-- **The copy gives the let** (`[let-poly]`): `N` filled with a closed λ-value, typed at `Γ`, is,
with the bound slot dead in front, the rule's premise term (`CDerives.insert_dead`).
`[spec §24]` -/
theorem CDerives.letPoly_of_fill {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} {j : Jdg}
    (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true) (hV : CDerives Δ [] (.val (.lam b)) j)
    (h : CDerives Δ Γ (N.subst 0 (Val.lam b)) (.comp C)) :
    CDerives Δ Γ (.app (.val (.lam N)) (.val (.lam b))) (.comp C) :=
  .letPoly b hcl hV (by simpa using h.insert_dead (Γd := [⟨.unit, false⟩]) (.cons .nil) [] Γ rfl)

/-- **A function copied at each use is let-bound once**: any derivation of `e` gives
`[let-poly]`'s derivation of the let of a closed λ-value typed at the empty context, its body
`e.unfill b 0`, whose filling is `e` (`subst_unfill`).  `[spec §18, §24]` -/
theorem CDerives.letPoly_copy {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} {j : Jdg}
    (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true) (hV : CDerives Δ [] (.val (.lam b)) j)
    (h : CDerives Δ Γ e (.comp C)) :
    CDerives Δ Γ (.app (.val (.lam (e.unfill b 0))) (.val (.lam b))) (.comp C) :=
  .letPoly_of_fill b hcl hV (by rw [subst_unfill hcl]; exact h)

/-- `CDerives.letPoly_of_fill` for a tied derivation.  `[spec §19, §24]` -/
theorem CDerivesAt.letPoly_of_fill {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy}
    {j : Jdg} (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true)
    (hV : CDerivesAt Ξ Δ [] (.val (.lam b)) j)
    (h : CDerivesAt Ξ Δ Γ (N.subst 0 (Val.lam b)) (.comp C)) :
    CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) (.val (.lam b))) (.comp C) :=
  .letPoly b hcl hV (by simpa using h.insert_dead (Γd := [⟨.unit, false⟩]) (.cons .nil) [] Γ rfl)

/-- `CDerives.letPoly_copy` for a tied derivation.  `[spec §18, §19, §24]` -/
theorem CDerivesAt.letPoly_copy {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy}
    {j : Jdg} (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true)
    (hV : CDerivesAt Ξ Δ [] (.val (.lam b)) j) (h : CDerivesAt Ξ Δ Γ e (.comp C)) :
    CDerivesAt Ξ Δ Γ (.app (.val (.lam (e.unfill b 0))) (.val (.lam b))) (.comp C) :=
  .letPoly_of_fill b hcl hV (by rw [subst_unfill hcl]; exact h)

end BoCa.Fig16.LogRel.Core

end
