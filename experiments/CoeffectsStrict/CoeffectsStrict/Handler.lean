import CoeffectsStrict.Fold

/-!
# Effects: a deep handler is the fold of the free model, on runs

The signature `Σ = {write : I32 ⇝ 1}` has, over a value type `A`, the free model
`Tree_Σ A = μX. A ⊕ (I32 ⊗ X)`: a computation that returns `a` is `inj₁ a`, and
`write(n); k` is `inj₂ (n, k)`.  It is data in the class `FShape` (`freeW A`), so `foldOwn`
applies.  A handler with return clause and operation clause is an algebra
`g : A ⊕ (I32 ⊗ R) → R`, and handling is `foldOwn g`.

Plotkin–Pretnar's homomorphism equations, as statements about runs:

* `handle_return`: `handle (return a) ↦* g (inj₁ a)`;
* `handle_write`: if `handle k` reaches `r`, then `handle (write(n); k) ↦* g (inj₂ (n, r))`;
* `handle_unique`: every homomorphism from the free model to a total algebra agrees with the
  handler on every finite tree (`fold_unique`).

`handle_write` hands the operation clause the handled rest `r`, a value: the fold is strict.
An operation clause that decides whether to resume takes `R = U C`, a thunk of the rest.
Free models of operations whose arity is not a finite sum of `1` (`read : 1 ⇝ I32 ⊕ 1`) need
`X` under `U` or `⊸` in the body, which `FShape` excludes (SPEC §6).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CoeffectsStrict
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head Kont)

/-- The free model of `{write : I32 ⇝ 1}` over `A`: `μX. A ⊕ (I32 ⊗ X)`. -/
def freeW (A : VTy) : FShape := .sum (.leaf A) (.tensor (.leaf .i32) .varX)

/-- `handle_g`, the handler with algebra `g`. -/
abbrev handle (A : VTy) (g : Val) (t : Val) : Expr :=
  .app (.app (.val (foldOwnV (freeW A))) (.val g)) (.val t)

/-- The return clause: `handle (return a) ↦* g (inj₁ a)`. -/
theorem handle_return (A : VTy) (g a : Val) :
    PureSteps (ℍ := ℍ) (handle A g (.inj₁ a)) (.app (.val g) (.val (.inj₁ a))) :=
  (PureSteps.plug (.appL .hole _) (foldOwn_app _ g)).trans
    (fold_beta_run _ g _ _ (functor_sum₁ _ _ _ _ _ (functor_leaf A _ a)))

/-- The operation clause: if the rest is handled to `r` (by `hO (freeW A) g`, the value
`foldOwn g` reduces to, `foldOwn_app`), then `handle (write(n); k) ↦* g (inj₂ (n, r))`. -/
theorem handle_write (A : VTy) (g n k r : Val)
    (hr : Evals (ℍ := ℍ) (.app (.val (hO (freeW A) g)) (.val k)) r) :
    PureSteps (ℍ := ℍ) (handle A g (.inj₂ (.pair n k))) (.app (.val g) (.val (.inj₂ (.pair n r)))) :=
  (PureSteps.plug (.appL .hole _) (foldOwn_app _ g)).trans
    (fold_beta_run _ g _ _ (functor_sum₂ _ _ _ _ _
      (functor_tensor _ _ _ _ _ _ _ (functor_leaf .i32 _ n) ((functor_varX _ k).trans hr))))

/-- Uniqueness: every homomorphism `h` from the free model to a total algebra `g` reaches the
handler's value on every finite tree. -/
theorem handle_unique {A : VTy} {g h : Val} (hg : Total (ℍ := ℍ) g)
    (eh : IsHom (ℍ := ℍ) (freeW A) g h) {t : Val} (ht : SV (freeW A) (freeW A) t) :
    ∃ r, Evals (ℍ := ℍ) (.app (.val h) (.val t)) r ∧ Evals (ℍ := ℍ) (handle A g t) r :=
  fold_unique hg eh ht

end BoCa.Fig16.LogRel.Core.CoeffectsStrict

end
