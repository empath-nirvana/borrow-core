import Frontend.Check.TDerives

/-!
# Frontend — Check — what the typed term does not fix  `[spec §3]`

A node holds its rule's arguments, and a typed derivation fixes each of them (`TDerivesAt`,
`Frontend/Check/TDerives.lean`). Two facts the checker computes are on the term without being
fixed by the derivation, because the rule's statement or `Fam` keeps them out of it:

* **A split's use mask.** The checker decides each split from the masks of `Fam`
  (`Frontend/Check/Fam.lean`), and builds a derivation at every liveness the enclosing rule may
  choose: the split's contexts `Γ₁`, `Γ₂` are chosen per liveness, after the node is built. A
  node at a split carries the mask of its left part as the checker computed it (`Fam.u`), and the
  derivation does not constrain it (`TDerivesAt.split_mask_free`). Relating the mask to `Γ₁`
  needs `Fam.split` to return the parts' masks with its family.
* **A side condition's witness.** `withbor2`'s premise `∃ b, Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b` (and the
  unwinding and slice borrows', and R1's) is a `Prop`: the lifetime the source writes is checked
  and is not an argument of the rule, so it is not a field of the node
  (`TDerivesAt.withbor2_witness_free`).
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- **A split's use mask is the checker's, not the derivation's**: a typed derivation of a pair
is one at any mask. -/
theorem TDerivesAt.split_mask_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J : Jdg}
    {A B : VTy} {u : List Bool} (u' : List Bool) {t₁ t₂ : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.tensorI i J A B u t₁ t₂) J) :
    TDerivesAt Ξ Δ Γ (.tensorI i J A B u' t₁ t₂) J := by
  cases h with
  | tensorI hs h₁ h₂ => exact .tensorI hs h₁ h₂

/-- **A side condition's witness is not on the node**: `withbor2`'s node is the same at every
lifetime that witnesses its side condition. -/
theorem TDerivesAt.withbor2_witness_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo}
    {A B : VTy} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (b₁ b₂ : Lifetime.Life)
    (h₁ : Δ.Defines b₁ ∧ VOutlivesLe Δ b₁ A) (h₂ : Δ.Defines b₂ ∧ VOutlivesLe Δ b₂ A) :
    TDerivesAt Ξ Δ Γ (.withbor2 i (.val (axWithbor2Ty x Δ.meetOfDom A B)) A B x)
        (.val (axWithbor2Ty x Δ.meetOfDom A B)) ∧
      TDerivesAt Ξ Δ Γ (.withbor2 i (.val (axWithbor2Ty x Δ.meetOfDom A B)) A B x)
        (.val (axWithbor2Ty x Δ.meetOfDom A B)) :=
  ⟨.withbor2 x hΓ hx ⟨b₁, h₁⟩ hfree₁ hfree₂, .withbor2 x hΓ hx ⟨b₂, h₂⟩ hfree₁ hfree₂⟩

end BoCa.Fig16.LogRel.Core.Check
