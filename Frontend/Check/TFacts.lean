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

A third is a field the checker adds to a node that its rule does not have:

* **The clause kinds at `[handle]`** (`ks`). The checker classifies each clause from the typed
  term of the value its clauses variable is bound to (`Frontend/Check/Kinds.lean`), and each kind
  gives its law's premise at that clause (`classify_sound`). The rule's premise is the clauses
  variable, not its binding, so the derivation does not constrain the kinds
  (`TDerivesAt.kinds_free`).
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

/-- **The clause kinds are the checker's, not the derivation's**: a typed derivation of a
`handle` node is one at any kinds. -/
theorem TDerivesAt.kinds_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J : Jdg}
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : List Bool} {ks : List ClauseKinds.HKind} (ks' : List ClauseKinds.HKind) {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks tc te) J) :
    TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks' tc te) J := by
  cases h with
  | effHandleV hAt hs hd hH hc hn0 hnS hlen hdv he => exact .effHandleV hAt hs hd hH hc hn0 hnS hlen hdv he

end BoCa.Fig16.LogRel.Core.Check
