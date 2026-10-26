import Frontend.Check.TDerives

/-!
# Frontend — Check — the clauses' context of a `handle` node is persistent  `[spec §54]`

At `[handle]` and `[handle-boxed]` the clauses are typed over `Γ₁`, the part of the node's
context the split gives them, and the rule's premise `Ctx.DeadP Γ₁` is that every live slot of
`Γ₁` is persistent (SPEC §21, §28). The node's use masks say which slots the clauses use (`u.u₁`,
related to the split by `SplitMasks`). So every slot the clauses use is live in the node's context
at a persistent type: **`Env_N`'s persistence**, R5's admission conjunct A8 (the scope's §5),
read from the checked premise and decided by nothing else.

The checker builds every `handle` node with its derivation (`Checked.tied`, whose second component
is a `TDerivesP` derivation of the whole term, `use` bodies included), so A8 holds at every node of
a checked program: `TDerivesP.handleV_env_persistent`, `TDerivesP.handleVB_env_persistent`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16.LogRel.Core

/-- A slot a part's mask uses is live in that part's context. -/
theorem SplitMasks.live₁ : ∀ {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool} {k : Nat},
    SplitMasks Γ₁ Γ₂ u₁ u₂ → u₁[k]? = some true → ∃ A, Γ₁[k]? = some ⟨A, true⟩
  | _, _, _, _, _, .nil, h => by simp at h
  | ⟨A, l₁⟩ :: _, _, _ :: _, _, 0, .cons h₁ _ _ _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨A, by simp [h₁ h]⟩
  | _ :: _, _, _ :: _, _, k + 1, .cons _ _ _ hs, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact SplitMasks.live₁ hs h

/-- A live slot of a consumed context (`Ctx.DeadP`) is persistent. -/
theorem deadP_persistent_at : ∀ {Γ : Ctx VTy} {k : Nat} {A : VTy},
    Ctx.DeadP Γ → Γ[k]? = some ⟨A, true⟩ → A.Persistent
  | _, _, _, .nil, h => by simp at h
  | _, 0, _, .cons _, h => by simp at h
  | _, k + 1, _, .cons hd, h => by simp only [List.getElem?_cons_succ] at h; exact deadP_persistent_at hd h
  | _, 0, _, .drop hT _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at h; exact h.1 ▸ hT
  | _, k + 1, _, .drop _ hd, h => by simp only [List.getElem?_cons_succ] at h; exact deadP_persistent_at hd h

/-- A slot live in a part of a split is live in the whole, at its type. -/
theorem splitP_slot_left : ∀ {Γ Γ₁ Γ₂ : Ctx VTy} {k : Nat} {A : VTy},
    Ctx.SplitP Γ Γ₁ Γ₂ → Γ₁[k]? = some ⟨A, true⟩ → Γ[k]? = some ⟨A, true⟩
  | _, _, _, _, _, .nil, h => by simp at h
  | _, _, _, 0, _, .left _, h | _, _, _, 0, _, .dup _ _, h => by simpa using h
  | _, _, _, 0, _, .right _, h | _, _, _, 0, _, .dead _, h => by simp at h
  | _, _, _, k + 1, _, .left hs, h | _, _, _, k + 1, _, .right hs, h
  | _, _, _, k + 1, _, .dead hs, h | _, _, _, k + 1, _, .dup _ hs, h => by
      simp only [List.getElem?_cons_succ] at h ⊢; exact splitP_slot_left hs h

/-- From a node's split, masks and consumed clause context: a slot its clauses' mask uses is live
in the node's context at a persistent type. -/
theorem env_persistent_of {Γ Γ₁ Γ₂ : Ctx VTy} {u : Masks} {k : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hm : u.Rel Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hk : u.u₁[k]? = some true) :
    ∃ A, Γ[k]? = some ⟨A, true⟩ ∧ A.Persistent := by
  obtain ⟨A, hA⟩ := SplitMasks.live₁ hm hk
  exact ⟨A, splitP_slot_left hs hA, deadP_persistent_at hd hA⟩

/-- **`Env_N` is persistent at `[handle]`** (A8): every slot the clauses of an `effHandleV` node
use is live in the node's context at a persistent type, by the rule's premise. -/
theorem TDerivesP.handleV_env_persistent {Δ : Lifetime.LifeCtx} {Γ : Ctx VTy} {i : TInfo} {jd : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy} {u : Masks}
    {ks : List ClauseKinds.HKind} {site : Option HSite} {ins : ClauseKinds.HIn} {tc te : TExpr}
    {J : Jdg} (h : TDerivesP Δ Γ (.effHandleV i jd S E fs n A R u ks site ins tc te) J) {k : Nat}
    (hk : u.u₁[k]? = some true) : ∃ T, Γ[k]? = some ⟨T, true⟩ ∧ T.Persistent := by
  cases h with
  | effHandleV hs hm hd => exact env_persistent_of hs hm hd hk

/-- **`Env_N` is persistent at `[handle-boxed]`** (A8). -/
theorem TDerivesP.handleVB_env_persistent {Δ : Lifetime.LifeCtx} {Γ : Ctx VTy} {i : TInfo} {jd : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life} {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite}
    {ins : ClauseKinds.HIn} {tc te : TExpr} {J : Jdg}
    (h : TDerivesP Δ Γ (.effHandleVB i jd S E fs n A R d u ks site ins tc te) J) {k : Nat}
    (hk : u.u₁[k]? = some true) : ∃ T, Γ[k]? = some ⟨T, true⟩ ∧ T.Persistent := by
  cases h with
  | effHandleVB hs hm hd => exact env_persistent_of hs hm hd hk

end BoCa.Fig16.LogRel.Core.Check
