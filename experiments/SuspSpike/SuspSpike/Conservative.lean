import SuspSpike.Defs

/-!
# SuspSpike — conservativity

* `opTableC_none`: at the empty grade the graded table **is** Core's `opTable`, so `ewpTS`, and
  every clause of Core's relation that reads a row through its table, is unchanged
  (`ewpTS_none`). A row with no call-like operation is read exactly as Core reads it.
* `opTableC_of_opTable`, `ewp_grade`: grading a row only weakens what its stops owe, so every
  computation in Core's relation at a row is in the graded relation at that row. No result of
  Core is lost by grading an operation.
* `opTableC_mono`, `opTableC_scoped_of`: the graded table is monotone; at a class-1 row it owes
  continuations only in scope.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Conservativity, definitionally.** At the empty grade the graded table is `opTable`. -/
theorem opTableC_none (T : OpTab) : opTableC T Grade.none = opTable T := rfl

/-- **Conservativity of the effectful `wp`**: at the empty grade, `ewpTS` at the graded table is
Core's `ewpTS` at `opTable`. -/
theorem ewpTS_none (T : OpTab) (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) :
    ewpTS ls e (opTableC T Grade.none) Q = ewpTS ls e (opTable T) Q := rfl

/-- Core's share gives the call-like one: a list with the stop's members is an `Ext`-extension
at every resource. -/
theorem contShareC_of_contShare {en : OpEnt} {ls : List SRec} {K : Kont}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : contShare en ls K Φ ρ) :
    contShareC en ls K Φ ρ :=
  fun ls' hs w => (h.2 ls' (owed_of_same en hs ρ)).1 w

theorem shareAt_of_contShare (C : Grade) (n i : UInt32) {en : OpEnt} {ls : List SRec} {K : Kont}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : contShare en ls K Φ ρ) :
    shareAt C n i en ls K Φ ρ := by
  cases hg : C n i
  · rw [shareAt_false hg]; exact h
  · rw [shareAt_true hg]; exact contShareC_of_contShare h

/-- **Grading weakens a protocol.** Every stop `opTable` admits, the graded table admits. -/
theorem opTableC_of_opTable (T : OpTab) (C : Grade) {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTable T ls t Φ ρ) :
    opTableC T C ls t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, shareAt_of_contShare C n i hk⟩⟩
  · exact Or.inr h

theorem shareAt_mono {C : Grade} {n i : UInt32} {en : OpEnt} {ls : List SRec} {K : Kont}
    {Φ Φ' : List SRec → Expr → WProp} (hΦ : ∀ ls e ρ, Φ ls e ρ → Φ' ls e ρ) {ρ : WRes}
    (h : shareAt C n i en ls K Φ ρ) : shareAt C n i en ls K Φ' ρ := by
  cases hg : C n i
  · rw [shareAt_false hg] at h ⊢
    exact ⟨h.1, fun ls' he => ⟨fun w τ₁ τ₂ hB hc => hΦ _ _ _ ((h.2 ls' he).1 w τ₁ τ₂ hB hc),
      (h.2 ls' he).2⟩⟩
  · rw [shareAt_true hg] at h ⊢
    exact fun ls' hs w τ₁ τ₂ hB hc => hΦ _ _ _ (h ls' hs w τ₁ τ₂ hB hc)

/-- The graded table is monotone. -/
theorem opTableC_mono (T : OpTab) (C : Grade) : (opTableC T C).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, shareAt_mono hΦ hk⟩⟩
  · exact Or.inr h

/-- **Grading keeps Core's relation**: a computation in `ewpTS` at `opTable T` is in `ewpTS` at
the graded table, at every grade. -/
theorem ewp_grade (T : OpTab) (C : Grade) {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) :
    ewpTS ls e (opTableC T C) Q ρ :=
  ewp_mono (opTableC_mono T C) (fun _ _ _ _ h => opTableC_of_opTable T C h)
    (fun _ _ _ h => h) h

/-- At a class-1 row every stop is call-like, so the table owes continuations only in scope. -/
theorem opTableC_scoped_of {T : OpTab} {C : Grade} (hC : CallRow T C) :
    Table.Scoped (opTableC T C) := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨hpure, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp hp
    have hg := (hC.1 n i en hpure.2.2.1).1
    rw [shareAt_true hg] at hk
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, ?_⟩⟩
    rw [shareAt_true hg]
    exact fun ls' hs w τ₁ τ₂ hB hcτ => hΦ _ _ _ hs (hk ls' hs w τ₁ τ₂ hB hcτ)
  · obtain ⟨hpure, -⟩ := pure_sep_iff.mp hp
    exact absurd (hC.1 n i en hpure.2.2.1).2.2 (by rw [hpure.2.2.2]; decide)

end SuspSpike

end
