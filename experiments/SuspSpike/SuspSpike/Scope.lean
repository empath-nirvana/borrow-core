import SuspSpike.Conservative

/-!
# SuspSpike — a run in scope ends in scope

`wpG` ends at a list with its start's members (its last conjunct). At a table that owes
continuations only at lists with the stop's members (`Table.Scoped`), every resumption is in
scope too, so every answer of an `ewpTS` run is at a list with the start's members
(`ewp_sameMem`). This is what a call-like operation's handler reads: the clause's `g x` answers
in the scope of the stop, and `κ` is resumed there.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `wpG` ends at a list with its start's members. -/
theorem wpG_sameMem {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} {ρ : WRes}
    (h : wpG ls e Q ρ) : wpG ls e (fun ls' t σ => SameMem ls ls' ∧ Q ls' t σ) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a14, a15⟩

/-- **In scope.** At a monotone scoped table, every answer of an `ewpTS` run is at a list with
the start's members. -/
theorem ewp_sameMem {Tb : Table} (hTb : Tb.Mono) (hS : Table.Scoped Tb)
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e Tb Q ρ) :
    ewpTS ls e Tb (fun ls' v σ => SameMem ls ls' ∧ Q ls' v σ) ρ := by
  refine (ewp_ind (fun ls e ρ => ∀ ls₀, SameMem ls₀ ls →
    ewpTS ls e Tb (fun ls' v σ => SameMem ls₀ ls' ∧ Q ls' v σ) ρ) ?_ h) ls (SameMem.refl ls)
  intro ls e ρ hs ls₀ h₀
  refine ewp_fold hTb (wpG_mono ?_ (wpG_sameMem hs))
  rintro ls' t σ ⟨hm, hq⟩
  rcases hq with ⟨v, rfl, hv⟩ | hq
  · exact Or.inl ⟨v, rfl, h₀.trans hm, hv⟩
  · exact Or.inr (hS ls' t _ _ σ (fun ls'' e' τ hs' hP => hP ls₀ ((h₀.trans hm).trans hs')) hq)

end SuspSpike

end
