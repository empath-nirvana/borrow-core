import GhostEnd.Relend

/-!
# GhostEnd — freeze: ending a suspended segment's lend, and the extent

**Admissibility of the ghost end.** BoLo ends a borrow when its borrower returns: 6.65's exit
(H26–H35). There the callback's final share is in `[α]`, holds no borrow at `α`, and gives
`ℓ ↦ w ⋆ P̂(w)` back. Freezing at a stop is admissible because nothing in that exit reads the
term the run ends at. `wpG_M_frameX` is 6.65 over `wpG`, whose postcondition is over any final
term, stopped or returned, by the printed proof unchanged. What a stop has to supply is exactly
what a return supplies: the share in the shape `[α] ∀w. ℓ ↦ w ─⋆ P̂(w) ─⋆ Φ`. Its borrower meets
that in two moves, and neither runs a step:

1. **The view goes to the leftover.** `ℓ ↦ M_α P̂` is a single `mut` cell and owns nothing
   (`noOwn_ptoMutS`). So it can join `ρ⁺` (`wpG_garbage`, 6.148's argument). The borrower's
   variable still holds `ℓ`, but only as a value in the stopped term, which is not a resource.
2. **The rest is in `[α]`.** Every other cell of the share outlives `α`. In a straight-line
   borrower the rest is empty. In general it is the borrower's frames' values: every one but
   the view has a type that outlives the internal lifetime, by 6.60.

`freeze_at` is these two moves, at a run of no steps (`wpG_here`). The lender's half, that
`ρ ↭ ρ′ ● ρ⁺` holds with the owner unfolded (6.28) and that the memories agree (6.25), is
`wpG_M_frameX`'s H33–H34, applied by `ewpTS_M_frameR`.

**The extent.** `wpG_box` is `[TR]` 6.147 at `wpG`: a run that starts in `Res_h` ends in `Res_h`,
at a stop as at a return. `frozen_above_extent` reads off the invariant the split needs. Let a
handler's extent `'h` be chosen as 6.65's H4 chooses a lend's lifetime, below every lifetime
live when the handler is installed, so that the body starts in `Res_h`. Then every borrow cell
of a frozen share is strictly longer-lived than `'h`, and none sits at `'h`. Internal cells are
not in the share at all, since freezing ended them. So the split external/owned is exhaustive.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The borrower's view owns nothing: it is a single `mut` cell. -/
theorem noOwn_ptoMutS {l : BoCa.Loc} {α : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoMutS l α ls P ρ) : NoOwn ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- **Freeze at a stop.** A borrower stopped at `t`, holding its view `ℓ ↦ M_α P̂` beside a share
already in the stop's postcondition, meets that postcondition with no step: the view is left
behind. -/
theorem freeze_at {l : BoCa.Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {t : Expr} {Φ : List SRec → Expr → WProp} :
    Entails (ptoMutS l α ls P ⋆ Φ ls t) (wpG ls t Φ) := by
  rintro ρ ⟨ρm, ρr, hc, hm, hr⟩
  exact wpG_garbage (wpG_here _ _ _ ρ ⟨ρr, ρm, ResU.CompS.comm hc, noOwn_ptoMutS hm, hr⟩)

/-- `[TR]` 6.147 (`wp-box`) at `wpG`: a run from `Res_h` ends in `Res_h`, at any final term. -/
theorem wpG_box (ls : List SRec) (h : Life) (e : Expr) (Q : List SRec → Expr → WProp) :
    Entails (box h (wpG ls e Q)) (wpG ls e fun ls' t => box h (Q ls' t)) := by
  rintro ρ ⟨hw, hout⟩ ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC, ((outlives_comp h₉ h).mp (updV_outlives hout hA)).1⟩

/-- **No frozen cell at the extent.** A share in `Res_h` has every borrow cell strictly
longer-lived than `h`: none is at `h`, and none below it. -/
theorem frozen_above_extent {h : Life} {ρ : WRes} (hρ : ρ.InStratum h) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (hl : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    h ⊏ ψ.at := by
  have := hρ l ψ hl
  cases ψ
  · exact absurd rfl hk
  · exact this
  · exact this

end GhostEnd
