import GhostEnd.Typed

/-!
# GhostEnd — the ghost lend table and its invariant (#262, item 1)

A lend at `α` records a cell at the lent location `ℓ`, at `α`. Inside the borrower that is the
only borrow cell recorded at an internal lifetime: every other borrow cell the borrower holds was
recorded strictly above `α`. The table maps the internal lifetime `α` to the location `ℓ`, and
`TabAt ℓ α ρ` says that `ρ` is consistent with it:

* every borrow cell of `ρ` is at a lifetime `⊒ α` (`ρ ∈ Res_{↓α}`), and
* every borrow cell of `ρ` away from `ℓ` is strictly above `α` (`Res_α` off `ℓ`).

So the cell at `ℓ` is the only one the ghost end touches, and the only one the re-lend replaces.

**It is a fact about runs.** `withbor` is the only introduction of a lifetime, and `↭` keeps the
lifetime of every flattened borrow cell at its location (`[TR]` 6.50). A run therefore cannot hand
back a cell at `α` at a new location: a lend it opens is at a fresh lifetime and ends before the
run returns or stops, and a load reads through cells whose lifetimes it keeps. `tabAt_updV` is
6.50 at `↓α` with 6.50 at one location (`ResU.updV_outlives_at`) away from `ℓ`, and `wpG_tabAt`
and `wpTS_tabAt` put it in the postcondition of every run, at a stop as at a return.

**The `⊒` half is the relation itself.** `𝒱⟦Mut 'x T⟧_{δ[x ↦ α]}` holds a cell at a lifetime
`⊒ α` (`ptoMutS`'s `α ⊑ b`). A view of a cell recorded strictly above `α`, such as an outer
borrow weakened to `'x`, stays in the relation at every later lend `α′ ⊑ α` (M Vary,
`vC_mut_vary`). Only the cell at `ℓ` needs the re-lend.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The table at a lend.** Every borrow cell of `ρ` is at a lifetime `⊒ α`, and every one away
from `ℓ` strictly above it: the only cell recorded at the internal lifetime `α` is at `ℓ`. -/
def TabAt (l : BoCa.Loc) (α : Life) (ρ : WRes) : Prop :=
  ρ.InStratum (↓α) ∧ ∀ k ψ, k ≠ l → ρ.get k = some ψ → ψ.InStratum α

theorem down_lt (α : Life) : (↓α) < α := by
  show OrderDual.ofDual α < OrderDual.ofDual α + 1
  omega

/-- A resource strictly above `α` is consistent with the table. -/
theorem tabAt_of_inStratum {l : BoCa.Loc} {α : Life} {ρ : WRes} (h : ρ.InStratum α) :
    TabAt l α ρ :=
  ⟨ResU.InStratum.mono (le_of_lt (down_lt α)) h, fun k _ _ e => h k _ e⟩

/-- The empty resource. -/
theorem tabAt_empty (l : BoCa.Loc) (α : Life) : TabAt l α PMap.empty :=
  tabAt_of_inStratum (ResU.inStratum_empty α)

/-- A later lend `α′ ⊑ α` keeps the table: a cell at a lifetime `⊒ α` is `⊒ α′`. -/
theorem tabAt_mono {l : BoCa.Loc} {α α' : Life} (hle : α' ≤ α) {ρ : WRes} (h : TabAt l α ρ) :
    TabAt l α' ρ := by
  refine ⟨fun k ψ e => ?_, fun k ψ hk e => (h.2 k ψ hk e).mono hle⟩
  have h₁ := h.1 k ψ e
  have hd : (↓α') ≤ (↓α) := by
    show OrderDual.ofDual α + 1 ≤ OrderDual.ofDual α' + 1
    have : OrderDual.ofDual α ≤ OrderDual.ofDual α' := hle
    omega
  exact h₁.mono hd

/-- **Parts and whole.** The table holds of a composite iff it holds of both parts. -/
theorem tabAt_comp {l : BoCa.Loc} {α : Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) :
    TabAt l α ρ ↔ (TabAt l α ρ₁ ∧ TabAt l α ρ₂) := by
  constructor
  · rintro ⟨hd, ho⟩
    obtain ⟨hd₁, hd₂⟩ := (outlives_comp hc (↓α)).mp hd
    exact ⟨⟨hd₁, fun k ψ hk e => ResU.CompS.inStratum_left_at hc (fun φ f => ho k φ hk f) e⟩,
      ⟨hd₂, fun k ψ hk e => ResU.CompS.inStratum_right_at hc (fun φ f => ho k φ hk f) e⟩⟩
  · rintro ⟨⟨hd₁, ho₁⟩, ⟨hd₂, ho₂⟩⟩
    exact ⟨(outlives_comp hc (↓α)).mpr ⟨hd₁, hd₂⟩, fun k ψ hk e =>
      ResU.inStratum_comp_at (CellU.compS_hC α) hc (fun φ f => ho₁ k φ hk f)
        (fun φ f => ho₂ k φ hk f) e⟩

/-- **`↭` keeps the table** (`[TR]` 6.50 at `↓α`, and at each location away from `ℓ`). -/
theorem tabAt_updV {l : BoCa.Loc} {α : Life} {ρ ρ' : WRes} (h : TabAt l α ρ)
    (hu : ResU.UpdV ρ ρ') : TabAt l α ρ' :=
  ⟨updV_outlives h.1 hu, fun k _ hk e =>
    ResU.updV_outlives_at h.1 hu (fun φ f => h.2 k φ hk f) e⟩

/-- **Every run keeps the table**, at a stop as at a return: `wpG` from a resource consistent
with it ends in one. -/
theorem wpG_tabAt (l : BoCa.Loc) (α : Life) (ls : List SRec) (e : Expr)
    (Q : List SRec → Expr → WProp) {ρ : WRes} (ht : TabAt l α ρ) (hw : wpG ls e Q ρ) :
    wpG ls e (fun ls' t ρ' => TabAt l α ρ' ∧ Q ls' t ρ') ρ := by
  intro ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, ((tabAt_comp h₉).mp (tabAt_updV ht hA)).1, hC⟩

/-- `wpG_tabAt` at `wpTS`. -/
theorem wpTS_tabAt (l : BoCa.Loc) (α : Life) (ls : List SRec) (e : Expr)
    (Q : List SRec → Val → WProp) {ρ : WRes} (ht : TabAt l α ρ) (hw : wpTS ls e Q ρ) :
    wpTS ls e (fun ls' v ρ' => TabAt l α ρ' ∧ Q ls' v ρ') ρ := by
  intro ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, ((tabAt_comp h₉).mp (tabAt_updV ht hA)).1, hC⟩

/-! ### The cell at `ℓ` -/

/-- A `mut` cell at a lifetime `⊒ α` is in `Res_{↓α}`. -/
theorem ptoMutS_down {l : BoCa.Loc} {α : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoMutS l α ls P ρ) : ρ.InStratum (↓α) := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, rfl, -⟩ := h
  intro k ψ e
  by_cases hk : k = l
  · subst hk
    rw [ResU.single_get_self] at e
    cases Option.some.inj e
    exact lt_of_lt_of_le (down_lt α) hab
  · rw [ResU.single_get_ne _ hk] at e
    exact absurd e (by simp)

/-- **The view at `ℓ` is consistent with the table.** -/
theorem tabAt_view {l : BoCa.Loc} {α : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoMutS l α ls P ρ) : TabAt l α ρ := by
  refine ⟨ptoMutS_down h, fun k ψ hk e => ?_⟩
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := h
  rw [ResU.single_get_ne _ hk] at e
  exact absurd e (by simp)

/-- **M Vary at the relation.** A view at `δ[x ↦ α]` is a view at every later lend `α′ ⊑ α`, the
cell untouched: `𝒱⟦Mut 'x T⟧` is antitone in `'x`. -/
theorem vC_mut_vary {x : LifeVar} {T : VTy} (hT : ¬ VFree x T) {ls : List SRec} {δ : LSub}
    {α α' : Life} (hle : α' ≤ α) {v : Val} {ρ : WRes}
    (h : vC true (.mut (.var x) T) ls (δ.extend x α) v ρ) :
    vC true (.mut (.var x) T) ls (δ.extend x α') v ρ := by
  obtain ⟨α₀, hα₀, l', hs⟩ := h
  rw [interp_ext_self] at hα₀
  cases Option.some.inj hα₀
  obtain ⟨hv, hm⟩ := pure_sep_iff.mp hs
  refine ⟨α', interp_ext_self δ x α', l', pure_sep_mk hv ?_⟩
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, hls₀, hunif⟩ := hm
  refine ⟨b, u, σ, hσ, Q, hw, ls₀, le_trans hle hab, hρ, ?_, hls₀, ?_⟩
  · refine hQ.trans ?_
    show vC true T ls₀ (δ.extend x α) = vC true T ls₀ (δ.extend x α')
    rw [vC_extend_of_not_free hT, vC_extend_of_not_free hT]
  · intro ls' u' σ' hP
    have hP' : vC true T ls' (δ.extend x α') u' σ' := hP
    rw [vC_extend_of_not_free hT] at hP'
    exact hunif ls' u' σ' (show vC true T ls' (δ.extend x α) u' σ' by
      rw [vC_extend_of_not_free hT]; exact hP')

end GhostEnd
