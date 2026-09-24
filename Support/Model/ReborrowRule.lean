import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Subtraction

/-!
# Support — Model — ReborrowRule

`[about ours]`.  What `[TR]` 6.150 names and does not prove: the hypothesis `RebEscrow` (6.55's two inputs at the reborrows `↺_β P̂` names), a lifetime below two given ones, and `ρ⁺|own = ∅` through the pieces of `ρᵢ ● ρ⁺′`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-- The two inputs `[TR]` 6.55 adds, at the reborrows `↺_β P̂` produces:
`χ ∈ reb_β(σ)` with `P̂(w)(χ)`.  `EscrowAgree σ χ a` is asked of every `a` that is
some resource's aliasable walk, as 6.55 takes it (`∀a. ag(ρ_f) = a ⇒ …`).
`[about ours: the two added inputs of `Fig16.ResU.six55`, at the reborrows
`[TR]` 6.150's precondition names]` -/
def RebEscrow (P : Life → BoCa.Val → WProp) : Prop :=
  ∀ (b : Life) (w : BoCa.Val) (σ χ : WRes),
    ResU.Reb b σ χ → P b w χ →
      (∃ A, AgW χ A) ∧ ∀ r a : WRes, AgW r a → EscrowAgree σ χ a

/-- *"Such a `β` always exists because for any lifetime, the set of lifetimes
shorter than it is infinite."* — `[TR]` p. 39, H11.
`[about ours: the sentence `[TR]` p. 39 gives for H11, at `↓`]` -/
theorem exists_shorter (gi gb : Life) : ∃ b : Life, b ⊏ gi ∧ b ⊏ gb :=
  ⟨↓(gi ⊓ gb),
    lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left,
    lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right⟩

/-- A single `imm` cell carries no `own` cell. -/
theorem noOwn_single_imm (l : BoCa.Loc) (s : LSet) (v : BoCa.Val) (σ : WRes)
    (hs : σ.InStratum s.join) : NoOwn (ResU.single l (CellU.immOf s v σ hs)) := by
  refine noOwn_iff.mpr fun m ψ hm => ?_
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    rw [CellU.kind_immOf]
    exact fun h => Kind.noConfusion h
  · rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)

/-- `ρ|own,mut` has no `own` cell when `ρ` has none. -/
theorem noOwn_exclPart {ρ : WRes} (h : NoOwn ρ) : NoOwn ρ.exclPart :=
  noOwn_iff.mpr fun l ψ hl =>
    noOwn_iff.mp h l ψ (ResU.exclPart_eq_some.mp hl).1

/-- A `●`-factor of an all-`imm` resource has no `own` cell.
`[about ours: the `|own = ∅` of a factor of `ρ|imm`, which `[TR]` 6.150's G6
takes in one step]` -/
theorem noOwn_le_restrict_imm {τ ρ : WRes} (h : ResU.Le τ (ρ.restrict Kind.imm)) :
    NoOwn τ := by
  obtain ⟨f, hf⟩ := h
  refine noOwn_iff.mpr fun l ψ hl hk => ?_
  have hc := hf.2 l
  rw [hl] at hc
  cases e : f.get l with
  | none =>
      rw [e] at hc
      have : (ρ.restrict Kind.imm).get l = some ψ := hc
      exact absurd (ResU.restrict_eq_some.mp this).2 (by rw [hk]; exact fun c => Kind.noConfusion c)
  | some φ =>
      rw [e] at hc
      obtain ⟨ζ, -, hC⟩ := hc
      obtain ⟨s₁, s₂, w, χ, k₁, k₂, k₃, e₁, -, -⟩ := hC
      rw [e₁, CellU.kind_immOf] at hk
      exact Kind.noConfusion hk

/-- `ρ⁺ ⊟ ρ_reb` has no `own` cell when `ρ⁺` has none. -/
theorem noOwn_subKeep {ρp D ψ : WRes} (h : ResU.SubKeep ρp D ψ) (hn : NoOwn ρp) :
    NoOwn ψ := by
  obtain ⟨ρ'', -, hle, -, -, hcomp⟩ := h
  exact noOwn_compS hcomp (noOwn_exclPart hn) (noOwn_le_restrict_imm hle)

end BoCa.Fig16.BoLo

end
