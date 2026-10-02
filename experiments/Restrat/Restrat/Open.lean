import Restrat.MutCounterexample
import Restrat.Flattening
import Paper.Examples.Model

/-!
# Restrat — what is not natural, and what is open

* `VDenNatural e`: every `𝒱⟦T⟧` agrees with itself along `e`.  **Refuted** at the shift
  `n ↦ n + 1` (`not_vDenNatural`), by `Restrat.MutCounterexample`.
* `WpNatural e`: `wp(e){Q̂′}` agrees with `wp(e){Q̂}` whenever `Q̂′` agrees with `Q̂` and is
  supported.  **Open**: not derived, and no obstruction to it is verified.  The step where the
  induction of `Restrat.Propositions`/`Restrat.Flattening` stops is `wp`'s `∀ρ_f # ρ`: at a moved
  resource, a frame need not be moved (`frame_outside_image`), so the hypothesis about moved
  resources does not apply to it.  This is a fact about the proof method, not about `wp`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Restrat.Open
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel
open BoCa.Lifetime (LSub)

/-- Every type interpretation agrees with itself along `e`. -/
def VDenNatural {c : Life} (e : Emb c) : Prop :=
  ∀ (T : Ty) (δ : LSub) (v : Val), e.Agree (vDen T (LSub.mapN e.toNat δ) v) (vDen T δ v)

/-- **Not natural.** -/
theorem not_vDenNatural : ¬ VDenNatural MutCounterexample.e := by
  intro h
  have := (h MutCounterexample.T MutCounterexample.δ (.loc MutCounterexample.ℓ)
    MutCounterexample.ρ₀).mpr MutCounterexample.holds
  exact MutCounterexample.fails this

/-- `wp` agrees along `e` at agreeing, supported postconditions.  Open. -/
def WpNatural {c : Life} (e : Emb c) : Prop :=
  ∀ (M : Expr) (Q' Q : Val → WProp), (∀ v, e.Agree (Q' v) (Q v)) → (∀ v, e.Supp (Q' v)) →
    e.Agree (wp M Q') (wp M Q)

/-- A frame of a moved resource that is not a moved resource: `ℓ ↦ mut(1, (), ∅, ⊤)` is `#` the
empty resource (which is moved), and its lifetime `1` is in the gap of `n ↦ n + 1`. -/
theorem frame_outside_image :
    ∃ ρ ρf : WRes, ResU.Hash ρf (MutCounterexample.e.relRU ρ) ∧
      ¬ ∃ ρf₀, ρf = MutCounterexample.e.relRU ρf₀ := by
  let X : WRes := ResU.single 0 (CellU.mutOf (OrderDual.toDual 1) Val.unit PMap.empty
    (ResU.inStratum_empty _) (fun _ _ => True) trivial)
  have hX : ResU.Valid X := by
    obtain ⟨-, ρ, hρ, hv⟩ := ResU.hash_empty_single_mut (Loc := BoCa.Loc) (Val := BoCa.Val) 0
      (OrderDual.toDual 1) Val.unit
    rwa [eq_of_compS_empty_left hρ] at hv
  refine ⟨PMap.empty, X, ?_, ?_⟩
  · rw [Emb.relRU_empty]; exact ResU.hash_empty_right hX
  · rintro ⟨ρf₀, h⟩
    have hc := congrArg (fun r => PMap.get r 0) h
    simp only [X, ResU.single_get_self, Emb.relRU_get] at hc
    obtain ⟨ψ, -, hψ⟩ := Option.map_eq_some_iff.mp hc.symm
    have hat := congrArg CellU.at hψ
    rw [Emb.at_relU, CellU.at_mutOf] at hat
    exact MutCounterexample.gap _ hat

end Restrat.Open
