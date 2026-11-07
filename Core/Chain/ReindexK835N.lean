import Core.Chain.Goal791N

/-!
# A run re-indexed along a world map  `[spec §19, §27]`

`docs/new-core/scope-835-tables.md` §10.3. A lend's callback is a thunk of the relation at the
typed world: `cN` at the lend's world, its tables indexed by its own worlds. The Mut Frame reads
the callback's run indexed by the lender's worlds, at the tables under the lend's world map
(`KW.lend`). `erwpK_comap` moves a run along a world map `g`: a run from `g x`, indexed by `ι`, is
a run from `x`, indexed by `ι′`, when the location family at `y` is the one at `g y`, every post
at a world `g x` reaches is one at a world `x` reaches, and every stop at `g y`'s table is a stop
at `y`'s whose continuation is owed only at the images of the worlds it is owed at.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- **`erwpK` along a world map, at the worlds an invariant holds at.** A run from `g x` over `ι`
is one from `x` over `ι′`, at `x` with `Inv x`: the location family at `y` is `Φ (g y)`; a post at
a world `g x` reaches is one at a world `x` reaches; a stop at `g y`'s table, `Inv y`, is one at
`y`'s, its continuation owed at `y′` (with `Inv y′`) wherever the first owes it at `g y′`. -/
theorem erwpK_comap {ι ι' : Type} (g : ι' → ι) (Inv : ι' → Prop) {V : ι → ι → Prop}
    {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN} {V' : ι' → ι' → Prop}
    {Φ' : ι' → LocFam} {Tb' : ι' → TableK ι'} {Q' : ι' → PostN} (hΦ : ∀ y, Φ' y = Φ (g y))
    (hQ : ∀ x, Inv x → ∀ y k ls v ρ, V (g x) y → Q y k ls v ρ → ∃ y', V' x y' ∧ Q' y' k ls v ρ)
    (hT : ∀ y, Inv y → ∀ k ls t (Ψ : ContK ι) (Ψ' : ContK ι') ρ,
      (∀ y' k', k' < k → Inv y' → ∀ ls e ρ, Ψ (g y') k' ls e ρ → Ψ' y' k' ls e ρ) →
      Tb (g y) k ls t Ψ ρ → Tb' y k ls t Ψ' ρ) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ Tb Q (g x) n ls e ρ →
      erwpK (ℍ := ℍ) V' Φ' Tb' Q' x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h
  rw [erwpK_eq] at h ⊢
  rw [hΦ x]
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ht
  · obtain ⟨y', hy', hq'⟩ := hQ x hx y _ _ _ _ hy hq
    exact Or.inl ⟨v, hv, y', hy', hq'⟩
  · refine Or.inr (hT x hx k ls' t _ _ σ (fun y' k' hk' hy' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpCK, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) y' hy' _ _ _ hΨ

/-- **Adding a lend at `α` is an extension at a resource in `Res_α`**, fresh or not: such a
resource reads only keys above `α`, which the lend leaves as they are (`LocTy.extR_of_add`'s
converse). -/
theorem LocTy.extR_add (Θ : LocTy) (l₀ : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α)
    {ρ : WRes} (hρ : ρ.InStratum α) : Θ.ExtR (Θ.add l₀ α F) ρ := by
  refine ⟨fun l a G hG hc => ?_, fun x hx _ => hx⟩
  have hαa : α < a := hc.of_stratum hρ
  rw [LocTy.add_keep Θ l₀ F l (ne_of_gt hαa)]
  exact ⟨hG, LocTy.above_add Θ l₀ (not_lt_of_gt hαa) F⟩

open Goal791N in
/-- **A lend below a bound is invisible to `𝒱⟦A⟧` of an `A` outliving the bound**, at every
world (`vN_add_eq_bnd` without freshness): the value's resource is in `Res_α`
(`vN_inStratum_bnd`), where adding and dropping the lend are both extensions. -/
theorem vN_add_eq {A : VTy} {bnd : Lifetime.Life}
    (hO : VOutlives BoCa.Lifetime.LifeCtx.empty bnd A) (δ : BoCa.Lifetime.LSub) {α : Life}
    (hLt : LogRel.LtLife δ bnd α) (Θ : LocTy) (l : Loc) (F : Nat → Val → SPropS Loc Val α) :
    vN (ℍ := ℍ) A δ (Θ.add l α F) = vN (ℍ := ℍ) A δ Θ := by
  funext n v ρ
  exact propext ⟨fun h => vN_local A δ Θ l α F n v ρ (vN_inStratum_bnd hO hLt h) h,
    fun h => vN_extR A δ n v ρ (LocTy.extR_add Θ l F (vN_inStratum_bnd hO hLt h)) h⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
