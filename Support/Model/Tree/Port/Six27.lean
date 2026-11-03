import Support.Model.Tree.Port.Down

/-!
# `[TR]` Lemma 6.27 over the tree-stratified carrier

`[spec §62]`. The printed proof (`Paper/S6_2_NonStandardLemmas/Lemmas.lean`) reads `↓α` (row
5.12, `α + 1`): `@ρ ⊐ α` puts `ρ ● ℓ ↦ mut(α, …)` in `Res_{↓α}`, so the `mut` cell sits in no
witness of `⦇ρ′⦈`. In a tree `↓α` is read as a stratum `D` with `K.DownOf D α` (`hD`,
`Tree/Port/Down.lean`). A stratum below an antichain exists only when the antichain is one
lifetime (`WCactus.downOf_anti_singleton`), so 6.27 is stated for a `mut` cell at `{a}`.

**Open: a `mut` cell at an antichain of two or more lifetimes.** Such a cell is a composite of
`mut` cells at siblings (`mut(β̄₁) ○ mut(β̄₂) = mut(min(β̄₁ ∪ β̄₂))`). For it 6.27 should
read: if `@ρ ⊐ x` at every `x ∈ ᾱ` and `ρ ● ℓ ↦ mut(ᾱ, v, ρ_v, P̂) ↭ ρ′`, then
`ρ′ = ρ′/ℓ ● ℓ ↦ mut(ᾱ, v′, ρ′_v, P̂)`. The printed proof does not carry over: it needs a
stratum below `ᾱ`, and no lifetime lies below two siblings. The step it serves, that the `mut`
cell sits in no witness of `⦇ρ′⦈`, would follow from a different fact: a cell inside a witness
lies in the stratum of the cell holding it, and no stratum lies below two siblings. That
statement is not derived here.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.27 · `[TR]` p. 10 · `variant`

> If @ρ ⊐ α and ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ ρ′ then ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)

**Printed proof, transcribed.** Let `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  `⦇ρ ● ρ_m⦈` and `⦇ρ′⦈` have the same borrows, so `⦇ρ′⦈` has a `mut` cell matching `ρ_m`: some `ℓ ↦ mut(α, v′, ρ′_v, P̂) ∈ ⦇ρ′⦈`.  Since `@ρ ⊐ α`, every other borrow in `⦇ρ′⦈` is disjoint from `α`, which by well-formedness of the resource `ρ′` means the cell cannot be in any `ρ″` of a `mut(_, _, ρ″, _)` or `imm(_, _, ρ″)` in `ρ′`.  So `ρ′(ℓ) = mut(α, v′, ρ′_v, P̂)` and `ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂)`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six27`, tag `[variant: the `mut` cell at one lifetime `{a}`; `↓α` read as the hypothesis `hD : K.DownOf D {a}`]`.
-/
/-- `[TR]` Lemma 6.27 (p. 10), over the tree-stratified carrier, for a `mut` cell at one
lifetime `{a}`. **Forced change:** `↓a` (row 5.12, `a + 1`) is read as a stratum `D` with
`K.DownOf D {a}` (`hD`): strictly below `a`, and anything strictly above it is at or above `a`.
A covering child of `a` gives one (`WCactus.downOf_covers`); in a tree `a` need not have a
child, so it is a hypothesis. `hD` would force an antichain to be one lifetime
(`WCactus.downOf_anti_singleton`), so stating 6.27 at an antichain with `hD` adds nothing. The
proof is the printed one with `↓a` read through `hD`. `[variant: the `mut` cell at `{a}`;
`hD`]` -/
theorem ResUT.six27 {l : BoCa.Loc} {a : Life} {v : BoCa.Val}
    {D : TSet} (hD : K.DownOf D (TSet.single a))
    {ρ ρv M ρ' : ResUT BoCa.Loc BoCa.Val K}
    {h : ResUT.InStratum (TSet.single a) ρv} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K (TSet.single a)}
    {hw : P v ⟨ρv, h⟩}
    (hout : ResUT.InStratum (TSet.single a) ρ)
    (hM : ResUT.CompS ρ (ResUT.single l (CellUT.mutOf (TSet.single a) v ρv h P hw)) M)
    (hu : ResUT.UpdV M ρ') :
    ∃ (v' : BoCa.Val) (χ : ResUT BoCa.Loc BoCa.Val K) (h' : ResUT.InStratum (TSet.single a) χ)
      (hw' : P v' ⟨χ, h'⟩),
      ResUT.CompS (ρ'.del l) (ResUT.single l (CellUT.mutOf (TSet.single a) v' χ h' P hw')) ρ' := by
  classical
  have hkm : (CellUT.mutOf (TSet.single a) v ρv h P hw).kind ≠ Kind.imm := by
    rw [CellUT.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hMl : M.get l = some (CellUT.mutOf (TSet.single a) v ρv h P hw) :=
    (ResUT.CompS.get_left_of_ne_imm (ResUT.CompS.comm hM)
      (ResUT.single_get_self _ _) hkm).2
  have hσl : σ.get l = some (CellUT.mutOf (TSet.single a) v ρv h P hw) :=
    ResUT.flat_get_of_ne_imm hσ hMl hkm
  obtain ⟨v', χ, h', hw', hflat⟩ := (hu.1.2 l (TSet.single a) P).mp ⟨v, ρv, h, hw, ⟨σ, hσ, hσl⟩⟩
  rw [ResUT.flatAt_iff hσ'] at hflat
  have hdown : ∀ x ∈ D.set, ∃ y ∈ (TSet.single a).set, K.le x y := fun x hx => by
    obtain ⟨y, hy⟩ := (TSet.single a).ne
    exact ⟨y, hy, (hD.1 x hx y hy).le⟩
  have hdM : M.InStratum D :=
    BoLo.inStratum_comp (BoLo.compS_hC D) hM
      (fun m ψ e => CellUT.InStratum.mono hdown (hout m ψ e))
      (ResUT.inStratum_single l ((CellUT.inStratum_mutOf D (TSet.single a) v ρv h P hw).mpr hD.1))
  have hd' : ρ'.InStratum D := ResUT.updV_inStratum hdM hu
  have hρ'l : ρ'.get l ≠ none := by
    intro hnone
    have hcon := ResUT.flat_inStratum_at hσ' hD hd'
      (fun φ e => absurd (hnone ▸ e) (by simp)) hflat
    rw [CellUT.inStratum_mutOf] at hcon
    obtain ⟨y, hy⟩ := (TSet.single a).ne
    exact Cactus.lt_irrefl _ _ (hcon y hy y hy)
  obtain ⟨φ, hφ⟩ : ∃ φ, ρ'.get l = some φ := by
    cases hg : ρ'.get l with
    | none => exact absurd hg hρ'l
    | some φ => exact ⟨φ, rfl⟩
  obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResUT.Flat.get hσ' hφ
  rw [hflat] at hχ₀
  obtain rfl : χ₀ = CellUT.mutOf (TSet.single a) v' χ h' P hw' := (Option.some.inj hχ₀).symm
  have hkφ : φ.kind ≠ Kind.imm := by
    rw [← hk₀, CellUT.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hgg : σ'.get l = some φ := ResUT.flat_get_of_ne_imm hσ' hφ hkφ
  rw [hflat] at hgg
  obtain rfl : φ = CellUT.mutOf (TSet.single a) v' χ h' P hw' := (Option.some.inj hgg).symm
  exact ⟨v', χ, h', hw', ResUT.del_compS hφ⟩

end BoCa.Fig16.Tree

end
