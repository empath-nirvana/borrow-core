import Spike743.Natural

/-!
# Spike743 — round P2: an arising configuration at which `LifeNatural`'s conclusion fails

`LifeNatural` asks for the shifted computation at any split `ρ = ρr ● ρv` of the configuration's
share, `ρv` the resource of *some* value `w : W` read at `δ`. Nothing ties `W` to the context
`Γ` the computation reads its environment at. So a view cell the computation reads at the moved
variable `'x` may be the resource of `w` at a type `W` that reads it at an unmoved variable
`'c`. Then `ρv' = ρv` is admitted (`W` does not mention `'x`), and the conclusion asks the
computation to read the old cell at the moved lifetime.

The configuration (`k2_arising`):

* `Δ = ∅`; `x : Mut 'x 1 ⊢ return x : F (Mut 'x 1)`, closed by `x := ℓ`;
* `δ₀ = ['x ↦ 2, 'c ↦ 2]`, the share `ℓ ↦ mut(2, (), ∅, 𝒱⟦1⟧)`, the list `[]`;
* the world: `alloc ℓ`, then `mutFold` at `2` (`TW.alloc`, `TW.mutFold`).

The instance (`k2_hyps`): `δ₁ = ['x ↦ 1, 'c ↦ 2]` (only `'x` moves, to a longer-lived
lifetime), `ls' = []`, `ρr = ∅`, `W = Mut 'c 1`, `w = ℓ`, `ρv = ρv'` the share. Every hypothesis
of `LifeNatural` holds; the conclusion `return ℓ ∈ 𝒞⟦F (Mut 'x 1)⟧(δ₁)` at the share does not
(`k2_fails`): the cell is at `2`, and `Mut` at `1` needs a cell at a lifetime `⊒ 1`.

So `¬ LifeNatural` (`not_lifeNatural`). The intended use (`relend_of_natural`) has `W = Mut 'x T`,
the moved variable's own view; `LifeNaturalV` below restates the principle with the view tied to
the context, separately.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.NaturalK2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Spike743.Natural

/-- Semantic lifetimes: `L n` is shorter-lived as `n` grows; `L 0 = ⊤`. -/
def L (n : ℕ) : Life := OrderDual.toDual n

/-- The view's location. -/
def ℓ : Loc := 0

/-- `['x ↦ 2, 'c ↦ 2]`, `'x = 0`, `'c = 1`. -/
def δ₀ : LSub := ⟨[(0, 2), (1, 2)]⟩
/-- `['x ↦ 1, 'c ↦ 2]`: `'x` moved. -/
def δ₁ : LSub := ⟨[(0, 1), (1, 2)]⟩

/-- The computation's type `F (Mut 'x 1)`. -/
abbrev A : VTy := .mut (.var 0) .unit
/-- The view's type in the split: `Mut 'c 1`. -/
abbrev W : VTy := .mut (.var 1) .unit

/-- The share: `ℓ ↦ mut(2, (), ∅, 𝒱⟦1⟧)`. -/
abbrev ρα : WRes := innerView ℓ (L 2)

theorem δ₀_x : δ₀.find? 0 = some (L 2) := rfl
theorem δ₀_c : δ₀.find? 1 = some (L 2) := rfl
theorem δ₁_x : δ₁.find? 0 = some (L 1) := rfl
theorem δ₁_c : δ₁.find? 1 = some (L 2) := rfl

/-- `𝒱⟦Mut 'y 1⟧(ls)δ(ℓ)` at the share whenever `δ('y) = 2`. -/
theorem vC_view {y : LifeVar} {δ : LSub} (hy : δ.find? y = some (L 2)) (ls : List SRec) :
    vC true (.mut (.var y) .unit) ls δ (.loc ℓ) ρα := by
  refine ⟨L 2, ?_, ℓ, pure_sep_mk rfl (innerView_ptoMutS ℓ (L 2) ls δ)⟩
  rw [Lifetime.Life.interp_var, hy]; rfl

/-- The share is a valid resource, `#` the empty frame. -/
theorem hash_ρα : ResU.Hash (PMap.empty : WRes) ρα :=
  ResU.six23 (hstr := ResU.inStratum_empty (L 2)) (P := unitQ (L 2)) (hw := unitQ_holds (L 2))
    (ResU.comp_empty_left _)
    ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), _, ResU.comp_empty_left _,
      ResU.valid_single_own ℓ Val.unit⟩

/-- **The world**: `alloc ℓ`, then `mutFold` at `2`. -/
theorem tw_ρα : TW ρα [] [] := by
  obtain ⟨x₁, σ₁, hx₁, -, hσ₁, hT₁, -, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (ρ := PMap.empty) (ps := []) (rs := []) (l := ℓ) Val.unit
      Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty Fig16.BoLo.lower_empty rfl
  obtain rfl := ResU.eq_of_comp_empty_left hx₁
  obtain rfl := ResU.eq_of_comp_empty_left hσ₁
  exact TW.mutFold (hstr := ResU.inStratum_empty (L 2)) (P := unitQ (L 2))
    (hw := unitQ_holds (L 2)) hT₁ (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (ResU.comp_empty_right _) (hash_valid hash_ρα).2

theorem worldArises_ρα : WorldArises [] ρα :=
  ⟨PMap.empty, ρα, [], hash_ρα, ResU.comp_empty_left _, tw_ρα, fun _ h => absurd h (by simp)⟩

/-- `return x` at `x : Mut 'x 1`. -/
theorem deriv : CDerivesP (⟨[]⟩ : LifeCtx) [⟨A, true⟩] (.var 0) (.comp (.ret A)) :=
  .ret (.var (.here .nil))

theorem models_empty (δ : LSub) : (⟨[]⟩ : LifeCtx).Models δ := by
  intro x u h
  simp [LifeCtx.find?, Lifetime.assocFind] at h

theorem subst_var0 : substAll [Val.loc ℓ] (.var 0) = .val (Val.loc ℓ) := by
  show Expr.psub 0 [Val.loc ℓ] (.var 0) = _
  rw [Expr.psub_cons 0 (Val.loc ℓ) [] _, Val.shift_zero, BoCa.Adequacy.psub_nil]
  rfl

/-- **Arising**: the typed segment `return x`, closed by first-order data, at `δ₀`, with the
share in `𝒢⟦x : Mut 'x 1⟧` and part of a tagged typed world. -/
theorem k2_arising :
    Arising ⟨[]⟩ [⟨A, true⟩] (.var 0) (.ret A) [Val.loc ℓ] δ₀ [] ρα :=
  ⟨deriv, .cons (.data .loc) .nil, models_empty δ₀,
    gDenC_mk (by simp [Ctx.LiveWithin])
      ⟨ρα, PMap.empty, ResU.comp_empty_right _, vC_view δ₀_x [], rfl, trivial⟩,
    worldArises_ρα⟩

/-- Only `'x` moves, from `2` to `1`; the rest `∅` is in every stratum, and the lists are
empty. -/
theorem k2_shift : RegionShift δ₀ δ₁ [] [] PMap.empty := by
  intro y hy
  by_cases h : y = 0
  · subst h
    exact ⟨L 2, L 1, rfl, rfl, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp),
      ResU.inStratum_empty _, ResU.inStratum_empty _⟩
  · exfalso; apply hy
    simp [δ₀, δ₁, LSub.find?, Lifetime.assocFind, Ne.symm h]

/-- **Every hypothesis of `LifeNatural`** at the configuration, with `W = Mut 'c 1`. -/
theorem k2_hyps :
    Arising ⟨[]⟩ [⟨A, true⟩] (.var 0) (.ret A) [Val.loc ℓ] δ₀ [] ρα ∧
    (⟨[]⟩ : LifeCtx).Models δ₁ ∧ RegionShift δ₀ δ₁ [] [] PMap.empty ∧
    Ext [] [] PMap.empty ∧ ResU.CompS PMap.empty ρα ρα ∧ ResU.CompS PMap.empty ρα ρα ∧
    SameMemory ρα ρα ∧ vC true W [] δ₀ (.loc ℓ) ρα ∧ vC true W [] δ₁ (.loc ℓ) ρα ∧
    cC (ℍ := ℍ) (.ret A) [] δ₀ (substAll [Val.loc ℓ] (.var 0)) ρα :=
  ⟨k2_arising, models_empty δ₁, k2_shift, ext_refl [] _, ResU.comp_empty_left _,
    ResU.comp_empty_left _, fun _ => Iff.rfl, vC_view δ₀_c [], vC_view δ₁_c [],
    by rw [subst_var0]; exact wpTS_val [] _ _ ρα (vC_view δ₀_x [])⟩

/-- **The conclusion fails**: `return ℓ` is not in `𝒞⟦F (Mut 'x 1)⟧([])(δ₁)` at the share. A run
from a value takes no step; its post-share is the cell at `ℓ` (`↭` keeps a `mut` cell's
lifetime), at `2`, and `Mut` at `δ₁('x) = 1` needs a cell at a lifetime `⊒ 1`. -/
theorem k2_fails : ¬ cC (ℍ := ℍ) (.ret A) [] δ₁ (substAll [Val.loc ℓ] (.var 0)) ρα := by
  rw [subst_var0]
  intro h
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, -, -, -, -, -, ⟨k', hrun⟩, hcπ, hupd,
    -, -, -, -, -, hQ⟩ :=
    h PMap.empty ρα [] hash_ρα (ResU.comp_empty_left _) tw_ρα (fun _ h => absurd h (by simp))
      BoCa.BoLo.Alloc.leastFree 0
  have hv : v = Val.loc ℓ := Val.ext (by simpa using arun_val hrun)
  subst hv
  obtain ⟨α, hα, ℓ₀, hs⟩ := hQ
  rw [Lifetime.Life.interp_var, δ₁_x] at hα
  obtain rfl : L 1 = α := Option.some.inj hα
  obtain ⟨hl, b, u, σ, hσ, Q, hw, ls₀, hle, rfl, -, -, -⟩ := pure_sep_iff.mp hs
  have hℓ : ℓ₀ = ℓ := by cases hl; rfl
  -- the post-share's cell sits in `π`, and so in a flattening of it
  have hk : (CellU.mutOf b u σ hσ Q hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hπ := (ResU.CompS.get_left_of_ne_imm hcπ (ResU.single_get_self _ _) hk).2
  obtain ⟨τ, hτ⟩ := hupd.2.2
  -- `↭` gives a `mut` cell at `b` in a flattening of the share
  obtain ⟨u₀, χ, hχ, hw₀, τ₀, hτ₀, hg₀⟩ :=
    (hupd.1.2 ℓ₀ b Q).mpr ⟨u, σ, hσ, hw, τ, hτ, ResU.flat_get_of_ne_imm hτ hπ hk⟩
  subst hℓ
  have hcell := ResU.flat_get_of_ne_imm hτ₀ (ResU.single_get_self ℓ _)
    (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)
  rw [hg₀] at hcell
  have hb : b = L 2 := CellU.mutOf_at (Option.some.inj hcell)
  subst hb
  exact absurd (show (2 : ℕ) ≤ 1 from hle) (by omega)

/-- **`LifeNatural`, as round P states it, does not hold.** -/
theorem not_lifeNatural : ¬ LifeNatural (ℍ := ℍ) := by
  intro hN
  obtain ⟨hA, hδ', hsh, hext, hc, hc', hm, hv, hv', h⟩ := k2_hyps (ℍ := ℍ)
  exact k2_fails (hN _ _ _ _ _ δ₀ δ₁ [] [] W (.loc ℓ) PMap.empty ρα ρα ρα ρα hA hδ' hsh hext hc
    hc' hm hv hv' h)

end Spike743.NaturalK2

end
