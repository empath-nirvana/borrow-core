import Restrat.Composition
import Support.LogicalRelation.Facts
import Support.Model.Singletons

/-!
# Restrat — `𝒱⟦Mut @a T⟧` is not natural under the image action

`ℓ ↦ Mut α P̂` (row 5.31, `ptoMut`) requires the cell's stored invariant to **equal** `P̂`
(`ofS Q = P`).  A re-stratification moves a stored invariant to its image (`relS`), and the image
of `𝒱⟦T⟧_δ` is in general not `𝒱⟦T⟧_{e∘δ}`: the moved interpretation also holds at resources
whose cells sit at lifetimes `e` leaves out (the *gap* every non-identity re-stratification has
between its cut and the moved interval).

The witness (`mut_not_natural`):

* `e = Emb.shift ⊤ 1`, i.e. `n ↦ n + 1` on every lifetime but `⊤ = 0`; the gap is `{1}`;
* `T = Mut 'a (Imm 'b 1)`, `δ = ['a ↦ 3, 'b ↦ 1]`, so `e∘δ = ['a ↦ 4, 'b ↦ 2]`;
* `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)`.

Then `𝒱⟦T⟧_δ(ℓ)(ρ₀)` holds, and `𝒱⟦T⟧_{e∘δ}(ℓ)(e·ρ₀)` does not: the moved cell stores the image
of `𝒱⟦Imm 'b 1⟧_δ`, which is false at `ℓ′ ↦ imm({1}, (), ∅)` (lifetime `1` is in no image), while
`𝒱⟦Imm 'b 1⟧_{e∘δ}` holds there (`2 ⊑ 1`).

What it shows: under the action that moves every cell, the type interpretation at a `Mut` type
whose payload mentions a moved lifetime is not invariant.  What repairs it: not moving such a
cell.  `Restrat.Fixed` shows that every cell in `Res_c` is fixed, so a resource whose `mut`
cells all lie above the cut is unaffected; D14.4's `Freeze` turns every internal `mut` cell into
an `own` cell before the move, and the re-lend at resume builds the cell afresh with
`𝒱⟦T⟧_{δ′}` (`Restrat.Segment`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Restrat.MutCounterexample
open BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel
open BoCa.Lifetime (LSub LifeVar)

/-- The re-stratification: `n ↦ n + 1` below `⊤`. -/
abbrev e : Emb (⊤ : Life) := Emb.shift ⊤ 1

theorem e_toNat (n : ℕ) : e.toNat n = if n ≤ 0 then n else n + 1 := rfl

/-- The gap: lifetime `1` is in no image. -/
theorem gap (x : Life) : e x ≠ OrderDual.toDual 1 := by
  intro h
  have := congrArg OrderDual.ofDual h
  change Emb.shiftN 0 1 (OrderDual.ofDual x) = 1 at this
  unfold Emb.shiftN at this
  split_ifs at this <;> omega

/-- `Mut 'a (Imm 'b 1)`. -/
def T : BoCa.Ty := .mut (.var 0) (.imm (.var 1) .unit)
/-- `Imm 'b 1`. -/
def S : BoCa.Ty := .imm (.var 1) .unit

/-- `['a ↦ 3, 'b ↦ 1]`. -/
def δ : LSub := ⟨[(0, 3), (1, 1)]⟩

def L (n : ℕ) : Life := OrderDual.toDual n

theorem L_le {m n : ℕ} (h : n ≤ m) : L m ≤ L n := h
theorem L_lt {m n : ℕ} (h : n < m) : L m < L n := h

/-- `ℓ′ ↦ imm({n}, (), ∅)`. -/
def immCell (n : ℕ) : CellU BoCa.Loc BoCa.Val :=
  CellU.immOf (LSet.singleton (L n)) .unit PMap.empty (ResU.inStratum_empty _)

def ℓ : BoCa.Loc := 0
def ℓ' : BoCa.Loc := 1

/-- `𝒱⟦Imm 'b 1⟧_θ(ℓ′)` at a single `imm` cell, whenever `θ('b) ⊑ {n}`. -/
theorem vS_holds {θ : LSub} {m n : ℕ} (hb : θ.find? 1 = some m) (hnm : n ≤ m) :
    vDen S θ (.loc ℓ') (ResU.single ℓ' (immCell n)) := by
  refine ⟨L m, hb, ℓ', pure_sep_mk rfl ?_⟩
  exact ⟨LSet.singleton (L n), .unit, PMap.empty, ResU.inStratum_empty _, rfl, ⟨rfl, rfl⟩,
    L_le hnm⟩

/-- Every resource `𝒱⟦Imm 'b 1⟧_δ` holds at lies in `Res_2`. -/
theorem vS_supported (w : BoCa.Val) (r : WRes) (h : vDen S δ w r) :
    r.InStratum (L 2) := by
  obtain ⟨α, hα, ℓ₀, hk⟩ := h
  have hα' : α = L 1 := Option.some.inj hα.symm
  obtain ⟨-, s, u, σ, hσ, rfl, -, hle⟩ := pure_sep_iff.mp hk
  refine ResU.inStratum_single _ ?_
  show L 2 < s.meet
  rw [hα'] at hle
  exact lt_of_lt_of_le (L_lt (by norm_num)) hle

/-- The stored invariant. -/
def Q : BoCa.Val → SPropS BoCa.Loc BoCa.Val (L 2) := fun v => SPropU.toS (L 2) (vDen S δ v)

theorem ofS_Q : ofS Q = vDen S δ := by
  funext v r
  apply propext
  constructor
  · rintro ⟨_, hS⟩; exact hS
  · intro hS; exact ⟨vS_supported v r hS, hS⟩

theorem σ_in : (ResU.single ℓ' (immCell 1) : WRes).InStratum (L 2) :=
  ResU.inStratum_single _ (show L 2 < L 1 from L_lt (by norm_num))

theorem hw : Q (.loc ℓ') ⟨ResU.single ℓ' (immCell 1), σ_in⟩ :=
  vS_holds (θ := δ) (m := 1) rfl le_rfl

/-- `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), Q)`. -/
def ρ₀ : WRes :=
  ResU.single ℓ (CellU.mutOf (L 2) (.loc ℓ') (ResU.single ℓ' (immCell 1)) σ_in Q hw)

/-- `𝒱⟦Mut 'a (Imm 'b 1)⟧_δ(ℓ)(ρ₀)`. -/
theorem holds : vDen T δ (.loc ℓ) ρ₀ := by
  refine ⟨L 3, rfl, ℓ, pure_sep_mk rfl ?_⟩
  exact ⟨L 2, .loc ℓ', _, σ_in, Q, hw, L_le (by norm_num), rfl, ofS_Q⟩

/-- …and `𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}(ℓ)(e·ρ₀)` fails. -/
theorem fails : ¬ vDen T (LSub.mapN e.toNat δ) (.loc ℓ) (e.relRU ρ₀) := by
  rintro ⟨α, hα, ℓ₀, hk⟩
  obtain ⟨hl, b, v, σ, hσ, Q', hw', -, hρ, hQ'⟩ := pure_sep_iff.mp hk
  have hl' : ℓ₀ = ℓ := by cases hl; rfl
  subst hl'
  -- the moved cell, read off the singleton
  have hget := congrArg (fun r => PMap.get r ℓ) hρ
  simp only [ρ₀, e.relRU_single, ResU.single_get_self, Option.some.injEq,
    e.relU_mutOf] at hget
  have hb : e (L 2) = b := CellU.mutOf_at hget
  subst hb
  obtain ⟨-, -, hQQ⟩ := CellU.mutOf_inj hget
  -- the moved invariant is the image of `𝒱⟦Imm 'b 1⟧_δ`
  have himg : vDen S (LSub.mapN e.toNat δ) = e.relW (vDen S δ) := by
    calc vDen S (LSub.mapN e.toNat δ) = ofS Q' := hQ'.symm
      _ = ofS (e.relS (L 2) Q) := by rw [hQQ]
      _ = e.relW (ofS Q) := e.ofS_relS _ _
      _ = e.relW (vDen S δ) := by rw [ofS_Q]
  -- `𝒱⟦Imm 'b 1⟧_{e∘δ}` holds at an `imm` cell in the gap
  have hgap : vDen S (LSub.mapN e.toNat δ) (.loc ℓ') (ResU.single ℓ' (immCell 1)) :=
    vS_holds (m := 2) rfl (by norm_num)
  rw [himg] at hgap
  obtain ⟨r₀, hr₀, -⟩ := hgap
  have hc := congrArg (fun r => PMap.get r ℓ') hr₀
  simp only [ResU.single_get_self, Emb.relRU_get] at hc
  obtain ⟨ψ, -, hψ⟩ := Option.map_eq_some_iff.mp hc
  have hat := congrArg CellU.at hψ
  rw [Emb.at_relU] at hat
  exact gap _ hat

/-- **Not natural**: `𝒱⟦Mut 'a (Imm 'b 1)⟧` holds at `(δ, ρ₀)` and fails at `(e∘δ, e·ρ₀)`. -/
theorem mut_not_natural :
    vDen T δ (.loc ℓ) ρ₀ ∧ ¬ vDen T (LSub.mapN e.toNat δ) (.loc ℓ) (e.relRU ρ₀) :=
  ⟨holds, fails⟩

end Restrat.MutCounterexample
