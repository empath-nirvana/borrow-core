import Outlives.Judgment

/-!
# Outlives — where `⊑` is not admissible, as Lean configurations

**1. The borrow rules of the outlives judgment, under `[]I`.** `[]I` asks every live slot of the
context to outlive `@a`, and its soundness reads that through 6.60 as membership of the slot's
resource in `Res_α` (`gSepC_outlives`, `boxI_compatX`). With the `Mut` rule non-strict,
`m : Mut 'x 1` outlives `'x`. `borrow_cell` builds the value of `Mut 'x 1` at `δ('x) = α`: a
single `mut` cell at `α`. It is in the relation, it is in every stratum strictly below `α`, and it
is not in `Res_α`, so 6.60 fails at `VOutLe` (`not_vC_outlives_le`). This is the exact case
`logState_not_outlives` (`Core/AffPrograms.lean`) refuses syntactically: a closure capturing
`Mut 'x T` is not boxed at `'x`.

The same configuration answers the callback's result box. `withbor`'s callback returns `['x] B`;
its resource must be in `Res_α`, which excludes exactly the borrow's own cell. A non-strict box
there (`@ρ ⊒ α`, `OutlivesLe`) admits that cell (`borrow_cell`'s second conjunct): the result
would be allowed to hold the borrow the scope is about to end.

**2. The strata.** `[α]` is membership in `Res_α`, and `Cell_α`'s `mut` cells are at lifetimes
`β ⊐ α` (`MutF.hβ`), holding a predicate over `Res_β`. That strictness is what makes the
recursion defining `Cell` well founded. With `β ⊒ α`, a cell at `β = α` would hold a predicate
over `Res_α = Loc ⇀ Cell_α` itself, so `Cell_α` would contain `MutSelf (Cell_α)` through the
`mut` constructor. No type does (`no_nonstrict_stratum`, by Cantor's theorem). So the box
modality cannot be made non-strict by relaxing the strata; a non-strict box is the different
predicate `OutlivesLe`, definable on the union of the strata, not a stratum.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Outlives
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### 1. A borrow at `α` is not in `Res_α` -/

/-- `δ = ['x ↦ 1]`, with `'x` the variable `0`. -/
def δx : LSub := ⟨[(0, 1)]⟩

theorem δx_models : Δ₁.Models δx := by
  intro x u e
  match x with
  | 0 => cases e; exact ⟨1, 0, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
  | (k+1) => exact absurd e (by simp [Δ₁, LifeCtx.extend, LifeCtx.find?, Lifetime.assocFind, LifeCtx.empty])

/-- The lifetime `δx` gives `'x`. -/
abbrev αx : Life := (1 : ℕ)

theorem interp_x : (Lifetime.Life.var 0).interp δx = some αx := rfl

/-- **The borrow's own cell.**  `m : Mut 'x 1` at `δ('x) = α` is a `mut` cell at `α`: it is in
the relation, it lies in every stratum strictly below `α`, and it is not in `Res_α`. -/
theorem borrow_cell (ℓ : BoCa.Loc) :
    ∃ ρ : WRes, vC true (.mut (.var 0) .unit) [] δx (.loc ℓ) ρ ∧ OutlivesLe ρ αx ∧
      ¬ BoLo.Outlives ρ αx := by
  have hunif : ∀ ls' u' σ', vC true VTy.unit ls' δx u' σ' → σ'.InStratum αx := by
    rintro ls' u' σ' ⟨rfl, -⟩
    exact ResU.inStratum_empty αx
  set Q : Val → SPropS BoCa.Loc BoCa.Val αx :=
    fun w r => vC true VTy.unit [] δx w r.1 with hQdef
  have hQ : BoLo.ofS Q = fun w => vC true VTy.unit [] δx w := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hunif [] w σ h, h⟩⟩
  have hv : vC true VTy.unit [] δx Val.unit (PMap.empty : WRes) := ⟨rfl, rfl⟩
  obtain ⟨hw, hpto⟩ := ptoMutX_create (l := ℓ) (α := αx) (b := αx) (ls := []) (S := .unit)
    (δ := δx) (Q := Q) le_rfl hQ (fun _ h => absurd h (List.not_mem_nil)) hunif
    (ResU.inStratum_empty αx) hv
  refine ⟨_, ⟨αx, interp_x, ℓ, pure_sep_mk rfl hpto⟩, ?_, ?_⟩
  · intro γ hγ
    exact ResU.inStratum_single ℓ
      (show (CellU.mutOf αx Val.unit PMap.empty (ResU.inStratum_empty αx) Q hw).InStratum γ
        from hγ)
  · intro h
    have := h ℓ _ (ResU.single_get_self ℓ _)
    exact lt_irrefl αx this

/-- `Mut 'x 1 ⊒ 'x` at the fully relaxed judgment. -/
theorem mut_outLe : VOutLe Δ₁ (.var 0) (.mut (.var 0) .unit) :=
  .mut (entailsLe_refl (LifeCtx.defines_of_wf rfl))

/-- **6.60 fails at the fully relaxed judgment**: there is a lifetime context, a substitution
modelling it, a type outliving `@a` with the borrow rules non-strict, and a value of that type
whose resource is not in `Res_{@aδ}`. -/
theorem not_vC_outlives_le :
    ¬ ∀ (Δ : LifeCtx) (δ : LSub) (a : Lifetime.Life) (α : Life) (T : VTy),
        Δ.Models δ → a.interp δ = some α → VOutLe Δ a T →
        ∀ ls v (ρ : WRes), vC true T ls δ v ρ → BoLo.Outlives ρ α := by
  intro h
  obtain ⟨ρ, hv, -, hno⟩ := borrow_cell 0
  exact hno (h Δ₁ δx (.var 0) αx _ δx_models interp_x mut_outLe [] _ ρ hv)

/-! ### 2. The strata cannot be non-strict -/

/-- A `mut` cell of a stratum whose predicate ranges over that same stratum: `Mut_α` at
`β = α`, over a carrier `C` for `Cell_α`. -/
structure MutSelf (C : Type) where
  v : Val
  ρ : PMap BoCa.Loc C
  P : Val → PMap BoCa.Loc C → Prop
  hw : P v ρ

open Classical in
/-- `ℓ ↦ c`. -/
def pSingle {C : Type} (l : BoCa.Loc) (c : C) : PMap BoCa.Loc C where
  get := fun l' => if l' = l then some c else none
  finite := by
    refine ⟨[l], fun l' h => ?_⟩
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h

theorem pSingle_get {C : Type} (l : BoCa.Loc) (c : C) : (pSingle l c).get l = some c := by
  classical
  simp [pSingle]

/-- **No stratum contains its own `mut` cells.**  No type `C` carries an injection
`MutSelf C → C`: a set `S ⊆ C` is coded as the cell `mut((), ∅, P_S)` with
`P_S w r ≜ w = () ∨ ∃ c, r(0) = c ∧ c ∈ S`, which determines `S`, contradicting Cantor's
theorem. -/
theorem no_nonstrict_stratum (C : Type) (f : MutSelf C → C) : ¬ Function.Injective f := by
  intro hf
  let P : Set C → Val → PMap BoCa.Loc C → Prop :=
    fun S w r => w = Val.unit ∨ ∃ c, r.get 0 = some c ∧ c ∈ S
  let g : Set C → C := fun S => f ⟨Val.unit, PMap.empty, P S, Or.inl rfl⟩
  refine Function.cantor_injective g fun S T hST => ?_
  have hP : P S = P T := congrArg MutSelf.P (hf hST)
  ext c
  have key : ∀ U : Set C, P U (Val.loc 0) (pSingle 0 c) ↔ c ∈ U := by
    intro U
    constructor
    · rintro (h | ⟨c', hc', hU⟩)
      · cases h
      · rw [pSingle_get] at hc'; cases Option.some.inj hc'; exact hU
    · intro h; exact Or.inr ⟨c, pSingle_get 0 c, h⟩
  rw [← key S, ← key T, hP]

end BoCa.Fig16.LogRel.Core.Outlives

end
