import Core.Compatibility

/-!
# Core — the token of a declared type: `mint` and `burn`  `[spec §11, §12, §42]`

`Tok = VTy.opq .tok` is the token a declared type with no derived drop carries beside its payload
(`N = A ⊗ Tok`, SPEC §42). Its value is a location owning a unit cell, the capture cell's pattern
(SPEC §25): `Opaque.rel .tok` is `Ref 1`'s clause. Two constants handle it:

    mint : 1 ⊸ Tok      mint ≜ λx. alloc x        (`CDerivesIn.tokMint`)
    burn : Tok ⊸ 1      burn ≜ λc. free c         (`CDerivesIn.tokBurn`)

`mint` allocates the cell by the ordinary `alloc` step and `burn` frees it, so their compatibility
lemmas are `[TR]` 6.141 and 6.142 (`wpTS_alloc`, `wpTS_free`, the steps `ewp_alloc` and `ewp_free`
take at an effect row). `burn` is the only constant that takes a `Tok`.

`Tok` has no derived drop (`HasDtor` has no `opq` constructor) and is not `VTy.OwnFree`, so neither
is a type holding it; `[let]`'s `hW` and `[raise]`'s `hd` refuse to abandon one at an abort.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `Tok`, the token of a declared type.  `[spec §11]` -/
abbrev tokTy : VTy := .opq .tok

/-- `mint ≜ λx. alloc x : 1 ⊸ Tok`: a fresh unit cell.  `[spec §11, §42]` -/
def mintE : Expr := .val (.lam (.app (.val (.prim .alloc)) (.var 0)))

/-- `burn ≜ λc. free c : Tok ⊸ 1`: the cell freed.  `[spec §11, §42]` -/
def burnE : Expr := .val (.lam (.app (.val (.prim .free)) (.var 0)))

/-- `mint`'s type. -/
abbrev mintTy : VTy := .lolli .unit tokTy

/-- `burn`'s type. -/
abbrev burnTy : VTy := .lolli tokTy .unit

theorem mintE_subst (γ : List Val) (v : Val) :
    Expr.subst 0 v (Expr.psub (0 + 1) γ (.app (.val (.prim .alloc)) (.var 0))) =
      .app (.val (.prim .alloc)) (.val v) := by
  simp [Expr.subst, Expr.psub]

theorem burnE_subst (γ : List Val) (v : Val) :
    Expr.subst 0 v (Expr.psub (0 + 1) γ (.app (.val (.prim .free)) (.var 0))) =
      .app (.val (.prim .free)) (.val v) := by
  simp [Expr.subst, Expr.psub]

/-- `Tok`'s relation is `Ref 1`'s, in both modes. -/
theorem vCE_tok_eq_ref (η : Option (Nat → TEnt)) (b : Bool) (ls : List SRec) (δ : LSub) (v : Val) :
    vCE η b tokTy ls δ v = vCE η b (.ref .unit) ls δ v := rfl

/-- **`mint` is sound** (`[TR]` 6.141 at the cell): `1 ⊸ Tok`, at a dead context.  `[spec §42]` -/
theorem tokMint_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ mintE mintTy := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  refine wpTS_val ls ⟨_, .lam⟩ _ _ ?_
  intro ls' _ v ρ₁ ρ₂ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨rfl, rfl⟩ := hv
  refine wpTS_lolli ls' _ Val.unit _ _ ?_
  rw [mintE_subst]
  refine wpTS_alloc ls' Val.unit _ _ ?_
  intro ℓ σ τ hcell hc
  have hσ : σ = ResU.single ℓ (CellU.ownOf Val.unit) := hcell
  subst hσ
  have hτ := eq_of_compS_empty_left hc
  subst hτ
  exact Opaque.rel_tok_intro ℓ

/-- **`burn` is sound** (`[TR]` 6.142 at the cell): `Tok ⊸ 1`, at a dead context.
`[spec §42]` -/
theorem tokBurn_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ burnE burnTy := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  refine wpTS_val ls ⟨_, .lam⟩ _ _ ?_
  intro ls' _ v ρ₁ ρ₂ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  rcases Opaque.rel_cases hv with ⟨hk, -, -⟩ | ⟨-, ℓ, w, rfl, rfl, rfl⟩
  · exact absurd hk Opaque.tok_not_host
  refine wpTS_lolli ls' _ (Val.loc ℓ) _ _ ?_
  rw [burnE_subst]
  refine wpTS_free ls' ℓ Val.unit _ _ ?_
  exact ⟨_, _, ResU.comp_empty_right _, rfl, ⟨rfl, rfl⟩⟩

/-! ### Abstract types: the representation iso  `[spec §63]`

An abstract type `abs n rep` has its representation's relation (`Opaque.rel_abs`), so the iso
between it and `rep` is the identity on the relation: the compatibility lemmas of `absSeal` and
`absUnseal` (`Fundamental.lean`) are `id`, at every representation. Only typing tells the two
apart, where the iso is gated on the provider (`CDerivesIn`). -/

/-- An abstract type `abs n rep`, named `n` and represented by `rep`. -/
abbrev absTy (n : Nat) (rep : Opaque) : VTy := .opq (.abs n rep)

/-- `Cell`, a location owning a cell that holds an `I32`. -/
abbrev cellTy : VTy := .opq .cell

/-- The name of the abstract type `File`, provided by the platform's `with_fs` (SPEC §62, §63). -/
abbrev fileName : Nat := 0

/-- **An abstract type's relation is its representation's**, in both modes.  `[spec §63]` -/
theorem vCE_abs_eq_rep (n : Nat) (rep : Opaque) (η : Option (Nat → TEnt)) (b : Bool)
    (ls : List SRec) (δ : LSub) (v : Val) :
    vCE η b (absTy n rep) ls δ v = vCE η b (.opq rep) ls δ v := rfl

/-- **At the token representation, an abstract type's relation is `Tok`'s.**  `[spec §63]` -/
theorem vCE_abs_eq_tok (n : Nat) (η : Option (Nat → TEnt)) (b : Bool) (ls : List SRec) (δ : LSub)
    (v : Val) : vCE η b (absTy n .tok) ls δ v = vCE η b tokTy ls δ v := rfl

/-- **`Cell`'s relation is `Ref I32`'s**, in both modes: an owned cell holding a value.
`[spec §63]` -/
theorem vCE_cell_eq_ref (η : Option (Nat → TEnt)) (b : Bool) (ls : List SRec) (δ : LSub)
    (v : Val) : vCE η b cellTy ls δ v = vCE η b (.ref (.int .w32)) ls δ v := rfl

/-- **`[abs-seal]` is sound**: a `rep` is an `abs n rep`.  `[spec §63]` -/
theorem absSeal_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {n : Nat} {rep : Opaque}
    (h : SemV Δ Γ e (.opq rep)) : SemV Δ Γ e (absTy n rep) := h

/-- **`[abs-unseal]` is sound**: an `abs n rep` is a `rep`.  `[spec §63]` -/
theorem absUnseal_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {n : Nat} {rep : Opaque}
    (h : SemV Δ Γ e (absTy n rep)) : SemV Δ Γ e (.opq rep) := h

end BoCa.Fig16.LogRel.Core
