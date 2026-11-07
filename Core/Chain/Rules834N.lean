import Core.Chain.TyEq834N
import Core.Alpha
import Core.Compat

/-!
# The rules L1 and L2 make mechanical, at `SemJN₀`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §3. Each rule's chain proof is Core's compatibility lemma
(`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/Integers.lean`, `Core/Alpha.lean`,
`Core/Fundamental.lean`), line by line, against the interface of `Core/Chain/Iface834N.lean` and
`Core/Chain/TyEq834N.lean`: `gDenC_split ↦ gN_split₀`/`gN_splitC₀`, `wpTS_bind_frame ↦
erwp_bind_frame`, `cC_bind ↦ cN_bind₀`, `gDenC_local ↦ gN_extR₀`, `cC_tyEq ↦ cN_tyEq₀`.

The chain's judgment carries a world, a view consistent with the resource and a step index
(`SemJN₀`'s `Θ`, `c`, `n`); Core's has none. They enter at the same places in every rule:
* a premise is read at the view, which a context split's part is consistent with where the
  resource is valid (`gN_splitC₀`): at `F`/`F_Σ` by `erwp_of_valid`, elsewhere by `cN_of_valid₀`,
  at every conclusion;
* a premise read after a run is read at the index the run leaves (`gN_le₀`, `vN_le₀`);
* a thunk moves its context along `ExtR` to the world it is forced at (`gN_extR₀`), as Core's
  `gDenC_local`; `⊸` is a plain wand and moves nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

private theorem substAll_cons₂ (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

private theorem substAll_forceE {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v)
    (C : CTy) : substAll γ (forceE C (.var i)) = forceE C (.val v) := by
  cases C with
  | ret A =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | eff n j q A B C =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | _ => exact substAll_var_some hv

/-! ### The context relation at a slot -/

/-- A live slot's liveness bit turned off keeps `LiveWithin`. -/
theorem liveWithin_dead {A : VTy} {Γ : Ctx VTy} {γ : List Val}
    (h : Ctx.LiveWithin (⟨A, true⟩ :: Γ) γ) : Ctx.LiveWithin (⟨A, false⟩ :: Γ) γ := by
  cases γ with
  | nil => exact absurd h.1 (by simp)
  | cons _ _ => exact h

/-! ### Values -/

/-! ### Computations -/

/-! ### Eliminations of values into computations -/

/-! ### `!` and `[@a]` -/

/-! ### Literals and host operations -/

/-! ### Call-by-value application -/

/-! ### `∀E` and `[α]` (L2) -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
