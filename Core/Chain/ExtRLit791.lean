import Core.Chain.Goal791N

/-!
# Core's `Ext` read literally on the per-lend world breaks `vN_extA` at `U`  `[spec §62]`

`docs/new-core/chain-interpretation.md` §5, D4. `LocTy.ExtR Θ Θ′ ρ` asks that nothing be added above a
lifetime `a` only where `a` is a key of `Θ` with `CellIn ρ a`. Core's `Ext ls ls′ ρ`
(`Core/FrameRecords.lean`) asks it above every `b` with `CellIn ρ b`. Read that way on the world
(`ExtRL`), `U` is not Kripke along `ExtA`.

The configuration. The type `U(Mut 'x 1 ⊸ ν(F 1))` at `'x ↦ α`; the thunk's resource
`ρ_b = m ↦ mut(b, (), ∅, ⊤)` with `b < α`, so `CellIn ρ_b b`; `ν`'s clause is `False`, so the thunk
is valid exactly where no `Mut @α 1` argument exists. From the empty world every literal extension
keeps nothing above `b`, so none has a key at `α`, and the thunk is valid there
(`valid_at_empty`). The world `∅ + (ℓ′, α) ↦ 𝒱⟦1⟧` is an `ExtA` extension of the empty one; it
holds the argument `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and the thunk is not valid there
(`not_valid_at_lend`).

`vUgen E` is `vN`'s `U` clause, reading the order `E`, followed by `cN`'s `⊸` clause at this type,
a plain wand at the world `U` reached; at `E = LocTy.ExtR` it is `vN` itself (`vN_eq_vUgen`). The `Mut` and `ν` clauses do not
read the order, so `vUgen ExtRL` is the literal reading's `𝒱⟦U(Mut 'x 1 ⊸ ν(F 1))⟧`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeVar)

/-- **Core's `Ext` read literally on the per-lend world**: the keys at a lifetime with a borrow cell
of `ρ` no longer-lived than it are kept, and nothing is added above *every* such lifetime. -/
def ExtRL (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  (∀ l a F, Θ l a = some F → CellIn ρ a → Θ' l a = some F) ∧
    ∀ b, CellIn ρ b → Θ'.above b = Θ.above b

theorem extRL_refl (Θ : LocTy) (ρ : WRes) : ExtRL Θ Θ ρ := ⟨fun _ _ _ h _ => h, fun _ _ => rfl⟩

/-- `Mut 'x 1 ⊸ ν(F 1)`. -/
def tyC (x : LifeVar) : CTy := .arr (.mut (.var x) .unit) (.nu (.ret .unit))

/-- **`𝒱⟦U(Mut 'x 1 ⊸ ν(F 1))⟧` with the Kripke order `E`**: `vN`'s `U` clause, reading `E` where
`vN` reads `LocTy.ExtR`, then `cN`'s `⊸` clause at the world reached. -/
def vUgen (E : LocTy → LocTy → WRes → Prop) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat)
    (v : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, E Θ Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls : List SRec,
    ∀ c', ∀ k, k ≤ n → ∀ (w : Val) (ρv ρ' : WRes),
      ResU.CompS ρ ρv ρ' → vN (ℍ := ℍ) (.mut (.var x) .unit) δ Θ' k w ρv → ConsistentX c' ρ' →
        cN (ℍ := ℍ) (.nu (.ret .unit)) δ Θ' c' k ls (.app (forceE (tyC x) v.1) (.val w)) ρ'

/-- At the interpretation's own order, `vUgen` is `vN`. -/
theorem vN_eq_vUgen (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) :
    vN (ℍ := ℍ) (.thunk (tyC x)) δ Θ n v ρ ↔ vUgen (ℍ := ℍ) LocTy.ExtR x δ Θ n v ρ := by
  simp only [vN, cN, tyC, vUgen]

/-- The thunk's resource: one `mut` cell at `b`. -/
def ρb (m : Loc) (b : Life) : WRes :=
  ResU.single m (CellU.mutOf b Val.unit PMap.empty (ResU.inStratum_empty b)
    (fun _ _ => True) trivial)

theorem cellIn_ρb (m : Loc) (b : Life) : CellIn (ρb m b) b := by
  have h := CellIn.single (l := m) (ψ := CellU.mutOf b Val.unit PMap.empty
    (ResU.inStratum_empty b) (fun _ _ => True) trivial)
    (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)
  rwa [CellU.at_mutOf] at h

/-- **Under the literal order the thunk is valid at the empty world**: every literal extension
keeps nothing above `b`, so none has a key at `α > b`, and no `Mut @α 1` argument exists. -/
theorem valid_at_empty (x : LifeVar) (δ : LSub) {α b : Life} (hbα : b < α) (m : Loc) (n : Nat)
    (v : Val) : vUgen (ℍ := ℍ) ExtRL x (δ.extend x α) LocTy.empty n v (ρb m b) := by
  intro Θ' hE _ c _ ls c' k _ w ρv ρ' _ hv _
  exfalso
  obtain ⟨β, hβ, b', hβb', ⟨l', _, _, _, _, _, _, _, hl, _⟩, -⟩ := hv
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  have habove := hE.2 b (cellIn_ρb m b)
  have h := congrArg (fun Θ : LocTy => Θ l' b') habove
  simp only [LocTy.above_apply, if_pos (lt_of_lt_of_le hbα hβb'), LocTy.empty_apply] at h
  rw [h] at hl
  cases hl

end BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791

end
