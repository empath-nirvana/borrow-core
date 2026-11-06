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
  simp only [vNE, cN, tyC, vUgen]

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

/-- **Under the literal order the thunk is not valid at the world with a lend at `α`**: that world
holds the argument `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `ν`'s clause is `False`. -/
theorem not_valid_at_lend (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) {m l' : Loc}
    (hml : l' ≠ m) (n : Nat) (v : Val) :
    ¬ vUgen (ℍ := ℍ) ExtRL x (δ.extend x α)
      (LocTy.empty.add l' α (famL α (fun Θ j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ j u r)
        LocTy.empty)) n v (ρb m b) := by
  intro h
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ j u r
  let Θ₁ := LocTy.empty.add l' α (famL α P LocTy.empty)
  have hfam : DownFam α (famL α P LocTy.empty) := vN_fam_down .unit _ α _
  have hOK : Θ₁.OK := ⟨LocTy.down_add LocTy.empty_down l' hfam,
    ⟨N, LocTy.fresh_add (N := N) (fun _ _ h => absurd rfl h) le_rfl hNα l' _⟩⟩
  have hw : famL α P LocTy.empty n Val.unit ⟨PMap.empty, ResU.inStratum_empty α⟩ := ⟨rfl, rfl⟩
  let cell : WRes := ResU.single l' (CellU.mutOf α Val.unit PMap.empty
    (ResU.inStratum_empty α) (famL α P LocTy.empty n) hw)
  have hv : vN (ℍ := ℍ) (.mut (.var x) .unit) (δ.extend x α) Θ₁ n (Val.loc l') cell :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL LocTy.empty l' α P le_rfl _ hw,
      fun _ _ _ r h => by obtain ⟨-, rfl⟩ := h; exact ResU.inStratum_empty α⟩
  obtain ⟨ρ', hρ'⟩ := (ResU.compS_defined_iff (ρb m b) cell).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hml))
  let c : Loc → Option Life := fun y => if y = m then some b else none
  let c' : Loc → Option Life := fun y => if y = m then some b else if y = l' then some α else none
  have hcb : ConsistentX c (ρb m b) :=
    consistentX_single_mut (consistentX_empty c) (by simp [c])
  have hcb' : ConsistentX c' (ρb m b) :=
    consistentX_single_mut (consistentX_empty c') (by simp [c'])
  have hcc : ConsistentX c' cell :=
    consistentX_single_mut (consistentX_empty c') (by simp [c', hml])
  have hc' : ConsistentX c' ρ' := consistentX_compS hρ' hcb' hcc
  exact h Θ₁ (extRL_refl _ _) hOK c hcb [] c' n le_rfl (Val.loc l') cell ρ' hρ' hv hc'

/-- **The literal reading of Core's `Ext` breaks `vN_extA` at `U`.** Both worlds are `OK`, the
second is an `ExtA` extension of the first (a fresh lend), and a value of
`U(Mut 'x 1 ⊸ ν(F 1))` under the literal order at the first is not one at the second. At the
interpretation's order `LocTy.ExtR`, `vN_extA` holds at every type. -/
theorem extRL_breaks_extA :
    ∃ (x : LifeVar) (δ : LSub) (Θ Θ' : LocTy) (n : Nat) (v : Val) (ρ : WRes),
      Θ.OK ∧ Θ'.OK ∧ Θ.ExtA Θ' ∧ vUgen (ℍ := ℍ) ExtRL x δ Θ n v ρ ∧
        ¬ vUgen (ℍ := ℍ) ExtRL x δ Θ' n v ρ := by
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit ((LSub.empty : LSub).extend 0 α) Θ j u r
  have hfam : DownFam α (famL α P LocTy.empty) := vN_fam_down .unit _ α _
  refine ⟨0, LSub.empty.extend 0 α, LocTy.empty, LocTy.empty.add 1 α (famL α P LocTy.empty), 1, Val.unit,
    ρb 0 b, LocTy.empty_ok, ⟨LocTy.down_add LocTy.empty_down 1 hfam,
      ⟨b, LocTy.fresh_add (N := b) (fun _ _ h => absurd rfl h) le_rfl hbα 1 _⟩⟩,
    LocTy.extA_add (fun _ _ h => absurd rfl h) 1 _, valid_at_empty 0 _ hbα 0 1 _,
    not_valid_at_lend 0 _ hbα (by decide) 1 _⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791

end
