import Core.Chain.RelBase791N
import Core.Chain.SI.CaptureScopeM

/-!
# Core's `Ext` read literally on the per-lend world breaks `vN_extA₀` at `U`  `[spec §62]`

`docs/new-core/chain-interpretation.md` §5, D4. `LocTy.ExtR Θ Θ′ ρ` asks that nothing be added above a
lifetime `a` only where `a` is a key of `Θ` with `CellIn ρ a`. Core's `Ext ls ls′ ρ`
(`Core/FrameRecords.lean`) asks it above every `b` with `CellIn ρ b`. Read that way on the world
(`ExtRL`), `U` is not Kripke along `ExtA`.

The configuration. The type `U(Mut 'x 1 ⊸ F 1)` at `'x ↦ α`, the thunk `()`; the thunk's resource
`ρ_b = m ↦ mut(b, (), ∅, ⊤)` with `b < α`, so `CellIn ρ_b b`. Applied, `()` is stuck, so the
thunk is valid exactly where no `Mut @α 1` argument exists. From the empty world every literal
extension keeps nothing above `b`, so none has a key at `α`, and the thunk is valid there
(`valid_at_empty`). The world `∅ + (ℓ′, α) ↦ 𝒱⟦1⟧` is an `ExtA` extension of the empty one; it
holds the argument `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and the thunk is not valid there
(`not_valid_at_lend`): the run of `() ℓ′` from the typed world of the two cells (`world_two`)
is stuck at its first configuration.

`vUgen E` is `vN₀`'s `U` clause, reading the order `E`, followed by `cN₀`'s `⊸` clause at this type,
a plain wand at the world `U` reached; at `E = LocTy.ExtR` it is `vN₀` itself (`vN_eq_vUgen`). The `Mut` and `F` clauses do not
read the order, so `vUgen ExtRL` is the literal reading's `𝒱⟦U(Mut 'x 1 ⊸ F 1)⟧`.
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

/-- `Mut 'x 1 ⊸ F 1`. -/
def tyC (x : LifeVar) : CTy := .arr (.mut (.var x) .unit) (.ret .unit)

/-- The thunk's resource: one `mut` cell at `b`. -/
def ρb (m : Loc) (b : Life) : WRes :=
  ResU.single m (CellU.mutOf b Val.unit PMap.empty (ResU.inStratum_empty b)
    (fun _ _ => True) trivial)

theorem cellIn_ρb (m : Loc) (b : Life) : CellIn (ρb m b) b := by
  have h := CellIn.single (l := m) (ψ := CellU.mutOf b Val.unit PMap.empty
    (ResU.inStratum_empty b) (fun _ _ => True) trivial)
    (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)
  rwa [CellU.at_mutOf] at h

/-- **The typed world of two `mut` cells**: `m ↦ mut(b, (), ∅, P)` beside
`ℓ′ ↦ mut(α, (), ∅, P′)`, entered as two allocations and two `mut` lends (`TWNC.alloc`,
`capture_worldM`), at the empty frame, with a memory. -/
theorem world_two {m l' : Loc} (hml : l' ≠ m) {b α : Life} (P : Val → SPropS Loc Val b)
    (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty b⟩) (P' : Val → SPropS Loc Val α)
    (hw' : P' Val.unit ⟨PMap.empty, ResU.inStratum_empty α⟩) {ρ' : WRes}
    (hρ' : ResU.CompS (ResU.single m (CellU.mutOf b Val.unit PMap.empty (ResU.inStratum_empty b) P hw))
      (ResU.single l' (CellU.mutOf α Val.unit PMap.empty (ResU.inStratum_empty α) P' hw')) ρ') :
    ∃ μ, ResU.Hash PMap.empty ρ' ∧ TWNC ρ' [] (rsOf []) ∧ Tagged ρ' [] [] ∧ ResU.Lower ρ' μ ∧
      FinDom μ := by
  let om : WRes := ResU.single m (CellU.ownOf Val.unit)
  let ol : WRes := ResU.single l' (CellU.ownOf Val.unit)
  have htg₀ : ∀ W : WRes, Tagged W [] [] := fun _ x hx => absurd hx (by simp)
  have hT₁ : TWNC om [] (rsOf []) :=
    TWNC.alloc TWNC.empty Fig16.BoLo.lower_empty rfl (compS_empty_left _)
      (ResU.valid_single_own m Val.unit)
  have hl₁ : ResU.Lower om (BoCa.BoLo.Heap.upd (fun _ => none) m Val.unit) :=
    lower_compS_own (compS_empty_left _) Fig16.BoLo.lower_empty rfl
  have hμl : BoCa.BoLo.Heap.upd (fun _ => none) m Val.unit l' = none := by
    simp [BoCa.BoLo.Heap.upd, hml]
  obtain ⟨W₂, hW₂⟩ := (ResU.compS_defined_iff om ol).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hml))
  obtain ⟨σ₂, hσ₂, hH₂, hl₂⟩ := hash_compS_own (compS_empty_left om) hl₁ hμl hW₂
  obtain rfl := eq_of_compS_empty_left hσ₂
  have hT₂ : TWNC σ₂ [] (rsOf []) := TWNC.alloc hT₁ hl₁ hμl hW₂ (hash_valid_comp hH₂ hσ₂)
  -- the lend at `m`
  obtain ⟨BM, fρ, hBM, hHBM, hfρ, hTfρ, -, hlfρ⟩ :=
    capture_worldM (l := m) (ResU.inStratum_empty b) hw (ResU.comp_empty_right om) hW₂ hH₂ hσ₂ hT₂
      (htg₀ _) hl₂
  obtain rfl := eq_of_compS_empty_left hfρ
  -- the lend at `ℓ′`
  obtain ⟨BM', fρ', hBM', hHBM', hfρ', hTfρ', -, hlfρ'⟩ :=
    capture_worldM (l := l') (ResU.inStratum_empty α) hw' (ResU.comp_empty_right ol) hBM hHBM hfρ
      hTfρ (htg₀ _) hlfρ
  obtain rfl := eq_of_compS_empty_left hfρ'
  obtain rfl := ResU.CompS.functional hBM' hρ'
  exact ⟨_, hHBM', hTfρ', htg₀ _, hlfρ', lower_finDom hlfρ'⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791

end
