import Core.Chain.ExtRLit791
import Core.Chain.ImmRec791N

/-!
# An `imm` lend's step at the per-lend world  `[spec §62]`

`docs/new-core/scope-831-map.md` §3 (risk 1). Core's `withbor1U_compatX` (`Core/EffBorrow.lean`)
runs the callback at the list with the lend's record added, along `ext_add hadd hout₂`: the
callback's resource is in the lend's stratum, and Core's `Ext` compares only the records
strictly longer-lived than each borrow cell of the resource, so a record lent below them is not
compared.

At the per-lend world the record goes into the world's `imm` records (`LocTy.addImm`), since
`vN₀`'s `Imm` clause reads its witness there (`Goal791N.ImmWitW`). `LocTy.above` is Core's `ls₀` (the
keys and the records lent strictly above the key), and `LocTy.ExtR`'s record conjunct is Core's
`Keeps` (the records relevant to the resource kept). So the world with the lend's record is an
extension at every resource in the lend's stratum (`LocTy.extR_addImm`, Core's `ext_add`), and
the world without it is one too (`LocTy.extR_of_addImm`, Core's `ext_drop`).

At the configuration the map's risk 1 was read at (an `OK` world with a `mut` key at `α`, a
callback resource holding that key's cell, `ExtRLit791.ρb`), the world with one more record lent
below `α` is an extension (`extR_addImm_inst`), and an extension of it holds an `Imm` value
(`imm_at_extension`). The argument that made `𝒱⟦U(Imm 'x A ⊸ C)⟧` admit every value at such a
resource was that no extension holds one; it does not apply.
-/

noncomputable section

open Classical

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Map831N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N (recT cellI escU escU_inStratum)
open BoCa.Lifetime (LSub LifeVar)

/-- **An `Imm` value is witnessed by a record of the world**, so the world has one. -/
theorem imm_world_ne_nil {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : Θ.imm ≠ [] := by
  obtain ⟨-, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, hw⟩ := h
  obtain ⟨x, hx, -⟩ := hw l s u σ hs rfl
  intro e
  rw [e] at hx
  exact List.not_mem_nil hx

/-- The configuration's world: `∅ + (0, α) ↦ 𝒱⟦1⟧`, `α = 1`. -/
def Θc : LocTy :=
  LocTy.empty.add 0 (OrderDual.toDual 1)
    (famL (OrderDual.toDual 1) (fun Θ j u r => vN₀ (ℍ := ℍ) .unit LSub.empty Θ j u r) LocTy.empty)

theorem Θc_ok : (Θc (ℍ := ℍ)).OK := by
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  have hfam := vN_fam_down₀ (ℍ := ℍ) .unit LSub.empty α LocTy.empty
  exact ⟨LocTy.down_add LocTy.empty_down 0 hfam,
    ⟨b, LocTy.fresh_add (N := b) (fun _ _ h => absurd rfl h) le_rfl hbα 0 _⟩⟩

/-- **Core's `ext_add` at the configuration, every hypothesis discharged**: at the callback
resource `0 ↦ mut(α, (), ∅, ⊤)`, which holds a borrow cell at the key's lifetime `α`, the world
with one more record lent at `β = 2 ⊏ α` is an extension. -/
theorem extR_addImm_inst (r : FrameRec) :
    (Θc (ℍ := ℍ)).ExtR ((Θc (ℍ := ℍ)).addImm (r, OrderDual.toDual 2))
      (ExtRLit791.ρb 0 (OrderDual.toDual 1)) := by
  refine LocTy.extR_addImm _ r (ResU.inStratum_single 0 ?_)
  rw [CellU.inStratum_mutOf]
  exact OrderDual.toDual_lt_toDual.mpr (by decide)

/-- **An extension of the configuration holds an `Imm` value**: the world with the record of
`ℓ ↦ own(loc ℓ′)` lent at `β = 2` holds `𝒱⟦Imm 'x (Ref 1)⟧` at `δ['x ↦ β]`, so the argument that
no extension at the callback's resource holds an `Imm` value fails. -/
theorem imm_at_extension (x : LifeVar) (l l' : Loc) (n : Nat) :
    ∃ Θ', (Θc (ℍ := ℍ)).ExtR Θ' (ExtRLit791.ρb 0 (OrderDual.toDual 1)) ∧
      vN₀ (ℍ := ℍ) (.imm (.var x) (.ref .unit)) (LSub.empty.extend x (OrderDual.toDual 2)) Θ' n
        (Val.loc l) (cellI (OrderDual.toDual 2) l l') := by
  let β : Life := OrderDual.toDual 2
  refine ⟨(Θc (ℍ := ℍ)).addImm (recT (.ref .unit) (LSub.empty.extend x β) l l', β),
    extR_addImm_inst _, ?_⟩
  refine ⟨β, interp_ext_self _ x β, ⟨l, LSet.singleton β, Val.loc l', escU l',
    escU_inStratum l' _, rfl, rfl, le_refl _, l', Val.unit, PMap.empty, rfl,
    ResU.comp_empty_right _, rfl, rfl⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
  obtain ⟨rfl, e'⟩ := single_immOf_inj e
  obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
  exact ⟨_, List.mem_cons_self .., le_refl _, _, DescR.refl _, .ref .unit,
    LSub.empty.extend x β, TyEq.refl _ _,
    Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Map831N

end
