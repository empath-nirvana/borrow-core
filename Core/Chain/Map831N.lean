import Core.Chain.ExtRLit791

/-!
# An `imm` lend's step against the per-lend world's `above`  `[spec §62]`

`docs/new-core/scope-831-map.md` §3 (risk 1). Core's `withbor1U_compatX` (`Core/EffBorrow.lean`)
runs the callback at the list with the lend's record added, along `ext_add hadd hout₂`: the
callback's resource is in the lend's stratum, and Core's `Ext` compares only the records
strictly longer-lived than each borrow cell of the resource, so a record lent below them is not
compared.

`LocTy.ExtR Θ Θ′ ρ` asks, at every key `(ℓ, a)` of `Θ` with `CellIn ρ a`, that
`Θ′.above a = Θ.above a`, and `LocTy.above` keeps the `imm` records whole. So at such a resource
`ExtR` fixes the `imm` records exactly (`extR_imm_eq`). An `Imm` value needs a record in the
world (`imm_world_ne_nil`). At a world without `imm` records, no `ExtR` extension at a resource
holding a borrow cell at a key's lifetime holds an `Imm` value (`not_imm_of_extR`), so
`𝒱⟦U(Imm 'x A ⊸ C)⟧` there admits every value with that resource (`callback_any`), at a world
and resource whose every hypothesis is discharged (`callback_any_inst`).

Read with Core's `ls₀` (`LocTy.aboveL`, the records lent strictly above the key, in the order
`ExtRL`), the lend's record at a fresh lifetime below the resource's stratum is not compared, and
the world with it is an extension (`extRL_addImm`): Core's `ext_add` at the per-lend world.

What is configured is the step, not the constant: that `withbor1U`'s semantic judgment fails at
the current interpretation is not built.
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
open BoCa.Lifetime (LSub LifeVar)

/-! ### `ExtR` at a resource with a borrow cell at a key fixes the `imm` records -/

/-- **At a resource with a borrow cell no longer-lived than a key's lifetime, `ExtR` keeps the
world's `imm` records exactly**: `LocTy.above` carries them whole, and `ExtR` asks the part
above the key to be unchanged. -/
theorem extR_imm_eq {Θ Θ' : LocTy} {ρ : WRes} {l : Loc} {a : Life}
    {F : Nat → Val → SPropS Loc Val a} (hl : Θ l a = some F) (hc : CellIn ρ a)
    (hE : Θ.ExtR Θ' ρ) : Θ'.imm = Θ.imm := by
  have h := congrArg LocTy.imm (hE.1 l a F hl hc).2
  simpa using h

/-- **An `Imm` value is witnessed by a record of the world**, so the world has one. -/
theorem imm_world_ne_nil {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : Θ.imm ≠ [] := by
  obtain ⟨-, -, ⟨l, -, -, -, -, hv, -⟩, hw⟩ := h
  obtain ⟨x, hx, -⟩ := hw l hv
  intro e
  rw [e] at hx
  exact List.not_mem_nil hx

/-- **No `Imm` value at an `ExtR` extension of a world without `imm` records**, at a resource
holding a borrow cell at a key's lifetime. -/
theorem not_imm_of_extR {Θ Θ' : LocTy} {ρ : WRes} {l : Loc} {a : Life}
    {F : Nat → Val → SPropS Loc Val a} (hI : Θ.imm = []) (hl : Θ l a = some F)
    (hc : CellIn ρ a) (hE : Θ.ExtR Θ' ρ) (b : Lifetime.Life) (A : VTy) (δ : LSub) (n : Nat)
    (v : Val) (ρv : WRes) : ¬ vN (ℍ := ℍ) (.imm b A) δ Θ' n v ρv := fun h =>
  imm_world_ne_nil h ((extR_imm_eq hl hc hE).trans hI)

/-- **`𝒱⟦U(Imm @b A ⊸ C)⟧` admits every value** at a world without `imm` records and a resource
holding a borrow cell at a key's lifetime: every world the thunk and its argument are read at is
an `ExtR` extension at that resource, and none holds an `Imm` value. -/
theorem callback_any {Θ : LocTy} {ρ : WRes} {l : Loc} {a : Life}
    {F : Nat → Val → SPropS Loc Val a} (hI : Θ.imm = []) (hl : Θ l a = some F)
    (hc : CellIn ρ a) (b : Lifetime.Life) (A : VTy) (C : CTy) (δ : LSub) (n : Nat) (v : Val) :
    vN (ℍ := ℍ) (.thunk (.arr (.imm b A) C)) δ Θ n v ρ := by
  simp only [vN, cN]
  intro Θ' hE _ _ _ _ Θ'' hE' _ _ k _ w ρw _ _ hw _
  exact absurd hw (not_imm_of_extR hI hl hc (hE.trans hE') b A δ k w ρw)

/-- **`callback_any` at an `OK` world, every hypothesis discharged**: the world
`∅ + (0, α) ↦ 𝒱⟦1⟧`, the resource `0 ↦ mut(α, (), ∅, ⊤)` (`ExtRLit791.ρb`), and the value `()`,
which is not a function, is a value of `U(Imm 'x 1 ⊸ F 1)`. -/
theorem callback_any_inst :
    ∃ (Θ : LocTy) (ρ : WRes), Θ.OK ∧ Θ.imm = [] ∧
      ∀ (x : LifeVar) (δ : LSub) (n : Nat),
        vN (ℍ := ℍ) (.thunk (.arr (.imm (.var x) .unit) (.ret .unit))) δ Θ n Val.unit ρ := by
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit LSub.empty Θ j u r
  have hfam : DownFam α (famL α P LocTy.empty) := vN_fam_down .unit _ α _
  let Θ := LocTy.empty.add 0 α (famL α P LocTy.empty)
  have hOK : Θ.OK := ⟨LocTy.down_add LocTy.empty_down 0 hfam,
    ⟨b, LocTy.fresh_add (N := b) (fun _ _ h => absurd rfl h) le_rfl hbα 0 _⟩⟩
  refine ⟨Θ, ExtRLit791.ρb 0 α, hOK, rfl, fun x δ n => ?_⟩
  exact callback_any rfl (LocTy.add_self LocTy.empty 0 α _) (ExtRLit791.cellIn_ρb 0 α)
    (.var x) .unit (.ret .unit) δ n Val.unit

/-! ### Core's `ls₀` at the per-lend world -/

/-- **The part of the world above `a`, Core's `ls₀`**: the keys strictly longer-lived than `a`
and the `imm` records lent strictly above `a`. -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.aboveL (Θ : LocTy) (a : Life) : LocTy :=
  ⟨fun x b => if a < b then Θ x b else none, Θ.imm.filter (fun x => decide (a < x.2))⟩

/-- **`ExtR` with Core's `ls₀`**: `LocTy.ExtR` with `aboveL` in place of `above`. -/
def ExtRL (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  (∀ l a F, Θ l a = some F → CellIn ρ a → Θ' l a = some F ∧ Θ'.aboveL a = Θ.aboveL a) ∧
    Θ.ImmLe Θ'

/-- An `imm` lend's record added to the world; the keys unchanged. -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.addImm (Θ : LocTy) (x : SRec) : LocTy :=
  ⟨Θ.fam, x :: Θ.imm⟩

/-- **Core's `ext_add` at the per-lend world, read with `ls₀`**: a record lent at `α` is not
compared at a resource in `Res_α`, whose borrow cells are all longer-lived than `α`. -/
theorem extRL_addImm (Θ : LocTy) (r : FrameRec) {α : Life} {ρ : WRes} (hρ : ρ.InStratum α) :
    ExtRL Θ (Θ.addImm (r, α)) ρ := by
  refine ⟨fun l a F hF hc => ⟨hF, ?_⟩, fun y hy => List.mem_cons_of_mem _ hy⟩
  have hαa : α < a := hc.of_stratum hρ
  refine LocTy.ext' (fun _ _ => rfl) ?_
  simp only [LocTy.aboveL, LocTy.addImm]
  rw [List.filter_cons_of_neg (by simpa using not_lt_of_gt hαa)]

/-- **With `above`, the same world is not an extension** at a resource with a borrow cell at a
key's lifetime: the records differ. -/
theorem not_extR_addImm {Θ : LocTy} {ρ : WRes} {l : Loc} {a : Life}
    {F : Nat → Val → SPropS Loc Val a} (hl : Θ l a = some F) (hc : CellIn ρ a) (x : SRec) :
    ¬ Θ.ExtR (Θ.addImm x) ρ := fun hE => by
  have h := extR_imm_eq hl hc hE
  simp only [LocTy.addImm] at h
  exact List.cons_ne_self x Θ.imm h

end BoCa.Fig16.LogRel.Core.Chain.SI.Map831N

end
