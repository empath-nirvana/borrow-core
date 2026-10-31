import Core.PinLaw
import Backend2.Lint

/-!
# Backend2 — spike: a stack machine level's frame lent to its `k` as an instance of `LendFrame` (#746)

This file is not imported by `Backend2.lean`. It has no `axiom` and no `sorry`.

The question: can the two `.drop` sites of `genStackMach` (the step's `k'` and a point's `mk`'s
`kv`, both listed in `Prog.stackKs`) be replaced by a lend of the level's frame to its `k`, with
the soundness across the suspension an instance of `LendFrame` (`Core/PinLaw.lean`)?

What `LendFrame` needs from an instance, each fact checked here:
- the place lent is at `Ref T` and the view at `Mut 'x T`, since `LendForm` has the one form
  `ref` (`lendForm_ref`);
- a value at `Ref T` in Core's relation is a location of Core's memory, owned in the world
  (`ref_val_loc`): the place has to be a cell of the Core program's heap.

And what the stack machine has:
- the `k₂` that takes over at a suspension, `clos kc [base]`, closes over one value at
  `.int .w64`, which no borrow type is (`stackAddr_not_borrow`), so `k₂` holds no view to hand
  over (`HandOverAsLend` is false).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Backend2.StackKLendSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Every lend form lends a place at `Ref T` as the view `Mut 'x T`, in the context `Δ` extended
by `x ⊏ b`. -/
theorem lendForm_ref {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {P V B : VTy} {Δb : LifeCtx}
    (h : LendForm Δ x b P V B Δb) :
    ∃ T, P = .ref T ∧ V = .mut (.var x) T ∧ Δb = Δ.extend x b := by
  cases h with
  | ref _ _ => exact ⟨_, rfl, rfl, rfl⟩

/-- A value at `Ref A` in Core's relation is a location `ℓ` of Core's memory. -/
theorem ref_val_loc {η : Option (Nat → TEnt)} {bv : Bool} {A : VTy} {ls : List SRec} {δ : LSub}
    {v : Val} {ρ : WRes} (h : vCE η bv (.ref A) ls δ v ρ) : ∃ ℓ, v = .loc ℓ := by
  simp only [vCE, BoCa.Fig16.BoLo.ex, BoCa.Fig16.BoLo.sep, BoCa.Fig16.BoLo.pure] at h
  obtain ⟨ℓ, _, _, _, _, ⟨_, hv⟩, _⟩ := h
  exact ⟨ℓ, hv⟩

/-- The type of a stack machine's address (`genStackMach`'s `aT`), the one value `k₂ = clos kc
[base]` closes over. -/
def stackAddrTy : LTy := .int .w64

/-- The obstruction to item 1 of the brief: the lend handed over to `k₂` would have to be held in
`k₂`'s environment, so the environment's one slot type would be a borrow. -/
def HandOverAsLend : Prop := ∃ T, stackAddrTy = .mut T ∨ stackAddrTy = .imm T

theorem stackAddr_not_borrow : ¬ HandOverAsLend := by
  rintro ⟨T, h | h⟩ <;> cases h

/-- `k₂`'s environment slot is droppable by type: it carries no borrow and no owned cell. -/
theorem stackAddr_droppable : Lint.droppable stackAddrTy = true := by decide

end Backend2.StackKLendSpike

end
