import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Host
import Support.Model.Notation
import Support.Model.Propositions
import Support.LogicalRelation.Facts

/-!
# Core — opaque host types  `[spec §11]`

The tags of the opaque value types `VTy.opaque k` and their models.  An opaque type has no
introduction or elimination rule; its relation is the predicate `k.Holds` on values, in both
modes (`Relation.lean`).

* `Input`: the input not yet read, a byte list.
* `Output`: `(fd, bs)`, the stream `fd` and the bytes written to it, most recent first.
* `Clock`: `t`, the time in nanoseconds (SPEC §34).
* `Args`: the arguments not yet read, a byte list, each argument followed by `0` (SPEC §34).
* `Tok`: the token of a declared type with no derived drop (SPEC §11, §12, §42). It is not a host
  type: its value is a location owning a unit cell, allocated by `mint` and freed by `burn`, the
  capture cell's pattern (SPEC §25). Its model is `Ref 1`'s (`Opaque.rel`).
* `Cell`: a location owning a cell that holds an `I32` (SPEC §63). It is not a host type; its
  model is `Ref I32`'s (`Opaque.rel`). No Core constant makes or takes one: it is a
  representation for an abstract type whose provider is a set of externs (`Core/Abstract.lean`).
* `abs n rep`: the abstract type named `n`, represented by the opaque type `rep` (SPEC §63). Its
  relation is `rep`'s. Only its provider may convert between the two (`CDerivesIn.absSeal`,
  `CDerivesIn.absUnseal`, `Fundamental.lean`).

The relation at an opaque type is `Opaque.rel`: `⌜k.Holds v⌝` at a host type, the owned unit cell
at `Tok`, the owned cell holding an `I32` at `Cell`, and the representation's at an abstract type.

A byte list is a value of `Bytes = μX. 1 ⊕ (U8 ⊗ X)` (`Stdio.lean`): `inj₁ ()`, or
`inj₂ (b, rest)` with `b` a byte literal.
-/

namespace BoCa.Fig16.LogRel.Core
open BoCa

/-- The opaque host types.  `[spec §11]` -/
inductive Opaque where
  /-- `Input`: the content of a readable stream's cell. -/
  | input
  /-- `Output`: the content of a writable stream's cell. -/
  | output
  /-- `Clock`: the content of a clock's cell (SPEC §34). -/
  | clock
  /-- `Args`: the content of the arguments' cell, the arguments not yet read (SPEC §34). -/
  | args
  /-- `Tok`: the token of a declared type with no derived drop, a location owning a unit cell.
  `[spec §11, §12, §42]` -/
  | tok
  /-- `Cell`: a location owning a cell that holds an `I32`.  `[spec §63]` -/
  | cell
  /-- `abs n rep`: the abstract type named `n`, represented by `rep`.  `[spec §63]` -/
  | abs (n : Nat) (rep : Opaque)
  deriving DecidableEq, Repr

/-- `v` is a byte list: `inj₁ ()`, or `inj₂ (u8[b], rest)` with `rest` a byte list.
`[spec §11]` -/
inductive BytesV : Val → Prop where
  | nil : BytesV (.inj₁ .unit)
  | cons (b : UInt8) {r : Val} : BytesV r → BytesV (.inj₂ (.pair (.u8 b) r))

/-- The model of an opaque type.  `[spec §11]` -/
def Opaque.Holds : Opaque → Val → Prop
  | .input, v => BytesV v
  | .output, v => ∃ fd bs, v = .pair (.i32 fd) bs ∧ BytesV bs
  | .clock, v => ∃ t, v = .i64 t
  | .args, v => BytesV v
  | .tok, v => ∃ ℓ, v = .loc ℓ
  | .cell, v => ∃ ℓ, v = .loc ℓ
  | .abs _ rep, v => rep.Holds v

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- The relation at an opaque type, in both modes: the model `⌜k.Holds v⌝` at a host type; at
`Tok` a location owning a unit cell, `Ref 1`'s clause; at `Cell` a location owning a cell that
holds an `I32`, `Ref I32`'s clause; at an abstract type its representation's.
`[spec §11, §12, §63]` -/
noncomputable def Opaque.rel : Opaque → Val → WProp
  | .tok, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ ⌜v' = .unit⌝
  | .cell, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ ⌜v'.IsInt .w32⌝
  | .abs _ rep, v => rep.rel v
  | .input, v => ⌜Opaque.Holds .input v⌝
  | .output, v => ⌜Opaque.Holds .output v⌝
  | .clock, v => ⌜Opaque.Holds .clock v⌝
  | .args, v => ⌜Opaque.Holds .args v⌝

/-- A host type: every opaque type but `Tok`, `Cell`, and the abstract types they represent.
Its relation is pure.  `[spec §11, §63]` -/
def Opaque.Host : Opaque → Prop
  | .tok | .cell => False
  | .abs _ rep => rep.Host
  | _ => True

/-- `Opaque.Host`, decided. -/
def Opaque.hostB : Opaque → Bool
  | .tok | .cell => false
  | .abs _ rep => rep.hostB
  | _ => true

theorem Opaque.host_iff : ∀ k : Opaque, k.hostB = true ↔ k.Host
  | .abs _ rep => Opaque.host_iff rep
  | .tok | .cell => by simp [Opaque.hostB, Opaque.Host]
  | .input | .output | .clock | .args => by simp [Opaque.hostB, Opaque.Host]

open BoCa.Fig16 BoCa.Fig16.BoLo in
theorem Opaque.rel_host : ∀ {k : Opaque} (_ : k.Host) (v : Val), k.rel v = ⌜k.Holds v⌝
  | .abs _ rep, hk, v => Opaque.rel_host (k := rep) hk v
  | .tok, hk, _ | .cell, hk, _ => hk.elim
  | .input, _, _ | .output, _, _ | .clock, _, _ | .args, _, _ => rfl

theorem Opaque.tok_not_host : ¬ Opaque.Host .tok := id

theorem Opaque.cell_not_host : ¬ Opaque.Host .cell := id

/-- An abstract type is a host type exactly when its representation is. -/
theorem Opaque.abs_not_host (n : Nat) {rep : Opaque} (h : ¬ rep.Host) :
    ¬ Opaque.Host (.abs n rep) := h

/-- **An abstract type's relation is its representation's.**  `[spec §63]` -/
theorem Opaque.rel_abs (n : Nat) (rep : Opaque) : Opaque.rel (.abs n rep) = Opaque.rel rep := rfl

/-- The content of the cell a non-host opaque value owns: `()` at `Tok`, an `I32` at `Cell`, the
representation's at an abstract type. -/
def Opaque.CellOk : Opaque → Val → Prop
  | .tok, w => w = .unit
  | .cell, w => w.IsInt .w32
  | .abs _ rep, w => rep.CellOk w
  | _, _ => False

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- The relation at an opaque type: at a host type the empty resource and the model; at `Tok`, at
`Cell` and at an abstract type over them a location and its owned cell, holding `k.CellOk`. -/
theorem Opaque.rel_cases : ∀ {k : Opaque} {v : Val} {ρ : WRes} (_ : k.rel v ρ),
    (k.Host ∧ ρ = PMap.empty ∧ k.Holds v) ∨
      (¬ k.Host ∧ ∃ ℓ w, v = .loc ℓ ∧ k.CellOk w ∧ ρ = ResU.single ℓ (CellU.ownOf w))
  | .abs _ rep, _, _, h => Opaque.rel_cases (k := rep) h
  | .tok, _, _, h => by
      right
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, rfl, hw⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, hw⟩ := hw
      exact ⟨id, ℓ, w, rfl, hw, (eq_of_compS_empty_left (ResU.CompS.comm hc))⟩
  | .cell, _, _, h => by
      right
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, rfl, hw⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, hw⟩ := hw
      exact ⟨id, ℓ, w, rfl, hw, (eq_of_compS_empty_left (ResU.CompS.comm hc))⟩
  | .input, _, _, h | .output, _, _, h | .clock, _, _, h | .args, _, _, h => by
      obtain ⟨h₁, h₂⟩ := h; exact Or.inl (And.intro trivial (And.intro h₁ h₂))

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- `Tok`'s relation at a location and its owned unit cell. -/
theorem Opaque.rel_tok_intro (ℓ : Loc) :
    Opaque.rel .tok (.loc ℓ) (ResU.single ℓ (CellU.ownOf .unit)) :=
  ⟨ℓ, .unit, pure_sep_mk rfl ⟨_, _, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩

end BoCa.Fig16.LogRel.Core
