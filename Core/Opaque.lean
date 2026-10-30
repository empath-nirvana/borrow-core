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

The relation at an opaque type is `Opaque.rel`: `⌜k.Holds v⌝` at a host type, and the owned
unit cell at `Tok`.

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

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- The relation at an opaque type, in both modes: the model `⌜k.Holds v⌝` at a host type; at
`Tok` a location owning a unit cell, `Ref 1`'s clause.  `[spec §11, §12]` -/
noncomputable def Opaque.rel : Opaque → Val → WProp
  | .tok, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ ⌜v' = .unit⌝
  | .input, v => ⌜Opaque.Holds .input v⌝
  | .output, v => ⌜Opaque.Holds .output v⌝
  | .clock, v => ⌜Opaque.Holds .clock v⌝
  | .args, v => ⌜Opaque.Holds .args v⌝

/-- A host type: every opaque type but `Tok`. Its relation is pure.  `[spec §11]` -/
def Opaque.Host (k : Opaque) : Prop := k ≠ .tok

open BoCa.Fig16 BoCa.Fig16.BoLo in
theorem Opaque.rel_host {k : Opaque} (hk : k.Host) (v : Val) : k.rel v = ⌜k.Holds v⌝ := by
  cases k <;> first | rfl | exact absurd rfl hk

theorem Opaque.tok_not_host : ¬ Opaque.Host .tok := fun h => h rfl

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- The relation at an opaque type: at a host type the empty resource and the model; at `Tok` a
location and its owned unit cell. -/
theorem Opaque.rel_cases {k : Opaque} {v : Val} {ρ : WRes} (h : k.rel v ρ) :
    (k.Host ∧ ρ = PMap.empty ∧ k.Holds v) ∨
      (k = .tok ∧ ∃ ℓ, v = .loc ℓ ∧ ρ = ResU.single ℓ (CellU.ownOf .unit)) := by
  cases k with
  | tok =>
      right
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, rfl, hw⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨rfl, ℓ, rfl, (eq_of_compS_empty_left (ResU.CompS.comm hc))⟩
  | _ => obtain ⟨h₁, h₂⟩ := h; exact Or.inl (And.intro (fun e => nomatch e) (And.intro h₁ h₂))

open BoCa.Fig16 BoCa.Fig16.BoLo in
/-- `Tok`'s relation at a location and its owned unit cell. -/
theorem Opaque.rel_tok_intro (ℓ : Loc) :
    Opaque.rel .tok (.loc ℓ) (ResU.single ℓ (CellU.ownOf .unit)) :=
  ⟨ℓ, .unit, pure_sep_mk rfl ⟨_, _, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩

end BoCa.Fig16.LogRel.Core
