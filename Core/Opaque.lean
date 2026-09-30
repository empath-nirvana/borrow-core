import Paper.S1_Syntax.Definitions
import Support.Dynamics.Host

/-!
# Core — opaque host types  `[spec §11]`

The tags of the opaque value types `VTy.opaque k` and their models.  An opaque type has no
introduction or elimination rule; its relation is the predicate `k.Holds` on values, in both
modes (`Relation.lean`).

* `Input`: the input not yet read, a byte list.
* `Output`: `(fd, bs)`, the stream `fd` and the bytes written to it, most recent first.

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

end BoCa.Fig16.LogRel.Core
