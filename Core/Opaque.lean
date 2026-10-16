import Paper.S1_Syntax.Definitions
import Support.Dynamics.Host

/-!
# Core — opaque host types  `[spec §11]`

The tags of the opaque value types `VTy.opaque k` and their models.  An opaque type has no
introduction or elimination rule; its relation is the predicate `k.Holds` on values, in both
modes (`Relation.lean`).

* `Input`: the input not yet read, a byte list.
* `Output`: `(fd, bs)`, the stream `fd` and the bytes written to it, most recent first.
* `Clock`: `t`, the time in milliseconds (SPEC §34).
* `Args`: the arguments not yet read, a byte list, each argument followed by `0` (SPEC §34).

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
  | .clock, v => ∃ t, v = .i32 t
  | .args, v => BytesV v

end BoCa.Fig16.LogRel.Core
