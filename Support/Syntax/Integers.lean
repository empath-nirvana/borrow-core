/-!
# Support — Syntax — Integers  `[spec §8]`

The integer literals and the names of the host operations: Wasm's integer instructions at
`i32` and `i64`. Both are constants of the term language (`Prim.lit`, `Prim.host`), so they
are values, and shifting and substitution leave them fixed.

What an operation computes is not fixed here. The machine applies a host operation through a
`Host` (`Support/Dynamics/Host.lean`), and every theorem is parametric in it.
-/

namespace BoCa

/-- An integer literal: `i32[n]`, `i64[n]`, or the byte `u8[n]`.  `[spec §8]` -/
inductive IntLit where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | u8 (n : UInt8)
  deriving DecidableEq, Repr

/-- The width of an integer type. The grouped operations are Wasm's, at `w32` and `w64`; `w8`
    is the byte, which has only its conversions (`wrap8`, `extend8_u`).  `[spec §8]` -/
inductive Width where
  | w32 | w64 | w8
  deriving DecidableEq, Repr

/-- Binary operations `I ⊗ I ⊸ F I`: wrapping arithmetic and the bitwise group.
    `[spec §8]` -/
inductive BinOp where
  | add | sub | mul
  | and | or | xor | shl | shr_s | shr_u | rotl | rotr
  deriving DecidableEq, Repr

/-- Partial binary operations `I ⊗ I ⊸ F (I ⊕ 1)`, where Wasm traps.  `[spec §8]` -/
inductive DivOp where
  | div_s | div_u | rem_s | rem_u
  deriving DecidableEq, Repr

/-- Unary operations `I ⊸ F I`: the counts and the same-width sign extensions.  `[spec §8]` -/
inductive UnOp where
  | clz | ctz | popcnt | extend8_s | extend16_s
  deriving DecidableEq, Repr

/-- Binary tests `I ⊗ I ⊸ F (1 ⊕ 1)`.  `[spec §8]` -/
inductive RelOp where
  | eq | ne | lt_s | lt_u | le_s | le_u | gt_s | gt_u | ge_s | ge_u
  deriving DecidableEq, Repr

/-- The host operations of §8, one name per Wasm integer instruction.  `[spec §8]`

    - `bin w o`, `div w o`, `un w o`, `eqz w`, `rel w o`: the grouped operations at width `w`;
    - `wrap` (`i32.wrap_i64`), `extend_s`/`extend_u` (`i64.extend_i32_s`/`_u`) and
      `extend32_s` (`i64.extend32_s`): the conversions;
    - `wrap8` (the low 8 bits of an `i32`, `i32.and 0xff`) and `extend8_u` (a byte as an
      `i32`): the byte's conversions. -/
inductive HostOp where
  | bin (w : Width) (o : BinOp)
  | div (w : Width) (o : DivOp)
  | un  (w : Width) (o : UnOp)
  | eqz (w : Width)
  | rel (w : Width) (o : RelOp)
  | wrap
  | extend_s
  | extend_u
  | extend32_s
  | wrap8
  | extend8_u
  deriving DecidableEq, Repr

end BoCa
