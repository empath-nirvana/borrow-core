/-!
# Support — Syntax — Integers  `[spec §8]`

The numeric literals and the names of the host operations: the language's integer operations at
`i32` and `i64` (§8) and its float operations at `f32` and `f64` (§37), each named as the Wasm
instruction that computes it. Both are constants of the term language (`Prim.lit`, `Prim.host`), so they
are values, and shifting and substitution leave them fixed.

What an operation computes is not fixed here. The machine applies a host operation through a
`Host` (`Support/Dynamics/Host.lean`), and every theorem is parametric in it.
-/

namespace BoCa

/-- A numeric literal: `i32[n]`, `i64[n]`, the byte `u8[n]`, or a float `f32[n]`/`f64[n]`
    given by its IEEE 754 bit pattern `n`.  `[spec §8, §37]` -/
inductive IntLit where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | u8 (n : UInt8)
  | f32 (n : UInt32)
  | f64 (n : UInt64)
  deriving DecidableEq, Repr

/-- The width of a numeric type. The grouped integer operations are at `w32` and `w64`;
    `w8` is the byte, which has only its conversions (`wrap8`, `extend8_u`); `f32` and `f64` are
    the floats, which have the float operations (§37).  `[spec §8, §37]` -/
inductive Width where
  | w32 | w64 | w8 | f32 | f64
  deriving DecidableEq, Repr

/-- The bits that hold a value of a width.  `[spec §8, §37]` -/
abbrev Width.bits : Width → Type
  | .w32 => UInt32
  | .w64 => UInt64
  | .w8 => UInt8
  | .f32 => UInt32
  | .f64 => UInt64

/-- A float width.  `[spec §37]` -/
inductive FWidth where
  | f32 | f64
  deriving DecidableEq, Repr

/-- The integer width of a float conversion.  `[spec §37]` -/
inductive IWidth where
  | i32 | i64
  deriving DecidableEq, Repr

def FWidth.width : FWidth → Width
  | .f32 => .f32
  | .f64 => .f64

def IWidth.width : IWidth → Width
  | .i32 => .w32
  | .i64 => .w64

/-- The float width of a width, if it is one.  `[spec §37]` -/
def Width.float? : Width → Option FWidth
  | .f32 => some .f32
  | .f64 => some .f64
  | _ => none

/-- The integer width of a float's size: `reinterpret`'s other side.  `[spec §37]` -/
def FWidth.int : FWidth → IWidth
  | .f32 => .i32
  | .f64 => .i64

/-- Signed or unsigned reading of an integer, in a conversion.  `[spec §37]` -/
inductive Sx where
  | s | u
  deriving DecidableEq, Repr

/-- Binary operations `I ⊗ I ⊸ F I`: wrapping arithmetic and the bitwise group.
    `[spec §8]` -/
inductive BinOp where
  | add | sub | mul
  | and | or | xor | shl | shr_s | shr_u | rotl | rotr
  deriving DecidableEq, Repr

/-- Partial binary operations `I ⊗ I ⊸ F (I ⊕ 1)`: `inr ()` where there is no answer.  `[spec §8]` -/
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

/-- Binary float operations `F ⊗ F ⊸ F`.  `[spec §37]` -/
inductive FBinOp where
  | add | sub | mul | div | min | max | copysign
  deriving DecidableEq, Repr

/-- Unary float operations `F ⊸ F`.  `[spec §37]` -/
inductive FUnOp where
  | abs | neg | sqrt | ceil | floor | trunc | nearest
  deriving DecidableEq, Repr

/-- Float comparisons `F ⊗ F ⊸ 1 ⊕ 1`, IEEE 754's: false when either operand is a NaN, except
    `ne`.  `[spec §37]` -/
inductive FRelOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- The host operations of §8 and §37, each named as the Wasm instruction that computes it.
    `[spec §8, §37]`

    - `bin w o`, `div w o`, `un w o`, `eqz w`, `rel w o`: the grouped operations at width `w`;
    - `wrap` (`i32.wrap_i64`), `extend_s`/`extend_u` (`i64.extend_i32_s`/`_u`) and
      `extend32_s` (`i64.extend32_s`): the conversions;
    - `wrap8` (the low 8 bits of an `i32`, `i32.and 0xff`) and `extend8_u` (a byte as an
      `i32`): the byte's conversions;
    - `fbin f o`, `fun1 f o`, `frel f o`: the float operations at `f` (§37);
    - `convert f i sx` (`f.convert_i_sx`), the total conversion of an integer to a float;
      `trunc i f sx` (`i.trunc_f_sx`), partial, `inr ()` where there is no answer; `trunc_sat i f sx`
      (`i.trunc_sat_f_sx`), total; `demote` (`f32.demote_f64`), `promote` (`f64.promote_f32`);
      `reinterpret_i f` (a float's bits as the integer of its size) and `reinterpret_f f` (the
      converse). -/
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
  | fbin (f : FWidth) (o : FBinOp)
  | fun1 (f : FWidth) (o : FUnOp)
  | frel (f : FWidth) (o : FRelOp)
  | convert (f : FWidth) (i : IWidth) (sx : Sx)
  | trunc (i : IWidth) (f : FWidth) (sx : Sx)
  | trunc_sat (i : IWidth) (f : FWidth) (sx : Sx)
  | demote
  | promote
  | reinterpret_i (f : FWidth)
  | reinterpret_f (f : FWidth)
  deriving DecidableEq, Repr

end BoCa
