import Support.Syntax.Integers

/-!
# Support — Dynamics — Floats  `[spec §37]`

Wasm's float instructions on the bits of `f32` and `f64` values, for `wasmHost`
(`Support/Dynamics/Host.lean`). The arithmetic is Lean's `Float32`/`Float`, IEEE 754 binary32 and
binary64 with round-to-nearest-even; what Wasm leaves to the implementation is fixed as its
deterministic profile fixes it: every NaN an arithmetic operation answers is the canonical NaN of
positive sign (`canon32`, `canon64`). `abs`, `neg`, `copysign` and `reinterpret` act on the bits
and keep a NaN's payload, as Wasm requires.

Every theorem holds at every host; this host is used by the interpreters only.
-/

namespace BoCa.WasmF

/-- The canonical NaNs: quiet, positive, zero payload. -/
def canon32 : UInt32 := 0x7FC00000
def canon64 : UInt64 := 0x7FF8000000000000

def sign32 : UInt32 := 0x80000000
def sign64 : UInt64 := 0x8000000000000000

def isNaN32 (a : UInt32) : Bool := (a &&& 0x7FFFFFFF) > 0x7F800000
def isNaN64 (a : UInt64) : Bool := (a &&& 0x7FFFFFFFFFFFFFFF) > 0x7FF0000000000000

/-- An arithmetic result, its NaN canonical. -/
def out32 (x : Float32) : UInt32 := if x.isNaN then canon32 else x.toBits
def out64 (x : Float) : UInt64 := if x.isNaN then canon64 else x.toBits

def f32 (a : UInt32) : Float32 := Float32.ofBits a
def f64 (a : UInt64) : Float := Float.ofBits a

/-- Wasm's `min`: a NaN if either operand is one, and `-0` below `+0`. Equal operands are equal
bits but for the zeros, where the sign bits are or'ed (`min`) or and'ed (`max`). -/
def min32 (a b : UInt32) : UInt32 :=
  if isNaN32 a || isNaN32 b then canon32
  else if f32 a < f32 b then a else if f32 b < f32 a then b else a ||| b
def max32 (a b : UInt32) : UInt32 :=
  if isNaN32 a || isNaN32 b then canon32
  else if f32 a < f32 b then b else if f32 b < f32 a then a else a &&& b
def min64 (a b : UInt64) : UInt64 :=
  if isNaN64 a || isNaN64 b then canon64
  else if f64 a < f64 b then a else if f64 b < f64 a then b else a ||| b
def max64 (a b : UInt64) : UInt64 :=
  if isNaN64 a || isNaN64 b then canon64
  else if f64 a < f64 b then b else if f64 b < f64 a then a else a &&& b

def bin32 : FBinOp → UInt32 → UInt32 → UInt32
  | .add, a, b => out32 (f32 a + f32 b)
  | .sub, a, b => out32 (f32 a - f32 b)
  | .mul, a, b => out32 (f32 a * f32 b)
  | .div, a, b => out32 (f32 a / f32 b)
  | .min, a, b => min32 a b
  | .max, a, b => max32 a b
  | .copysign, a, b => (a &&& ~~~sign32) ||| (b &&& sign32)

def bin64 : FBinOp → UInt64 → UInt64 → UInt64
  | .add, a, b => out64 (f64 a + f64 b)
  | .sub, a, b => out64 (f64 a - f64 b)
  | .mul, a, b => out64 (f64 a * f64 b)
  | .div, a, b => out64 (f64 a / f64 b)
  | .min, a, b => min64 a b
  | .max, a, b => max64 a b
  | .copysign, a, b => (a &&& ~~~sign64) ||| (b &&& sign64)

/-- Round to the nearest integer, ties to even, keeping the sign of a zero result. Below `2^23`
(`2^52`) the fraction `x - ⌊x⌋` is exact; at or above it every float is an integer. -/
def nearest32 (a : UInt32) : UInt32 :=
  if isNaN32 a then canon32
  else
    let x := f32 a
    if (f32 (a &&& ~~~sign32)) ≥ Float32.ofBits 0x4B000000 then a
    else
      let r := x.floor
      let d := x - r
      let r := if d > 0.5 then r + 1 else if d < 0.5 then r
        else if (r / 2).floor * 2 == r then r else r + 1
      (r.toBits &&& ~~~sign32) ||| (a &&& sign32)

def nearest64 (a : UInt64) : UInt64 :=
  if isNaN64 a then canon64
  else
    let x := f64 a
    if (f64 (a &&& ~~~sign64)) ≥ Float.ofBits 0x4330000000000000 then a
    else
      let r := x.floor
      let d := x - r
      let r := if d > 0.5 then r + 1 else if d < 0.5 then r
        else if (r / 2).floor * 2 == r then r else r + 1
      (r.toBits &&& ~~~sign64) ||| (a &&& sign64)

def un32 : FUnOp → UInt32 → UInt32
  | .abs, a => a &&& ~~~sign32
  | .neg, a => a ^^^ sign32
  | .sqrt, a => out32 (f32 a).sqrt
  | .ceil, a => out32 (f32 a).ceil
  | .floor, a => out32 (f32 a).floor
  | .trunc, a => out32 (if f32 a < 0 then (f32 a).ceil else (f32 a).floor)
  | .nearest, a => nearest32 a

def un64 : FUnOp → UInt64 → UInt64
  | .abs, a => a &&& ~~~sign64
  | .neg, a => a ^^^ sign64
  | .sqrt, a => out64 (f64 a).sqrt
  | .ceil, a => out64 (f64 a).ceil
  | .floor, a => out64 (f64 a).floor
  | .trunc, a => out64 (if f64 a < 0 then (f64 a).ceil else (f64 a).floor)
  | .nearest, a => nearest64 a

/-- IEEE 754's comparisons: every one but `ne` is false at a NaN, and `-0 = +0`. -/
def relF {α : Type} [LT α] [LE α] [BEq α] [DecidableRel (α := α) (· < ·)]
    [DecidableRel (α := α) (· ≤ ·)] : FRelOp → α → α → Bool
  | .eq, x, y => x == y
  | .ne, x, y => !(x == y)
  | .lt, x, y => decide (x < y)
  | .gt, x, y => decide (y < x)
  | .le, x, y => decide (x ≤ y)
  | .ge, x, y => decide (y ≤ x)

/-- The magnitude of an integer read signed or unsigned, and whether it is negative. -/
def mag32 : Sx → UInt32 → Bool × UInt64
  | .u, a => (false, a.toUInt64)
  | .s, a => if a.toInt32 < 0 then (true, (0 - a).toUInt64) else (false, a.toUInt64)
def mag64 : Sx → UInt64 → Bool × UInt64
  | .u, a => (false, a)
  | .s, a => if a.toInt64 < 0 then (true, 0 - a) else (false, a)

/-- An integer converted, correctly rounded: rounding to nearest is symmetric, so the magnitude
is rounded and the sign applied. -/
def cvt32 (m : Bool × UInt64) : UInt32 :=
  let x := m.2.toFloat32
  (if m.1 then -x else x).toBits
def cvt64 (m : Bool × UInt64) : UInt64 :=
  let x := m.2.toFloat
  (if m.1 then -x else x).toBits

def convert : (f : FWidth) → (i : IWidth) → Sx → i.width.bits → f.width.bits
  | .f32, .i32, sx, a => cvt32 (mag32 sx a)
  | .f32, .i64, sx, a => cvt32 (mag64 sx a)
  | .f64, .i32, sx, a => cvt64 (mag32 sx a)
  | .f64, .i64, sx, a => cvt64 (mag64 sx a)

/-- A float operand as a `Float`: exact, as binary64 holds every binary32. -/
def toF64 : (f : FWidth) → f.width.bits → Float
  | .f32, a => (f32 a).toFloat
  | .f64, a => f64 a

def pow2 (k : Nat) : Float := Float.scaleB 1 k

/-- The integer part of `x` is representable at `i` read by `sx`: Wasm's range for `trunc`. -/
def inRange (i : IWidth) (sx : Sx) (x : Float) : Bool :=
  match i, sx with
  | .i32, .s => decide (-(pow2 31) - 1 < x) && decide (x < pow2 31)
  | .i32, .u => decide (-1 < x) && decide (x < pow2 32)
  | .i64, .s => decide (-(pow2 63) ≤ x) && decide (x < pow2 63)
  | .i64, .u => decide (-1 < x) && decide (x < pow2 64)

/-- The integer part of `x`, in range: its magnitude is exact in a `UInt64`. -/
def truncBits (x : Float) : UInt64 :=
  let t := if x < 0 then x.ceil else x.floor
  if t < 0 then 0 - (-t).toUInt64 else t.toUInt64

def ofU64 : (i : IWidth) → UInt64 → i.width.bits
  | .i32, n => n.toUInt32
  | .i64, n => n

def trunc (i : IWidth) (f : FWidth) (sx : Sx) (a : f.width.bits) : Option i.width.bits :=
  let x := toF64 f a
  if x.isNaN || !inRange i sx x then none else some (ofU64 i (truncBits x))

/-- `trunc_sat`: `0` at a NaN, the least or greatest integer out of range. -/
def truncSat (i : IWidth) (f : FWidth) (sx : Sx) (a : f.width.bits) : i.width.bits :=
  let x := toF64 f a
  if x.isNaN then ofU64 i 0
  else if inRange i sx x then ofU64 i (truncBits x)
  else
    let lo : UInt64 := match i, sx with
      | .i32, .s => 0x80000000 | .i64, .s => 0x8000000000000000 | _, .u => 0
    let hi : UInt64 := match i, sx with
      | .i32, .s => 0x7FFFFFFF | .i64, .s => 0x7FFFFFFFFFFFFFFF
      | .i32, .u => 0xFFFFFFFF | .i64, .u => 0xFFFFFFFFFFFFFFFF
    ofU64 i (if x < 0 then lo else hi)

def fbin : (f : FWidth) → FBinOp → f.width.bits → f.width.bits → f.width.bits
  | .f32, o, a, b => bin32 o a b
  | .f64, o, a, b => bin64 o a b

def fun1 : (f : FWidth) → FUnOp → f.width.bits → f.width.bits
  | .f32, o, a => un32 o a
  | .f64, o, a => un64 o a

def frel : (f : FWidth) → FRelOp → f.width.bits → f.width.bits → Bool
  | .f32, o, a, b => relF o (f32 a) (f32 b)
  | .f64, o, a, b => relF o (f64 a) (f64 b)

def demote (a : UInt64) : UInt32 := out32 (f64 a).toFloat32
def promote (a : UInt32) : UInt64 := out64 (f32 a).toFloat

end BoCa.WasmF
