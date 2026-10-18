import Support.Syntax.Integers

/-!
# Support — Dynamics — Floats  `[spec §37]`

The language's float operations on the bits of `f32` and `f64` values, for `wasmHost`
(`Support/Dynamics/Host.lean`). The arithmetic is Lean's `Float32`/`Float`, IEEE 754 binary32 and
binary64 with round-to-nearest-even. The sign and payload of a NaN that an arithmetic operation
answers are unspecified (SPEC §37): each function here takes a resolution `r : NaNs`, the NaN it
answers at each width, and `wasmHost` takes `NaNs.canonical`. `abs`, `neg`, `copysign` and
`reinterpret` act on the bits and keep a NaN's sign and payload.

Every theorem holds at every host; these hosts are used by the interpreters only.
-/

namespace BoCa.PrimF

/-- The canonical NaNs: quiet, positive, zero payload. -/
def canon32 : UInt32 := 0x7FC00000
def canon64 : UInt64 := 0x7FF8000000000000

/-- A resolution of the NaN an arithmetic operation answers: the NaN's bits at each width. -/
structure NaNs where
  nan32 : UInt32
  nan64 : UInt64

/-- The canonical NaNs, `wasmHost`'s resolution. -/
def NaNs.canonical : NaNs := ⟨canon32, canon64⟩
/-- The canonical NaNs with the sign set: the NaN x86 generates. -/
def NaNs.negative : NaNs := ⟨0xFFC00000, 0xFFF8000000000000⟩
/-- A positive quiet NaN of payload `1`. -/
def NaNs.payload : NaNs := ⟨0x7FC00001, 0x7FF8000000000001⟩

def sign32 : UInt32 := 0x80000000
def sign64 : UInt64 := 0x8000000000000000

def isNaN32 (a : UInt32) : Bool := (a &&& 0x7FFFFFFF) > 0x7F800000
def isNaN64 (a : UInt64) : Bool := (a &&& 0x7FFFFFFFFFFFFFFF) > 0x7FF0000000000000

/-- An arithmetic result, a NaN resolved by `r`. -/
def out32 (r : NaNs) (x : Float32) : UInt32 := if x.isNaN then r.nan32 else x.toBits
def out64 (r : NaNs) (x : Float) : UInt64 := if x.isNaN then r.nan64 else x.toBits

def f32 (a : UInt32) : Float32 := Float32.ofBits a
def f64 (a : UInt64) : Float := Float.ofBits a

/-- `min`: a NaN if either operand is one, and `-0` below `+0`. Equal operands are equal
bits but for the zeros, where the sign bits are or'ed (`min`) or and'ed (`max`). -/
def min32 (r : NaNs) (a b : UInt32) : UInt32 :=
  if isNaN32 a || isNaN32 b then r.nan32
  else if f32 a < f32 b then a else if f32 b < f32 a then b else a ||| b
def max32 (r : NaNs) (a b : UInt32) : UInt32 :=
  if isNaN32 a || isNaN32 b then r.nan32
  else if f32 a < f32 b then b else if f32 b < f32 a then a else a &&& b
def min64 (r : NaNs) (a b : UInt64) : UInt64 :=
  if isNaN64 a || isNaN64 b then r.nan64
  else if f64 a < f64 b then a else if f64 b < f64 a then b else a ||| b
def max64 (r : NaNs) (a b : UInt64) : UInt64 :=
  if isNaN64 a || isNaN64 b then r.nan64
  else if f64 a < f64 b then b else if f64 b < f64 a then a else a &&& b

def bin32 (r : NaNs) : FBinOp → UInt32 → UInt32 → UInt32
  | .add, a, b => out32 r (f32 a + f32 b)
  | .sub, a, b => out32 r (f32 a - f32 b)
  | .mul, a, b => out32 r (f32 a * f32 b)
  | .div, a, b => out32 r (f32 a / f32 b)
  | .min, a, b => min32 r a b
  | .max, a, b => max32 r a b
  | .copysign, a, b => (a &&& ~~~sign32) ||| (b &&& sign32)

def bin64 (r : NaNs) : FBinOp → UInt64 → UInt64 → UInt64
  | .add, a, b => out64 r (f64 a + f64 b)
  | .sub, a, b => out64 r (f64 a - f64 b)
  | .mul, a, b => out64 r (f64 a * f64 b)
  | .div, a, b => out64 r (f64 a / f64 b)
  | .min, a, b => min64 r a b
  | .max, a, b => max64 r a b
  | .copysign, a, b => (a &&& ~~~sign64) ||| (b &&& sign64)

/-- Round to the nearest integer, ties to even, keeping the sign of a zero result. Below `2^23`
(`2^52`) the fraction `x - ⌊x⌋` is exact; at or above it every float is an integer. -/
def nearest32 (r : NaNs) (a : UInt32) : UInt32 :=
  if isNaN32 a then r.nan32
  else
    let x := f32 a
    if (f32 (a &&& ~~~sign32)) ≥ Float32.ofBits 0x4B000000 then a
    else
      let k := x.floor
      let d := x - k
      let k := if d > 0.5 then k + 1 else if d < 0.5 then k
        else if (k / 2).floor * 2 == k then k else k + 1
      (k.toBits &&& ~~~sign32) ||| (a &&& sign32)

def nearest64 (r : NaNs) (a : UInt64) : UInt64 :=
  if isNaN64 a then r.nan64
  else
    let x := f64 a
    if (f64 (a &&& ~~~sign64)) ≥ Float.ofBits 0x4330000000000000 then a
    else
      let k := x.floor
      let d := x - k
      let k := if d > 0.5 then k + 1 else if d < 0.5 then k
        else if (k / 2).floor * 2 == k then k else k + 1
      (k.toBits &&& ~~~sign64) ||| (a &&& sign64)

def un32 (r : NaNs) : FUnOp → UInt32 → UInt32
  | .abs, a => a &&& ~~~sign32
  | .neg, a => a ^^^ sign32
  | .sqrt, a => out32 r (f32 a).sqrt
  | .ceil, a => out32 r (f32 a).ceil
  | .floor, a => out32 r (f32 a).floor
  | .trunc, a => out32 r (if f32 a < 0 then (f32 a).ceil else (f32 a).floor)
  | .nearest, a => nearest32 r a

def un64 (r : NaNs) : FUnOp → UInt64 → UInt64
  | .abs, a => a &&& ~~~sign64
  | .neg, a => a ^^^ sign64
  | .sqrt, a => out64 r (f64 a).sqrt
  | .ceil, a => out64 r (f64 a).ceil
  | .floor, a => out64 r (f64 a).floor
  | .trunc, a => out64 r (if f64 a < 0 then (f64 a).ceil else (f64 a).floor)
  | .nearest, a => nearest64 r a

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

def fbin (r : NaNs) : (f : FWidth) → FBinOp → f.width.bits → f.width.bits → f.width.bits
  | .f32, o, a, b => bin32 r o a b
  | .f64, o, a, b => bin64 r o a b

def fun1 (r : NaNs) : (f : FWidth) → FUnOp → f.width.bits → f.width.bits
  | .f32, o, a => un32 r o a
  | .f64, o, a => un64 r o a

def frel : (f : FWidth) → FRelOp → f.width.bits → f.width.bits → Bool
  | .f32, o, a, b => relF o (f32 a) (f32 b)
  | .f64, o, a, b => relF o (f64 a) (f64 b)

def demote (r : NaNs) (a : UInt64) : UInt32 := out32 r (f64 a).toFloat32
def promote (r : NaNs) (a : UInt32) : UInt64 := out64 r (f32 a).toFloat

/-! ### Results up to a NaN's sign and payload -/

/-- Two results at `f` agree up to a NaN's sign and payload: the same bits, or both NaNs. -/
def NaNEq : (f : FWidth) → f.width.bits → f.width.bits → Prop
  | .f32, a, b => a = b ∨ (isNaN32 a ∧ isNaN32 b)
  | .f64, a, b => a = b ∨ (isNaN64 a ∧ isNaN64 b)

/-- `r`'s answers are NaNs. -/
def NaNs.Ok (r : NaNs) : Prop := isNaN32 r.nan32 ∧ isNaN64 r.nan64

theorem NaNs.canonical_ok : NaNs.canonical.Ok := ⟨by decide, by decide⟩
theorem NaNs.negative_ok : NaNs.negative.Ok := ⟨by decide, by decide⟩
theorem NaNs.payload_ok : NaNs.payload.Ok := ⟨by decide, by decide⟩

theorem nanEq32_ite {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (c : Prop) [Decidable c] (v : UInt32) :
    NaNEq .f32 (if c then r.nan32 else v) (if c then s.nan32 else v) := by
  by_cases h : c
  · simp only [h]; exact Or.inr ⟨hr.1, hs.1⟩
  · simp only [h]; exact Or.inl rfl

theorem nanEq64_ite {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (c : Prop) [Decidable c] (v : UInt64) :
    NaNEq .f64 (if c then r.nan64 else v) (if c then s.nan64 else v) := by
  by_cases h : c
  · simp only [h]; exact Or.inr ⟨hr.2, hs.2⟩
  · simp only [h]; exact Or.inl rfl

/-- At two resolutions, every arithmetic operation agrees up to a NaN's sign and payload. -/
theorem fbin_nanEq {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (f : FWidth) (o : FBinOp)
    (a b : f.width.bits) : NaNEq f (fbin r f o a b) (fbin s f o a b) := by
  cases f <;> cases o <;>
    first
    | exact nanEq32_ite hr hs _ _
    | exact nanEq64_ite hr hs _ _
    | exact Or.inl rfl

theorem fun1_nanEq {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (f : FWidth) (o : FUnOp)
    (a : f.width.bits) : NaNEq f (fun1 r f o a) (fun1 s f o a) := by
  cases f <;> cases o <;>
    first
    | exact nanEq32_ite hr hs _ _
    | exact nanEq64_ite hr hs _ _
    | exact Or.inl rfl

theorem demote_nanEq {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (a : UInt64) :
    NaNEq .f32 (demote r a) (demote s a) := nanEq32_ite hr hs _ _

theorem promote_nanEq {r s : NaNs} (hr : r.Ok) (hs : s.Ok) (a : UInt32) :
    NaNEq .f64 (promote r a) (promote s a) := nanEq64_ite hr hs _ _

/-- `copysign`, `abs` and `neg` act on the bits: no resolution reaches them. -/
theorem fbin_copysign (r s : NaNs) (f : FWidth) (a b : f.width.bits) :
    fbin r f .copysign a b = fbin s f .copysign a b := by cases f <;> rfl
theorem fun1_abs (r s : NaNs) (f : FWidth) (a : f.width.bits) :
    fun1 r f .abs a = fun1 s f .abs a := by cases f <;> rfl
theorem fun1_neg (r s : NaNs) (f : FWidth) (a : f.width.bits) :
    fun1 r f .neg a = fun1 s f .neg a := by cases f <;> rfl

end BoCa.PrimF
