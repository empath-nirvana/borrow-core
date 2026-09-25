import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms

/-!
# Support — Dynamics — Host  `[spec §8]`

The host that applies §8's integer operations. `Host` gives each operation a Lean function of
its stated type, so every host is well sorted by construction; `Host.call` decodes an argument
value, applies the function and encodes the result. The machine's host step
(`BoLo.Head.host`) is `Host.call`, so the machine is deterministic at each host. Nothing about
arithmetic is proved.

The host is threaded as `{ℍ : Host} [HostIs ℍ]`. `HostIs ℍ` carries no data; its `outParam`
lets instance search find the host from the local instance, and a section variable
`variable {ℍ : Host} [HostIs ℍ]` is included in exactly the declarations whose statements
mention the machine. There is no global instance, so every theorem over the machine holds at
every host.

`wasmHost` is one host, Wasm's integer semantics on `UInt32`/`UInt64`. It is used by the
interpreter (`eval`) and by kernel-checked runs of programs only.

Encodings of results: a literal is `Prim.lit`; a test answers `inj₁ ()` for false and
`inj₂ ()` for true (the `1 ⊕ 1` booleans of `Core/Folds.lean`); a partial operation answers
`inj₁ n`, or `inj₂ ()` where Wasm traps.
-/

namespace BoCa

/-- An implementation of §8's operations, one function per operation at its type.  `[spec §8]` -/
structure Host where
  bin32   : BinOp → UInt32 → UInt32 → UInt32
  bin64   : BinOp → UInt64 → UInt64 → UInt64
  div32   : DivOp → UInt32 → UInt32 → Option UInt32
  div64   : DivOp → UInt64 → UInt64 → Option UInt64
  un32    : UnOp → UInt32 → UInt32
  un64    : UnOp → UInt64 → UInt64
  eqz32   : UInt32 → Bool
  eqz64   : UInt64 → Bool
  rel32   : RelOp → UInt32 → UInt32 → Bool
  rel64   : RelOp → UInt64 → UInt64 → Bool
  wrap    : UInt64 → UInt32
  extendS : UInt32 → UInt64
  extendU : UInt32 → UInt64
  extend32S : UInt64 → UInt64

/-- The machine runs at the host `ℍ`.  `[spec §8]` -/
class HostIs (ℍ : outParam Host) : Prop where
  intro ::

namespace Val

/-- `i32[n]` as a value.  `[spec §8]` -/
def i32 (n : UInt32) : Val := ⟨.prim (.lit (.i32 n)), .prim⟩

/-- `i64[n]` as a value.  `[spec §8]` -/
def i64 (n : UInt64) : Val := ⟨.prim (.lit (.i64 n)), .prim⟩

/-- A boolean at `1 ⊕ 1`: `inj₁ ()` is false, `inj₂ ()` is true.  `[spec §8]` -/
def bool (b : Bool) : Val := if b then .inj₂ .unit else .inj₁ .unit

/-- A partial result at `I ⊕ 1`: `inj₁ v`, or `inj₂ ()` where Wasm traps.  `[spec §8]` -/
def opt (o : Option Val) : Val :=
  match o with
  | some v => .inj₁ v
  | none   => .inj₂ .unit

end Val

/-- The literal an expression is, if it is one.  `[spec §8]` -/
def Expr.lit? : Expr → Option IntLit
  | .prim (.lit c) => some c
  | _ => none

/-- The operand of a unary operation at width `w`.  `[spec §8]` -/
def Expr.arg32? (e : Expr) : Option UInt32 :=
  match e.lit? with
  | some (.i32 n) => some n
  | _ => none

def Expr.arg64? (e : Expr) : Option UInt64 :=
  match e.lit? with
  | some (.i64 n) => some n
  | _ => none

/-- The operands of a binary operation: a pair of literals of one width.  `[spec §8]` -/
def Expr.args32? : Expr → Option (UInt32 × UInt32)
  | .pair a b => do pure (← a.arg32?, ← b.arg32?)
  | _ => none

def Expr.args64? : Expr → Option (UInt64 × UInt64)
  | .pair a b => do pure (← a.arg64?, ← b.arg64?)
  | _ => none

/-- Apply a host operation to an argument value. `none` when the argument is not of the
    operation's shape; a typed program never reaches that case.  `[spec §8]` -/
def Host.call (H : Host) : HostOp → Val → Option Val
  | .bin .w32 o, v => v.1.args32?.map fun (a, b) => .i32 (H.bin32 o a b)
  | .bin .w64 o, v => v.1.args64?.map fun (a, b) => .i64 (H.bin64 o a b)
  | .div .w32 o, v => v.1.args32?.map fun (a, b) => .opt ((H.div32 o a b).map .i32)
  | .div .w64 o, v => v.1.args64?.map fun (a, b) => .opt ((H.div64 o a b).map .i64)
  | .un .w32 o,  v => v.1.arg32?.map fun a => .i32 (H.un32 o a)
  | .un .w64 o,  v => v.1.arg64?.map fun a => .i64 (H.un64 o a)
  | .eqz .w32,   v => v.1.arg32?.map fun a => .bool (H.eqz32 a)
  | .eqz .w64,   v => v.1.arg64?.map fun a => .bool (H.eqz64 a)
  | .rel .w32 o, v => v.1.args32?.map fun (a, b) => .bool (H.rel32 o a b)
  | .rel .w64 o, v => v.1.args64?.map fun (a, b) => .bool (H.rel64 o a b)
  | .wrap,       v => v.1.arg64?.map fun a => .i32 (H.wrap a)
  | .extend_s,   v => v.1.arg32?.map fun a => .i64 (H.extendS a)
  | .extend_u,   v => v.1.arg32?.map fun a => .i64 (H.extendU a)
  | .extend32_s, v => v.1.arg64?.map fun a => .i64 (H.extend32S a)

/-! ### Wasm's integer semantics -/

namespace Wasm

/-- Leading zeros of the low `w` bits of `n`, counting from bit `w - 1`. -/
def clzN : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, n => if n.testBit w then 0 else clzN w n + 1

/-- Trailing zeros of `n` among its low `w` bits. -/
def ctzN (w n : Nat) : Nat := ((List.range w).takeWhile fun i => !n.testBit i).length

/-- Set bits of `n` among its low `w` bits. -/
def popcntN (w n : Nat) : Nat := (List.range w).countP fun i => n.testBit i

/-- Wasm's binary operations on `n`-bit vectors: wrapping, shift counts taken mod `n`. -/
def bin {n : Nat} : BinOp → BitVec n → BitVec n → BitVec n
  | .add,   a, b => a + b
  | .sub,   a, b => a - b
  | .mul,   a, b => a * b
  | .and,   a, b => a &&& b
  | .or,    a, b => a ||| b
  | .xor,   a, b => a ^^^ b
  | .shl,   a, b => a <<< (b.toNat % n)
  | .shr_s, a, b => a.sshiftRight (b.toNat % n)
  | .shr_u, a, b => a >>> (b.toNat % n)
  | .rotl,  a, b => a.rotateLeft (b.toNat % n)
  | .rotr,  a, b => a.rotateRight (b.toNat % n)

/-- Wasm's division and remainder: `none` at a zero divisor, and at `INT_MIN / -1`. -/
def div {n : Nat} : DivOp → BitVec n → BitVec n → Option (BitVec n)
  | .div_s, a, b =>
      if b = 0 then none
      else if a = BitVec.intMin n ∧ b = BitVec.allOnes n then none
      else some (a.sdiv b)
  | .div_u, a, b => if b = 0 then none else some (a / b)
  | .rem_s, a, b => if b = 0 then none else some (a.srem b)
  | .rem_u, a, b => if b = 0 then none else some (a % b)

def un {n : Nat} : UnOp → BitVec n → BitVec n
  | .clz,        a => BitVec.ofNat n (clzN n a.toNat)
  | .ctz,        a => BitVec.ofNat n (ctzN n a.toNat)
  | .popcnt,     a => BitVec.ofNat n (popcntN n a.toNat)
  | .extend8_s,  a => (a.truncate 8).signExtend n
  | .extend16_s, a => (a.truncate 16).signExtend n

def rel {n : Nat} : RelOp → BitVec n → BitVec n → Bool
  | .eq,   a, b => a == b
  | .ne,   a, b => a != b
  | .lt_s, a, b => a.slt b
  | .lt_u, a, b => a.ult b
  | .le_s, a, b => a.sle b
  | .le_u, a, b => a.ule b
  | .gt_s, a, b => b.slt a
  | .gt_u, a, b => b.ult a
  | .ge_s, a, b => b.sle a
  | .ge_u, a, b => b.ule a

end Wasm

/-- Wasm's integer instructions on `UInt32`/`UInt64`. For the interpreter and kernel-checked
    runs only; no theorem about the relation, the Fundamental Property or adequacy uses it.
    `[spec §8]` -/
def wasmHost : Host where
  bin32 o a b := .ofBitVec (Wasm.bin o a.toBitVec b.toBitVec)
  bin64 o a b := .ofBitVec (Wasm.bin o a.toBitVec b.toBitVec)
  div32 o a b := (Wasm.div o a.toBitVec b.toBitVec).map .ofBitVec
  div64 o a b := (Wasm.div o a.toBitVec b.toBitVec).map .ofBitVec
  un32 o a := .ofBitVec (Wasm.un o a.toBitVec)
  un64 o a := .ofBitVec (Wasm.un o a.toBitVec)
  eqz32 a := a == 0
  eqz64 a := a == 0
  rel32 o a b := Wasm.rel o a.toBitVec b.toBitVec
  rel64 o a b := Wasm.rel o a.toBitVec b.toBitVec
  wrap a := .ofBitVec (a.toBitVec.truncate 32)
  extendS a := .ofBitVec (a.toBitVec.signExtend 64)
  extendU a := .ofBitVec (a.toBitVec.zeroExtend 64)
  extend32S a := .ofBitVec ((a.toBitVec.truncate 32).signExtend 64)

/-! Spot checks of `wasmHost` against Wasm's reference results, by the kernel. -/

example : wasmHost.bin32 .add 0xFFFFFFFF 2 = 1 := by decide
example : wasmHost.bin32 .mul 0x10000 0x10000 = 0 := by decide
example : wasmHost.bin32 .sub 3 5 = 0xFFFFFFFE := by decide
example : wasmHost.bin32 .shl 1 33 = 2 := by decide
example : wasmHost.bin32 .shr_s 0x80000000 4 = 0xF8000000 := by decide
example : wasmHost.bin32 .shr_u 0x80000000 4 = 0x08000000 := by decide
example : wasmHost.bin32 .rotl 0x80000001 1 = 3 := by decide
example : wasmHost.bin32 .rotr 3 1 = 0x80000001 := by decide
example : wasmHost.div32 .div_s 0xFFFFFFF9 2 = some 0xFFFFFFFD := by decide
example : wasmHost.div32 .div_u 0xFFFFFFF9 2 = some 0x7FFFFFFC := by decide
example : wasmHost.div32 .rem_s 0xFFFFFFF9 2 = some 0xFFFFFFFF := by decide
example : wasmHost.div32 .rem_u 7 0 = none := by decide
example : wasmHost.div32 .div_s 0x80000000 0xFFFFFFFF = none := by decide
example : wasmHost.un32 .clz 1 = 31 := by decide
example : wasmHost.un32 .clz 0 = 32 := by decide
example : wasmHost.un32 .ctz 8 = 3 := by decide
example : wasmHost.un32 .popcnt 0xF0F0 = 8 := by decide
example : wasmHost.un32 .extend8_s 0x80 = 0xFFFFFF80 := by decide
example : wasmHost.rel32 .lt_s 0xFFFFFFFF 0 = true := by decide
example : wasmHost.rel32 .lt_u 0xFFFFFFFF 0 = false := by decide
example : wasmHost.wrap 0x100000005 = 5 := by decide
example : wasmHost.extendS 0xFFFFFFFF = 0xFFFFFFFFFFFFFFFF := by decide
example : wasmHost.extendU 0xFFFFFFFF = 0xFFFFFFFF := by decide
example : wasmHost.extend32S 0x80000000 = 0xFFFFFFFF80000000 := by decide
example : wasmHost.bin64 .mul 0x100000000 0x100000000 = 0 := by decide
example : wasmHost.un64 .clz 1 = 63 := by decide

end BoCa
