import Target.Flat.Syntax

/-!
# Backend — host operations at the word IR  `[spec §8, §37]`

What the word IR (`Target/Flat/Syntax.lean`) and its targets need to know of a host operation:
its operands' width, whether it takes a pair, the kind of its result, and the range at which a
float-to-integer `trunc` has an answer. Shared by every backend that lowers to the word IR and by
the Wasm and LLVM emitters.
-/

namespace Backend.Flat
open BoCa

/-! ### Host operations  `[spec §8]` -/

/-- The machine width of a width: `u32` and `u64` are the machine's `i32` and `i64`, which are
signless, so an operation at an unsigned width is the one at its signed sibling on the same bits.
Every other width is its own.  `[spec §73]` -/
def machineWidth : Width → Width
  | .u32 => .w32
  | .u64 => .w64
  | w => w

/-- A host operation at machine widths: the grouped operations at `u32`/`u64` are those at
`w32`/`w64` (`ℍ.call` computes them with the same functions).  `[spec §73]` -/
def machineOp : HostOp → HostOp
  | .bin w o => .bin (machineWidth w) o
  | .div w o => .div (machineWidth w) o
  | .un w o => .un (machineWidth w) o
  | .eqz w => .eqz (machineWidth w)
  | .rel w o => .rel (machineWidth w) o
  | o => o

/-- The width of a host operation's operands. -/
def hostArgWidth : HostOp → Width
  | .bin w _ | .div w _ | .un w _ | .eqz w | .rel w _ => w
  | .wrap => .w64
  | .extend_s | .extend_u => .w32
  | .extend32_s => .w64
  | .wrap8 => .w32
  | .extend8_u => .w8
  | .fbin f _ | .fun1 f _ | .frel f _ | .trunc _ f _ | .trunc_sat _ f _ | .reinterpret_i f => f.width
  | .convert _ i _ => i.width
  | .demote => .f64
  | .promote => .f32
  | .reinterpret_f f => f.int.width
  | .reinterpret_u i => i.width
  | .reinterpret_s i => i.uwidth

/-- The operation takes a pair. -/
def hostBinary : HostOp → Bool
  | .bin .. | .div .. | .rel .. | .fbin .. | .frel .. => true
  | _ => false

/-- The type of a host operation's result: an integer, a test (`inr ()` for true), or a partial
operation's `inl n` or `inr ()`. -/
inductive ResKind where
  | int (w : Width)
  | test
  | trapping (w : Width)

def hostResKind : HostOp → ResKind
  | .bin w _ | .un w _ => .int w
  | .div w _ => .trapping w
  | .eqz _ | .rel .. => .test
  | .wrap => .int .w32
  | .extend_s | .extend_u | .extend32_s => .int .w64
  | .wrap8 => .int .w8
  | .extend8_u => .int .w32
  | .fbin f _ | .fun1 f _ | .convert f _ _ | .reinterpret_f f => .int f.width
  | .frel .. => .test
  | .trunc i _ _ => .trapping i.width
  | .trunc_sat i _ _ => .int i.width
  | .demote => .int .f32
  | .promote => .int .f64
  | .reinterpret_i f => .int f.int.width
  | .reinterpret_u i => .int i.uwidth
  | .reinterpret_s i => .int i.width

/-- A float constant, given by its bits, at a float operation's operand: an `f32` is 32 bits. -/
def fconst (f : FWidth) (b32 : UInt32) (b64 : UInt64) : Exp :=
  match f with
  | .f32 => .c32 b32
  | .f64 => .c64 b64

/-- `trunc`'s range at `f` (Wasm's): the integer part of `x` fits `i` read by `sx` exactly when
`x` compares above the lower bound (`>`, or `≥` where the bound is a float of the format) and
below the upper. Both comparisons are false at a NaN. -/
def truncRange (i : IWidth) (f : FWidth) (sx : Sx) : FRelOp × Exp × Exp :=
  match i, sx, f with
  | .i32, .s, .f64 => (.gt, .c64 0xC1E0000000200000, .c64 0x41E0000000000000)
  | .i32, .s, .f32 => (.ge, .c32 0xCF000000, .c32 0x4F000000)
  | .i64, .s, f => (.ge, fconst f 0xDF000000 0xC3E0000000000000, fconst f 0x5F000000 0x43E0000000000000)
  | .i32, .u, f => (.gt, fconst f 0xBF800000 0xBFF0000000000000, fconst f 0x4F800000 0x41F0000000000000)
  | .i64, .u, f => (.gt, fconst f 0xBF800000 0xBFF0000000000000, fconst f 0x5F800000 0x43F0000000000000)

end Backend.Flat
