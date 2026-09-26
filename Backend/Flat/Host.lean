import Backend.Flat.Syntax

/-!
# Backend — host operations  `[spec §8]`

One flat-IR function per host operation a program applies, `hostFn op`, taking the argument
value and returning the result value. It unpacks the argument (freeing the pair of a binary
operation, and the box of an `i64`), applies the operation's Wasm instruction, and encodes the
result as §8 does:

- arithmetic: the integer (`i32[n]` immediate, or a fresh `i64` box);
- a test: `inr ()` for true, `inl ()` for false;
- a partial operation (`div`): `inr ()` where the Wasm instruction would trap (a zero divisor, or
  `INT_MIN / -1` for `div_s`), checked before the instruction runs; otherwise `inl n`.
-/

namespace Backend.Flat
open BoCa

/-- The width of the operands. -/
def argWidth : HostOp → Width
  | .bin w _ | .div w _ | .un w _ | .eqz w | .rel w _ => w
  | .wrap => .w64
  | .extend_s | .extend_u => .w32
  | .extend32_s => .w64

/-- The operation takes a pair. -/
def binary : HostOp → Bool
  | .bin .. | .div .. | .rel .. => true
  | _ => false

/-- How a result is encoded. -/
inductive ResKind where
  | int (w : Width)
  | test
  | trapping (w : Width)

def resKind : HostOp → ResKind
  | .bin w _ | .un w _ => .int w
  | .div w _ => .trapping w
  | .eqz _ | .rel .. => .test
  | .wrap => .int .w32
  | .extend_s | .extend_u | .extend32_s => .int .w64

/-- A constant at width `w`. -/
def cw : Width → UInt64 → Exp
  | .w32, n => .c32 n.toUInt32
  | .w64, n => .c64 n

/-- Where the instruction traps, as a 32-bit test on the raw operands. -/
def trapCond (w : Width) (o : DivOp) (a b : Exp) : Exp :=
  let zero := Exp.op (.eqz w) [b]
  match o with
  | .div_s =>
    let intMin := match w with | .w32 => cw w 0x80000000 | .w64 => cw w 0x8000000000000000
    or32 zero (and32 (.op (.rel w .eq) [a, intMin]) (.op (.rel w .eq) [b, cw w 0xFFFFFFFFFFFFFFFF]))
  | _ => zero

/-- Locals: `0` the argument, `1`, `2` the operand words, `3` a result, `4` a new object. -/
def hostFn (o : HostOp) : Fn :=
  let p := Exp.loc 0
  -- Unpack: `1`, `2` hold the operand words and the argument's pair is freed.
  let unpack : List Stmt :=
    if binary o then [.set 1 (.load p 1), .set 2 (.load p 2), .free p] else [.set 1 p]
  -- The raw operand in word local `i`; a boxed `i64` is unboxed into it and freed.
  let unboxAt (i : Nat) : List Stmt := match argWidth o with
    | .w32 => []
    | .w64 => [.set 3 (.load (.loc i) 1), .free (.loc i), .set i (.loc 3)]
  let raw (i : Nat) : Exp := match argWidth o with
    | .w32 => unbox32 (.loc i)
    | .w64 => .loc i
  let operands := if binary o then unboxAt 1 ++ unboxAt 2 else unboxAt 1
  let args := if binary o then [raw 1, raw 2] else [raw 1]
  -- Encode an integer result `r` of width `w`, and return it.
  let retInt (w : Width) (r : Exp) : List Stmt := match w with
    | .w32 => [.ret (box32 r)]
    | .w64 => [.set 3 r] ++ mkObj 4 hI64 [.loc 3] ++ [.ret (.loc 4)]
  let retInj (h : UInt64) (pre : List Stmt) (payload : Exp) : List Stmt :=
    pre ++ mkObj 4 h [payload] ++ [.ret (.loc 4)]
  let result : List Stmt := match resKind o, o with
    | .int w, _ => retInt w (.op o args)
    | .test, _ =>
      [.ite (.op o args) (retInj hInj₂ [] (.c64 unitW)) (retInj hInj₁ [] (.c64 unitW))]
    | .trapping w, .div _ d =>
      let a := args.headD (.c64 0); let b := args.getD 1 (.c64 0)
      let boxed : List Stmt × Exp := match w with
        | .w32 => ([], box32 (.op o args))
        | .w64 => ([.set 3 (.op o args)] ++ mkObj 2 hI64 [.loc 3], .loc 2)
      [.ite (trapCond w d a b) (retInj hInj₂ [] (.c64 unitW))
        (retInj hInj₁ boxed.1 boxed.2)]
    | .trapping _, _ => [.trap]
  { name := s!"host_{reprStr o}", params := 1, locals := 4,
    body := unpack ++ operands ++ result ++ [.trap] }

end Backend.Flat
