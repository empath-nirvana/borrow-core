import Support.Syntax.Integers

/-!
# Backend — the flat IR

Functions over 64-bit words with numbered locals, explicit allocation and free, direct and
indirect calls, explicit tail calls, and structured control (`ite`, `switch`); no closures and
no variables beyond locals. It is meant to lower as directly to LLVM IR as to Wasm.

Words are `i64`. An operation's operands and result have the widths §8 gives it: the numeric
operations are `HostOp`, the integer instructions of Wasm, and a test yields a 32-bit `0`/`1`.
Addresses are words; `load a k` and `store a k v` access the word at `a + 8k`.

## Representation

A value is one word:

| value | word |
|---|---|
| `()` | `1` |
| `i32[n]` | `n << 32 ∣ 3` |
| any other value | the address of an object (8-aligned, so bit 0 is clear) |

Objects start with a header word; bits 0–7 are the kind:

| kind | header | fields |
|---|---|---|
| pair | `1` | the two components |
| `inj₁` / `inj₂` | `2` / `3` | the payload |
| closure | `4 ∣ n << 8` | the code's table index, then the `n` captured values |
| `i64[n]` | `5` | the raw 64 bits of `n` |
| cell | `6` | the contents |

An array (SPEC §9) is one range of `max n 1` cells, two words each, and its value is the pair
`(base, i32[n])`; the cell at `base + 16·i` is element `i` (`Backend/Flat/Runtime.lean`).

`i64` is boxed because the erasure is untyped: a deep copy or drop must tell a pointer from an
immediate by the word alone.
-/

namespace Backend.Flat
open BoCa

inductive Exp where
  | loc (i : Nat)
  | c64 (n : UInt64)
  | c32 (n : UInt32)
  /-- The word at `addr + 8·off`. -/
  | load (addr : Exp) (off : Nat)
  /-- A Wasm integer instruction; a partial one traps where its §8 form answers `inr ()`. -/
  | op (o : HostOp) (args : List Exp)
  | call (f : Nat) (args : List Exp)
  /-- A call through the function table. -/
  | callInd (f : Exp) (args : List Exp)
  /-- The allocator: a fresh range of `words` words. -/
  | alloc (words : Exp)
  /-- The allocator's count of live ranges. -/
  | live
  deriving Repr, Inhabited

inductive Stmt where
  | set (i : Nat) (e : Exp)
  | store (addr : Exp) (off : Nat) (v : Exp)
  /-- Return a range to the allocator. -/
  | free (addr : Exp)
  | eval (e : Exp)
  /-- Write the byte `b` to standard output. -/
  | out (b : Exp)
  /-- `c` is a 32-bit test. -/
  | ite (c : Exp) (t e : List Stmt)
  /-- `s` is 32-bit; arm `k` runs when `s = k`, the last arm otherwise. -/
  | switch (s : Exp) (arms : List (List Stmt))
  | ret (e : Exp)
  | tailCall (f : Nat) (args : List Exp)
  | tailCallInd (f : Exp) (args : List Exp)
  | trap
  deriving Repr, Inhabited

structure Fn where
  name : String
  params : Nat
  /-- Locals beyond the parameters. -/
  locals : Nat
  body : List Stmt
  deriving Repr, Inhabited

structure Prog where
  fns : Array Fn
  /-- The function table: closure code `c` is `fns[table[c]]`. -/
  table : Array Nat
  /-- Runs `main`, prints its value, drops it, and prints the live count. -/
  entry : Nat
  deriving Repr, Inhabited

/-! ### Words and objects -/

def hPair : UInt64 := 1
def hInj₁ : UInt64 := 2
def hInj₂ : UInt64 := 3
def hClos : UInt64 := 4
def hI64 : UInt64 := 5
def hCell : UInt64 := 6

def unitW : UInt64 := 1
def i32W (n : UInt32) : UInt64 := (n.toUInt64 <<< 32) ||| 3

def add64 (a b : Exp) : Exp := .op (.bin .w64 .add) [a, b]
def and64 (a b : Exp) : Exp := .op (.bin .w64 .and) [a, b]
def or64 (a b : Exp) : Exp := .op (.bin .w64 .or) [a, b]
def shl64 (a b : Exp) : Exp := .op (.bin .w64 .shl) [a, b]
def shr64 (a b : Exp) : Exp := .op (.bin .w64 .shr_u) [a, b]
def eq64 (a b : Exp) : Exp := .op (.rel .w64 .eq) [a, b]
def ltu64 (a b : Exp) : Exp := .op (.rel .w64 .lt_u) [a, b]
def or32 (a b : Exp) : Exp := .op (.bin .w32 .or) [a, b]
def and32 (a b : Exp) : Exp := .op (.bin .w32 .and) [a, b]
def wrap (a : Exp) : Exp := .op .wrap [a]

/-- Bit 0 of a word: set for an immediate. -/
def isImm (w : Exp) : Exp := wrap (and64 w (.c64 1))
/-- The kind of the object at `w`. -/
def kindOf (h : Exp) : Exp := wrap (and64 h (.c64 0xff))
/-- `i32[r]` from the 32-bit `r`. -/
def box32 (r : Exp) : Exp := or64 (shl64 (.op .extend_u [r]) (.c64 32)) (.c64 3)
/-- The 32-bit integer of an `i32[n]` word. -/
def unbox32 (w : Exp) : Exp := wrap (shr64 w (.c64 32))
/-- The address of field `i` counted from word `2` (a closure's environment). -/
def envAddr (base i : Exp) : Exp := add64 base (shl64 i (.c64 3))

/-- Write the bytes of `s`. -/
def outStr (s : String) : List Stmt := s.toList.map fun c => .out (.c64 c.toNat.toUInt64)

/-- `t := new object with header `h` and `fields``; then `k`. -/
def mkObj (t : Nat) (h : UInt64) (fields : List Exp) : List Stmt :=
  [.set t (.alloc (.c64 (fields.length + 1).toUInt64)), .store (.loc t) 0 (.c64 h)] ++
    (fields.zipIdx.map fun (e, i) => .store (.loc t) (i + 1) e)

end Backend.Flat
