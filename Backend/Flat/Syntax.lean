import Support.Syntax.Integers

/-!
# Backend — the flat IR

Functions over 64-bit words with numbered locals, explicit allocation and free, direct calls
with any number of results, explicit tail calls, and structured control (`ite`, `switch`); no
closures, no function pointers and no variables beyond locals. It is meant to lower as directly
to LLVM IR as to Wasm: a function of several results is a Wasm multi-value function, and an LLVM
function returning a struct by value (or through an `sret` pointer when it is wide); `switch` is
Wasm's `br_table` and LLVM's `switch`.

Words are `i64`. An operation's operands and result have the widths §8 gives it: the numeric
operations are `HostOp`, the integer instructions of Wasm, and a test yields a 32-bit `0`/`1`.
Addresses are words; `load a k` and `store a k v` access the word at `a + 8k`.

A value of layout type `A` (`Backend/Clos/Types.lean`) is `|A|` words, held in `|A|` locals,
passed as `|A|` arguments and returned as `|A|` results (`Backend/README.md`, Representation).
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
  /-- The allocator: a fresh range of `words` words. -/
  | alloc (words : Exp)
  /-- The allocator's count of live ranges. -/
  | live
  /-- The next byte of the stream `fd`, or `2⁶⁴ - 1` at its end (SPEC §11). -/
  | getc (fd : Exp)
  /-- A run's counter: `0` the allocations so far, `1` the dispatched calls so far. -/
  | stat (k : Nat)
  deriving Repr, Inhabited

inductive Stmt where
  | set (i : Nat) (e : Exp)
  | store (addr : Exp) (off : Nat) (v : Exp)
  /-- Return a range to the allocator. -/
  | free (addr : Exp)
  /-- Write the byte `b` to standard output. -/
  | out (b : Exp)
  /-- Write the low byte of `b` to the stream `fd` (SPEC §11). -/
  | putc (fd b : Exp)
  /-- `c` is a 32-bit test. -/
  | ite (c : Exp) (t e : List Stmt)
  /-- `cases[k]` when `e` is `k < cases.length`, else `dflt`. -/
  | switch (e : Exp) (cases : List (List Stmt)) (dflt : List Stmt)
  /-- Call function `f`; its results go to the locals `dsts`. -/
  | call (dsts : List Nat) (f : Nat) (args : List Exp)
  | ret (es : List Exp)
  /-- A tail call: the callee's results are the caller's. -/
  | tailCall (f : Nat) (args : List Exp)
  /-- Count a dispatched call: a closure call whose code is chosen at run time. -/
  | tick
  | trap
  deriving Repr, Inhabited

structure Fn where
  name : String
  params : Nat
  results : Nat
  /-- Locals beyond the parameters. -/
  locals : Nat
  body : List Stmt
  deriving Repr, Inhabited

structure Prog where
  fns : Array Fn
  /-- Runs `main`, prints its value, drops it, and prints the live count. -/
  entry : Nat
  deriving Repr, Inhabited

/-! ### Words -/

def add64 (a b : Exp) : Exp := .op (.bin .w64 .add) [a, b]
def and64 (a b : Exp) : Exp := .op (.bin .w64 .and) [a, b]
def shl64 (a b : Exp) : Exp := .op (.bin .w64 .shl) [a, b]
def shr64 (a b : Exp) : Exp := .op (.bin .w64 .shr_u) [a, b]
def mul64 (a b : Exp) : Exp := .op (.bin .w64 .mul) [a, b]
def eq64 (a b : Exp) : Exp := .op (.rel .w64 .eq) [a, b]
def eqz64 (a : Exp) : Exp := .op (.eqz .w64) [a]
def ltu64 (a b : Exp) : Exp := .op (.rel .w64 .lt_u) [a, b]
def or32 (a b : Exp) : Exp := .op (.bin .w32 .or) [a, b]
def and32 (a b : Exp) : Exp := .op (.bin .w32 .and) [a, b]
def wrap (a : Exp) : Exp := .op .wrap [a]
def extendU (a : Exp) : Exp := .op .extend_u [a]

/-- Write the bytes of `s`. -/
def outStr (s : String) : List Stmt := s.toList.map fun c => .out (.c64 c.toNat.toUInt64)

end Backend.Flat
