import Support.Syntax.Integers

/-!
# Backend — the Wasm AST

The subset of Wasm the backend emits: `i64` locals, one linear memory, `i64` loads and stores,
the integer instructions of §8 (`HostOp`), direct and tail calls, functions of several `i64`
results (multi-value), `if`, and `block` with `br` and `br_table` (a switch). There is no function
table and no indirect call. Functions are named; a function refers to another by
name. The runtime functions (`Backend/Wasm/Runtime.lean`) are written in WAT and referred to
by name: `$alloc`, `$free`, `$live`, `$putc`.
-/

namespace Backend.Wasm
open BoCa

inductive Instr where
  | i32Const (n : UInt32)
  | i64Const (n : UInt64)
  | localGet (i : Nat)
  | localSet (i : Nat)
  /-- `i64.load offset=off`, at an `i32` address. -/
  | i64Load (off : Nat)
  | i64Store (off : Nat)
  /-- `i64.load8_u` and `i64.store8`: a byte slot. -/
  | i64Load8U
  | i64Store8
  /-- `i64.load32_u` and `i64.store32`: a 4-byte slot. -/
  | i64Load32U
  | i64Store32
  | num (o : HostOp)
  | call (f : String)
  | returnCall (f : String)
  | ifElse (t e : List Instr)
  /-- A block of no result; `br k` from inside it, at depth `k`, leaves it. -/
  | block (body : List Instr)
  | br (depth : Nat)
  /-- `br_table`: the `i32` operand `k` branches to `targets[k]`, or to `dflt` out of range. -/
  | brTable (targets : List Nat) (dflt : Nat)
  | ret
  | drop
  | unreachable
  /-- The value of the runtime's global `name`. -/
  | globalGet (name : String)
  /-- Set the runtime's global `name` (the stack pointer `$sp`). -/
  | globalSet (name : String)
  /-- Add one to the runtime's count of dispatched calls. -/
  | countInd
  /-- Add one to the runtime's count of copies at a non-trivial type. -/
  | countCopy
  deriving Repr, Inhabited

structure Func where
  name : String
  params : Nat
  /-- The number of `i64` results. -/
  results : Nat
  locals : Nat
  body : List Instr
  export? : Option String := none
  deriving Repr, Inhabited

structure Module where
  funcs : List Func
  /-- The read-only data, at `Flat.dataBase`. -/
  data : Array UInt8 := #[]
  /-- Some function has a frame: the module has a stack (`Backend/Wasm/Runtime.lean`). -/
  stack : Bool := false
  deriving Repr, Inhabited

end Backend.Wasm
