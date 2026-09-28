import Support.Syntax.Integers

/-!
# Backend — the Wasm AST

The subset of Wasm the backend emits: `i64` locals, one linear memory, `i64` loads and stores,
the integer instructions of §8 (`HostOp`), direct, indirect and tail calls through one function
table, and `block`/`if`/`br`/`br_table`. Functions are named; a function refers to another by
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
  | num (o : HostOp)
  | call (f : String)
  /-- `call_indirect` at the type of `arity` `i64` parameters and an `i64` result. -/
  | callIndirect (arity : Nat)
  | returnCall (f : String)
  | returnCallIndirect (arity : Nat)
  | block (body : List Instr)
  | ifElse (t e : List Instr)
  | br (l : Nat)
  | brTable (ls : List Nat) (d : Nat)
  | ret
  | drop
  | unreachable
  /-- The value of the runtime's global `name`. -/
  | globalGet (name : String)
  /-- Add one to the runtime's count of indirect calls. -/
  | countInd
  deriving Repr, Inhabited

structure Func where
  name : String
  params : Nat
  /-- One `i64` result, or none. -/
  result : Bool
  locals : Nat
  body : List Instr
  export? : Option String := none
  deriving Repr, Inhabited

structure Module where
  funcs : List Func
  /-- The function table, by name. -/
  table : List String
  deriving Repr, Inhabited

end Backend.Wasm
