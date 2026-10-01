import Support.Syntax.Integers

/-!
# Backend — the closure IR

The first intermediate language. It differs from the erased `Expr` in four ways:

- **Named variables.** Every binder introduces a variable numbered uniquely in the program.
- **A-normal form.** Operands of constructors, primitives and calls are variables; `letv` names
  every intermediate result, so the evaluation order of the source (pairs left to right,
  application argument first) is explicit.
- **Explicit environments.** A `λ` is `clos c xs`: code `c` with the captured variables `xs`
  stored in a fresh environment record. Code refers to nothing outside its environment and
  parameter.
- **Ownership.** Every variable is consumed exactly once on every path. A variable the source
  uses more than once is duplicated by `copy` (a deep copy); a variable a path does not use is
  consumed by `drop` (a deep free). Eliminations consume their operand: `letpair` frees the pair,
  `case` the injection, a call the closure's environment.
-/

namespace Backend.Clos
open BoCa

abbrev Var := Nat

/-- The standard I/O operations of SPEC §11, the host implementations of the externs
`read_byte`, `write_byte`, `write_all` and `read_into`. -/
inductive IOOp where
  /-- `read_byte m`: `(m, inl u8[b])` with the next byte of the stream in the cell `m`, or
  `(m, inr ())` at its end. -/
  | readByte
  /-- `write_byte (m, u8[b])`: the byte `b` written to the stream in the cell `m`; the result is
  `m`. -/
  | writeByte
  /-- `write_all (m, (p, n))`: the `n` bytes of the view at `p` written to the stream in the cell
  `m`; the result is `m`. -/
  | writeAll
  /-- `read_into (m, (p, n))`: bytes of the stream in the cell `m` read into the view at `p` until
  it is full or the stream ends; the result is `(m, ((p, n), k))`, `k` the bytes read. -/
  | readInto
  deriving Repr, DecidableEq

/-- The lifetime parameters of an operation's extern: the `Λ`s before its argument. -/
def IOOp.lifes : IOOp → Nat
  | .readByte | .writeByte => 1
  | .writeAll | .readInto => 2

/-- The primitives of `[TR]` §1, §8 and §9, saturated, and the I/O operations of §11. -/
inductive Op where
  /-- `alloc v`: a fresh cell holding `v`. -/
  | alloc
  /-- `free ℓ`: the cell's contents; the cell is freed. -/
  | free
  /-- `load ℓ`: a copy of the cell's contents. -/
  | load
  /-- `store ℓ v`: the old contents are dropped and `v` stored; the result is `()`. -/
  | store
  /-- `swap ℓ v`: `(ℓ, old)`, the old contents moved out and `v` moved in. It is the axiom
  `swap ≜ λx.λy. let z = load x; store x y; (x, z)` ([TR] 3.24) with its copy of the old contents
  and their drop cancelled; the contents may change type (`Ref A ⊸ B ⊸ Ref B ⊗ A`). -/
  | swap
  /-- A host operation of §8, applied to its (consumed) argument. -/
  | host (op : HostOp)
  /-- `tab (n, f)`: an array of `len(n)` slots, slot `i` holding `f i` (§9). -/
  | tab
  /-- `idx ((ℓ, n), i)`: `inl` of the `i`-th slot's location when `i < n`, else `inr ()` (§9). -/
  | idx
  /-- `split ((ℓ, n), i)`: `inl ((ℓ, i), (ℓ + i, n − i))` when `i ≤ n`, else `inr (ℓ, n)` (§9). -/
  | split
  /-- The base of the empty family `(0, 0)`: a location that holds nothing (§9). -/
  | nullLoc
  /-- `drop (f, (ℓ, n))`: each slot's contents to `f`, in order, then the array freed (§9). -/
  | drop
  /-- `count (f, (n, (i, s)))`: `f` at `i, …, len(n) − 1`, threading `s` (§16). -/
  | count
  /-- `count_try (f, (n, (i, s)))`: `f` at `i, …, len(n) − 1` while it answers `inl` of the next
  state; its first `inr` is the answer, else `inl` of the last state (§16). -/
  | countTry
  /-- A standard I/O operation (§11). -/
  | io (k : IOOp)
  /-- `litByte (a, n, i)`: byte `i` of the literal whose `n` bytes are at `a` in the program's
  read-only data (`Prog.data`), or `0` when `i ≥ n`, unsigned. -/
  | litByte
  /-- `litTab (n, t)`: `tab (n, t)` of a literal's tabulator where the array is only read and
  then dropped (`Convert.litView?`): the array is the literal's own bytes in the read-only data
  when `t` is a literal's closure and `n` its length at most, and `tab`'s array otherwise. -/
  | litTab
  deriving Repr, DecidableEq

inductive Tm where
  | var (x : Var)
  | unit
  | lit (c : IntLit)
  | pair (a b : Var)
  | inj (right : Bool) (a : Var)
  /-- A closure: code `code`, environment the values of `env` (moved into it). -/
  | clos (code : Nat) (env : List Var)
  | prim (op : Op) (args : List Var)
  /-- Call the closure `f` on `a`; the call frees `f`'s environment. -/
  | app (f a : Var)
  | letv (x : Var) (e body : Tm)
  /-- `let (x, y) = p; body`, freeing the pair `p`. -/
  | letpair (x y p : Var) (body : Tm)
  /-- `case s {inl x. b₁ | inr y. b₂}`, freeing the injection `s`. -/
  | case (s x : Var) (b₁ : Tm) (y : Var) (b₂ : Tm)
  /-- `x'` is a deep copy of `x`; `x` stays owned. -/
  | copy (x x' : Var) (body : Tm)
  /-- `x` is deep-freed. -/
  | drop (x : Var) (body : Tm)
  /-- `raise p`: the abortive operation of spec §19, `p = (n, (i, v))`. `Unwind` lowers it. -/
  | raise (p : Var)
  /-- `hnd n (hr, cls) body`: a handler of the name `n` for abortive operations (§19), `hr` its
  answer clause and `cls` its operations' clauses. `Unwind` lowers it. -/
  | hnd (n : UInt32) (hr cls : Var) (body : Tm)
  /-- `ubind (nn, dd) body`: `body` then `nn`, or the finaliser `dd` when `body` unwinds (§19).
  `Unwind` lowers it. -/
  | ubind (nn dd : Var) (body : Tm)
  deriving Repr, Inhabited

/-- Closure code: on entry the environment record is unpacked into `env` and freed. -/
structure Code where
  env : List Var
  param : Var
  body : Tm
  deriving Repr, Inhabited

/-- A fold's shape (`Core/FoldImm.lean`, `FShape`) with its leaves' types erased. -/
inductive FSh where
  | leaf
  | refX
  | varX
  | tensor (F G : FSh)
  | sum (F G : FSh)
  deriving Repr, Inhabited, BEq

/-- `F` has a recursive position. -/
def FSh.hasX : FSh → Bool
  | .leaf => false
  | .refX | .varX => true
  | .tensor F G | .sum F G => F.hasX || G.hasX

/-- A code that is the step of an owned fold, `λu. trav T (λw. self g w) u to r. g r` of
`fold_own` (`reuse = false`) or `fold_reuse` (`reuse = true`) at the shape `shape`. -/
structure FoldCode where
  code : Nat
  reuse : Bool
  shape : FSh
  /-- The position of the algebra `g` in the code's environment. -/
  alg : Nat
  deriving Repr, Inhabited

structure Prog where
  codes : Array Code
  main : Tm
  /-- The owned folds' steps, which the flat IR may compile by pointer reversal. -/
  folds : List FoldCode := []
  /-- For a `main` that returns a loop (SPEC §11): the code run on the value the loop finishes
  with, once the stage has driven it. -/
  fin : Option Nat := none
  /-- The literals' bytes, in read-only data from address `dataBase`. -/
  data : Array UInt8 := #[]
  /-- The code of a literal's tabulator, `λi. litByte (a, n, i)` over its captured `(a, n)`,
  when the program has a literal. -/
  litCode : Option Nat := none
  deriving Repr, Inhabited

/-- The address of the read-only data: after the runtime's own memory, before the heap
(`Backend/Wasm/Runtime.lean`). -/
def dataBase : Nat := 16384

end Backend.Clos
