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
`read_byte` and `write_byte`. -/
inductive IOOp where
  /-- `read_byte m`: `(m, inl i32[b])` with the next byte of the stream in the cell `m`, or
  `(m, inr ())` at its end. -/
  | readByte
  /-- `write_byte (m, i32[b])`: the low byte of `b` written to the stream in the cell `m`;
  the result is `m`. -/
  | writeByte
  deriving Repr, DecidableEq

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
  /-- A host operation of §8, applied to its (consumed) argument. -/
  | host (op : HostOp)
  /-- `tab (n, f)`: an array of `len(n)` slots, slot `i` holding `f i` (§9). -/
  | tab
  /-- `idx ((ℓ, n), i)`: `inl` of the `i`-th slot's location when `i < n`, else `inr ()` (§9). -/
  | idx
  /-- `drop (f, (ℓ, n))`: each slot's contents to `f`, in order, then the array freed (§9). -/
  | drop
  /-- A standard I/O operation (§11). -/
  | io (k : IOOp)
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
  deriving Repr, Inhabited

/-- Closure code: on entry the environment record is unpacked into `env` and freed. -/
structure Code where
  env : List Var
  param : Var
  body : Tm
  deriving Repr, Inhabited

structure Prog where
  codes : Array Code
  main : Tm
  deriving Repr, Inhabited

/-- The host operations a term applies. -/
def Tm.hostOps : Tm → List HostOp
  | .prim (.host op) _ => [op]
  | .letv _ e b => e.hostOps ++ b.hostOps
  | .letpair _ _ _ b => b.hostOps
  | .case _ _ b₁ _ b₂ => b₁.hostOps ++ b₂.hostOps
  | .copy _ _ b => b.hostOps
  | .drop _ b => b.hostOps
  | _ => []

/-- The host operations a program applies, each once. -/
def Prog.hostOps (p : Prog) : List HostOp :=
  ((p.codes.toList.map (·.body)).foldr (fun t acc => t.hostOps ++ acc) p.main.hostOps).eraseDups

end Backend.Clos
