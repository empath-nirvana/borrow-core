import Std.Data.HashMap
import Backend2.Types

/-!
# Backend2 — the low IR  `[spec §3]`

The low IR (LIR) is named A-normal form over typed variables, with first-order functions and
closures as values:

- **Variables** are numbered uniquely in the program, and each has its `LTy` (`Prog.ty`).
- **Ownership is explicit.** Every variable is consumed exactly once on every path: by an
  operation that takes it, by `drop`, or by being the term's value. `copy x x'` makes `x'` a copy
  of `x`, which stays owned. Closure conversion places copies and drops from the typed term's
  split masks (`Backend2/Convert.lean`), not from occurrences.
- **Functions** (`Fn`) take parameters and answer a value. A closure code's function takes the
  captured values, then its argument when it has one. A closure is `clos c env`: code `c`, its
  captured values moved in. A code is `lam` (it takes an argument: `A ⊸ C`), `unit` (it takes
  none: `F A`, `∀`), or `amp` (a `&`: one function per component, sharing the environment, each
  taking none).
- **Eliminations consume their operand**: `letpair` the pair, `case` the injection, a call the
  closure.

A term's value is its last form's. `letv x e b` names `e`'s value `x` in `b`; `e` may be any term,
a `case` among them, which is then a join.
-/

namespace Backend2
open BoCa

abbrev Var := Nat

/-- The host implementations of the externs that are operations. -/
inductive IOKind where
  | readByte | writeByte | writeAll | readInto | clockNow | clockSleep
  deriving Inhabited, BEq, Repr

/-- A primitive: an operation on its arguments' values that runs no code of the program. -/
inductive Op where
  /-- A host operation (SPEC §8): its argument is the operand, or a pair of operands. -/
  | host (op : HostOp)
  /-- A division whose divisor is a literal at which it cannot fail (`TExpr.divLit`): the
  quotient or remainder itself, with no error arm. The arguments are the dividend and the
  divisor. -/
  | divLit (op : HostOp)
  /-- A fresh cell holding the argument. -/
  | alloc
  /-- A fresh cell holding the argument, allocated for one lend (`TExpr.lendCell`): a frame slot
  when its owner is freed in its function (`Backend2/Frames.lean`). -/
  | allocLent
  /-- The cell's contents; the cell is freed. -/
  | free
  /-- `swap ℓ v`: `(ℓ, old)`, the old contents moved out and `v` moved in. -/
  | swap
  /-- A borrow of the cell or family the argument owns, at the result's mode: `(owner, borrow)`,
  the borrow the owner's address. -/
  | lend
  /-- A reborrow of a borrow: `(borrow, borrow')`, the same address. -/
  | relend
  /-- The contents of the cell a borrow points at, read as the result's type (`Imm̲`): a word at a
  cell, a copy of persistent data, nothing at a closure (`Unk`). -/
  | load
  /-- The contents moved out of the cell a `mut` borrow points at, the cell left unwritten until
  `put`: `(borrow, contents)`. -/
  | take
  /-- `put b v`: `v` moved into the cell `b` points at, unwritten since `take`; the result is `b`. -/
  | put
  /-- `newArr n`: an array of `n` unwritten slots (`n` unsigned). -/
  | newArr
  /-- `tab fi (f, n)` (`array_new`): an array of `n` slots, slot `i` filled with `f i` by the loop
  function `fi`, called on `(f, a, 0, n)`. -/
  | tab (fi : Nat)
  /-- `tab fi (f, n)` where `f` is a closure of the literal tables' code, whose environment is the
  literal's offset in the data and its length `len`, and the array is only read before it is
  destroyed (`Backend2/LitViews.lean`): at `n ≤ len` the array is the literal's bytes in the
  data, and nothing is allocated; else `tab`'s. -/
  | tabLit (fi : Nat)
  /-- `slotPut a i v`: `v` moved into slot `i` of the array `a`, unwritten; the result is `a`. -/
  | slotPut
  /-- `slotTake a i`: slot `i`'s contents moved out, the slot left unwritten: `(a, contents)`. -/
  | slotTake
  /-- The array's base freed, every slot unwritten. -/
  | freeArr
  /-- `size v`: `(v, n)`, the family and its length. -/
  | size
  /-- `len v`: the length of a shared family, which is consumed. -/
  | len
  /-- `idx v i`: `inl` of slot `i`'s leaf when `i < n`, else `inr ()`; `check = false` when the typed
  term proves the index in range (`TExpr.walk`), and there is no test. -/
  | idx (check : Bool)
  /-- `split v i`: `inl (v[0, i), v[i, n))` when `i ≤ n`, else `inr v`. -/
  | split (check : Bool)
  /-- The empty family `(0, 0)`. -/
  | emptyFam
  /-- `replace v i x`: `(v, inl old)` with `x` moved into slot `i` when `i < n`, else
  `(v, inr x)`: a slot swap (#608), no copy and no drop of either value. -/
  | replace
  /-- `swapSlots v i j`: slots `i` and `j` exchanged when both are below `n`; the result is `v`. -/
  | swapSlots
  /-- `μ`'s fold: a value of the unrolling is a value of `μX. A`. -/
  | roll
  /-- `μ`'s unfold. -/
  | unroll
  /-- A byte of a literal's table (`TExpr.litFn`), on `(off, n, i)`: the byte at index `i` of the
  `n` bytes at `off` in the program's data, `0` past the end. One code reads every literal, so the
  tables of a program are one closure class's single code. -/
  | litByte
  /-- The view of a literal's table as a family of bytes in the program's data, when the table
  is the closure of code `c` (`TExpr.litFn`) and the length at most its own: `inl (base, n)`,
  else `inr ()`. -/
  | litView (c : Nat)
  /-- A standard I/O operation (SPEC §11, §34), on its argument. -/
  | io (k : IOKind)
  /-- `len(c)`: `c` when `c < 2³¹`, else `0` (SPEC §9). -/
  | clampLen
  /-- A capability's cell (SPEC §11, §34): the `k`-th static word of the program's data, holding
  the argument. Freeing it frees nothing. -/
  | staticCell (k : Nat)
  deriving Inhabited, BEq, Repr


/-- A closure code's shape. -/
inductive CodeKind where
  /-- `A ⊸ C`: its function takes the argument after the environment. -/
  | lam
  /-- `F A` and `∀'x. C`: its function takes the environment only. -/
  | unit
  /-- `C & D`: one function per component, each taking the environment only. -/
  | amp
  deriving Inhabited, BEq, Repr

inductive Tm where
  | var (x : Var)
  | unit
  | lit (c : IntLit)
  | pair (a b : Var)
  | inj (right : Bool) (a : Var)
  /-- A closure of code `code`, its environment `env` (moved in). -/
  | clos (code : Nat) (env : List Var)
  /-- Call the closure `f` (a `lam` code) on `a`. -/
  | app (f a : Var)
  /-- Run the closure `f` (a `unit` code). -/
  | app0 (f : Var)
  /-- Observe component `j` of the closure `f` (an `amp` code). -/
  | sel (f : Var) (j : Nat)
  /-- Call the function `fn` directly on `args`. -/
  | call (fn : Nat) (args : List Var)
  | prim (op : Op) (args : List Var)
  | letv (x : Var) (e b : Tm)
  /-- `let (x, y) = p; b`, consuming `p`. -/
  | letpair (x y p : Var) (b : Tm)
  /-- `case s {inl x. b₁ | inr y. b₂}`, consuming `s`. -/
  | case (s x : Var) (b₁ : Tm) (y : Var) (b₂ : Tm)
  /-- Unreachable: `s` has type `0`. -/
  | absurd (s : Var)
  /-- `x'` a copy of `x`; `x` stays owned. -/
  | copy (x x' : Var) (b : Tm)
  /-- `x` consumed: its destructor. -/
  | drop (x : Var) (b : Tm)
  deriving Inhabited

/-- A closure code: its kind, its functions (one, or a `&`'s two), the closure type it builds. -/
structure Code where
  kind : CodeKind
  fns : List Nat
  ty : LCTy
  deriving Inhabited

/-- What a function is, for its reader: a closure code's, or a generated helper's. -/
structure Fn where
  name : String
  params : List Var
  body : Tm
  /-- The type of the value it answers. -/
  ret : LTy
  deriving Inhabited

/-- A program: its functions, its codes, `main`'s term and every variable's type. -/
structure Prog where
  fns : Array Fn
  codes : Array Code
  main : Tm
  mainTy : LTy
  ty : Std.HashMap Var LTy
  /-- The literals' bytes, the program's read-only data. -/
  data : Array UInt8 := #[]
  /-- The number of capabilities' static cells (`Op.staticCell`). -/
  statics : Nat := 0
  deriving Inhabited

end Backend2
