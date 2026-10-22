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

/-- The standard I/O operations of SPEC §11 and §34, the host implementations of the externs
`read_byte`, `write_byte`, `write_all`, `read_into`, `clock_now` and `clock_sleep`. -/
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
  /-- `clock_now m`: `(m, t)`, `t` the time of the clock in the cell `m` in nanoseconds, an
  `i64` (SPEC §34). -/
  | clockNow
  /-- `clock_sleep (m, ns)`: wait at least `max(ns, 0)` nanoseconds on the clock in the cell `m`;
  the result is `m` (SPEC §34). -/
  | clockSleep
  deriving Repr, DecidableEq

/-- The lifetime parameters of an operation's extern: the `Λ`s before its argument. -/
def IOOp.lifes : IOOp → Nat
  | .readByte | .writeByte | .clockNow | .clockSleep => 1
  | .writeAll | .readInto => 2

/-- The primitives of `[TR]` §1, §8 and §9, saturated, and the I/O operations of §11. -/
inductive Op where
  /-- `alloc v`: a fresh cell holding `v`. -/
  | alloc
  /-- `free ℓ`: the cell's contents; the cell is freed. -/
  | free
  /-- `alloc v` of a cell the elaborator scopes to one borrow (the lend of a value, `modify` of a
  value, a handler's state given as a value: `Convert.markScoped`), `k` naming the scope. It is
  `alloc`; the flat IR places the cell in a frame slot when the scope's `scopedFree k` is in the
  same code (`Flat/Lower.lean`, `frameScopes`). -/
  | scopedAlloc (k : Nat)
  /-- `free ℓ` of the cell `scopedAlloc k` allocates: `free`. -/
  | scopedFree (k : Nat)
  /-- `alloc v` of a capability's cell (SPEC §11, §34): `alloc`; the flat IR places the cell at
  `addr`, a word of the program's data, and frees nothing. -/
  | staticCell (addr : Nat)
  /-- The address `addr` of a byte of the program's data (a literal's bytes, SPEC §17), an `i32`
  word: a backend places the data (`Flat.Exp.data`). -/
  | dataAddr (addr : Nat)
  /-- `load ℓ`: a copy of the cell's contents. -/
  | load
  /-- `store ℓ v`: the old contents are dropped and `v` stored; the result is `()`. -/
  | store
  /-- `swap ℓ v`: `(ℓ, old)`, the old contents moved out and `v` moved in. It is the axiom
  `swap ≜ λx.λy. let z = load x; store x y; (x, z)` ([TR] 3.24) with its copy of the old contents
  and their drop cancelled; the contents may change type (`Ref A ⊸ B ⊸ Ref B ⊗ A`). -/
  | swap
  /-- `swapSlot ℓ v`: `(ℓ, old)`, the old contents moved out and `v` moved in, at a location whose
  contents keep their type (an array's slot): `array_replace`'s `(λold. store ℓ v; old) (load ℓ)`
  (`Core/Arrays.lean`, `swapCellE`) with its copy of the old contents and their drop cancelled,
  as `swap`'s are. -/
  | swapSlot
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
  /-- `hnd n (hr, cls) body`: a handler of the name `n` (§19), `hr` its answer clause and `cls`
  its operations' clauses. `Capture` lowers it. -/
  | hnd (n : UInt32) (hr cls : Var) (body : Tm)
  /-- `ubind (nn, dd) body`: `body` then `nn`, or the finaliser `dd` when `body` unwinds (§19).
  `Capture` lowers it. -/
  | ubind (nn dd : Var) (body : Tm)
  /-- `perform p`: a control operation of spec §19, `p = (n, (i, v))`, whose continuation is
  captured. `Capture` lowers it. -/
  | perform (p : Var)
  /-- Variant `k` of an `n`-ary sum, its payload `a`: one tag word and the payload. -/
  | con (k n : Nat) (a : Var)
  /-- `when s is k ⇒ x. b else r`: when the `n`-ary sum `s` is variant `k`, `b` with its payload
  bound to `x` (which frees `s`); otherwise `r`, with `s` still owned. A chain of `when`s on one
  `s` is one `switch` on its tag. -/
  | when (s : Var) (k n : Nat) (x : Var) (b r : Tm)
  /-- Unreachable: `s` cannot occur here (a variant no enclosing `when` names, or an error a
  `reraise` cannot raise, since no finaliser raises). -/
  | absurd (s : Var)
  /-- `catch n body`: `inl v` when `body` returns `v`, `inr p` when it raises `p` of the name
  `n`; a raise of another name passes on. `Unwind` lowers it. -/
  | catch (n : UInt32) (body : Tm)
  /-- `fin poll dd body`: `body`; when it unwinds, the finaliser `dd` on `()`, then the raise
  again. When it returns, `dd` is dropped; with `poll`, `body` answers a suspension's outcome
  (`Capture`), and `dd` is dropped only at its `inl`, since a suspension has moved `dd` into its
  state. `Unwind` lowers it. -/
  | fin (poll : Bool) (dd : Var) (body : Tm)
  /-- `catchAll body`: `inl v` when `body` returns `v`, `inr p` when it raises `p` of any name.
  `Unwind` lowers it. -/
  | catchAll (body : Tm)
  /-- `reraise p`: raise the payload `p`, the first error a finaliser raised during a cancel, at
  the canceller. `Unwind` lowers it. -/
  | reraise (p : Var)
  /-- `run f a`: call `f` on `a`, a code that may suspend, and answer its outcome (`inl v`, or
  `inr (payload, κ)`) as a value. `Capture` introduces and lowers it. -/
  | run (f a : Var)
  /-- `await p k`: suspend with the payload `p`, the suspended computation `k` held in the
  state; resumed at `y`, answer `run k (inl y)`. `Capture` introduces and lowers it. -/
  | await (p k : Var)
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
  /-- The scoped cells (`Op.scopedAlloc`) open at a resumption point of their code: their
  address is held in a suspended computation's state (`Capture`, `crossedScopes`). -/
  suspendedScopes : List Nat := []
  /-- `main`'s value is `inl v`, or `inr ()` when a division's error reached it, which ends the
  run with exit status `1` (SPEC §39). -/
  exits : Bool := false
  /-- The control operations, as `(name, operation)`, that `Capture` lowered as direct calls of
  their clause (tail-resumptive). -/
  tailOps : List (UInt32 × UInt32) := []
  /-- The control operations and the abortive operations the program performs, as `(name,
  operation)`: `Capture`'s lowering of each, beside `tailOps`, for the gate's comparison with the
  checker's clause kinds (`bcc-counts --lowering`). -/
  ctlOps : List (UInt32 × UInt32) := []
  abortOps : List (UInt32 × UInt32) := []
  /-- Why each other control operation is not a direct call. -/
  notTail : List ((UInt32 × UInt32) × String) := []
  /-- The codes `Capture` made machines, which answer an outcome: those that may suspend, and the
  handlers' bodies, which answer `inl` alone when they cannot. -/
  machines : Nat := 0
  /-- Of `machines`, those that may suspend. -/
  suspending : Nat := 0
  deriving Repr, Inhabited

/-- The address of the program's data: the Wasm target's, after its runtime's own memory and
before the heap (`Backend/Wasm/Runtime.lean`). It is a detail of that backend, not of the IR
(`Backend.Flat.dataBase`). -/
def dataBase : Nat := 16384

end Backend.Clos
