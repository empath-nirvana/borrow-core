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
  /-- A fresh cell holding the argument, as wide as the widest of the types `cls` (its width class,
  `Checked.classAt`, SPEC §57; none: the argument's own type). -/
  | alloc (cls : List LTy)
  /-- A fresh cell holding the argument, allocated for the lend of the scope `s` (`TExpr.lendCell`,
  `TExpr.lendScope`): a frame slot when `s` is one of the program's `slots`. -/
  | allocLent (s : Nat) (cls : List LTy)
  /-- The cell's contents; the cell is freed. -/
  | free
  /-- The cell freed, its contents taken (`take`) and not put back: a machine's state cell when
  the machine does not suspend again (SPEC §49). -/
  | release
  /-- `swap ℓ v`: `(ℓ, old)`, the old contents moved out and `v` moved in. -/
  | swap
  /-- A borrow of the cell or family the argument owns, `mut` when `m` (the borrow constant's kind,
  `lendKindB`): `(owner, borrow)`, the borrow the owner's address. -/
  | lend (m : Bool)
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
  /-- `tab fi (f, n)` of a literal's view (`TExpr.litView`, SPEC §57: the array is only read
  before it is destroyed): where `f` is a closure of the literal tables' code (`Prog.lits`), whose
  environment is the literal's offset in the data and its length `len`, and `n ≤ len`, the array
  is the literal's bytes in the data and nothing is allocated; else `tab`'s. -/
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
  /-- `i < n` of a counted loop's index and bound, the bound below `2³¹` (`arrLen`): `inr ()` when
  it holds, else `inl ()`. Both are `i32`s, held zero-extended, so they are compared as words. -/
  | cntLt
  /-- `i + 1` of a counted loop's index below its bound: below `2³¹`, so it does not wrap. -/
  | cntSucc
  /-- `k − 1` of a budget that is not `0` (`bounded_fix`'s count, read unsigned, SPEC §20): it does
  not wrap. -/
  | cntPred
  /-- **The task stack** (SPEC §52). `stackSwap h`: the current stack becomes `h` (`0`: none yet),
  and the one it was is the result; the register is the static word `k`. -/
  | stackSwap (k : Nat)
  /-- `stackFree h`: the stack `h`, empty, freed; nothing at `0`. -/
  | stackFree
  /-- A stack made for the site `s`, with a `κ` region (SPEC §52): its handle. It is not current. -/
  | stackNew (s : Nat)
  /-- `kappaPut h v`: `v` written into the `κ` region of the stack `h` (site `s`), empty before. -/
  | kappaPut (s : Nat)
  /-- `kappaTake h`: `(h, v)`, the contents of the `κ` region of the stack `h` (site `s`) taken out. -/
  | kappaTake (s : Nat)
  /-- A frame of machine `m` reserved on top of the current stack, unwritten; the stack is made
  when there is none (the register `k`). The result is the frame's cell and its address. -/
  | framePush (m k : Nat)
  /-- The top frame of the current stack, a frame of machine `m` (the register `k`): its cell and
  its address. -/
  | frameTop (m k : Nat)
  /-- `framePut f v`: `v` moved into the frame `f`, which stays on the stack. -/
  | framePut
  /-- `framePop f`: the frame `f`, unwritten and on top of the current stack, popped. -/
  | framePop (k : Nat)
  /-- Never reached: the frame below a finished level is at a call of it (SPEC §52). -/
  | unreachable
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

/-- **The rule an `abandon` node is at** (decision 2): a computation that does not return to its
context absorbs it. Not a drop: no destructor runs. `Lint.abandonable` checks each rule's premise:
at a `[let]`'s abort, the abandoned values hold no owned cell (`VTy.OwnFree`, `vC_noOwn_of_ownFree`);
`⊤` has none. -/
inductive Abandon where
  /-- `[let]`'s abort (`CDerives.effLet`'s `hW : S.Weak → Γ₂.Drops`): `N`'s context, at the abort
  branch of the `[let]` or of a frame it pushed. -/
  | letAbort
  /-- `⊤`'s introduction (`CDerives.topI`): the whole context. -/
  | top
  /-- A raise's payload superseded by a finaliser's (`then_fin`, `unwind_prefix`): the payload
  of a raise holds no owned cell (`CDerives.effRaise`'s `hd : o.A.Drop`). -/
  | superseded
  deriving Inhabited, BEq, Repr

def Abandon.name : Abandon → String
  | .letAbort => "let abort"
  | .top => "top"
  | .superseded => "superseded"

/-- **The rule a `drop` node is at**: the kernel rule that discards the value there. `Lint.dropsAt`
checks each rule's premise on the variable's LIR type. -/
inductive DropRule where
  /-- Weakening at an unrestricted type (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`): a leaf's other slots,
  a `use`'s slots it does not read, a handler's values (`effHandleV`'s `DeadP`), a pure frame's
  arguments at an abort, and the machine's own words (a unit, a counter). -/
  | dead
  /-- A `forget` constant applied (`CDerives.forgetImm`, `forgetMut`, `forgetUnk`, `arrForget`):
  a borrow, `Unk`, or a family of `imm` borrows. -/
  | forget
  /-- A piece of the destructor of a `dtor` node's type (`drop_derives` over `dtor_wf`): each leaf
  the type's `HasDtor` derivation forgets, among them a family of `mut` borrows
  (`HasDtor.arrayMut`, whose `dtorAt` is `idx` then `forget`). Only in a destructor function
  (`Prog.dtorFns`). -/
  | dtor
  /-- A live slot of a split's context that neither part's mask holds: weakened
  (`Ctx.DeadP.drop`), at a persistent type, where the kernel weakens it at the leaves of the part
  that receives it. The kernel may instead absorb it (`⊤`, `absurd`); `Lint` refuses such a drop
  at a type that is not persistent. `UNPROVED:` that no checked program has one
  (`Check.SplitMasks.NeitherAbsorbed`). -/
  | unused
  /-- A stack machine's hand-over (`genStackMach`): a level's suspended computation, a closure
  `clos kc [a]` of the machine's code over a frame's address, dropped for `clos kc [base]`, which
  the node's body binds first (`let k₂ = clos kc [base] in …`). `Lint.handsOver` checks that shape
  from the node. `UNPROVED:` that `base` is at or below `a` on the task stack, so that `k₂` takes
  over the frames the dropped `k` stands for (`Backend2.StackKHandOver`; #755 is the route to a
  proof). -/
  | stackK
  deriving Inhabited, BEq, Repr

def DropRule.name : DropRule → String
  | .dead => "dead" | .forget => "forget" | .dtor => "dtor" | .unused => "unused"
  | .stackK => "stack k"

/-- **The rule a `copy` node is at.** `Lint.copiesAt` checks each rule's premise on the LIR type. -/
inductive CopyRule where
  /-- A split that gives an unrestricted slot to both parts (`Ctx.SplitP.dup`). -/
  | dup
  /-- The `copy` or `array_copy` constant applied (`CDerives.copy`, `CDerives.arrCopy`). -/
  | const
  /-- The derived copy of an `imm` borrow or a family of them, where no constant is written
  (`copy_derives` at `DerivedCopy`, `Core/Classes.lean`): `copyE A i e` is a derivation whenever
  `e` is one with both copies live, so a copy at any site is licensed. -/
  | derived
  deriving Inhabited, BEq, Repr

def CopyRule.name : CopyRule → String
  | .dup => "dup" | .const => "const" | .derived => "derived"

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
  /-- `x'` a copy of `x` at the rule `r`; `x` stays owned. -/
  | copy (r : CopyRule) (x x' : Var) (b : Tm)
  /-- `x` consumed at the rule `r`: its destructor. -/
  | drop (r : DropRule) (x : Var) (b : Tm)
  /-- `x` abandoned at the rule `r`, which the typed term applies here (`Abandon`): nothing runs.
  `Lint` admits an opaque value here and at no `drop`. -/
  | abandon (r : Abandon) (x : Var) (b : Tm)
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
  /-- The function is part of its caller's code and is to be inlined at every call, with the
  reason (the native target's `alwaysinline`, checked: SPEC §50). -/
  inline : Option String := none
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
  /-- The static words' cells (the stack register, `Op.stackSwap`): each one's width class (none:
  one word). -/
  statics : Array (List LTy) := #[]
  /-- The literal tables' code (`Op.litByte`). -/
  lits : Option Nat := none
  /-- The lend scopes whose cell is a frame slot (`Op.allocLent`), and each one's owner, the
  variable its `free` releases (`Backend2/Driver.lean`, `slotsOf`). -/
  slots : Std.HashMap Var Nat := {}
  /-- `main` is served `Fail[DivError]` by the platform's handler (`Checked.exitsOnDivError`,
  SPEC §39): its value is `inl v`, whose `v` is reported, or `inr ()`, the exit status `1`. -/
  exits : Bool := false
  /-- The functions that drop a leaf of a `dtor` node's destructor (`Convert.leafDtor`): the only
  functions where `Lint` admits a `drop` at the rule `dtor`. -/
  dtorFns : Std.HashSet Nat := {}
  deriving Inhabited

end Backend2
