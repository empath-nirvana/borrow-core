# Backend: the compiler

`bcc` compiles a checked, closed `main` (`Frontend/`) through the closure IR and the flat IR to a
target. The flat IR is target-neutral (`Flat/Syntax.lean`): its operations are SPEC §8's and
§37's, and where its data lives is the target's choice. WebAssembly is one target, compiled to
text and run under `wasmtime`; a native target through LLVM is #529. The input is `main`'s erasure, the untyped BoLo `Expr` that
`Frontend.Check.checkProgram_soundP` derives `CDerivesP` for (`CDerives` at `assurance:
unconditional`, `checkProgram_sound`). The closure IR recovers layout types
from it (`Clos/Types.lean`), and every stage from the flat IR on lays values out by type.

    lake exe bcc compile <file> -o <out.wat>   compile to WAT
    lake exe bcc run <file>                    compile, run under `wasmtime -W tail-call=y`
    lake exe bcc compile --target native <file> -o <out.ll>
                                               compile to LLVM IR for the host (Native)
    lake exe bcc run --native <file>           compile to LLVM IR, build with clang, run
    lake exe bcc interp [--stage S] <file>     interpret stage S: source (default), clos, flat
    lake exe bcc trusted <file>                the program's externs: contracts, host code, levels
    lake exe bcc-counts <file>                 allocations, indirect calls and deep copies of a run
    lake exe bcc-counts --sites <file>         the closure calls: direct, dispatched; recursive types
    scripts/compile-corpus.sh                  the corpus, compiled against the interpreter
    scripts/compile-native.sh                  the corpus, built natively, against the flat IR
    lake exe bcc compile --timings <file> -o <out.wat>
                                               each stage's time and output size, on stderr
    scripts/compile-scaling.sh                 compile time against program size, per stage

Every stage prints the same report: `main`'s value, then `live N`, the number of objects live
after the value has been dropped (`Backend.report`, `Backend/Value.lean`). Values print in
the syntax of `docs/syntax-core.md` (`inl`, `inr`, pairs, `()`, `i32[n]`/`i64[n]` unsigned);
a function prints as `<fun>` and a location as `<loc>`. A `main` whose value is codata (a thunk
of a `nu` type such as `delay`, `stream` or `iter`) prints `<fun>`; the corpus drives such values
inside `main`, as `Core/DelayPrograms.lean` does. Codata needs nothing of its own here: `nu_in`
and `nu_out` erase, and `unfold` is a closed λ-term. A `main` served `Fail[DivError]` by
`main_div_error` (SPEC §39) answers `inl v` or `inr ()`: every stage prints `v`'s report, or, at `inr ()`, the live
count alone and ends with exit status `1` (`Backend.reportExit`; the flat IR's `Stmt.status`, the
runtime's `$exit`).

## Pipeline

| stage | file | what it is | interpreter |
|---|---|---|---|
| source | `Source.lean` | `main`'s erasure | `Support`'s `step` at `wasmHost` (the reference; the canonical NaN) |
| closure IR | `Clos/Syntax.lean`, `Clos/Convert.lean`, `Clos/Poly.lean`, `Clos/Capture.lean`, `Clos/Unwind.lean`, `Clos/Collapse.lean` | named A-normal form, explicit environments and ownership; a let used at different rows per use; §19's handlers, operations and cancels lowered | `Clos/Interp.lean` (at `wasmHostAt .negative`) |
| layout types | `Clos/Types.lean` | a layout type for every closure-IR variable, code and constructor; each type's layout; each closure type's union of codes | — |
| closure flow | `Clos/Flow.lean` | a 0-CFA: the codes each call may call | — |
| flat IR | `Flat/Syntax.lean`, `Flat/Lower.lean` | functions over words, locals, allocation, calls and tail calls of several results, `ite`; target-neutral | `Flat/Interp.lean` (at `wasmHostAt .payload`) |
| Wasm | `Wasm/Syntax.lean`, `Wasm/Lower.lean` | the Wasm subset, as an AST | `wasmtime` |
| WAT | `Wasm/Print.lean`, `Wasm/Runtime.lean` | text; the runtime inserted as written | — |
| LLVM IR | `Native/Lower.lean`, `Native/Runtime.lean` | text from the flat IR, beside the native runtime in C, built by `clang` | — |

All passes are structural recursion (the interpreters take fuel); `Driver.lean` composes them.

**The falsifier** (`Falsify.lean`, `FalsifyTests.lean`; docs/async-capabilities.md §6.1) is a
dynamic check at the source stage, outside the semantics: `bcc interp --alloc least` runs the
erasure under the least-free allocator (a freed location is reused at once), `--check fresh` under
a never-reuse allocator that reports a use after free, and `--check tags` also tags every lend
(the lend combinators of the erasure are marked before the run) and reports an access through an
ended or suspended lend, an aliased access, an owner access while lent, and a lend that never
ends. `scripts/falsify.sh` runs every accepted program the four ways and requires one output and
`live 0`; `bcc kernel negatives` are untyped terms that must trip each check.
No stage optimizes beyond choosing layouts, defunctionalizing closures, calling known codes
directly, compiling `let` as a binding, cancelling the copy and drop inside `swap`, compiling
the Z combinator's fixed point natively, building codata thunks eagerly, merging equal codes,
compiling owned folds by pointer reversal (Stack), placing scoped cells in frame slots and
capability cells in the data (Representation). The WAT printer and the runtime are the only
steps no Lean interpreter observes, and natively the LLVM IR printer, the native runtime and
`clang`.

**Closure conversion** (`Clos/Convert.lean`). De Bruijn indices become variables, and each
intermediate result is named, in the machine's evaluation order: pairs left to right, an
application's argument before its function. A `λ` becomes `clos c xs`, code `c` with its free
variables `xs` captured by value; a β-redex `(λx. b) a`, the erasure's `let`, is `letv x a b`
and makes no closure. A primitive applied to its argument is `prim`; used as a value it is
η-expanded into closure code. The axiom `swap ≜ λx.λy. let z = load x; store x y; (x, z)` is the
primitive `swap`, which moves the old contents out where the axiom copies and then drops them.

Two more shapes are recognized, as `swap` is. **The Z combinator's fixed point**
`selfV B = λv. X X v`, `X = λx. (λself. λx. B) (λv. x x v)` (`Core/Fix.lean`), with `B` closed
under `self` and `x`, is one code `c`, `λx. B[self := clos c []]`: it captures nothing, and
`self` is a closure of its own code, built where it is used (it is never captured, copied or
dropped), so the recursion is a call of `c` by its code index. Applied to an argument,
`selfV B a` is that call, not a `let`. Every fixed point of the core is built this
way: `fold_imm`, `fold_own`, `fold_reuse`, `unfold` (so `ν`, loops, `fixd`, streams and
iterators) and the programs of `Core/`. **η** `λv. y v` of a variable `y` is `y` itself, as
`unfold`'s map at a recursive position forwards the rest of the codata: no closure wraps a closure
of its own type. A term of neither shape is converted as any other λ; the combinator written
some other way (a bare `X X`, as `Core/DelayNaive.lean` does) stays the λ-terms it is.

**Polymorphic lets** (`Clos/Poly.lean`, SPEC §24). A let of a closed λ, `(λx. N) (λy. b)`,
is `[let-poly]`'s: each use of `x` may be at its own row. A code is lowered once, at one
convention, and the closure flow gives it every value any use passes it, so a let whose uses are at
different rows is converted as its β-reduct `N[λy. b / x]` (`polyLets`): each use is a code of its
own, and a use that applies the λ is a `let` of its argument, inlined as a definition is. Which
lets: the program is first converted with every such let used more than once replaced, each use's
λ marked so that the conversion records the codes it makes, and analysed as `Capture` analyses it
(`Prog.effects`). A use's row is, for each of its codes, the operations the code may suspend with
and the keys it may raise, and the same of every closure the code may be given, answer or capture;
the uses of one instance of a let are at one row when these agree code by code. Only the lets
whose uses differ are replaced in the program compiled, so a program whose lets are each used at
one row is converted as written. A self-application `(λx. N) (λx. N)`, the Z combinator's `X X`,
is not a let.

**Handlers and control operations** (`Clos/Capture.lean`, SPEC §19). `Convert` keeps `perform p`,
a handler `hnd n (hr, cls) e` and a finaliser frame `ubind (N, D) M` as closure-IR nodes, and
`Capture` lowers them, as Rust lowers `async`, to state machines, with no handler stack and no
search:

- A finaliser frame is `let r = fin D M in N r`, and a handler of a name with no control
  operation is `catch n e`, then a `case` that calls the answer clause or the caught operation's
  clause: both are then `Unwind`'s.
- A handler of a name with control operations runs its body as a code of its own and *drives*
  its outcome: a value to the answer clause, an operation of its name to that operation's clause
  with `κ`, any other operation outward (forwarding), resuming the body and driving again when
  it is resumed.
- A code that may suspend answers its *outcome*: `inl v`, or `inr (p, k)` with the payload `p`,
  a variant per operation of the program, and `k` the suspended computation, a closure of the
  code's *resume code* over its *state*. The state is an `n`-ary sum, one variant per resumption
  point (a `perform`, a non-tail call of a code that may suspend, a forwarding), holding the
  variables live there and, at a call point, the callee's `k`. So a caller's state contains its
  callee's, and `κ` has a size known statically. At a point the code builds its state and returns
  `inr`, and each frame it suspends through passes the `inr` on.
- The resume code takes `inl y` to resume: a switch on the state, then the point's continuation
  with its frames rebuilt around `y`. It takes `inr ()` to cancel: the callee's `k` first, then
  the point's finalisers, innermost first, every other variable dropped; the first error a
  finaliser raises is kept, and `κ`'s cancel re-raises it at the canceller (`reraise`).
- Which codes may suspend is the least solution of the operations their bodies and callees may
  perform, over the closure flow. Codes called at one site share a convention, and so do a code
  and a code it calls in tail position when the call closes a loop of tail calls or the caller has
  no resumption point of its own; such a tail call passes its callee's outcome on (Stack), and any
  other is a resumption point.
- An operation whose handlers all have one closed clause that resumes `κ` in tail position, and
  neither suspends nor raises, is a direct call of that clause with its resume removed: nothing
  suspends.

**Abortive operations** (`Clos/Unwind.lean`, SPEC §19). `Unwind` lowers `raise p` and the frames
`Capture` leaves (`catch`, `fin`, `catchAll`, `reraise`) to **branch-per-call propagation**, the
representation of Rust's `Result` and `?`:

- A `raise` carries its name and operation as literals (§19's names are static). A code *raises*
  the keys `(n, i)` its body may raise and no frame of it catches: a `raise`'s, those of the codes
  a call may call (the closure flow, below), a `catch n`'s body less its name's keys, and a
  finaliser frame's body and finaliser. The least solution is found by iteration.
- A code that raises answers a sum: `inl v` when it returns `v`, `inr p` when it raises `p`. The
  codes called at one site share a convention: a class with a raising code answers sums.
- A term that may raise is computed as such a sum. `let x = e in b`, `e` raising, is
  `case e {inl x ⇒ b | inr p ⇒ drop (b's variables); inr p}`; a term that cannot raise is not
  touched, so a call branches exactly when its callee may raise, and a tail call passes the sum
  on with no branch. A `catch n` cases on its body's sum (a compare of the name when the body
  raises more than one), and passes any other name on. A finaliser frame runs its finaliser on
  `inr p` and raises `p` again, or the finaliser's own error, which supersedes it.

There is no handler stack and no search: a `raise`'s sum arrives at the `case` of the frame that
catches it. The answering operations of §18 and §19 are calls on a capability, which the
pipeline already compiles as calls, direct when the flow finds one code. The kernel programs
(`Backend/Kernel.lean`, `bcc kernel`) are compiled and run at every stage by
`scripts/compile-kernel.sh`; their counts are `corpus/kernel-counts.expected`, and
`corpus/capture-*-hand.bc` are their hand-written equivalents.

**Codata thunks and equal codes** (`Clos/Collapse.lean`). A loop, stream or iterator is first
the thunk `nu_in ⟨(nu_out (force f s₀)).1, (nu_out (force f s₀)).2⟩` the program builds, and
after its first observation the thunk `unfold`'s map builds, so an observation would see two
codes. The first is replaced by what forcing it computes first when that is a value: `t` itself
when both projections observe the captured `t` (η), or the call `f s₀`, made where the thunk is
built, when the flow analysis finds that `f` is always one code whose body only builds a value
(`unfold step` is `λs. λo. …`). Then codes equal up to their variables' names, of the same layout
type and with captured values of the same types, are merged: `unfold`'s first state
`λo. self g s o` and its map's `λo. self g s′ o` are one code once `self` is native. A code no
closure of which is built (from `main`, transitively) is in no union and is compiled as a stub.

**Layout types** (`Clos/Types.lean`). Unification over the closure IR gives every variable a
layout type `1 | i32 | i64 | u8 | f32 | f64 | A ⊗ B | A ⊕ B | ⊕[A, …] | fn(A; C, D) | loc A` (see Representation).
Value types are monomorphic: a definition is substituted at each use, and polymorphism is over
lifetimes only, whose arguments are `()`; a let-bound λ used at different value types but at one
row is reported (SPEC §24 *Open*). Unification has no occurs check, since `μ` and `ν`
leave regular trees. Two code shapes carry the typing of `&`: a code that cases on its parameter
answers `inl ()` and `inr ()` at its two arms' types, and a call whose argument is a literal
injection is a projection; a code that passes its parameter to a function in tail position (as
`unfold` forwards an observation) has that function's type. A program the unification rejects
is reported, not compiled; the source's typing derivation is what makes the corpus pass.

**Closure flow** (`Clos/Flow.lean`). A monovariant 0-CFA over the whole closure IR: every value
is abstracted by its construction site (a closure by its code, a pair or injection by its
operands, a cell or array by its contents), and the least solution of the inclusion constraints
gives, for every call and for the loop driver, the codes whose closures may reach it. The helpers
that call closures (`tab`, an array's `drop`, the loop driver) are constraints too. Like the layout
types, it reads `&`: a code that cases on its parameter has one answer per arm, a call whose
argument is a literal injection takes that arm's answer only, and a code that forwards its
parameter answers each projection as the function it forwards to does. Without this, every
observation of a thunk would receive what both projections answer, and the sets would grow with
the program. The solver is a worklist indexed by the keys each constraint reads, passing on only
the values a key gains, so its time is about the size of the solution. A call's code
is known when the codes the analysis finds there that are in its type's union are one: each set
over-approximates, so their intersection does.

**Flat IR** (`Flat/Lower.lean`). A value of layout type `A` is `|A|` words: in `|A|` locals,
passed as `|A|` arguments, returned as `|A|` results. Closures are defunctionalized (see
Representation): a closure code is a function of its captured values' words and the argument's
words, returning the answer's words. A call is a direct call of the code when it is known (the
closure type's union has one code, or the flow analysis finds one code of it at the call; the
loop driver's call too), and otherwise a call of the type's dispatcher `apply`, a `switch` on the closure's tag whose cases
tail-call the codes. A call in return position whose callee answers the caller's words is a tail
call. `case` is an `if` on the tag word. Copy, drop, the
printer, the array primitives, the counted loop and the loop driver are flat-IR functions
generated per layout type; host operations are inline. Every local is set once, where it is made,
so a `let` whose value's words are already in locals (a variable, a component, a call's results)
binds its variable to those locals, and moves no word; only words computed there get locals of
their own.

**Wasm** (`Wasm/Lower.lean`). One Wasm function per flat-IR function, `i64` locals, several
results as a multi-value function, tail calls as `return_call`, a `switch` as `br_table` over
nested blocks. There is no function table and no `call_indirect`. `_start` runs the entry, which
prints through WASI `fd_write`. The LLVM counterpart of a multi-value function is a function
returning a struct by value (an `sret` pointer when it is wide), of a flattened pair or closure
union its fields as separate SSA values, of `switch` LLVM's `switch`, and of a tail call a
`musttail` call (decision 25): the native target (Native) is that counterpart.

## Native (LLVM, SPEC §40)

`Native/Lower.lean` prints LLVM IR text from the flat IR, as `Wasm/Lower.lean` builds Wasm from
it: the two are implementations of SPEC, and neither is the other's reference. `bcc run --native`
writes the IR and the runtime (`Native/Runtime.lean`, C) to a temporary directory and builds them
with `clang -O2` (no `opt` or `llc` is needed).

**Functions.** Each flat-IR function is an `internal` LLVM function of the C calling convention
over `i64` parameters. Locals are `alloca`s of the entry block, initialised as the
flat-IR interpreter initialises them (parameters, then `0`), which `mem2reg` promotes; every
expression is computed as an `i64` word in the interpreter's evaluation order, a 32-bit operand
as the word's low half and a 32-bit result zero-extended. `ite` is a branch on the word `≠ 0`,
`switch` LLVM's `switch` on the word, a frame (`Flat.Fn.frame`) one `alloca` of its words: frame
slots are on the native stack, given back by the return or tail call that ends the frame, so the
runtime keeps no stack of its own.

**Tail calls: one prototype per tail-call class, and `musttail`.** A flat-IR tail call passes
the caller's results on, but its callee may take other parameters. Under the C convention LLVM's
`musttail` guarantees a jump when the prototypes match, so the functions joined by tail calls (a
*class*, the components of the tail-call graph, `classArity`) share one: each takes the class's
most parameters, a call passing `poison` for those it lacks, and their results agree already. A
tail call's stack arguments are then the caller's incoming ones, and every call's arguments are
popped by its caller. A `poison` argument is never materialised, so the padding costs nothing
in a class whose parameters fit the argument registers (eight on AArch64); a wider class reserves
stack for its widest member at each call.

The conventions that let prototypes differ, `tailcc` and `swifttailcc`, are not used: under them the callee pops its stack arguments, and Apple clang 21 miscompiles
that on AArch64. At `-O0` a call whose callee tail-calls a function of fewer stack arguments
reloads its spills from a stack pointer the callee has already moved (a function of 21 parameters
that tail-calls one of 3, called twice from a function with locals, faults); at `-O2`, two corpus
programs whose state machines tail-call between functions of 9 and 13 parameters
(`gen-adapters`, `list-generic`) returned to address `0`. Both run at every level from `-O0` to
`-O3` with the shared prototypes (#535).

`bcc tailcalls` runs 10⁸ turns of a loop of tail calls between functions of two and four
parameters, at nine results and at two, on a stack of 64 KiB; `corpus/deep-list.bc` and the
kernel program `loop-tail` run in 64 KiB too (`scripts/compile-native.sh`).

**Several results.** A function of one result returns an `i64`, of two to eight an anonymous
struct of `i64`s by value, which AArch64 returns in `x0`–`x7` (`regResults`: four on x86-64,
in `rax`, `rdx`, `rcx`, `r8`). A wider function returns `void` and writes its results through a
pointer, its first parameter: the caller passes an `alloca` of its entry block, and a tail call
passes its own pointer on, since the callee's results are the caller's. LLVM would itself demote
a wide struct return to a hidden `sret` pointer, but `musttail` forbids that demotion ("the return
type must not undergo automatic conversion to an `sret` pointer"), so the pointer is explicit.

**Addresses.** Words are real pointers (`inttoptr`, `ptrtoint`): there is no linear memory. The
program's data is the global `@bc_data`, and its addresses are the flat IR's `Exp.data off`
(the closure IR's `Op.dataAddr`, a literal's address, and a capability cell's): `@bc_data + off`
natively, `dataBase + off` in Wasm and in the flat-IR interpreter. The data is writable, since a
capability's cell is a word of it; `bc_free` skips an address in it, as Wasm's `$free` skips one
below the heap.

**Host operations, with no undefined behaviour or poison.** Each `HostOp` is emitted as follows
(`Native/Lower.lean`, `hostOp`), with no `nsw`, `nuw`, `exact` or fast-math flag anywhere:

| operation | LLVM | where LLVM is undefined or poison, and why it is not reached |
|---|---|---|
| `add`, `sub`, `mul`, `and`, `or`, `xor` | the instruction | wrapping: no flags |
| `shl`, `shr_s`, `shr_u` | `shl`, `ashr`, `lshr` of the amount `and` 31 or 63 | an amount ≥ the width is poison: masked (SPEC §8) |
| `rotl`, `rotr` | `llvm.fshl`, `llvm.fshr` of `a, a, b` | none: the funnel shifts take the amount modulo the width |
| `div_s` | `sdiv` after a branch to `llvm.trap` when `b = 0` or `a = MIN ∧ b = -1` | both are undefined: the flat IR tests them first (SPEC §39), and the branch makes any other path a trap |
| `div_u`, `rem_u` | `udiv`, `urem` after a branch to `llvm.trap` when `b = 0` | as above |
| `rem_s` | `srem a (b = -1 ? 1 : b)` after a branch to `llvm.trap` when `b = 0` | `MIN srem -1` is undefined, and SPEC's answer is `0`, `x % 1`'s |
| `clz`, `ctz`, `popcnt` | `llvm.ctlz`, `llvm.cttz` with `is_zero_poison = false`, `llvm.ctpop` | zero is the width, not poison |
| `extend8_s`, `extend16_s`, `extend_s`, `extend32_s` | `trunc` then `sext` | none |
| `wrap`, `extend_u`, `wrap8`, `extend8_u` | `and` | none |
| `eqz`, the comparisons | `icmp`, `zext` | none |
| float `add`, `sub`, `mul`, `div` | `fadd`, `fsub`, `fmul`, `fdiv` | none in the default environment (round to nearest); a NaN's payload is unspecified, as SPEC leaves it |
| `min`, `max` | `llvm.minimum`, `llvm.maximum` | none: NaN-propagating, `-0 < +0`, as SPEC (`llvm.minnum` would differ at NaN) |
| `copysign`, `abs`, `neg` | `llvm.copysign`, `llvm.fabs`, `fneg` | none: they act on the bits |
| `sqrt`, `ceil`, `floor`, `trunc`, `nearest` | `llvm.sqrt`, `llvm.ceil`, `llvm.floor`, `llvm.trunc`, `llvm.roundeven` | none (`nearest` is ties-to-even: `llvm.round` would differ) |
| float comparisons | `fcmp oeq`, `une`, `olt`, `ogt`, `ole`, `oge` | none |
| `convert` | `sitofp`, `uitofp` | none |
| `trunc` (partial) | the range test of `Flat.truncRange`, a branch to `llvm.trap` outside it, then `llvm.fpto[su]i.sat` | `fptosi`/`fptoui` out of range is poison: never emitted; the flat IR tests first |
| `trunc_sat` | `llvm.fpto[su]i.sat` | none: NaN is `0` and the rest saturate |
| `demote`, `promote` | `fptrunc`, `fpext` | none |
| `reinterpret` | the word | none |

`bcc hostops flat|native` runs every operation (138, at every width) on a table of operands read
from standard input (so that `clang` cannot fold them): 58 thousand cases, at the flat-IR
interpreter, whose operations are `flatHost`'s (`wasmHost` at a NaN resolution, §37), and natively; `scripts/compile-native.sh`
requires the same text. A partial operation is applied where it has an answer; a NaN that an
arithmetic operation answers prints as `nan`, its payload being unspecified (SPEC §37), and the
operations on bits print theirs.

**The runtime** (`Native/Runtime.lean`, trusted as the Wasm runtime is) is the allocator with the
Wasm runtime's specification and algorithm (a size word before each range, a free list per size
below 1024 words, a bump arena of 1 MiB chunks; a larger range is a `malloc` of its own, and is
given back to `free`), so `live` and `bcc-counts` agree with the flat IR and Wasm; and the POSIX
platform: `read(2)`/`write(2)` on the descriptors, unbuffered as WASI's are, `SIGPIPE` ignored so
a write's error is dropped as Wasm's is; the arguments' stream from `argv` (counted as one
allocation at its first read, as `$args`); `clock_gettime(CLOCK_MONOTONIC)` and `nanosleep`; the
exit status `bc_status` sets, returned from `main` once the entry returns. `main` runs the entry
on a thread of a 512 MiB stack (`BC_STACK` sets another), past Wasm's 64 MiB, so the recursions
calibrated against Wasm (`bounded`'s budget, `fold_imm`) run natively; overflow is not detected
(SPEC §40 *Open*).

**Checked.** `scripts/compile-native.sh`, a step of the gate (skipped with a notice when `clang`
is not installed): every corpus program built natively prints its golden standard output and
standard error and exits with its golden status, which `compile-corpus.sh` checks the flat IR
against; `bcc-counts --native` requires the native build's counts to equal the flat IR's; every
kernel program prints at native what it prints at the flat IR; `bcc hostops`; and the tail-call
runs above.

## Representation

A value's layout is chosen by its layout type (`Clos/Types.lean`, `Flat/Lower.lean`). Every
word is an `i64` local; `|A|` is the number of words of `A`.

| layout type | words | layout |
|---|---|---|
| `1` | 0 | nothing |
| `i32`, `i64`, `u8` | 1 | the integer (an `i32` or a `u8` zero-extended) |
| `f32`, `f64` | 1 | the float's bits (an `f32`'s zero-extended); a float operation reinterprets its operands as `f32`/`f64` and its result back (`Wasm/Lower.lean`), and is the target's float instruction alone: a NaN result's sign and payload are the target's (SPEC §37) |
| `A ⊗ B` | `\|A\| + \|B\|` | `A`'s words, then `B`'s |
| `A ⊕ B` | `1 + max \|A\| \|B\|` | a tag word (`0` for `inl`), then the payload's words, padded |
| `⊕[A₀, …, Aₙ₋₁]` | `1 + maxᵢ \|Aᵢ\|` | a tag word `i`, then variant `i`'s payload's words, padded: a suspended computation's state, an operation's payload |
| `loc A` | 1 | the address of the cell's contents |
| `fn(A; C, D)` | `1 + max_c \|env c\|` | a closure: its code's tag in the type's union, then the captured values' words, padded |
| `fn(A; C, D)`, recursive | 1 | a closure: the word `2t + 1`, or the address of a heap environment object |

So a pair is never an object, a `bool` (`1 + 1`) is one tag word, `1 + A` is a tag and `A`, an
`i64` is unboxed, a closure is a tag and its captured values, and none of these allocates.

**Closures are defunctionalized** (Reynolds). The codes whose type unifies with a closure type
`fn(A; C, D)` are that type's *union*, numbered (tagged) in code order; `Clos/Types.lean` groups
them by the closure IR's inferred types. A closure is a stack value: its tag, then its captured
values' words, padded to the union's widest environment. Building it moves the captured words
in; calling it moves them into the code's parameters. A known call is a direct call; any other
call goes through the type's dispatcher, one `switch` per type. A union that contains itself
(a closure type on a cycle of the graph whose edges are pair and sum fields and a union's
captured values' types) would be infinitely wide, and under the explicit-heap rule (#54) the
source would say `box` there; the source language cannot yet, so such a *recursive closure
type* keeps the heap representation: the word `2t + 1` for a code `t` that captures nothing,
and otherwise an object holding `t` and the captured values' words.

The only objects are:

- **Cells.** `alloc v` allocates the cell's contents, `max 1 w` words with no header, where `w`
  is the widest contents its *cell class* holds: `swap` changes a cell's type
  (`Ref A ⊸ B ⊸ Ref B ⊗ A`), so the locations that may be one cell are a class, and a cell is as
  wide as its class needs. A cell whose class takes no words (every contents it holds is `1`, or
  a closure capturing nothing) allocates nothing: its address is `0`, it is never read or written,
  and `free` frees nothing (`zeroCell`). So `main`'s lifetime, a borrow of a unit cell (SPEC
  §23), costs nothing.
- **Arrays** (SPEC §9). One allocation of `n·s` words, `s` the class width of the element
  type: element `i`'s location is `base + 8·s·i`, a cell address like any other. The array value
  is the pair `(base, n)`, two words. `idx` is an unsigned compare and an address computation,
  and allocates nothing. An array whose slots are bytes (a cell class that holds only `u8`,
  `Types.byteCell`) has one byte per slot, at `base + i`, in `⌈n/8⌉` words, read and written by
  `load8_u`/`store8` (`loadCell`, `storeCell`); every access to a location of that class is a
  byte access, so a cell of the class is one byte too. An empty array, or one whose slots take
  no words, allocates nothing: its base is `0`, and `drop` frees nothing. `split` on a
  borrowed family `(p, n)` at `i` is an unsigned compare and `(p, i)`, `(p + s·i, n − i)`, with
  no allocation; the empty family `slice_empty_*` is `(0, 0)`, its base the null word (the
  source term's location `0`, which the closure IR's interpreter never allocates).
- **Closures of a recursive closure type that capture.** An object: the tag `t`, then the
  captured values' words. A code that captures nothing is the word `2t + 1` (objects are
  8-aligned, so bit 0 tells the two apart) and allocates nothing. A code of such a type keeps the
  object it is called with until it returns, and builds the first closure of the same width in
  it, in place; a path that builds none frees it. So a suspended computation that holds its own
  continuation (recursion through a resumption point, SPEC §19) has one object per level, updated
  each time the level is resumed and suspends again, as a pinned `async` frame is.
- **Boxed fields.** A recursive type would be infinitely wide, so the fields that close a cycle
  of pair and sum edges (the back edges of one depth-first search over the types) are stored as
  a pointer to an object of the field's own layout. `μX. 1 + (A ⊗ X)` is a tag and a payload
  `A ⊗ X` whose `X` is a pointer: `nil` allocates nothing, each `cons` one object. Where the
  search boxes two fields or more of one cycle, a sum's payload is boxed instead when that boxes
  fewer (`Clos/Types.lean`, `sumBoxes`): a tree `μX. 1 + X ⊗ (A ⊗ X)` is a tag and a pointer to
  an object holding the node, its two children inline, so a node is one object and an empty
  child none, as Rust's `Option<Box<Node>>` (two objects a node, the empty children's among them,
  when each child is boxed).

Not objects:

- **Scoped cells** (SPEC §35). The cell a lend of a value (`f(&x)`, `f(&mut x)`), a `modify` of a
  value or a handler's state given as a value (`with h(e) { … }`) borrows lives exactly as long
  as the borrow: the erasure is `let (c, r) = withbor (alloc v) cb; … free c …`, which the
  conversion recognises (`Clos/Convert.lean`, `markScoped`) and marks (`scopedAlloc`,
  `scopedFree`, which every stage runs as `alloc` and `free`). When no resumption point lies
  between the two (`Clos/Capture.lean`, `crossedScopes`), the cell is a slot of its code's frame
  on the stack (`Flat.Exp.slot`, `Flat/Lower.lean`, `frameScopes`), as C and Rust place a local
  whose address is taken: no allocation and no live range. A scope a suspension crosses keeps a
  heap cell, since the suspended state holds its address; typing excludes it today (a
  continuation held across a lend is T1, #172), so no program has one.
- **Capability cells.** `stdin`, `stdout`, `stderr`, `args` and `clock` are words of the
  program's data, after its literals (`Clos/Convert.lean`, `staticWord`; `Op.staticCell`):
  the prologue stores the descriptor there, and the epilogue's `free` frees nothing.

- **Literals** (SPEC §17). A string literal's tabulator, the λ the elaborator writes for `"…"`
  (a compare with the length, then a search on the index down to one byte), is recognised by
  its shape (`Clos/Convert.lean`, `litTable?`) and converted to a closure of one shared code,
  `litCode`, capturing the address and length of the literal's bytes; its body is `litByte`, a
  compare and a byte load. The bytes are the program's read-only data (`Prog.data`), each literal
  once, at `dataBase`; the heap starts past them. Where that data lives is the target's choice
  (`Flat/Syntax.lean`, `dataBase`): the Wasm target's is a data segment from `16384`. A literal is then two
  words and no object, and every literal is one code, so a call of one is direct. A literal
  view's array (the borrow block on a literal: `tab` of the literal, lent to a callback that
  first copies the family, then dropped; `litView?`) is `litTab`: `(address, n)` in the data when
  the tabulator is `litCode`'s closure and `n` at most the literal's length, with nothing
  allocated, and `tab` otherwise. `$free` skips an address below the heap.

The printer is generated per type and writes the text of `Backend.PV.render`: the type says
whether a word is an integer, a tag, a closure (`<fun>`) or a location (`<loc>`).

`fn(A; C, D)` answers `C` to `inl ()` and `D` to `inr ()`: a thunk of `C & D` is one closure
answering two projections at two types. Its code returns `max |C| |D|` words, the arm's own
words then zeros; a projection's caller takes the first `|C|` or `|D|`.

**Open.** With fixed points native, a recursive closure type is one the program builds as
data: a closure that captures a closure of its own type, as a fold whose result is a function
does (`add` of `13-2-sum-prog` and `sum-prog-exact`, one type). `bcc-counts --sites` lists
them. They keep the heap
representation until the source can say `box` (#54). Placement of the objects that remain
(stack, frame arena or heap, by escape analysis) is also open; the scoped cells' frame slots are
the one placement made, by the elaborator's scope, not by an analysis.

The dispatched calls that remain are calls of those closures: a chain of functions built by
a fold, whose links are different codes (`13-2-sum-prog`'s and `sum-prog-exact`'s `add`).
Every other call of the corpus is direct.

## Stack

A call is a tail call (`return_call`; LLVM `musttail`) when it is in return position and its
callee answers the caller's words. What runs in constant stack:

- **Loops.** Every `ν`-type program, `unfold`, `fixd`, `div_bind` and the `for` loop: an
  observation runs the step once and returns the next state inside the rest, so the depth does
  not grow with the number of observations. The loop driver (`drive`) calls the loop and then
  tail-calls itself.
- **Counted loops.** `count_fold` (SPEC §16) is a generated loop of tail calls (`count_loop`),
  one call of the step per count, allocating nothing; `div_fuel` is one.
  A left fold is written as a loop whose state is the rest of the structure and the accumulator
  (`corpus/deep-list.bc`); this is the only left-fold shape the core has.
- **A self-call in tail position**, of the native fixed point: its code is known, so the call is
  a direct tail call of the code itself.
- **Loops through a suspension** (SPEC §19). A tail call that closes a loop of tail calls passes
  its callee's outcome on, so a loop that performs an operation at each turn stays a loop of tail
  calls. An operation whose clause resumes in tail position is a direct call (`loop-tail`: 100000
  operations); when the clause captures values it is not, and the handler's driver, clause and
  resume closure tail-call one another, in constant stack (`loop-captured`).
- **Arrays.** `tab` and an array's `drop` are loops of tail calls.
- **Owned folds by pointer reversal** (Deutsch–Schorr–Waite). The step of `fold_own` or
  `fold_reuse` (`λu. trav T (λw. self g w) u to r. g r`, recognized as the conversion recognizes
  the fixed point) is compiled as two loops of tail calls (`Flat/Lower.lean`, `foldDown`,
  `foldUp`) when the shape `T` is linear (a `⊗` has a recursive position on at most one side,
  so lists and unary numbers are) and the node reaches its child through one pointer: the boxed
  field at `X`, or the cell at `Ref X`. The descent stores each node's words in its child's
  object, with the pointer to the child replaced by the pointer to the node's own object (`0`
  at the root), and goes on with the child; at a node with no child it calls the algebra `g`.
  The ascent loads each stored node back, calls `g` on it with the child's result at the
  recursive position, and frees the object (`fold_own`) or hands it to `g` as the emptied cell
  `Ref 1` (`fold_reuse`). The child's object is exactly as wide as a node, so nothing is
  allocated. It is safe because the fold owns the structure linearly: while the pointers are
  reversed, no other word can reach it. Every owned fold of the corpus qualifies
  (`bcc-counts --sites`, `owned-folds reversed`).

What does not:

- **`fold_imm`** keeps a native frame per level of the structure: it traverses borrowed data,
  whose pointers it cannot reverse. Under wasmtime's default stack a list of about 2500
  elements is the limit. A heap-allocated stack of the pending nodes, or a left-fold (loop)
  reformulation where the algebra allows, would remove it.
- **Owned folds over non-linear shapes** (trees, with a recursive position on both sides of a
  `⊗`) or whose child is reached through more than one pointer recurse natively. Pointer
  reversal extends to them with a mark per node saying which child is being visited, and room
  in the node for the results of the children already folded; the objects are not always wide
  enough for those results, so it is not done.

## Memory discipline

Source values are trees whose only shared parts are locations. The compiled program keeps every
object owned by exactly one word, so it can free an object where the source stops using it. At
typed layouts:

- **Eliminations free.** `let (x, y) = p` and `case` bind the components' or payload's words
  (and load and free a boxed field); calling a closure moves its captured words into the
  code's parameters (at a recursive closure type, the code unpacks the environment object into
  locals and frees it). A pair, an injection, an integer, a closure union and a word `2t + 1` hold
  no object of their own, so there is nothing else to free.
- **Duplication copies.** A variable used by two sequential parts of a term (the halves of a
  pair, the argument and function of an application, a `let`'s bound term and body, a `case`'s
  scrutinee and arms) is copied for all but the last. The two arms of a `case` are one part:
  only one runs. At a *trivial* type the copy is the words themselves; otherwise it is the
  type's generated copy, which allocates a new object for each boxed field and heap environment
  it meets (`bcc-counts` counts these copies; at the surface, a use that makes one at a type
  holding recursive data is written `clone(x)`, SPEC §10). A type is trivial when it has no
  boxed field, no recursive closure type, and no
  closure whose code captures a non-trivial value. A closure is copied by a `switch` on its tag
  that copies that code's captured values; so a closure whose captures are all trivial, as a `!`
  closure's persistent captures are unless they hold a boxed field or a recursive closure, is
  copied as plain words.
- **Discarding drops.** A variable that a path does not use is dropped where its scope starts
  on that path: an unused binder, or in a `case` arm, what only the other arm uses. At a
  trivial type a drop is nothing; otherwise the type's generated drop frees each heap
  environment and boxed field, a closure's by a `switch` on its tag.
- **Cells.** `alloc v` allocates a cell holding `v`'s words; `load` copies the contents (the
  source copies the value out); `store` drops the old contents; `free` moves them out and frees
  the cell; `swap` moves the old contents out and the new in. A copy copies a location as a
  word, and a drop leaves cells alone: cells are freed only by `free`. So a location to a freed
  cell may still be held, copied and dropped (a finaliser frees a cell a dropped closure still
  names); the closure-IR interpreter records the freed cells, and any other address that is not
  live is a fault.

So each variable is consumed exactly once on every path, as substitution does in the source;
the closure-IR interpreter, which keeps the uniform boxed objects, checks this as it runs, and the
flat IR follows the same consumption at typed layouts. For a closure union: the captured words
after its tag are owned by that union value alone, and the padding words own nothing; building
moves the captures in, a call moves them out to the code (so a linear closure's captures are
moved, never shared), a copy copies them by the tag, and a drop drops them by the tag. Persistent types (SPEC §10) hold no
resource, so copying a persistent value copies no resource. After `main`'s value is printed and
dropped, the live count is 0 exactly when the source run ends with empty memory.

## The allocator (trusted)

The allocator is WAT, in `Wasm/Runtime.lean`. Its specification is the hypothesis every stage
from the flat IR on relies on:

1. `alloc n`, for `n ≥ 1`, returns an 8-aligned address `a` such that the range
   `[a, a + 8n)` is disjoint from every live range and from memory the program does not own;
   the range becomes live. Its contents are unspecified.
2. `free a`, for `a` returned by `alloc` and not freed since, ends that range's life.
3. `live` is the number of live ranges.

The flat-IR interpreter implements exactly this (and never reuses an address, so it reports a
load, store or free outside a live range). The WAT implementation keeps one free list per size
below 1024 words and bumps a heap pointer otherwise, growing memory as needed; each range is
preceded by a word holding its size, and the runtime's own data sits below address 16384.
A module with frames has a stack of 1 MiB between the program's data and the heap, growing down;
`$sp` is its pointer, lowered by a function's frame on entry and raised back before each return
and tail call (`Wasm/Lower.lean`, `lowerFn`), with a trap past its end. Frame slots are no
ranges: `live` does not count them, and the flat-IR interpreter gives each call fresh frame
addresses and checks every access to a slot against the slot's scope and its frame's call.
`live` is exported as `live_objects`; `$putc` writes a byte to standard output, `$putfd` a byte to a
descriptor and `$getc` reads one (SPEC §11). `$allocs` counts the calls of `$alloc` and `$indirect`
the dispatched calls, which the compiled code counts when it is built to count.

## Host operations (SPEC §8)

A literal is a constant word. Each host operation is inline: the target's instruction for it on
the operands' words (`Flat/Lower.lean`, `hostVals`; in Wasm the instruction it is named after). Tests produce `inr ()` for true and `inl ()` for
false, the tag word `1` or `0`. A partial operation is checked before the instruction runs: a
zero divisor, or `INT_MIN / -1` for `div_s`, produces `inr ()`, anything else `inl n`. A division
by a local the function sets to a constant at which it has an answer has no check, and a `case` on a
division's answer is the division's own test (`divTest`, SPEC §39). The flat-IR interpreter
evaluates the operations with `flatHost`, `wasmHost` but for the NaN an arithmetic float
operation answers (payload `1`), and the closure-IR interpreter with `closHost` (the negative
NaN), so the compiled stages agree with the source on every result SPEC fixes by construction,
and a program whose output depends on a NaN's sign or payload differs from its golden at one of
them (SPEC §37, *Engines*). Wasm agreeing with `wasmHost` is tested, not proved (SPEC §8).

## Standard I/O (SPEC §11)

A `main` may declare the standard externs (`Frontend/Check/Externs.lean`): the capabilities
`stdin`, `stdout`, `stderr` (`ref input`, `ref output`) and the operations `read_byte`,
`write_byte`, `write_all`, `read_into`. Its type is then `F (Caps ⊗ A)`, handing the capabilities back after `A`, or
`F (U (loop (Caps ⊗ A) (Caps ⊗ B)))` for a program that runs until its input ends.

- **Compiled stages.** `Clos.convertMain` binds each extern before `main` runs: a capability to a
  cell holding its file descriptor (`i32[0]`, `[1]`, `[2]`), a word of the program's data
  (Representation), an operation to the closure
  `Λ. λm. op m` over the closure-IR primitive `io readByte`/`io writeByte`. An extern `main` does
  not use is dropped. After `main`, its result `(caps, a)` is taken apart, each capability cell
  freed, and `a` is the program's value. In the flat IR the operations are inline, over the
  statements `getc fd` and `putc fd b`, and `read_byte`'s answer `(m, inl b)` or `(m, inr ())` is
  three words; in Wasm those statements are `$getc` and `$putfd`, WASI `fd_read` and `fd_write`
  of one byte. `write_all` and `read_into` (`Λ. Λ. λp. op p`) take a byte view `(p, n)`: the
  flat IR's `putv fd p n` and `getv fd p n`, in Wasm `$putv` (`fd_write` of the `n` bytes, again
  after a short write) and `$getv` (`fd_read` into them until they are full or a read answers
  nothing, answering the count). They are unbuffered, so a
  prompt is out before the next read. The plain LLVM/libc counterpart is `read(2)`/`write(2)`
  on the same descriptors; nothing WASI-specific is part of the semantics.
- **The clock and the arguments (SPEC §34).** `clock` is a cell holding the model's time
  (`i64[0]`, nanoseconds), and `clock_now`/`clock_sleep` are the closure-IR primitives `io clockNow` and
  `io clockSleep`: in the flat IR the expression `now c` and the statement `sleep c ns`, which the
  flat-IR interpreter runs on the cell (the model: a sleep adds `max(ns, 0)`, saturating at `2^63 − 1`), and
  Wasm as `$now` (`clock_time_get` of the monotonic clock, in nanoseconds since the clock's first
  use) and `$sleep` (`poll_oneoff` on one relative clock subscription). `args` is a cell holding
  the stream `0xFFFFFFFF`, which `$getc` and `$getv` read from the arguments `$args` reads once
  (`args_sizes_get`, `args_get`) into memory `$reserve` takes from the top of the heap: no object,
  never freed, and counted as one allocation (the flat-IR interpreter counts it at the first
  read of `args` too). The interpreters read it from the arguments they are given (`bcc interp … --
  arg…`). The libc counterparts are `clock_gettime`, `nanosleep` and `argv`.
- **Loops.** When `main` returns a loop, every stage drives it: it calls the loop on `inl ()`
  until the answer is `inl r` (the source stage by `driveSource`, the closure IR by its `drive`,
  the flat IR by a `drive` function generated at the loop's type), then runs the epilogue on `r`, which the closure
  conversion registers as the code `fin`. The source stage's run that finishes after `k`
  observations is the run of `driveE k`, the program `IORun.loop_every_run` covers.
- **The source stage** runs the model: the checker's `run_io` wrapper, with every extern given
  its Lean model (`IORun`), applied to standard input as a byte list, from the empty memory. Its
  value holds the bytes written to each stream; the stage writes them, then the report of
  `main`'s result. This is the term `IORun.every_run` (`io_every_run`) is about. It reads all of
  standard input before it runs, and holds it as a byte list in a cell, which each read copies:
  it is a reference, quadratic in the input.
- **The interpreters** `clos` and `flat` read a scripted standard input and collect the two
  output streams; the flat IR's checks (every read and write inside a live range) cover the I/O
  runtime functions too. That is the host implementations' assurance: interpreter-checked (2),
  and agreement with the model on the corpus.

Every stage writes the program's standard output, then the report, to standard output, and the
program's standard error to standard error. `scripts/compile-corpus.sh` compares both with a
program's golden `corpus/<name>.out` and `.err`, on `corpus/<name>.in`.

## Counts

`bcc-counts <file>` runs the program at the flat IR and under `wasmtime`, each built to count
(`Driver.flatOf`, `compileWat` with `counts`: the entry writes `allocs N`, `indirect M` and
`copies K` after the report), and prints the objects the run allocates, the indirect calls it
makes and the deep copies it makes; the two stages must agree. An indirect call is a dispatched
one: a call of a type's `apply`, whose code the `switch` on the tag chooses at run time. There is
no other kind of indirect call. A deep copy is a `copy` of the closure IR (Memory discipline: a
variable used by two sequential parts) at a non-trivial type, which calls the type's generated
copy; a copy at a trivial type is the words themselves and is not counted. `scripts/compile-corpus.sh` checks every corpus program's counts against
`corpus/counts.expected`: a count above the file fails the gate, one below it is reported, and
`--write-counts` rewrites the file. A pure arithmetic program (`int-arith`, `int-ops`) allocates
nothing and makes no indirect call; frame slots and capability cells are not counted (they are no
allocation); what remains is cells, arrays, boxed recursive fields (a
list's nodes), and the heap environments of the few recursive closure types (Open), whose calls
are the only dispatched ones. `bcc-counts --native <file>` runs the native build (Native) in place of `wasmtime`, and requires
the same counts and exit status as the flat IR. `bcc-counts --sites <file>` prints the program's closure calls: how
many are direct because the union has one code, how many more because the flow analysis finds
one, how many are dispatched; the recursive closure types; the owned folds, how many are
compiled by pointer reversal and how many recurse; and the scoped cells, how many are frame
slots and how many are allocated.

## Verification (#15)

The semantic theorems do not change: layout is below the model, whose values are terms. What
changes is the refinement a compiler proof (#15) would establish between the stages. The flat
IR's runtime invariants are now layout-aware:

- a closure-IR variable of layout type `A` corresponds to `|A|` flat-IR words, related to the
  closure IR's boxed object graph by `A`'s layout (a pair by its components' words, an injection
  by its tag and padded payload, a boxed field by an object of the field's layout, a closure by
  its code's tag in the union and its captured values' words, related to the environment
  object's fields, or at a recursive closure type by `2t + 1` or an environment object);
- the words of every live object are written (`Flat/Interp.lean` checks every read), and a cell
  is as wide as its class;
- a call's results match the callee's signature, which the flat-IR interpreter checks, and
  Wasm validation checks for every direct call and tail call;
- the layout types are an obligation of their own: the closure IR must be typable, which the
  source's `CDerives` derivation should give for everything but the axioms' bodies (`swap`,
  whose contents change type, is why cell classes exist).

The ownership invariant (each object owned by exactly one word, consumed once per path) is the
same as before, restated over typed words and closure unions (Memory discipline).

**Defunctionalization** is a compiler obligation of its own: calling a closure through its type's
`apply` behaves as calling it through its code. The standard proof (Reynolds; Danvy and
Nielsen, *Defunctionalization at work*; Pottier and Gauthier's typed version) is a simulation
relating a closure to the tag and captured values of its code, and `apply`'s case to that code's
body. Here it needs, besides the layout typing above, that a closure's union contains its code
(every closure of a type is built by a code of that type, which unification gives), and the
word relation of a recursive closure type. A direct call adds the flow analysis's soundness: the
0-CFA's solution over-approximates the codes that reach every call, including the calls the
helpers and the entry make, so a call where it finds one code calls that code on every run.
Nothing checks the solution at run time; a proof would show that the abstraction of every run's
values is included in it.

**Collapsing and merging.** Merging codes equal up to renaming needs nothing: a closure of one
is a closure of the other with the same captured values. Building a codata thunk eagerly needs
that the call made early, `f s₀` of a known code whose body only builds a value, cannot fail and
reads or writes no memory but that value, so it commutes with everything between the thunk's
construction and its first observation; the thunk's captures are consumed by it as either
projection would consume them, and a thunk that is dropped unobserved drops the same values
(the call's result holds them). η of a thunk of `&` for a variable is the same step as η above.
Removing unbuilt codes from the unions needs the reachability argument (a closure is built only
by a `clos` of a code whose closure is built, or by `main`).

**State machines** (`Clos/Capture.lean`) are an obligation of their own: a code's outcome
simulates the source's run of its body to a value or to a stop `K[perform (n, v)]`, the state
relating to `K` frame by frame (its variant to the point, its fields to the values `K`'s frames
hold, its callee's `k` to the inner frames), and the resume code's entry at `y` to `K[y]`; its
cancel entry simulates the cancel run of the dead region, `K†[raise (⊥, err)]` to `ccatch`: the
cancel arms run only the points' `fin` frames, which are the finaliser frames `K†` keeps. The
handler's driver simulates `[ret]`, `[op]` and forwarding. Nothing checks these at run time beyond
the interpreters agreeing.

**Polymorphic lets** need nothing of their own: the program converted is the source one β-step
later at each let replaced (`letPoly_compatC`'s step), which neither allocates nor touches the
heap; a use's copy of the λ is a closure of a code of its own, or a `let` where it is applied.

**Native fixed points** are an obligation of their own: the code `λx. B[self := clos c []]`
simulates the combinator's `selfV B`. The source side is `Core/Fix.lean`'s unrolling
(`selfV_steps_in`: `selfV w` reaches `fixV w = B[selfV/self][w/x]` by three pure β-steps, in any
evaluation context), so the simulation relates `selfV B` to `clos c []` and a call of `c` on `w`
to those three steps and `fixV w`; the closure IR skips the steps, which neither allocate nor
touch the heap. η for a variable (`λv. y v` is `y`) is the same kind of step: calling the wrapper
is one β-step and then calling `y`. The ownership invariant is unchanged: `self` captures nothing,
so its copies are its tag word.

**Pointer reversal** needs the classic separation-logic proof of Deutsch–Schorr–Waite (Yang,
*Verifying the Schorr–Waite algorithm*; Bornat; Mehta and Nipkow), here for a linear shape: the
invariant is that the objects on the reversed path, each holding its node's words with the child
pointer replaced by the parent's, together with the current node, form the original structure
with the path's pointers reversed, disjoint from everything else. The fold's ownership of the
structure gives the disjointness; the algebra is called on the same arguments, in the same
order, as the recursive step calls it, so the refinement is to the recursive code. The flat-IR
interpreter checks every load and store of the reversal against the live ranges.

## Compile time (#122)

`bcc compile --timings` writes each stage's time and output size, and times the flow analysis
and the layout types on their own on the program each stage receives. `scripts/compile-scaling.sh`
compiles programs of 1, 2, 4, 8 and 16 copies of a corpus-like body (functions of loops over
generators and adapters, `imm` and `mut` borrows, and per copy a loop and calls in `main`) and
fits each stage's growth; with `--guard` it is a step of the gate, which fails when the 8× program
takes more than 16 times the 1× program's time.

Every backend pass grows about linearly on that benchmark (fitted exponents 1.0 to 1.25 from 1×
to 32×; the time per step of the flow analysis grows as its tables outgrow the caches): the
closure conversion computes every subterm's free indices once, bottom-up, and keeps its context
in a map by level; the flow analysis's worklist passes each value along each edge once, and its
sets stay the size of the program because it reads `&` (above); collapsing's last round of code
merging finds the layout types of its result, which the flat IR reuses.

**Known slow shapes.** These are superlinear and are left so:

- *One body with many resumption points.* A generator or div body is one state machine (SPEC
  §15) whose state is a sum with one summand per point, nested to the right. Each summand
  adds a tag word to the state's width, and a transition to point `k` builds `k` nested
  injections, so the source's and the closure IR's size, the state's width and the words each
  transition passes are all proportional to the number of points: a body of `P` points costs
  about `P²`. A `main` of 160 points (loops and direct-style div calls) compiles in about 4 s.
- *A polymorphic let.* A program with a let of a closed λ used more than once is converted and
  analysed twice (Polymorphic lets), and its first conversion has every such let replaced, so
  nested lets copy their bodies once per use at each level.
- *The checker on a large body.* `Frontend/Check` keeps a use mask as long as the context at each
  node (`orL`, `subL`), and decides freeness by walking types (`vfreeB`); on the body of such a
  `main` it grows about as the square of the body (1.1 s of the 4 s above). Its masks carry the
  checker's proofs (`Frontend/Check/Fam.lean`), and are left for their own change.
## Scope

No optimizations beyond the layouts, defunctionalization, direct calls of known codes, native
fixed points, pointer reversal, building a closure in its code's own environment object, frame
slots for scoped cells and static capability cells; no stack switching. SPEC §19's handlers,
operations and cancels are lowered, but for a name with both
control and abortive operations and a cancel whose finalisers may raise under a handler reached
from its own body (rejected). A tail-resumptive operation is a direct call when its handlers have
one closed clause; one whose clause captures values is a state machine (its captures passed as
evidence is open). The cancel frames `ccatch` and
`cfin` occur only in the source machine's continuations and are rejected by `Convert`. The only externs compiled are the
standard I/O ones; the model's harness (`mk_input`, …) is not compiled. `fold_imm` and the owned
folds that pointer reversal does not cover recurse on the Wasm stack (Stack). Closures of
recursive closure types keep an environment object (Representation, Open), and unboxed recursive
values (`μX. 1 + (i32 ⊗ X)` laid out flat) are a follow-up.
