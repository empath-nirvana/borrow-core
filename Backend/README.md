# Backend: the compiler to WebAssembly

`bcc` compiles a checked, closed `main` (`Frontend/`) to WebAssembly text and runs it under
`wasmtime`. The input is `main`'s erasure, the untyped BoLo `Expr` that
`Frontend.Check.checkProgram_sound` derives `CDerives` for. The closure IR recovers layout types
from it (`Clos/Types.lean`), and every stage from the flat IR on lays values out by type.

    lake exe bcc compile <file> -o <out.wat>   compile to WAT
    lake exe bcc run <file>                    compile, run under `wasmtime -W tail-call=y`
    lake exe bcc interp [--stage S] <file>     interpret stage S: source (default), clos, flat
    lake exe bcc trusted <file>                the program's externs: contracts, host code, levels
    lake exe bcc-counts <file>                 allocations and indirect calls of a run
    lake exe bcc-counts --sites <file>         the closure calls: direct, dispatched; recursive types
    scripts/compile-corpus.sh                  the corpus, compiled against the interpreter

Every stage prints the same report: `main`'s value, then `live N`, the number of objects live
after the value has been dropped (`Backend.report`, `Backend/Value.lean`). Values print in
the syntax of `docs/syntax-core.md` (`inl`, `inr`, pairs, `()`, `i32[n]`/`i64[n]` unsigned);
a function prints as `<fun>` and a location as `<loc>`. A `main` whose value is codata (a thunk
of a `nu` type such as `delay`, `stream` or `iter`) prints `<fun>`; the corpus drives such values
inside `main`, as `Core/DelayPrograms.lean` does. Codata needs nothing of its own here: `nu_in`
and `nu_out` erase, and `unfold` is a closed λ-term.

## Pipeline

| stage | file | what it is | interpreter |
|---|---|---|---|
| source | `Source.lean` | `main`'s erasure | `Support`'s `step` at `wasmHost` |
| closure IR | `Clos/Syntax.lean`, `Clos/Convert.lean`, `Clos/Collapse.lean` | named A-normal form, explicit environments and ownership | `Clos/Interp.lean` |
| layout types | `Clos/Types.lean` | a layout type for every closure-IR variable, code and constructor; each type's layout; each closure type's union of codes | — |
| closure flow | `Clos/Flow.lean` | a 0-CFA: the codes each call may call | — |
| flat IR | `Flat/Syntax.lean`, `Flat/Lower.lean` | functions over words, locals, allocation, calls and tail calls of several results, `ite` | `Flat/Interp.lean` |
| Wasm | `Wasm/Syntax.lean`, `Wasm/Lower.lean` | the Wasm subset, as an AST | `wasmtime` |
| WAT | `Wasm/Print.lean`, `Wasm/Runtime.lean` | text; the runtime inserted as written | — |

All passes are structural recursion (the interpreters take fuel); `Driver.lean` composes them.
No stage optimizes beyond choosing layouts, defunctionalizing closures, calling known codes
directly, compiling `let` as a binding, cancelling the copy and drop inside `swap`, compiling
the Z combinator's fixed point natively, building codata thunks eagerly, merging equal codes, and
compiling owned folds by pointer reversal (Stack). The WAT printer and the runtime are the only steps no Lean interpreter
observes.

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
layout type `1 | i32 | i64 | A ⊗ B | A ⊕ B | fn(A; C, D) | loc A` (see Representation).
Value types are monomorphic: a definition is substituted at each use, and polymorphism is over
lifetimes only, whose arguments are `()`. Unification has no occurs check, since `μ` and `ν`
leave regular trees. Two code shapes carry the typing of `&`: a code that cases on its parameter
answers `inl ()` and `inr ()` at its two arms' types, and a call whose argument is a literal
injection is a projection; a code that passes its parameter to a function in tail position (as
`unfold` forwards an observation) has that function's type. A program the unification rejects
is reported, not compiled; the source's typing derivation is what makes the corpus pass.

**Closure flow** (`Clos/Flow.lean`). A monovariant 0-CFA over the whole closure IR: every value
is abstracted by its construction site (a closure by its code, a pair or injection by its
operands, a cell or array by its contents), and the least solution of the inclusion constraints
gives, for every call and for the loop driver, the codes whose closures may reach it. The helpers
that call closures (`tab`, an array's `drop`, the loop driver) are constraints too. A call's code
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
printer, the array primitives and the loop driver are flat-IR functions generated per layout
type; host operations are inline.

**Wasm** (`Wasm/Lower.lean`). One Wasm function per flat-IR function, `i64` locals, several
results as a multi-value function, tail calls as `return_call`, a `switch` as `br_table` over
nested blocks. There is no function table and no `call_indirect`. `_start` runs the entry, which
prints through WASI `fd_write`. The LLVM counterpart of a multi-value function is a function
returning a struct by value (an `sret` pointer when it is wide), of a flattened pair or closure
union its fields as separate SSA values, of `switch` LLVM's `switch`, and of a tail call a
`musttail` call (decision 25).

## Representation

A value's layout is chosen by its layout type (`Clos/Types.lean`, `Flat/Lower.lean`). Every
word is an `i64` local; `|A|` is the number of words of `A`.

| layout type | words | layout |
|---|---|---|
| `1` | 0 | nothing |
| `i32`, `i64` | 1 | the integer (an `i32` zero-extended) |
| `A ⊗ B` | `\|A\| + \|B\|` | `A`'s words, then `B`'s |
| `A ⊕ B` | `1 + max \|A\| \|B\|` | a tag word (`0` for `inl`), then the payload's words, padded |
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
  wide as its class needs.
- **Arrays** (SPEC §9). One allocation of `max 1 (n·s)` words, `s` the class width of the
  element type: element `i`'s location is `base + 8·s·i`, a cell address like any other. The
  array value is the pair `(base, n)`, two words. `idx` is an unsigned compare and an address
  computation, and allocates nothing.
- **Closures of a recursive closure type that capture.** An object: the tag `t`, then the
  captured values' words. A code that captures nothing is the word `2t + 1` (objects are
  8-aligned, so bit 0 tells the two apart) and allocates nothing.
- **Boxed fields.** A recursive type would be infinitely wide, so the fields that close a cycle
  of pair and sum edges (the back edges of one depth-first search over the types) are stored as
  a pointer to an object of the field's own layout. `μX. 1 + (A ⊗ X)` is a tag and a payload
  `A ⊗ X` whose `X` is a pointer: `nil` allocates nothing, each `cons` one object.

The printer is generated per type and writes the text of `Backend.PV.render`: the type says
whether a word is an integer, a tag, a closure (`<fun>`) or a location (`<loc>`).

`fn(A; C, D)` answers `C` to `inl ()` and `D` to `inr ()`: a thunk of `C & D` is one closure
answering two projections at two types. Its code returns `max |C| |D|` words, the arm's own
words then zeros; a projection's caller takes the first `|C|` or `|D|`.

**Open.** With fixed points native, a recursive closure type is one the program builds as
data: a closure that captures a closure of its own type, as a fold whose result is a function
does (`add` of `13-2-sum-prog` and `sum-prog-exact`, one type; `div_fuel`'s handler in
`lib/div.bc`, used by `io-fuel`, four). `bcc-counts --sites` lists them. They keep the heap
representation until the source can say `box` (#54). Placement of the objects that remain
(stack, frame arena or heap, by escape analysis) is also open.

The dispatched calls that remain are calls of those closures: a chain of functions built by
a fold, whose links are different codes (`13-2-sum-prog`'s and `sum-prog-exact`'s `add`,
`io-fuel`'s fuel handler). Every other call of the corpus is direct.

## Stack

A call is a tail call (`return_call`; LLVM `musttail`) when it is in return position and its
callee answers the caller's words. What runs in constant stack:

- **Loops.** Every `ν`-type program, `unfold`, `fixd`, `div_bind` and the `for` loop: an
  observation runs the step once and returns the next state inside the rest, so the depth does
  not grow with the number of observations. The loop driver (`drive`) calls the loop and then
  tail-calls itself; `div_fuel`'s handler ends each observation with a tail call of the next.
  A left fold is written as a loop whose state is the rest of the structure and the accumulator
  (`corpus/deep-list.bc`); this is the only left-fold shape the core has.
- **A self-call in tail position**, of the native fixed point: its code is known, so the call is
  a direct tail call of the code itself.
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
  it meets. A type is trivial when it has no boxed field, no recursive closure type, and no
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
  word, and a drop leaves cells alone: cells are freed only by `free`.

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
`live` is exported as `live_objects`; `$putc` writes a byte to standard output, `$putfd` a byte to a
descriptor and `$getc` reads one (SPEC §11). `$allocs` counts the calls of `$alloc` and `$indirect`
the dispatched calls, which the compiled code counts when it is built to count.

## Host operations (SPEC §8)

A literal is a constant word. Each host operation is inline: its Wasm instruction on the
operands' words (`Flat/Lower.lean`, `hostVals`). Tests produce `inr ()` for true and `inl ()` for
false, the tag word `1` or `0`. A partial operation is checked before the instruction runs: a
zero divisor, or `INT_MIN / -1` for `div_s`, produces `inr ()`, anything else `inl n`. The flat-IR interpreter
evaluates the instructions with `wasmHost`, so the flat IR and the source agree on arithmetic by
construction; Wasm agreeing with `wasmHost` is tested, not proved (SPEC §8).

## Standard I/O (SPEC §11)

A `main` may declare the standard externs (`Frontend/Check/Externs.lean`): the capabilities
`stdin`, `stdout`, `stderr` (`ref input`, `ref output`) and the operations `read_byte`,
`write_byte`. Its type is then `F (Caps ⊗ A)`, handing the capabilities back after `A`, or
`F (U (loop (Caps ⊗ A) (Caps ⊗ B)))` for a program that runs until its input ends.

- **Compiled stages.** `Clos.convertMain` binds each extern before `main` runs: a capability to a
  fresh cell holding its file descriptor (`i32[0]`, `[1]`, `[2]`), an operation to the closure
  `Λ. λm. op m` over the closure-IR primitive `io readByte`/`io writeByte`. An extern `main` does
  not use is dropped. After `main`, its result `(caps, a)` is taken apart, each capability cell
  freed, and `a` is the program's value. In the flat IR the operations are inline, over the
  statements `getc fd` and `putc fd b`, and `read_byte`'s answer `(m, inl b)` or `(m, inr ())` is
  three words; in Wasm those statements are `$getc` and `$putfd`, WASI `fd_read` and `fd_write`
  of one byte. They are unbuffered, so a
  prompt is out before the next read. The plain LLVM/libc counterpart is `read(2)`/`write(2)`
  on the same descriptors; nothing WASI-specific is part of the semantics.
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
(`Driver.flatOf`, `compileWat` with `counts`: the entry writes `allocs N` and `indirect M` after
the report), and prints the objects the run allocates and the indirect calls it makes; the two
stages must agree. An indirect call is a dispatched one: a call of a type's `apply`, whose code
the `switch` on the tag chooses at run time. There is no other kind of indirect call. `scripts/compile-corpus.sh` checks every corpus program's counts against
`corpus/counts.expected`: a count above the file fails the gate, one below it is reported, and
`--write-counts` rewrites the file. A pure arithmetic program (`int-arith`, `int-ops`) allocates
nothing and makes no indirect call; what remains is cells, arrays, boxed recursive fields (a
list's nodes), and the heap environments of the few recursive closure types (Open), whose calls
are the only dispatched ones. `bcc-counts --sites <file>` prints the program's closure calls: how
many are direct because the union has one code, how many more because the flow analysis finds
one, how many are dispatched; the recursive closure types; and the owned folds, how many are
compiled by pointer reversal and how many recurse.

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

## Scope

No optimizations beyond the layouts, defunctionalization, direct calls of known codes, native
fixed points and pointer reversal; no stack switching. The only externs compiled are the
standard I/O ones; the model's harness (`mk_input`, …) is not compiled. `fold_imm` and the owned
folds that pointer reversal does not cover recurse on the Wasm stack (Stack). Closures of
recursive closure types keep an environment object (Representation, Open), and unboxed recursive
values (`μX. 1 + (i32 ⊗ X)` laid out flat) are a follow-up.
