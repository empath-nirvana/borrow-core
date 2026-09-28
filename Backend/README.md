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
| closure IR | `Clos/Syntax.lean`, `Clos/Convert.lean` | named A-normal form, explicit environments and ownership | `Clos/Interp.lean` |
| layout types | `Clos/Types.lean` | a layout type for every closure-IR variable, code and constructor; each type's layout | — |
| flat IR | `Flat/Syntax.lean`, `Flat/Lower.lean` | functions over words, locals, allocation, calls and tail calls of several results, `ite` | `Flat/Interp.lean` |
| Wasm | `Wasm/Syntax.lean`, `Wasm/Lower.lean` | the Wasm subset, as an AST | `wasmtime` |
| WAT | `Wasm/Print.lean`, `Wasm/Runtime.lean` | text; the runtime inserted as written | — |

All passes are structural recursion (the interpreters take fuel); `Driver.lean` composes them.
No stage optimizes beyond choosing layouts, compiling `let` as a binding and cancelling the copy
and drop inside `swap`. The WAT printer and the runtime are the only steps no Lean interpreter
observes.

**Closure conversion** (`Clos/Convert.lean`). De Bruijn indices become variables, and each
intermediate result is named, in the machine's evaluation order: pairs left to right, an
application's argument before its function. A `λ` becomes `clos c xs`, code `c` with its free
variables `xs` captured by value; a β-redex `(λx. b) a`, the erasure's `let`, is `letv x a b`
and makes no closure. A primitive applied to its argument is `prim`; used as a value it is
η-expanded into closure code. The axiom `swap ≜ λx.λy. let z = load x; store x y; (x, z)` is the
primitive `swap`, which moves the old contents out where the axiom copies and then drops them.

**Layout types** (`Clos/Types.lean`). Unification over the closure IR gives every variable a
layout type `1 | i32 | i64 | A ⊗ B | A ⊕ B | fn(A; C, D) | loc A` (see Representation).
Value types are monomorphic: a definition is substituted at each use, and polymorphism is over
lifetimes only, whose arguments are `()`. Unification has no occurs check, since `μ` and `ν`
leave regular trees. Two code shapes carry the typing of `&`: a code that cases on its parameter
answers `inl ()` and `inr ()` at its two arms' types, and a call whose argument is a literal
injection is a projection; a code that passes its parameter to a function in tail position (as
`unfold` forwards an observation) has that function's type. A program the unification rejects
is reported, not compiled; the source's typing derivation is what makes the corpus pass.

**Flat IR** (`Flat/Lower.lean`). A value of layout type `A` is `|A|` words: in `|A|` locals,
passed as `|A|` arguments, returned as `|A|` results. A closure code is a function of the
closure and the argument's words, returning the answer's words; a call is an indirect call
through the table on the closure's code index, and a call in return position whose callee
answers the caller's words is a tail call. `case` is an `if` on the tag word. Copy, drop, the
printer, the array primitives and the loop driver are flat-IR functions generated per layout
type; host operations are inline.

**Wasm** (`Wasm/Lower.lean`). One Wasm function per flat-IR function, `i64` locals, several
results as a multi-value function, tail calls as `return_call`/`return_call_indirect`. `_start`
runs the entry, which prints through WASI `fd_write`. The LLVM counterpart of a multi-value
function is a function returning a struct by value (an `sret` pointer when it is wide), and of a
flattened pair its fields as separate SSA values (decision 25).

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
| `fn(A; C, D)` | 1 | a closure: the word `2c + 1`, or the address of an environment object |

So a pair is never an object, a `bool` (`1 + 1`) is one tag word, `1 + A` is a tag and `A`, an
`i64` is unboxed, and none of these allocates. The only objects are:

- **Cells.** `alloc v` allocates the cell's contents, `max 1 w` words with no header, where `w`
  is the widest contents its *cell class* holds: `swap` changes a cell's type
  (`Ref A ⊸ B ⊸ Ref B ⊗ A`), so the locations that may be one cell are a class, and a cell is as
  wide as its class needs.
- **Arrays** (SPEC §9). One allocation of `max 1 (n·s)` words, `s` the class width of the
  element type: element `i`'s location is `base + 8·s·i`, a cell address like any other. The
  array value is the pair `(base, n)`, two words. `idx` is an unsigned compare and an address
  computation, and allocates nothing.
- **Closures that capture.** An object: the code index `c`, then the captured values' words. A
  code that captures nothing is the word `2c + 1` (objects are 8-aligned, so bit 0 tells the two
  apart) and allocates nothing.
- **Boxed fields.** A recursive type would be infinitely wide, so the fields that close a cycle
  of pair and sum edges (the back edges of one depth-first search over the types) are stored as
  a pointer to an object of the field's own layout. `μX. 1 + (A ⊗ X)` is a tag and a payload
  `A ⊗ X` whose `X` is a pointer: `nil` allocates nothing, each `cons` one object.

The printer is generated per type and writes the text of `Backend.PV.render`: the type says
whether a word is an integer, a tag, a closure (`<fun>`) or a location (`<loc>`).

`fn(A; C, D)` answers `C` to `inl ()` and `D` to `inr ()`: a thunk of `C & D` is one closure
answering two projections at two types. Its code returns `max |C| |D|` words, the arm's own
words then zeros; a projection's caller takes the first `|C|` or `|D|`.

**Open.** A closure that captures stays an environment object, allocated when it is built and
freed when it is called, and a closure call is an indirect call. This conflicts with the
explicit-heap decision (#54, #80): closures and codata state should be sized values on the
stack unless boxed, by whole-program defunctionalization (each `U C` a tagged union of the
codes that flow there), and calls of known code direct. Placement of the objects that remain
(stack, frame arena or heap, by escape analysis) is also open.

## Memory discipline

Source values are trees whose only shared parts are locations. The compiled program keeps every
object owned by exactly one word, so it can free an object where the source stops using it. At
typed layouts:

- **Eliminations free.** `let (x, y) = p` and `case` bind the components' or payload's words
  (and load and free a boxed field); calling a closure frees its environment object (the code
  unpacks it into locals first). A pair, an injection, an integer and a code word `2c + 1` hold
  no object of their own, so there is nothing else to free.
- **Duplication copies.** A variable used by two sequential parts of a term (the halves of a
  pair, the argument and function of an application, a `let`'s bound term and body, a `case`'s
  scrutinee and arms) is copied for all but the last. The two arms of a `case` are one part:
  only one runs. At a *trivial* type (one with no closure and no boxed field) the copy is the
  words themselves; otherwise it is the type's generated copy, which allocates a new object for
  each environment and boxed field it meets. A closure is copied by its code's copy function,
  chosen by a binary search on the code index among the codes of its type.
- **Discarding drops.** A variable that a path does not use is dropped where its scope starts
  on that path: an unused binder, or in a `case` arm, what only the other arm uses. At a
  trivial type a drop is nothing; otherwise the type's generated drop frees each environment
  and boxed field.
- **Cells.** `alloc v` allocates a cell holding `v`'s words; `load` copies the contents (the
  source copies the value out); `store` drops the old contents; `free` moves them out and frees
  the cell; `swap` moves the old contents out and the new in. A copy copies a location as a
  word, and a drop leaves cells alone: cells are freed only by `free`.

So each variable is consumed exactly once on every path, as substitution does in the source;
the closure-IR interpreter, which keeps the uniform boxed objects, checks this as it runs, and the
flat IR follows the same consumption at typed layouts. Persistent types (SPEC §10) hold no
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
the indirect calls, which the compiled code counts when it is built to count.

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
stages must agree. `scripts/compile-corpus.sh` checks every corpus program's counts against
`corpus/counts.expected`: a count above the file fails the gate, one below it is reported, and
`--write-counts` rewrites the file. A pure arithmetic program (`int-arith`, `int-ops`) allocates
nothing and makes no indirect call; what remains is cells, arrays, closures that capture, and
boxed recursive fields, and the indirect calls are closure calls.

## Verification (#15)

The semantic theorems do not change: layout is below the model, whose values are terms. What
changes is the refinement a compiler proof (#15) would establish between the stages. The flat
IR's runtime invariants are now layout-aware:

- a closure-IR variable of layout type `A` corresponds to `|A|` flat-IR words, related to the
  closure IR's boxed object graph by `A`'s layout (a pair by its components' words, an injection
  by its tag and padded payload, a boxed field by an object of the field's layout, a closure by
  `2c + 1` or an environment object);
- the words of every live object are written (`Flat/Interp.lean` checks every read), and a cell
  is as wide as its class;
- a call's results match the callee's signature, which Wasm's `call_indirect` checks and the
  flat-IR interpreter checks too;
- the layout types are an obligation of their own: the closure IR must be typable, which the
  source's `CDerives` derivation should give for everything but the axioms' bodies (`swap`,
  whose contents change type, is why cell classes exist).

The ownership invariant (each object owned by exactly one word, consumed once per path) is the
same as before, restated over typed words.

## Scope

No optimizations beyond the layouts, no stack switching. The only externs compiled are the
standard I/O ones; the model's harness (`mk_input`, …) is not compiled. Recursion (the folds'
fixed points) is non-tail and uses the Wasm stack. Closures that capture keep an environment
object, and unboxed recursive values (`μX. 1 + (i32 ⊗ X)` laid out flat) are a follow-up.
