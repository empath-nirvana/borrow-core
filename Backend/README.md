# Backend: the compiler to WebAssembly

`bcc` compiles a checked, closed `main` (`Frontend/`) to WebAssembly text and runs it under
`wasmtime`. The input is `main`'s erasure, the untyped BoLo `Expr` that
`Frontend.Check.checkProgram_sound` derives `CDerives` for; types are not used.

    lake exe bcc compile <file> -o <out.wat>   compile to WAT
    lake exe bcc run <file>                    compile, run under `wasmtime -W tail-call=y`
    lake exe bcc interp [--stage S] <file>     interpret stage S: source (default), clos, flat
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
| flat IR | `Flat/Syntax.lean`, `Flat/Lower.lean`, `Flat/Runtime.lean`, `Flat/Host.lean` | functions over words, locals, allocation, calls, tail calls, `ite`/`switch` | `Flat/Interp.lean` |
| Wasm | `Wasm/Syntax.lean`, `Wasm/Lower.lean` | the Wasm subset, as an AST | `wasmtime` |
| WAT | `Wasm/Print.lean`, `Wasm/Runtime.lean` | text; the runtime inserted as written | — |

All passes are structural recursion (the interpreters take fuel); `Driver.lean` composes them.
No stage optimizes. The WAT printer and the runtime are the only steps no Lean interpreter
observes.

**Closure conversion** (`Clos/Convert.lean`). De Bruijn indices become variables, and each
intermediate result is named, in the machine's evaluation order: pairs left to right, an
application's argument before its function. A `λ` becomes `clos c xs`, code `c` with its free
variables `xs` captured by value. A primitive applied to its argument is `prim`; used as a
value it is η-expanded into closure code.

**Flat IR** (`Flat/Lower.lean`). A closure code is a function of the closure and the argument;
a call is an indirect call through the table on the closure's code index, and a call in return
position is a tail call. `case` is an `if` on the injection's header.

**Wasm** (`Wasm/Lower.lean`). One Wasm function per flat-IR function, `i64` locals, `switch` as
`br_table` over nested blocks, tail calls as `return_call`/`return_call_indirect`. `_start`
runs the entry, which prints through WASI `fd_write`.

## Representation

A value is one 64-bit word. `()` is `1`; `i32[n]` is `n << 32 | 3`; every other value is the
address of an object (8-aligned, so bit 0 is clear). An object is a header word, whose low
byte is its kind, and its fields:

| kind | header | fields |
|---|---|---|
| pair | `1` | two values |
| `inl` / `inr` | `2` / `3` | one value |
| closure | `4 \| n << 8` | code index, `n` captured values |
| `i64[n]` | `5` | the 64 bits |
| cell | `6` | the contents |

An array (SPEC §9) is one allocation of `max n 1` slots of two words, each an ordinary cell
(header `6`, then the contents); element `i` is the slot at `base + 16·i`, so its location is a
cell address and `load`, `store`, copies and drops treat it as any cell. The array value is the
pair `(base, i32[n])`. `idx` compares the index with `n` unsigned and computes the address;
`tab` allocates the slots and fills them in a loop, calling a copy of the tabulator per element;
`drop` moves each element to a copy of the consumer and frees the allocation once
(`Backend/Flat/Runtime.lean`). The closure IR keeps an array as consecutive cells, as the source
machine does. A type-directed layout would drop the header, making the slot `sizeof A`.

`i64` is boxed: the erasure is untyped, so a deep copy or drop tells a pointer from an
immediate by the word alone, and a full-width `i64` leaves no bit for that. A type-directed
layout would unbox it.

## Memory discipline

Source values are trees whose only shared parts are locations. The compiled program keeps every
object owned by exactly one word, so it can free an object where the source stops using it:

- **Eliminations free.** `let (x, y) = p` frees the pair; `case` frees the injection; calling a
  closure frees it (the code unpacks its environment into locals first); a host operation frees
  its argument pair and any `i64` box it reads.
- **Duplication copies.** A variable used by two sequential parts of a term (the halves of a
  pair, the argument and function of an application, a `let`'s bound term and body, a `case`'s
  scrutinee and arms) is deep-copied for all but the last. The two arms of a `case` are one
  part: only one runs.
- **Discarding drops.** A variable that a path does not use is deep-freed where its scope
  starts on that path: an unused binder, or in a `case` arm, what only the other arm uses.
- **Cells.** `alloc v` allocates a cell owning `v`; `load` deep-copies the contents (the source
  copies the value out); `store` drops the old contents; `free` moves them out and frees the
  cell. A deep copy copies a location as a word, and a deep drop leaves cells alone: cells are
  freed only by `free`.

So each variable is consumed exactly once on every path, as substitution does in the source;
the closure-IR interpreter checks this as it runs. Persistent types (SPEC §10) hold no resource, so
copying a persistent value copies no resource. After `main`'s value is printed and dropped, the
live count is 0 exactly when the source run ends with empty memory.

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
`live` is exported as `live_objects`; `$putc` writes a byte to standard output.

## Host operations (SPEC §8)

A literal is a constant (`i32`) or a fresh box (`i64`). Each host operation is a flat-IR
function (`Flat/Host.lean`) around its Wasm instruction. Tests produce `inr ()` for true and
`inl ()` for false. A partial operation is checked before the instruction runs: a zero divisor,
or `INT_MIN / -1` for `div_s`, produces `inr ()`, anything else `inl n`. The flat-IR interpreter
evaluates the instructions with `wasmHost`, so the flat IR and the source agree on arithmetic by
construction; Wasm agreeing with `wasmHost` is tested, not proved (SPEC §8).

## Scope

No optimizations, no type-directed layout, no externs (`main` must be closed), no stack
switching. Recursion (the folds' fixed points) is non-tail and uses the Wasm stack.
