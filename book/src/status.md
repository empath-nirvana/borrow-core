# Status

What the language has today, the gaps you are likely to run into, and what is planned but not
built. The SPEC links give the precise rule for each feature; the issue links track each gap.

## Built

| feature | where | guide |
|---|---|---|
| Ownership, `imm`/`mut` borrows, lexical lifetimes, borrow blocks, `&x`/`&mut x` | [§1](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#1-baseline), [§3](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#3-entry-2--the-call-by-push-value-core), [§23](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#23-entry-22--non-strict-outlives-the-box-rule-and-withbors-side-condition-lifetime-bounds-and-mains-lifetime) | [Ownership and borrows](guide/ownership.md) |
| `let mut` locals | [§41](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#41-entry-40--let-mut-names-resolved-to-their-binders-compositional-writes-one-boundary-rule) | [Ownership and borrows](guide/ownership.md) |
| Closures: reusable `!{ … }` and one-shot `{ … }` | [§2](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#2-entry-1--the-exponential-t), [§10](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#10-entry-9--persistent-variables), [§22](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#22-entry-21--the-affine-closure-observations-with-arguments-and-a-boxed-rest) | [Values, functions and numbers](guide/basics.md#functions-as-values) |
| Integers `i32`, `i64`, `u8`; operators chosen by type | [§8](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#8-entry-7--integers) | [Numbers](guide/basics.md#numbers) |
| Floats `f32`, `f64`, shortest printing and exact parsing | [§37](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#37-entry-36--floats-f32-and-f64) | [Floats](guide/basics.md#floats) |
| Integer `/` and `%` raising `Fail[DivError]` | [§39](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#39-entry-38--integer--and--a-division-with-no-answer-raises-faildiverror) | [Division](guide/errors.md#division) |
| `data` declarations: records, variants, generic types, recursion under `box`, `match` | [§42](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#42-entry-41--data-declarations-records-variants-recursion-under-box-match-compilation) | [Data and generics](guide/data.md) |
| Recursive types and folds; `fold` blocks | [§6](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#6-entry-5--recursive-types-and-folds), [§60](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#60-entry-59--the-fold-block-arms-whose-recursive-fields-arrive-folded-718) | [Data and generics](guide/data.md) |
| Recursion: bounded by default, `deep` on the heap, layers; generic recursion | [§20](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#20-entry-19--recursion-as-an-effect), [§21](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#21-entry-20--recursion-as-the-fixed-point-of-a-generator-closure-conversion-at-the-seams), [§31](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#31-entry-30--generic-recursion-blocks-to-generic-callees-and-the-inference-gaps) | [Recursion](guide/data.md#recursion) |
| Arrays, views and slices: split, replace, swap, sort | [§9](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#9-entry-8--arrays) | [Arrays](guide/data.md#arrays) |
| Buffers, UTF-8 strings, text views, literals | [§17](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#17-entry-16--buffers-text-and-literals) | [Buffers and strings](guide/data.md#buffers-and-strings) |
| Generics: generic functions and types, one copy per type | [§15](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#15-entry-14--generators), [§31](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#31-entry-30--generic-recursion-blocks-to-generic-callees-and-the-inference-gaps) | [Generic functions](guide/basics.md#generic-functions) |
| `poly` families, operators at user types, `equal`/`hash`/`order`, the hash map and set | [§36](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#36-entry-35--poly-families-one-case-per-type-operators-as-families-the-hash-map) | [`poly` families](guide/data.md#poly-families) |
| Implicit destructors | [§12](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#12-entry-11--implicit-destructors) | [Ownership and borrows](guide/ownership.md) |
| Divergence inferred; `total` checked | [§14](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#14-entry-13--divergence-as-an-effect) | [Iteration](guide/iteration.md) |
| Counted `for` over ranges, arrays and views, with `break`, `continue`, `else` | [§16](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#16-entry-15--counted-loops) | [Iteration](guide/iteration.md) |
| Generators, stored generators, adapters, `\|>` pipelines | [§15](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#15-entry-14--generators), [§33](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#33-entry-32--computation-parameters-and-) | [Generators](guide/iteration.md#generators) |
| Effects and handlers: answering and control operations, inferred effects | [§18](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#18-entry-17--effects-and-handlers), [§19](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#19-entry-18--native-capture-handle-and-perform) | [Effects and handlers](guide/effects.md) |
| Several instances of an effect, named handlers | [§38](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#38-entry-37--instances-of-an-effect-rows-with-types-names-abstraction-safety) | [Effects and handlers](guide/effects.md) |
| Blocks that perform effects; computation parameters | [§30](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#30-entry-29--effectful-blocks-and-async-tasks-at-the-surface), [§33](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#33-entry-32--computation-parameters-and-) | [Effects and handlers](guide/effects.md) |
| Errors as `raise` and handlers | [§18](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#18-entry-17--effects-and-handlers), [§19](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#19-entry-18--native-capture-handle-and-perform) | [Errors](guide/errors.md) |
| Standard streams, clock and arguments as effects, on WASI | [§34](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#34-entry-33--io-as-effects-the-platform-as-the-outermost-handler) | [Input and output](guide/io.md) |
| Standard streams as capabilities; externs, `bcc trusted` | [§11](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#11-entry-10--externs-and-standard-io) | [Standard I/O as capabilities](elaboration/standard-io.md) |
| Async tasks: `spawn`, `resume`, `cancel`, a round-robin scheduler as a library handler | [§30](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#30-entry-29--effectful-blocks-and-async-tasks-at-the-surface), [§32](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#32-entry-31--logged-and-scoped-tasks-blocks-that-use-capabilities-a-handlers-lifetimes) | [Async tasks](guide/async.md) |
| A task holding a borrow of its own data across `await` | [§29](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#29-entry-28--a-borrow-held-across-a-suspension-the-relaxed-lend-r1-under-pinlaw) | [Async tasks](guide/async.md) |
| WebAssembly, with handlers compiled to calls, branches and state machines | [§35](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#35-entry-34--implicit-allocations-frame-slots-static-cells-one-box-a-node) | [Getting started](getting-started.md) |
| Native code through LLVM (`bcc run --native`) | [§40](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#40-entry-39--the-native-target-llvm-ir-from-the-flat-ir) | [Getting started](getting-started.md) |
| Safety and termination proved in Lean; a type checker that produces a proof | [§1](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#1-baseline), [§13](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#13-entry-12--every-run-is-safe) | [What is proved](proved.md) |

## Gaps you may run into

**Types and generics**
- No bounds on type parameters (traits) and no derived cases ([#489](https://github.com/empath-nirvana/borrow-core/issues/489)).
- No modules: everything shares one namespace ([#63](https://github.com/empath-nirvana/borrow-core/issues/63)).
- Some generic calls need a type written out that could be inferred ([#477](https://github.com/empath-nirvana/borrow-core/issues/477)).
- A `Vec` cannot hold recursive data directly; use a buffer of options.
- The unit type is spelled `1` ([#148](https://github.com/empath-nirvana/borrow-core/issues/148)).

**Syntax**
- No bitwise or shift operators: write `host[and32](a, b)` and the like ([#144](https://github.com/empath-nirvana/borrow-core/issues/144)).
- No unary minus: write `0 - 3`.
- No `+=`, and no indexing sugar such as `v[i]` ([#143](https://github.com/empath-nirvana/borrow-core/issues/143)).

**Borrows**
- `&x` and `&mut x` must be the whole call of a `let` or statement: write
  `let n = len(&v); f(n)`, not `f(len(&v))` ([#510](https://github.com/empath-nirvana/borrow-core/issues/510)).
- No reborrow `&mut m` of a borrow ([#142](https://github.com/empath-nirvana/borrow-core/issues/142)).
- A generator cannot use a capability, such as stdout, across `yield`.

**Loops and effects**
- A `while` or `loop` cannot raise ([#522](https://github.com/empath-nirvana/borrow-core/issues/522)).
- A callback stored with its effects, rather than called, is not supported yet ([#161](https://github.com/empath-nirvana/borrow-core/issues/161)).
- An error cannot carry an owned value yet ([#215](https://github.com/empath-nirvana/borrow-core/issues/215)).

**I/O and async**
- One platform, WASI. I/O is the standard streams, the clock and arguments.
- Async is cooperative and single-threaded, with no event loop over real I/O yet ([#52](https://github.com/empath-nirvana/borrow-core/issues/52)).

**Diagnostics.** Some error messages describe the translated program rather than the one you
wrote ([#145](https://github.com/empath-nirvana/borrow-core/issues/145)).

**Compiler.** The compiler is tested against the reference interpreter on every program, not
proved ([#15](https://github.com/empath-nirvana/borrow-core/issues/15)). Some programs are still
slower than their Rust versions ([#213](https://github.com/empath-nirvana/borrow-core/issues/213)).

## Planned

| feature | tracked |
|---|---|
| Modules and packages | [#63](https://github.com/empath-nirvana/borrow-core/issues/63) |
| Files, the environment, the network, randomness, the exit status | [#66](https://github.com/empath-nirvana/borrow-core/issues/66) |
| Interior mutability | [#119](https://github.com/empath-nirvana/borrow-core/issues/119) |
| Threads and parallelism | [#212](https://github.com/empath-nirvana/borrow-core/issues/212) |
| Unsafe code and a C FFI | [#79](https://github.com/empath-nirvana/borrow-core/issues/79) |
| Panics and backtraces | [#192](https://github.com/empath-nirvana/borrow-core/issues/192) |
| Libraries: JSON, regular expressions | [#65](https://github.com/empath-nirvana/borrow-core/issues/65), [#225](https://github.com/empath-nirvana/borrow-core/issues/225) |
| Sized types | [#72](https://github.com/empath-nirvana/borrow-core/issues/72) |
