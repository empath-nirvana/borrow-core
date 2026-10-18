# Status

What the language has today, what it has with known gaps, and what is designed or tracked but
not built. Each line links the SPEC entry that specifies it or the issue that tracks it. A
feature is *built* when it has a SPEC entry, is checked by the certifying checker (so the
theorems of [What is proved](proved.md) cover it), is compiled, and runs in the corpus; the guide
teaches only built features.

## Built

| feature | where | guide |
|---|---|---|
| Ownership, `imm`/`mut` borrows, lexical lifetimes, borrow blocks, `&x`/`&mut x` | [§1](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#1-baseline), [§3](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#3-entry-2--the-call-by-push-value-core), [§23](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#23-entry-22--non-strict-outlives-the-box-rule-and-withbors-side-condition-lifetime-bounds-and-mains-lifetime) | [Ownership and borrows](guide/ownership.md) |
| `!A`, persistent and one-shot closures; the affine closure `Aff` | [§2](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#2-entry-1--the-exponential-t), [§10](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#10-entry-9--persistent-variables), [§22](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#22-entry-21--the-affine-closure-observations-with-arguments-and-a-boxed-rest) | [Values, functions and numbers](guide/basics.md#functions-as-values) |
| Integers `i32`, `i64`, `u8`; operators chosen by type | [§8](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#8-entry-7--integers) | [Numbers](guide/basics.md#numbers) |
| Floats `f32`, `f64`, shortest printing and exact parsing | [§37](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#37-entry-36--floats-f32-and-f64) | [Floats](guide/basics.md#floats) |
| Integer `/` and `%` raising `Fail[DivError]` | [§39](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#39-entry-38--integer--and--a-division-with-no-answer-raises-faildiverror) | [Division](guide/errors.md#division) |
| Recursive types and folds | [§6](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#6-entry-5--recursive-types-and-folds) | [Data and generics](guide/data.md) |
| Recursion: bounded by default, `deep` on the heap, layers; generic recursion | [§20](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#20-entry-19--recursion-as-an-effect), [§21](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#21-entry-20--recursion-as-the-fixed-point-of-a-generator-closure-conversion-at-the-seams), [§31](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#31-entry-30--generic-recursion-blocks-to-generic-callees-and-the-inference-gaps) | [Recursion](guide/data.md#recursion) |
| Arrays, views and slices: split, replace, swap, sort | [§9](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#9-entry-8--arrays) | [Arrays](guide/data.md#arrays) |
| Buffers, UTF-8 strings, text views, literals | [§17](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#17-entry-16--buffers-text-and-literals) | [Buffers and strings](guide/data.md#buffers-and-strings) |
| Generics: generic functions and types, one copy per type | [§15](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#15-entry-14--generators), [§31](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#31-entry-30--generic-recursion-blocks-to-generic-callees-and-the-inference-gaps) | [Generic functions](guide/basics.md#generic-functions) |
| `poly` families, operators at user types, `equal`/`hash`/`order`, the hash map and set | [§36](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#36-entry-35--poly-families-one-case-per-type-operators-as-families-the-hash-map) | [`poly` families](guide/data.md#poly-families) |
| Implicit destructors | [§12](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#12-entry-11--implicit-destructors) | [Ownership and borrows](guide/ownership.md) |
| Divergence inferred; `total` checked | [§14](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#14-entry-13--divergence-as-an-effect) | [Iteration](guide/iteration.md#loops-that-may-not-end) |
| Counted `for` over ranges, arrays and views, with `break`, `continue`, `else` | [§16](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#16-entry-15--counted-loops) | [Iteration](guide/iteration.md) |
| Generators, stored generators, adapters, `\|>` pipelines | [§15](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#15-entry-14--generators), [§33](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#33-entry-32--computation-parameters-and-) | [Generators](guide/iteration.md#generators) |
| Effects and handlers: answering and control operations, rows inferred, continuations affine or linear | [§18](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#18-entry-17--effects-and-handlers), [§19](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#19-entry-18--native-capture-handle-and-perform), [§24](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#24-entry-23--the-polymorphic-let-the-general-handle-and-then-at-option-a)–[§28](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#28-entry-27--boxed-κ-a-handler-clause-that-receives-its-continuation-boxed) | [Effects and handlers](guide/effects.md) |
| Several instances of an effect, named handlers | [§38](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#38-entry-37--instances-of-an-effect-rows-with-types-names-abstraction-safety) | [Several instances](guide/effects.md#several-instances-and-names) |
| Blocks that perform effects; computation parameters | [§30](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#30-entry-29--effectful-blocks-and-async-tasks-at-the-surface), [§32](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#32-entry-31--logged-and-scoped-tasks-blocks-that-use-capabilities-a-handlers-lifetimes), [§33](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#33-entry-32--computation-parameters-and-) | [Blocks](guide/effects.md#blocks-that-perform-effects) |
| Errors as `raise` and handlers | [§18](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#18-entry-17--effects-and-handlers), [§19](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#19-entry-18--native-capture-handle-and-perform) | [Errors](guide/errors.md) |
| Standard streams, clock and arguments as effects, served by the WASI platform | [§34](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#34-entry-33--io-as-effects-the-platform-as-the-outermost-handler) | [Input and output](guide/io.md) |
| Standard streams as capability cells; externs with contracts, `bcc trusted` | [§11](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#11-entry-10--externs-and-standard-io) | [Standard I/O as capabilities](elaboration/standard-io.md) |
| Async tasks: `spawn`, `resume`, `cancel`, a round-robin scheduler as a library handler | [§30](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#30-entry-29--effectful-blocks-and-async-tasks-at-the-surface), [§32](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#32-entry-31--logged-and-scoped-tasks-blocks-that-use-capabilities-a-handlers-lifetimes) | [Async tasks](guide/async.md) |
| A task holding a borrow of its own data across `await` (under `PinLaw`) | [§29](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#29-entry-28--a-borrow-held-across-a-suspension-the-relaxed-lend-r1-under-pinlaw) | [Borrows across `await`](guide/async.md#borrows-across-await) |
| Compilation to WebAssembly; handlers as calls, branches and state machines; frame slots for scoped cells | [§35](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#35-entry-34--implicit-allocations-frame-slots-static-cells-one-box-a-node) | [Getting started](getting-started.md) |
| Proofs: Fundamental Property, adequacy on every run, totality, a certifying checker | [§1](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#1-baseline), [§13](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#13-entry-12--every-run-is-safe) | [What is proved](proved.md) |

## Partial

Built, with gaps that programs meet. Each gap has the issue that tracks it.

**Data and generics.**
- No `data` declarations: no named constructors, records with named fields, newtypes or hidden
  representations; a type is a `mu`, sums and pairs ([#489](https://github.com/empath-nirvana/borrow-core/issues/489), [§36](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#36-entry-35--poly-families-one-case-per-type-operators-as-families-the-hash-map) *Not provided*).
- No bounds on type parameters (`ability Key[K]`), no derived cases, no `!=` from `==`
  ([#489](https://github.com/empath-nirvana/borrow-core/issues/489), [#508](https://github.com/empath-nirvana/borrow-core/issues/508)). A generic `fn` cannot be called at a generic `def`'s type variables ([#136](https://github.com/empath-nirvana/borrow-core/issues/136));
  other inference gaps ([#477](https://github.com/empath-nirvana/borrow-core/issues/477), [#167](https://github.com/empath-nirvana/borrow-core/issues/167)).
- No modules, so a family's cases are global ([#63](https://github.com/empath-nirvana/borrow-core/issues/63)).
- The unit type is spelled `1` ([#148](https://github.com/empath-nirvana/borrow-core/issues/148)).

**Operators and numbers.**
- No bitwise or shift operators: `host[and32](a, b)` and the like ([#144](https://github.com/empath-nirvana/borrow-core/issues/144)). No unary minus.
- No indexing sugar, `v[i]` or `v.swap(i, j)` ([#143](https://github.com/empath-nirvana/borrow-core/issues/143)).
- Floats: no formatting options; no map key without `ord_f64` ([§37](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#37-entry-36--floats-f32-and-f64) *Not provided*).

**Borrows.**
- A lend must be the whole of a `let` or a statement: not nested in an argument ([#510](https://github.com/empath-nirvana/borrow-core/issues/510)), a tuple,
  a `match` scrutinee or an operand ([#525](https://github.com/empath-nirvana/borrow-core/issues/525)).
- An owner borrowed inside another borrow block is not handed back after it ([#495](https://github.com/empath-nirvana/borrow-core/issues/495)); a
  loop-local binding that shadows an owner ([#493](https://github.com/empath-nirvana/borrow-core/issues/493)).
- No reborrow `&mut m` of a borrow at the surface; shared views are not freely duplicable
  ([#142](https://github.com/empath-nirvana/borrow-core/issues/142), [#58](https://github.com/empath-nirvana/borrow-core/issues/58)).
- A borrow held across a generator's turns, the spanning lend ([#172](https://github.com/empath-nirvana/borrow-core/issues/172)).

**Loops.**
- A `while` or `loop` cannot raise, nor divide by a variable ([#522](https://github.com/empath-nirvana/borrow-core/issues/522), [#517](https://github.com/empath-nirvana/borrow-core/issues/517)).
- Some `for` shapes are refused: over a buffer's view inline in its borrow block ([#501](https://github.com/empath-nirvana/borrow-core/issues/501)), a lend
  in an `if` arm off the spine ([#502](https://github.com/empath-nirvana/borrow-core/issues/502)), a recursive call that threads an array ([#492](https://github.com/empath-nirvana/borrow-core/issues/492)), a view
  that is not a typed parameter ([#491](https://github.com/empath-nirvana/borrow-core/issues/491)); a div call in a counted `for` ([#503](https://github.com/empath-nirvana/borrow-core/issues/503)).
- A generator cannot use a capability across `yield` ([§15](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#15-entry-14--generators), [Iteration](guide/iteration.md#not-yet)).

**Effects.**
- A callback stored with its row ([#161](https://github.com/empath-nirvana/borrow-core/issues/161)); projection operations ([#160](https://github.com/empath-nirvana/borrow-core/issues/160)); an error raised in a
  fold's algebra ([#178](https://github.com/empath-nirvana/borrow-core/issues/178)); an error carrying an owned value ([#215](https://github.com/empath-nirvana/borrow-core/issues/215)).
- A block that uses a capability, called inside the callee's control `with` ([#487](https://github.com/empath-nirvana/borrow-core/issues/487)); a computation
  parameter called inside and outside its callee's handler ([§33](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#33-entry-32--computation-parameters-and-) *Open*); a resuming clause that
  cancels `k` and raises under two sites ([#514](https://github.com/empath-nirvana/borrow-core/issues/514)).
- Recursion: the budget and its calibration ([#230](https://github.com/empath-nirvana/borrow-core/issues/230)); `Exhausted` reaching `main` unhandled
  ([#228](https://github.com/empath-nirvana/borrow-core/issues/228)); answering capabilities and resuming operations inside a recursion ([#229](https://github.com/empath-nirvana/borrow-core/issues/229)); the
  `memo` layer.

**I/O and async.**
- One platform, WASI; a POSIX one is designed ([§34](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#34-entry-33--io-as-effects-the-platform-as-the-outermost-handler)). Two tasks cannot share an output stream
  ([§34](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#34-entry-33--io-as-effects-the-platform-as-the-outermost-handler) *Open*). A program that includes the I/O library but performs no I/O fails to run ([#515](https://github.com/empath-nirvana/borrow-core/issues/515)).
- Async has no event loop over real I/O, no wakers, no spawning from a scheduler handle, and no
  `imm` or segmented lend across `await` ([#52](https://github.com/empath-nirvana/borrow-core/issues/52), [§30](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#30-entry-29--effectful-blocks-and-async-tasks-at-the-surface) *Open*). A task's borrow across `await`
  rests on `PinLaw`, a stated hypothesis that is not proved ([§29](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#29-entry-28--a-borrow-held-across-a-suspension-the-relaxed-lend-r1-under-pinlaw)).

**Diagnostics.** Messages that name internal forms or the wrong construct ([#522](https://github.com/empath-nirvana/borrow-core/issues/522), [#503](https://github.com/empath-nirvana/borrow-core/issues/503), [#526](https://github.com/empath-nirvana/borrow-core/issues/526),
[#527](https://github.com/empath-nirvana/borrow-core/issues/527), [#145](https://github.com/empath-nirvana/borrow-core/issues/145)).

**Compiler and performance.**
- The compiler is tested against the interpreter on every program, not proved ([#15](https://github.com/empath-nirvana/borrow-core/issues/15)).
- Folds recurse on the WebAssembly stack ([#50](https://github.com/empath-nirvana/borrow-core/issues/50)); every use of a definition is a copy of its body
  ([#509](https://github.com/empath-nirvana/borrow-core/issues/509)); a call-scoped lend cell is not yet a stack slot ([#500](https://github.com/empath-nirvana/borrow-core/issues/500)); a fixed-size table is a heap
  allocation ([#496](https://github.com/empath-nirvana/borrow-core/issues/496)); the library's sort is an insertion sort ([#497](https://github.com/empath-nirvana/borrow-core/issues/497)); loops and array access
  against Rust ([#213](https://github.com/empath-nirvana/borrow-core/issues/213)).

## Open

Designed or tracked, not built.

| feature | tracked |
|---|---|
| Modules and packages | [#63](https://github.com/empath-nirvana/borrow-core/issues/63) |
| Files, the environment, the network, randomness, the exit status as effects | [§34](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md#34-entry-33--io-as-effects-the-platform-as-the-outermost-handler) *Open*, [#66](https://github.com/empath-nirvana/borrow-core/issues/66) |
| Interior mutability | [#119](https://github.com/empath-nirvana/borrow-core/issues/119) |
| Threads, fork-join parallelism | [#212](https://github.com/empath-nirvana/borrow-core/issues/212), [#22](https://github.com/empath-nirvana/borrow-core/issues/22) |
| Unsafe code: extern bodies the compiler compiles, with contracts in the trusted base | [#79](https://github.com/empath-nirvana/borrow-core/issues/79), decision 27 |
| Panics and backtraces on the unwind mechanism | [#192](https://github.com/empath-nirvana/borrow-core/issues/192) |
| A native (LLVM or C) backend | [#21](https://github.com/empath-nirvana/borrow-core/issues/21) |
| Libraries: JSON, regular expressions | [#65](https://github.com/empath-nirvana/borrow-core/issues/65), [#225](https://github.com/empath-nirvana/borrow-core/issues/225) |
| Variants in place, block provenance | [#19](https://github.com/empath-nirvana/borrow-core/issues/19), [#20](https://github.com/empath-nirvana/borrow-core/issues/20) |
| Sized types | [#72](https://github.com/empath-nirvana/borrow-core/issues/72) |

An extern today is checked against its declared type and, where the compiler has no
implementation for it, checked but not compiled; the theorems hold for every implementation that
meets its type:

```bc,check
extern c : ref i32

main : F i32 = return (free[i32] c)
```
