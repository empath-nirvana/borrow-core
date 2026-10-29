# Status

borrow-core is young and still changing, but you can write real programs in it today. This page
says what works, what you are likely to trip over, and what is coming. It is the one place the
book lists what isn't built yet.

## What works today

- **Ownership and borrows**: `imm` and `mut` borrows, `&x` and `&mut x`, borrow blocks, `let mut`
  ([Ownership and borrows](guide/ownership.md))
- **Functions and closures**, reusable and one-shot
  ([Functions as values](guide/basics.md#functions-as-values))
- **Numbers**: `i32`, `i64`, `u8`, `f32`, `f64`; integer division by zero raises an error you can
  handle ([Numbers](guide/basics.md#numbers), [Division](guide/errors.md#division))
- **Records and variants** with `match` ([Records and variants](guide/basics.md#records-and-variants))
- **Recursive data**: lists and trees, folds, and types that hold a `Vec` or an array of
  themselves ([Data and generics](guide/data.md))
- **Recursion**, with deep recursion on the heap ([Recursion](guide/data.md#recursion))
- **Arrays, views and slices**: split, swap, sort ([Arrays](guide/data.md#arrays))
- **Vectors, buffers and UTF-8 strings** ([Buffers and strings](guide/data.md#buffers-and-strings))
- **Generics**: generic functions and types ([Generic functions](guide/basics.md#generic-functions))
- **`poly` families**: operators, equality, hashing and order at your own types
  ([`poly` families](guide/data.md#poly-families))
- **Hash maps and sets** ([Maps and sets](guide/data.md#maps-and-sets))
- **Loops**: counted `for` with `break`, `continue` and `else`; `while` and `loop`; bounded runs
  with `div_fuel` ([Iteration](guide/iteration.md))
- **Generators and `|>` pipelines** ([Generators](guide/iteration.md#generators))
- **Effects and handlers**, with effects inferred ([Effects and handlers](guide/effects.md))
- **Errors** as `raise` and handlers, no `?` needed ([Errors](guide/errors.md))
- **I/O**: standard input, output and error, the clock and the command-line arguments
  ([Input and output](guide/io.md))
- **Async tasks**: `spawn`, `resume`, `cancel`, logged and scoped tasks, and a task that borrows
  its own data across `await` ([Async tasks](guide/async.md))
- **Two targets**: WebAssembly (`bcc run`) and native code through LLVM (`bcc run --native`),
  with the same I/O on both ([Getting started](getting-started.md))
- **Safety proved in Lean**: a program that compiles can't use memory after freeing it, free it
  twice or leak it ([Safety guarantees](safety.md))

## Things you'll run into

**Types and syntax**
- The unit type is spelled `1`, not `()`
  ([#148](https://github.com/empath-nirvana/borrow-core/issues/148)).
- No unary minus, `+=`, or bitwise and shift operators: write `0 - x`, `x = x + 1`,
  `host[and32](a, b)`, `host[shl64](n, 3)`
  ([#583](https://github.com/empath-nirvana/borrow-core/issues/583)).
- No indexing sugar such as `v[i]`
  ([#143](https://github.com/empath-nirvana/borrow-core/issues/143)).
- `total`, `leaf`, `node` and `swap` are reserved, so they can't be names of variables or
  functions.
- `==` doesn't compare two `bool`s; use `if` or `match`.
- An `if` or `borrow` block can't be a call's argument: bind it with `let` first.

**Borrows**
- `&mut r.field` doesn't parse: take the record apart, borrow the field, and build it again.
- `&x` and `&mut x` must be the whole call of a `let` or statement: write
  `let n = len(&v); f(n)`, not `f(len(&v))`
  ([#510](https://github.com/empath-nirvana/borrow-core/issues/510)).
- A heap cell can't be lent with `&c` to a function that does I/O or performs an effect; lend it
  with a block instead, `borrow imm c { r -> show(r) }`.
- A borrow can't be lent on with `&mut m`; pass it and hand it back instead
  ([Borrow blocks](guide/ownership.md#borrow-blocks)).
- Two borrow blocks can't be nested over two different owners; inside a block, lend the second
  owner to a call with `&d` instead.
- A `for` over a view of a buffer or string must be in a function that takes the view, not
  directly inside the `borrow` block (a view of an array works either way).

**Data**
- A text view can be used only once, so a word can't be looked up in a map and then inserted as
  a key.
- Folds (`fold_imm`, `fold_own`, `fold_reuse`) don't walk a type that holds a `Vec` of itself;
  write the recursion, as in [Collections of recursive data](guide/data.md#collections-of-recursive-data).

**Loops, generators and effects**
- The body of a `while` or `loop` can't perform an operation that a handler in the program
  serves: no `raise`, no division by a variable, and no operation of your own effects. The
  platform's I/O works. Use a counted `for`, or do it after the loop
  ([#522](https://github.com/empath-nirvana/borrow-core/issues/522)).
- A generator can't use a capability, such as standard output, across a `yield`. The body of a
  `for` over a library adapter (`map`, `filter`, `take`, …), or over a generator that calls
  another generator directly, can't do I/O: collect the values in the loop and print after it.
- A callback stored with its effects, rather than called, isn't supported yet
  ([#161](https://github.com/empath-nirvana/borrow-core/issues/161)).
- An effect can't mix answering (`fn`) and control (`ctl`) operations, and an operation can't
  answer with a borrow into its handler's state.
- An error can't carry an owned value yet
  ([#215](https://github.com/empath-nirvana/borrow-core/issues/215)).
- A reusable closure that keeps state between calls (Rust's `FnMut`) has no surface syntax yet; a
  handler with state does the same job ([Effects and handlers](guide/effects.md)).

**I/O and async**
- A program can't set its exit status.
- Async is cooperative and single-threaded, with no event loop over real I/O, platform timers or
  wakers yet ([#52](https://github.com/empath-nirvana/borrow-core/issues/52)).
- A task can hold a `mut` borrow across `await`, but not an `imm` one, and two tasks can't share
  one output stream.

**Performance**
- Some programs are still slower than their Rust versions
  ([#213](https://github.com/empath-nirvana/borrow-core/issues/213)).

## On the roadmap

- Modules and packages ([#63](https://github.com/empath-nirvana/borrow-core/issues/63))
- Traits, or bounds on type parameters, and derived cases
  ([#489](https://github.com/empath-nirvana/borrow-core/issues/489))
- Operator sugar: unary minus, compound assignment, bitwise and shifts
  ([#583](https://github.com/empath-nirvana/borrow-core/issues/583))
- Files, environment variables and randomness; networking ([#597](https://github.com/empath-nirvana/borrow-core/issues/597))
- Threads and parallelism ([#212](https://github.com/empath-nirvana/borrow-core/issues/212))
- Interior mutability ([#119](https://github.com/empath-nirvana/borrow-core/issues/119))
- Unsafe code and a C FFI ([#79](https://github.com/empath-nirvana/borrow-core/issues/79))
- Panics and backtraces ([#192](https://github.com/empath-nirvana/borrow-core/issues/192))
- Libraries: JSON ([#65](https://github.com/empath-nirvana/borrow-core/issues/65)), regular
  expressions ([#225](https://github.com/empath-nirvana/borrow-core/issues/225))
- Sized types ([#72](https://github.com/empath-nirvana/borrow-core/issues/72))
