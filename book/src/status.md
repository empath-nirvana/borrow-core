# Status

borrow-core is young and still changing, but you can write real programs in it today. This page
says what works, what you are likely to trip over, and what is coming.

## What works today

- **Ownership and borrows**: `imm` and `mut` borrows, `&x` and `&mut x`, borrow blocks, `let mut`
  ([Ownership and borrows](guide/ownership.md))
- **Functions and closures**, reusable and one-shot
  ([Functions as values](guide/basics.md#functions-as-values))
- **Numbers**: `i32`, `i64`, `u8`, `f32`, `f64`; integer division by zero raises an error you can
  handle ([Numbers](guide/basics.md#numbers), [Division](guide/errors.md#division))
- **Records and variants** with `match` ([Records and variants](guide/basics.md#records-and-variants))
- **Recursive data**: lists and trees, folds, and types that hold a `Vec` of themselves
  ([Data and generics](guide/data.md))
- **Recursion**, with deep recursion on the heap ([Recursion](guide/data.md#recursion))
- **Arrays, views and slices**: split, swap, sort ([Arrays](guide/data.md#arrays))
- **Buffers and UTF-8 strings** ([Buffers and strings](guide/data.md#buffers-and-strings))
- **Generics**: generic functions and types ([Generic functions](guide/basics.md#generic-functions))
- **`poly` families**: operators, equality, hashing and order at your own types
  ([`poly` families](guide/data.md#poly-families))
- **Hash maps and sets** ([Maps and sets](guide/data.md#maps-and-sets))
- **Loops**: counted `for` with `break`, `continue` and `else`; `while` and `loop`
  ([Iteration](guide/iteration.md))
- **Generators and `|>` pipelines** ([Generators](guide/iteration.md#generators))
- **Effects and handlers**, with effects inferred ([Effects and handlers](guide/effects.md))
- **Errors** as `raise` and handlers, no `?` needed ([Errors](guide/errors.md))
- **I/O**: standard input, output and error, the clock and the command-line arguments
  ([Input and output](guide/io.md))
- **Async tasks**: `spawn`, `resume`, `cancel`, and a task that borrows its own data across
  `await` ([Async tasks](guide/async.md))
- **Two targets**: WebAssembly (`bcc run`) and native code through LLVM (`bcc run --native`),
  with the same I/O on both ([Getting started](getting-started.md))
- **Safety proved in Lean**: a program that compiles can't use memory after freeing it, free it
  twice or leak it ([What is proved](proved.md))

## Things you'll run into

**Types**
- No traits or bounds on type parameters (not implemented yet,
  [#489](https://github.com/empath-nirvana/borrow-core/issues/489)).
- No modules: everything shares one namespace (not implemented yet,
  [#63](https://github.com/empath-nirvana/borrow-core/issues/63)).
- The unit type is spelled `1`, not `()`
  ([#148](https://github.com/empath-nirvana/borrow-core/issues/148)).

**Syntax**
- No unary minus, `+=`, or bitwise and shift operators: write `0 - x`, `x = x + 1`,
  `host[and32](a, b)`, `host[shl64](n, 3)`
  ([#583](https://github.com/empath-nirvana/borrow-core/issues/583)).
- No indexing sugar such as `v[i]`
  ([#143](https://github.com/empath-nirvana/borrow-core/issues/143)).

**Borrows**
- `&x` and `&mut x` must be the whole call of a `let` or statement: write
  `let n = len(&v); f(n)`, not `f(len(&v))`
  ([#510](https://github.com/empath-nirvana/borrow-core/issues/510)).
- A borrow can't be lent on with `&mut m`; pass it and hand it back instead
  ([Borrow blocks](guide/ownership.md#borrow-blocks)).
- A generator can't use a capability, such as standard output, across a `yield`
  ([Iteration](guide/iteration.md#not-yet)).

**Loops and effects**
- A `while` or `loop` can't raise; raise after the loop, or use a counted `for`
  ([#522](https://github.com/empath-nirvana/borrow-core/issues/522)).
- A callback stored with its effects, rather than called, isn't supported yet
  ([#161](https://github.com/empath-nirvana/borrow-core/issues/161)).
- An error can't carry an owned value yet
  ([#215](https://github.com/empath-nirvana/borrow-core/issues/215)).

**I/O and async**
- No files, environment variables, network or randomness yet (the network is
  [#597](https://github.com/empath-nirvana/borrow-core/issues/597)).
- Async is cooperative and single-threaded, with no event loop over real I/O yet
  ([#52](https://github.com/empath-nirvana/borrow-core/issues/52)).

**Performance**
- Some programs are still slower than their Rust versions
  ([#213](https://github.com/empath-nirvana/borrow-core/issues/213)).

## On the roadmap

- Modules and packages ([#63](https://github.com/empath-nirvana/borrow-core/issues/63))
- Traits, or bounds on type parameters, and derived cases
  ([#489](https://github.com/empath-nirvana/borrow-core/issues/489))
- Operator sugar: unary minus, compound assignment, bitwise and shifts
  ([#583](https://github.com/empath-nirvana/borrow-core/issues/583))
- Networking ([#597](https://github.com/empath-nirvana/borrow-core/issues/597))
- Threads and parallelism ([#212](https://github.com/empath-nirvana/borrow-core/issues/212))
- Interior mutability ([#119](https://github.com/empath-nirvana/borrow-core/issues/119))
- Unsafe code and a C FFI ([#79](https://github.com/empath-nirvana/borrow-core/issues/79))
- Panics and backtraces ([#192](https://github.com/empath-nirvana/borrow-core/issues/192))
- Libraries: JSON ([#65](https://github.com/empath-nirvana/borrow-core/issues/65)), regular
  expressions ([#225](https://github.com/empath-nirvana/borrow-core/issues/225))
- Sized types ([#72](https://github.com/empath-nirvana/borrow-core/issues/72))
