# Introduction

borrow-core is a systems language for people who like Rust's ownership model and want a simpler
story for everything else. You own values and borrow them with `&` and `&mut`, as in Rust. There
is no garbage collector and no hidden reference counting: you write the allocations, and the
compiler inserts the frees. Programs compile to WebAssembly or, through LLVM, to native code.

```bc
include textio

fn greet(n: i32) -> 1 =
  print_lit("hello, ");
  print_dec(n);
  print_byte(b'\n')

main -> 1 = greet(42)
-- output: hello, 42
```

It's meant for the programs you'd write in Rust or C, such as command-line tools, services and
systems code, without fighting the borrow checker over errors and async.

- **One mechanism for effects.** Errors, I/O, generators and async tasks are all *effects*:
  operations called like functions, given their meaning by a handler further up. `raise` is an
  operation, a generator is a function that performs `yield`, and `await` is an operation. There
  is no `Result` threaded by hand, no `?`, no separate exception system and no separate iterator
  protocol.
- **No coloured functions.** A function that raises, waits or writes is called like any other.
  Its effects are inferred, and the handler around the call serves them. A higher-order function
  such as `map` is written once and serves a pure callback, a failing one and an awaiting one
  alike.
- **Handlers compile away.** There is no handler stack and no run-time search. An operation that
  answers at once is a direct call, `raise` is a branch after each call that may raise, and a task
  or generator that suspends is a state machine, the way Rust compiles `async fn`.
- **No garbage collector, and allocation where C or Rust would allocate.** Owned values are freed
  when their owner is done with them, and nothing is reference counted. A borrowed local and a
  handler's state live in the stack frame.
- **Safety that's proved, not just tested.** If your program compiles, it doesn't use freed
  memory, free anything twice or leak ([Safety guarantees](safety.md)).

The chapters under *The language* teach it in the order you meet it: values and functions,
ownership, data, errors, I/O, iteration, effects and async. [Effects and
handlers](guide/effects.md#computation-parameters-and-) ends with a generic `retry` with
exponential backoff, tested against a fake timer, which uses most of it at once.
[Recipes](recipes.md) shows short programs for everyday tasks, and the [Language
reference](language-reference.md) and [Standard library](stdlib.md) are for looking things up.

The language is young, and [Status](status.md) lists what isn't built yet. Every example in this
book is a program the test suite runs, and the output shown is its output.
