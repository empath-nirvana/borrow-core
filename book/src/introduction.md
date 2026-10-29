# Introduction

borrow-core is a systems language for people who like Rust's ownership model and want a simpler
story for everything else. You own values and borrow them with `&` and `&mut`, as in Rust. There
is no garbage collector and no hidden reference counting: you write the allocations, and the
compiler inserts the frees. Errors, I/O, generators and async tasks are all one thing, *effects*,
served by ordinary handlers. Programs compile to WebAssembly or, through LLVM, to native code.

```bc
include textio

fn greet(n: i32) -> 1 =
  print_lit("hello, ");
  print_dec(n);
  print_byte(b'\n')

main -> i32 = greet(42); 0
-- output: hello, 42
-- answer: i32[0]
```

## What it is for

It's meant for the programs you'd write in Rust or C, such as command-line tools, services and
systems code, without fighting the borrow checker over errors and async.

- **One mechanism for effects.** Errors, I/O, iteration and async tasks are all *effects*: operations called like functions and given their meaning by
  handlers. `raise` is an operation, a generator is a function that performs `yield`, `await` is
  an operation, and standard output is an effect that `main` is given. There is no `Result`
  threaded by hand, no `?`, no separate exception system and no separate iterator protocol.
- **No coloured functions.** A function that raises, waits or writes is called like any other.
  The effects it performs are inferred, and the handler around the call serves them. A
  higher-order function such as `map` is written once and serves a pure callback, a failing one
  and an awaiting one alike.
- **Handlers compile away.** There is no handler stack and no run-time search. An operation that
  answers at once is a direct call; `raise` is a branch after each call that may raise; a task or
  generator that suspends is a state machine, the way Rust compiles `async fn`.
- **No garbage collector, and allocation where C or Rust would allocate.** Owned values are freed
  when their owner is done with them, by destructors the compiler inserts, and nothing is
  reference counted. A borrowed local and a handler's state live in the stack frame.
- **Safety that's proved, not just tested.** The rules are proved in Lean: if your program
  compiles, it doesn't use freed memory, free anything twice or leak, and a function the compiler
  calls total really does finish. [What is proved](proved.md) has the details.

Here is most of that in one program: a flaky service, a generic `retry` with exponential
backoff, and a fake timer to test it with.

```bc
include fail
include textio

effect Timer { fn pause_for(ms: i32) }

-- A flaky service: down for its first two attempts.
fn call(attempt: i32) -> i32 with Fail[i32] =
  if attempt < 2 { raise(503) } else { 200 }

-- Try `f` up to `times` times, doubling the pause after each failure.
fn retry[A](times: i32, base: i32, f: !(i32 => A with Fail[i32])) -> A with Fail[i32], Timer =
  let mut pause = base;
  let mut last = 0;
  let r : Option[A] = for attempt in 0..times {
    match with to_result { f(attempt) } {
      inl a -> break Some(a)
    | inr e -> last = e; if attempt + 1 < times { pause_for(pause); pause = pause * 2 }
    }
  } else { None };
  match r { Some(a) -> a | None -> raise(last) }

-- A fake timer for testing: it adds up the time it was asked to wait.
handler fake_timer(mut waited: i32): Timer = { pause_for(ms) = { waited = waited + ms; () } }

fn attempt(times: i32) -> 1 =
  let c = alloc(0);
  let r = with fake_timer(&mut c) {
    with to_result { retry(times, 10, !{ n -> call(n) }) }
  };
  match r {
    inl ok -> print_lit("ok "); print_dec(ok)
  | inr e -> print_lit("gave up: "); print_dec(e)
  };
  print_lit(" after waiting "); print_dec(free(c)); print_lit("ms\n")

main -> 1 = attempt(5); attempt(2)
-- output: ok 200 after waiting 30ms
-- output: gave up: 503 after waiting 10ms
-- answer: ()
```

`raise` is an operation, and `with to_result { … }` is the handler that turns it into a value.
`retry` never says which timer it uses; its caller picks one, here a fake that just adds up the
waits. [Errors](guide/errors.md) and
[Effects and handlers](guide/effects.md) explain each piece.

It's still young: modules, traits, files and networking, threads and a real async event loop
aren't built yet. See [Status](status.md).

## How this book is organised

- **The language** teaches the surface language in the order a programmer meets it: values and
  functions, ownership, data and generics, errors, input and output, iteration, effects, async.
- **How it elaborates** shows the *core* the surface is translated into before checking: a
  call-by-push-value calculus in which every bind, thunk and borrow is written out. It is for
  readers who want to see what a program means to the checker and the proofs.
- **The reference** states the core syntax, the constants and their types, and the checker's
  errors.
- **About the project** has the status page, the theorems, how to contribute, the design
  decisions and a glossary.

Every example in this book is a program that the test suite checks and runs, and its output is
the output shown.
