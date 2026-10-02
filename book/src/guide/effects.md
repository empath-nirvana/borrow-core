# Effects and handlers

An **effect** is a set of operations; a **handler** gives each operation a clause over a state of
its own; `with h(e) { … }` runs a block with `h` handling the effect. An operation is called like
a function. Spellings are provisional (SPEC §18, decisions 51 and 55).

```bc
-- answer: i32[12]
effect Counter { fn tick() -> i32 }

handler count(mut n: i32): Counter = { tick() = { n = n + 1; n } }

main -> i32 = with count(0) { let a = tick(); let b = tick(); a * 10 + b }
```

In a clause the handler's state, here `n`, is a `let mut` variable: the clause may assign it,
and its value is the operation's answer.

## What a handler is

A handler is defined by what it elaborates to (`bcc desugar` prints it), and that is the
program you would write by hand in capability-passing style:

- each clause is a function over a `mut` borrow of the state, run by `modify`: here
  `count__tick(c: mut 'l i32) -> mut 'l i32 * i32`, which hands the borrow back;
- `with count(0) { … }` is a borrow block of a cell holding the state: the block's parameter is
  the **capability**, the borrow;
- each `tick()` is a call of `count__tick` on the capability, which is bound again after it.

So a handler adds nothing at run time: no handler stack, no search, no dispatch. `bcc check`
reports each handler's shape and, per call site, which clause an operation calls.

## Functions that perform effects

A function that calls an operation, or calls a function that does, has the effect in its
**row**, which is inferred, never written. It runs under whichever handler is in scope where it
is called: it is elaborated once per handler, as a generic function is once per type.

```bc
-- answer: (i32[3], i32[30])
include slice

effect Log { fn note(x: i32) }

handler summed(mut s: i32): Log = { note(x) = { s = s + x; () } }
handler count(mut n: i32): Log = { note(x) = { n = n + 1; () } }

fn walk<'a>(v: array_imm 'a i32) -> 1 =
  for p in v { note(*p) };
  ()

main -> i32 * i32 =
  let a = array_new[i32] (3, !{ i -> (i + 1) * 5 });
  let c = alloc(0);
  let t = alloc(0);
  borrow imm a { v -> with count(&mut c) { walk(v) } };
  borrow imm a { v -> with summed(&mut t) { walk(v) } };
  (free(c), free(t))
```

`with h(&mut c) { … }` lends the state from a cell, which holds the final state after the
block. `walk` is copied twice, `walk__count` and `walk__summed`, each calling its handler's
clause directly.

## Control effects and errors

An operation declared `ctl` is a **control** operation: its handler receives the rest of the
computation, its continuation, and decides whether and how to go on (SPEC §19). Each `with` of a
control handler is a handler of its own, and an operation goes to the innermost one of its effect.
An operation that answers `never` cannot be resumed: it is **abortive**, and its clause receives
only its argument.

Errors are such an effect, `Fail[E]`, declared in the library (`include fail`) with three
handlers: `to_result` answers `inl` the value or `inr` the error, `default(d)` the value or
`d`, and `map_err(f)` raises `f(e)` to the handler around it. A function that raises writes its
error type in its row, `with Fail[E]`, unless it gets it from a function it calls. There is no
`?`: a call of a function that raises propagates the error by itself.

```bc
-- answer: (inl i32[60], (inr i32[2], i32[0]))
include slice
include fail

-- The sum of the elements; a negative one raises its index.
fn checked<'a>(v: array_imm 'a i32) -> i32 with Fail[i32] =
  let mut s = 0;
  let mut i = 0;
  for p in v { let x = *p; if x < 0 { raise(i) } else { () }; s = s + x; i = i + 1 };
  s

-- A function that calls one that raises raises too: its row is inferred.
fn twice<'a>(v: array_imm 'a i32) -> i32 = checked(v) * 2

fn good(i: i32) -> i32 = i * 10
fn bad(i: i32) -> i32 = if i == 2 { 0 - 1 } else { i }

main -> (i32 + i32) * ((i32 + i32) * i32) =
  let a = array_new[i32] (3, good);
  let b = array_new[i32] (3, bad);
  let x: i32 + i32 = borrow imm a { v -> with to_result { twice(v) } };
  let y: i32 + i32 = borrow imm b { v -> with to_result { twice(v) } };
  let z: i32 = borrow imm b { v -> with default(0) { twice(v) } };
  (x, (y, z))
```

A handler is an ordinary declaration. `to_result` is

```bc,ignore
effect Fail[E] { ctl raise(e: E) -> never }

handler to_result[E, A]: Fail[E], A -> A + E = {
  return(a) = inl a;
  raise(e) = inr e
}
```

`Fail[E], A -> A + E` says that it handles `Fail[E]` around a body of type `A`, and answers
`A + E`. Every operation of `Fail` is abortive, so a clause runs at most once, after the handler:
what a handler is given is an ordinary value, such as `default`'s fallback, owned and dropped when
the body answers, and a clause may use the capabilities in scope at the `with`.

An operation that resumes passes its continuation `k` to its clause, and `k(v)` resumes it: the
body goes on with `v` as the operation's answer, and `k(v)` answers what the handler answers for
the rest of the body. Such a clause may run many times, once per operation, so what it uses is
the handler's **state**: its parameters (`mut` ones may be assigned) and the capabilities its
clauses use, passed to each clause and, at each resume, to the rest of the body.

```bc
effect Ask { ctl ask() -> i32 }

-- Answers each `ask` with the cell's content, which it then increments.
handler asking(mut c: ref i32): Ask, i32 -> i32 = {
  return(a) = a + free(c);
  ask(k) = { let v = free(c); c = alloc(v + 1); k(v) }
}

main -> i32 = with asking(alloc(5)) { let x = ask(); let y = ask(); x * 10 + y }
-- answer: i32[63]
```

The two `ask`s read 5 and 6, and the return clause adds the cell's last content, 7.

An abort unwinds: what the abandoned code owned is dropped by its destructors, and a borrow it
was inside ends, the place going back to its owner. A value with no destructor (a thunk, a
capability) cannot be live where an abort may leave: the checker names it. A `raise` in the body
of a counted `for` leaves the loop by its exit and is raised again after it.

## Passing computations

A function may take a computation: a parameter of a function type, `body: !(1 => A)`, is a
**computation parameter**, and a closure or a function passed there may perform effects (SPEC §22,
decision 57). What it performs goes to the handlers where it was written, through the function
that runs it, unless the parameter's type says the function **provides** it: `body: !(1 => A) with
Fail[E]` says that `retry` handles the `Fail` of what it is given.

```bc
-- answer: ((inl i32[300], inr i32[5]), i32[5])
include fail

effect Count { fn tick() -> i32 }
handler count(mut n: i32): Count = { tick() = { n = n + 1; n } }

-- Runs `body` at most `n` times, until it does not raise; the last error is raised.
fn retry[A, E](body: !(1 => A) with Fail[E], n: i32) -> A with Fail[E] =
  let r = for i in 1..n {
    match body() |> to_result { inl a -> break (inl a : A + 1) | inr e -> () }
  } else { (inr () : A + 1) };
  match r { inl a -> a | inr u -> body() }

-- Fails until its `k`-th tick.
fn flaky(k: i32) -> i32 with Count, Fail[i32] =
  let t = tick();
  if t < k { raise(t) } else { t * 100 }

main -> ((i32 + i32) * (i32 + i32)) * i32 =
  let c = alloc(0);
  let k = 3;
  let r = with count(&mut c) {
    let a = retry({ u -> flaky(k) }, 5) |> to_result;
    let b = flaky(10) |> retry(2) |> to_result;
    (a, b)
  };
  (r, free(c))
```

The first computation fails at ticks 1 and 2 and answers at 3; the second fails at both of its
attempts, and its second error, at tick 5, reaches the caller.

- **`|>`** puts its left side first (decision 50): `e |> retry(2)` is `retry(e, 2)`, `e` passed as
  a computation since `retry`'s first parameter is one, and `e |> to_result` is
  `with to_result { e }`, since `to_result` is a handler. A chain applies innermost first.
- **The callback is a closure value**: its code, `!` code that takes its capabilities and the
  variables it captures (`k`, its **environment**) first and hands them back, and the environment
  itself, passed beside them. `retry` is elaborated once for each **profile** of the callbacks it
  is given (what they perform, and what serves it), not once per callback: both calls here are
  calls of one copy of `retry` for `Count`, its parameter the callback's code.
- **What `retry` provides is at its port.** The callback's `raise` goes to `retry`'s
  `to_result`, a handler named by `retry`'s port for `Fail`; the last attempt, outside it, raises
  again at the caller's handler. The callback's `tick` goes to `count` in `main`: its capability
  is lent again to each attempt, so an attempt that raises gives it back, and the next attempt
  sees its ticks.
- **A computation parameter is second class**: it is called, or passed on at another function's
  computation parameter, and never stored, returned or bound to a value. A callback captures
  variables it does not bind again: state it keeps belongs in a handler's capability, which it
  may share with its caller and with other callbacks.

The library's `lib/callbacks.bc` has `each`, `fold`, `map_buf` and `filter_buf` over counts, and
`attempt` and `retry`, each written once:

```bc
-- answer: ((i32[20], i32[10]), inr i32[3])
include callbacks

effect Log { fn note(x: i32) }
handler tally(mut n: i32): Log = { note(x) = { n = n + x; () } }

fn check(x: i32) -> i32 with Fail[i32] = if x > 2 { raise(x) } else { x }

main -> (i32 * i32) * (i32 + i32) =
  let l = alloc(0);
  let q = with tally(&mut l) { fold(5, 0, { (s, i) -> note(i); s + i * 2 }) };
  let r = fold(5, 0, { (s, i) -> s + check(i) }) |> to_result;
  ((q, free(l)), r)
```

`fold` logs and raises through the same source: a copy for the logging callback, one for the
raising one, and `fold` itself for a callback that does neither.

## Not yet

A callback stored in data, returned, or bound to a value (R6 of decision 57), a callback whose
parameter is itself a computation, and codata whose observations perform effects are not built
(`corpus/pending/cb-*.bc`); an operation inside a fold's algebra waits for K4. Named instances
when two handlers of one effect are in scope, and operations that answer a borrow into the
handler's state, are later stages (SPEC §18 *Open*).
