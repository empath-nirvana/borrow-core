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
`d(())`, and `map_err(f)` raises `f(e)` to the handler around it. A function that raises writes its
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
  let z: i32 = borrow imm b { v -> with default(!{ u -> 0 }) { twice(v) } };
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
`A + E`. Its clauses are `!` code, so what a handler is given is a `!` value, such as `default`'s
function.

An abort unwinds: what the abandoned code owned is dropped by its destructors, and a borrow it
was inside ends, the place going back to its owner. A value with no destructor (a thunk, a
capability) cannot be live where an abort may leave: the checker names it. A `raise` in the body
of a counted `for` leaves the loop by its exit and is raised again after it.

## Not yet

An operation inside a closure (a callback passed or stored, or a fold's algebra), functions over
computations (`retry`, `|>` into a handler), named instances when two handlers of one effect are
in scope, and operations that answer a borrow into the handler's state are later stages (SPEC §18
*Open*).
