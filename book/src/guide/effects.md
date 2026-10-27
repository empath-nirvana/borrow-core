# Effects and handlers

An **effect** is a set of operations; a **handler** gives each operation a meaning; `with h { … }`
runs a block with `h` handling the effect. An operation is called like a function. Errors
([Errors](errors.md)), I/O ([Input and output](io.md)), generators ([Iteration](iteration.md)) and
tasks ([Async tasks](async.md)) are all effects of this one kind, declared in the library; this
chapter is the mechanism they share.

There are no colored functions. A function that performs an effect is called like any other; its
row, the effects it performs, is inferred, and the handler that serves them is the one around
the call. Handlers are compiled away: an operation that answers at once is a direct call of its
clause, an error is a branch after the call, and a computation that suspends is a state machine.
There is no handler stack and no run-time search.

## Answering operations

An operation declared `fn` answers its caller at once. Its handler has a state, its `mut`
parameter, which each clause may read and assign:

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

So an answering handler adds nothing at run time: no handler stack, no search, no dispatch.
`bcc check` reports each handler's shape and, per call site, which clause an operation calls.

## Functions that perform effects

A function that calls an operation, or calls a function that does, has the effect in its
**row**, which is inferred. It runs under whichever handler is in scope where it is called: it
is elaborated once per handler, as a generic function is once per type.

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

A row may be written after the result type, `fn f(…) -> T with Log, Fail[i32]`: a promise the
checker holds the function to. An effect is either answering or control (below), never both.

## Control operations and their continuation

An operation declared `ctl` is a **control** operation: its clause receives the rest of the
computation, its continuation `k`, and decides whether and how to go on (SPEC §19). `k(v)`
resumes the body with `v` as the operation's answer, and answers what the handler answers for
the rest of the body. The qualifier says how often the continuation may be resumed:

| declared | the clause |
|---|---|
| `ctl op(…) -> B` | resumes `k` at most once; if it does not, the rest of the body is cancelled |
| `linear ctl op(…) -> B` | resumes `k` exactly once |
| `ctl op(…) -> never` | receives no `k`: the operation is **abortive**, as `raise` is |

A control handler names the type of the body it handles and what it answers, `Peek, i32 -> i32`
below, and its `return(a)` clause receives the body's value. Here the handler resumes while the
values are small and abandons the body at the first large one:

```bc
effect Peek { ctl peek(x: i32) -> bool }

-- Resumes with `true` while the value is small; at the first large one, stops the body there.
handler until_large: Peek, i32 -> i32 = {
  return(a) = a;
  peek(x, k) = if x < 100 { k(true) } else { 0 - x }
}

fn walk(n: i32) -> i32 =
  let c = alloc(0);
  let mut s = 0;
  for i in 0..n { if peek(i * i) { s = s + 1 } else { () } };
  s + free(c)

main -> i32 * i32 = (with until_large { walk(5) }, with until_large { walk(20) })
-- answer: (i32[5], i32[4294967196])
```

When the clause does not resume, the rest of `walk` is cancelled: what it owns, the cell `c`, is
freed by its destructor, and the run ends with `live 0`.

A clause may run many times, once per operation, so what it uses is the handler's **state**: its
parameters (`mut` ones may be assigned) and the capabilities its clauses use, passed to each
clause and, at each resume, to the rest of the body.

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

Each `with` of a control handler is a handler of its own, with a static name the compiler
assigns, and each operation is resolved at compile time to the innermost one around it. An
operation that may suspend compiles to a state machine: the code after it is a resume point of
the function's machine, as an `async fn` is in Rust.

## Several instances, and names

`Fail[i32]` and `Fail[ParseError]` are two **instances** of `Fail`, and a row may hold both (SPEC
§38). An operation goes to the innermost handler of its instance, read off its argument's type, so
nesting two handlers in either order changes nothing. Two handlers of one instance are told apart
by name: `with n = h(…) { … }` names a handler, `n.op(v)` performs at it, and a row may name its
entries, `with src: Kube, dst: Kube`, each served by the handler of its name where the function is
called. An operation whose instance is not known (a literal, `raise(1)`) where two instances are
in scope is an error that asks for an ascription, `raise((1 : u8))`, or a name.

```bc
-- answer: ((inr i32[4294967295], inl (inr u8[2])), (inl (inr i32[1]), inr i32[2]))
include fail

-- Raises its own error, an `i32`, or a `u8` from `small`: two instances, no conversion between them.
fn small(n: i32) -> i32 with Fail[u8] = if n > 9 { raise(u8[2]) } else { n }
fn check(n: i32) -> i32 with Fail[i32], Fail[u8] = if n < 0 { raise(n) } else { small(n) }

-- Each raise reaches its own instance's handler, whatever their order.
fn both(n: i32) -> (i32 + u8) + i32 = with to_result[i32, i32 + u8] { with to_result[u8, i32] { check(n) } }

-- Two handlers of one instance: `raise` goes to the inner one, `outer.raise` to the outer one.
fn pick(b: bool) -> (i32 + i32) + i32 =
  with outer = to_result[i32, i32 + i32] {
    with to_result[i32, i32] { if b { raise(1) } else { () }; if b { () } else { outer.raise(2) }; 0 } }

main -> (((i32 + u8) + i32) * ((i32 + u8) + i32)) * (((i32 + i32) + i32) * ((i32 + i32) + i32)) =
  ((both(0 - 1), both(10)), (pick(true), pick(false)))
```

A generic function keeps its meaning at every instance: in `f[E]` with the row
`Fail[E], Fail[ParseError]`, an operation goes to the entry it is at `f`'s own types, and at
`E := ParseError` the two entries are still two, served by one handler. A handler of `Fail[E]`
inside `f` does not catch a `Fail[ParseError]` that passes it at that instance
(`corpus/effects-abstraction.bc`).

## Blocks that perform effects

A closure passed to a function at a parameter of function type is a **block**. Its type names no
effect, and its operations go to the handlers around it where it is written, never to a handler
inside the function it is passed to. The function is copied at the block's row, as it is per
handler above, so one function serves pure blocks and effectful ones with nothing written.

```bc
-- answer: (i32[11], inr ())
include fail

fn twice(f: !(i32 => i32), x: i32) -> i32 = f(f(x))

fn guarded(f: !(i32 => i32)) -> i32 = with default[1, i32](0) { f(1) }

main -> i32 * (i32 + 1) =
  let a = twice(!{ x -> x + 5 }, 1);
  let b = with to_result[1, i32] { guarded(!{ x -> raise(()) }) };
  (a, b)
```

`twice` is used as written; `guarded` is copied at the block's row, and the block's `raise` passes
`guarded`'s own `default` to reach `to_result` (`bcc check` reports the copy and where the block's
operations go). A block is called, or passed on to another function's block parameter: it is
never stored or returned (SPEC §30).

A block may use a handler's capability, or yield to a `for` it is written inside: it takes what it
uses at each call and hands it back, and the function's copy passes it along (SPEC §32).

## Computation parameters and `|>`

Sometimes the function *should* handle what its argument does: `retry` catches the errors of the
attempt it is given, a timeout stops it. A parameter whose function type carries a row,
`f: !(i32 => A with Fail[i32])`, is a **computation parameter**: the callee serves the listed
effects of each call `f(…)`, with the handlers around that call in the callee. Every other effect
of the argument still goes where the argument is written (SPEC §33).

```bc
include fail

effect Wait { fn pause(ms: i32) }

handler fake_wait(mut waited: i32): Wait = { pause(ms) = { waited = waited + ms; () } }

-- A flaky service: unavailable until its third attempt.
fn call(attempt: i32) -> i32 with Fail[i32] = if attempt < 2 { raise(503) } else { 200 }

-- `f(0)`, `f(1)`, … until one answers, pausing `base`, `2 * base`, … between attempts; after
-- `times` failures, the last error is raised.
fn retry[A](times: i32, base: i32, f: !(i32 => A with Fail[i32])) -> A with Fail[i32], Wait =
  let mut gap = base;
  let mut last = 0;
  let r = for attempt in 0..times {
    match with to_result { f(attempt) } {
      inl a -> break (inl a : A + 1)
    | inr e -> last = e; if attempt + 1 < times { pause(gap); gap = gap * 2 } else { () }
    }
  } else { (inr () : A + 1) };
  match r { inl a -> a | inr u -> raise(last) }

fn with_budget(times: i32) -> (i32 + i32) * i32 =
  let c = alloc(0);
  let r = with fake_wait(&mut c) {
    with to_result { retry(times, 10, !{ attempt -> call(attempt) }) }
  };
  (r, free(c))

main -> ((i32 + i32) * i32) * ((i32 + i32) * i32) = (with_budget(5), with_budget(2))
-- answer: ((inl i32[200], i32[30]), (inr i32[503], i32[10]))
```

With five attempts the third answers 200 after waits of 10 and 20; with two, both fail and the
last error reaches the caller. Written as a plain block parameter, `f: !(i32 => A)`, the block's
`raise` would go to the `to_result` in `with_budget`, where it is written, and nothing would be
retried. A named function passed at either kind of parameter means the same as the block that
calls it: `retry(3, 10, call)` is `retry(3, 10, !{ a -> call(a) })`.

`e |> h` applies a stage to a computation: when `h` is a handler, `e |> h(…)` is
`with h(…) { e }`, and when `h` is a function whose first parameter is a computation parameter,
it is `h(!{ () -> e }, …)`. A chain reads in the order it runs, innermost first:
`step() |> timeout |> retry(3, 10) |> logged` (`corpus/reconcile-chain.bc`,
`corpus/pipe-handlers.bc`). For any other function, `e |> f(a)` is `f(e, a)`
([Iteration](iteration.md#pipelines)).

## Not yet

- An operation inside a closure that is stored or returned rather than called (a stored
  callback with a row, #161), or inside a fold's algebra (#178).
- An effect with both answering and control operations; type parameters on an answering effect;
  an answering operation performed inside a clause of an answering handler.
- A computation parameter called both inside and outside the callee's own handler of its effect,
  and an argument that uses a capability under the callee's handler (#487).
- Renaming a handler to serve a row entry of another name; an operation that answers a borrow
  into the handler's state (#160). SPEC §18 *Open*, §30 *Open*, §33 *Open* and §38 list the rest.
