# Effects and handlers

An **effect** is a set of operations. A **handler** gives each operation a meaning, and
`with h { … }` runs a block with `h` handling the effect. You call an operation like a function.
Errors ([Errors](errors.md)), I/O ([Input and output](io.md)), generators
([Iteration](iteration.md)) and tasks ([Async tasks](async.md)) are all effects of this one kind,
declared in the library. This chapter covers the mechanism they share.

There are no coloured functions. A function that performs an effect is called like any other.
Its row (the effects it performs) is inferred, and the handler around the call serves them.
Handlers compile away: an operation that answers straight away is a direct call of its clause,
an error is a branch after the call, and a computation that suspends is a state machine. There
is no handler stack and no search at run time.

## Answering operations

An operation declared `fn` answers its caller straight away. Its handler can keep state in a
`mut` parameter, which each clause can read and assign:

```bc
-- answer: i32[12]
effect Counter { fn tick() -> i32 }

handler count(mut n: i32): Counter = { tick() = { n = n + 1; n } }

main -> i32 = with count(0) { let a = tick(); let b = tick(); a * 10 + b }
```

Inside a clause, the state (`n` here) behaves like a `let mut` variable, and the clause's value
is the operation's answer.

## What a handler is

A handler is shorthand for a program you could write by hand, passing a capability around
(`bcc desugar` shows it):

- each clause is a function over a `mut` borrow of the state, run by `modify`: here
  `count__tick(c: mut 'l i32) -> mut 'l i32 * i32`, which hands the borrow back;
- `with count(0) { … }` is a borrow block of a cell holding the state: the block's parameter is
  the **capability**, the borrow;
- each `tick()` is a call of `count__tick` on the capability, which is bound again after it.

`bcc check` reports, for each call site, which clause an operation calls.

## Functions that perform effects

A function that calls an operation, or calls a function that does, has the effect in its
**row**, which is inferred. It runs under whichever handler is in scope where it's called. The
compiler makes one copy of it per handler, the way a generic function gets one copy per type.

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

`with h(&mut c) { … }` lends the state from a cell, and the cell holds the final state after the
block. `walk` is compiled twice, once per handler, and each copy calls its handler's clause
directly.

You can write a row after the result type, `fn f(…) -> T with Log, Fail[i32]`, and the checker
holds the function to it. An effect is either answering or control (below), not both.

## Control operations and their continuation

An operation declared `ctl` is a **control** operation. Its clause receives the rest of the
computation as a continuation `k` and decides whether and how to go on. `k(v)` resumes the body
with `v` as the operation's answer, and returns what the handler returns for the rest of the
body. The declaration says how often `k` may be resumed:

| declared | the clause |
|---|---|
| `ctl op(…) -> B` | resumes `k` at most once; if it does not, the rest of the body is cancelled |
| `linear ctl op(…) -> B` | resumes `k` exactly once |
| `ctl op(…) -> never` | receives no `k`: the operation is **abortive**, as `raise` is |

A control handler names the type of the body it handles and what it returns (`Peek, i32 -> i32`
below), and its `return(a)` clause receives the body's value. This handler resumes while the
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

When the clause doesn't resume, the rest of `walk` is cancelled. The cell `c` it owns is freed,
and the run ends with `live 0`.

A clause runs once per operation, so anything it needs across calls lives in the handler's
**state**: its parameters (`mut` ones can be assigned) and any capabilities its clauses use.

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

An abort unwinds: whatever the abandoned code owned is dropped, and any borrow it was inside
ends, so the place goes back to its owner. A value with no destructor (a thunk, a capability)
can't be live where an abort may leave, and the checker tells you which one it is.

Each operation goes to the innermost handler around it, decided at compile time.

## Several instances, and names

`Fail[i32]` and `Fail[ParseError]` are two **instances** of `Fail`, and a row can hold both. An
operation goes to the innermost handler of its instance, worked out from its argument's type, so
the order you nest the two handlers in doesn't matter. Two handlers of the same instance are told
apart by name: `with n = h(…) { … }` names a handler and `n.op(v)` performs at it. A row can name
its entries too, `with src: Kube, dst: Kube`. If an operation's instance is ambiguous (`raise(1)`
with two integer instances in scope), the checker asks you for an ascription, `raise((1 : u8))`,
or a name.

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

A generic function means the same thing at every type. In `f[E]` with the row
`Fail[E], Fail[ParseError]`, each operation goes to the entry it names in `f`'s own types, even
when `f` is used at `E := ParseError`. A handler of `Fail[E]` inside `f` never accidentally
catches the caller's `Fail[ParseError]` (`corpus/effects-abstraction.bc`).

## Blocks that perform effects

A closure passed as an argument is a **block**. Its type names no effects, and its operations go
to the handlers around the place it's written, never to a handler inside the function it's
passed to. The function is compiled once per block row, so one function serves pure blocks and
effectful ones without any annotation.

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

The block's `raise` skips past `guarded`'s own `default` and reaches the `to_result` where the
block was written. A block can be called or passed on to another function, but not stored or
returned.

A block can also use a handler's capability, or yield to a `for` it's written inside.

## Computation parameters and `|>`

Sometimes the function *should* handle what its argument does: `retry` catches the errors of the
attempt it's given, and a timeout stops it. A parameter whose type carries a row,
`f: !(i32 => A with Fail[i32])`, is a **computation parameter**. The callee handles the listed
effects of each call `f(…)` itself. Any other effect of the argument still goes to where the
argument was written.

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

With five attempts, the third succeeds with 200 after waits of 10 and 20. With two, both fail
and the last error reaches the caller. Had `f` been a plain block parameter, `f: !(i32 => A)`,
the block's `raise` would go straight to the `to_result` in `with_budget` and nothing would be
retried. Passing a named function works too: `retry(3, 10, call)` means
`retry(3, 10, !{ a -> call(a) })`.

`|>` stacks these stages. When `h` is a handler, `e |> h(…)` is `with h(…) { e }`, and when `h`
is a function whose first parameter is a computation parameter, it's `h(!{ () -> e }, …)`. A
chain reads in the order it wraps, innermost first:
`step() |> timeout |> retry(3, 10) |> logged` (`corpus/reconcile-chain.bc`,
`corpus/pipe-handlers.bc`). For any other function, `e |> f(a)` is `f(e, a)`
([Iteration](iteration.md#pipelines)).

## Not yet

A few combinations aren't supported yet: performing an operation inside a closure that is stored
rather than called, an effect that mixes answering and control operations, and an operation that
answers with a borrow into the handler's state. The [Status](../status.md) page has the details.
