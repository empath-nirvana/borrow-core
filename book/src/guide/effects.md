# Effects and handlers

An **effect** is a set of operations. A **handler** gives each operation a meaning, and
`with h { … }` runs a block with `h` handling the effect. You call an operation like a function.
Errors ([Errors](errors.md)), I/O ([Input and output](io.md)), generators
([Iteration](iteration.md)) and tasks ([Async tasks](async.md)) are all effects of this one kind,
declared in the library. This chapter covers the mechanism they share.

There are no coloured functions. A function that performs an effect is called like any other.
Its row (the effects it performs) is inferred, and the handler around the call serves them.

## Answering operations

An operation declared `fn` answers its caller straight away. Its handler can keep state in a
`mut` parameter, which each clause can read and assign:

```bc
include textio

effect Counter { fn tick() -> i32 }

handler count(mut n: i32): Counter = { tick() = { n = n + 1; n } }

main -> 1 =
  let r = with count(0) { let a = tick(); let b = tick(); a * 10 + b };
  print_dec(r);
  print_byte(b'\n')
-- output: 12
```

Inside a clause, the state (`n` here) behaves like a `let mut` variable, and the clause's value
is the operation's answer. An operation that answers straight away compiles to a direct call of
its clause.

## Functions that perform effects

A function that calls an operation, or calls a function that does, has the effect in its
**row**, which is inferred. It runs under whichever handler is in scope where it's called. The
compiler makes one copy of it per handler, the way a generic function gets one copy per type.

```bc
include textio
include slice

effect Log { fn note(x: i32) }

handler summed(mut s: i32): Log = { note(x) = { s = s + x; () } }
handler count(mut n: i32): Log = { note(x) = { n = n + 1; () } }

fn walk<'a>(v: array_imm 'a i32) -> 1 =
  for p in v { note(*p) };
  ()

main -> 1 =
  let a = array_new[i32](3, !{ i -> (i + 1) * 5 });
  let c = alloc(0);
  let t = alloc(0);
  borrow imm a { v -> with count(&mut c) { walk(v) } };
  borrow imm a { v -> with summed(&mut t) { walk(v) } };
  print_dec(free(c));
  print_lit(" notes, adding up to ");
  print_dec(free(t));
  print_byte(b'\n')
-- output: 3 notes, adding up to 30
```

`with h(&mut c) { … }` lends the state from a cell, and the cell holds the final state after the
block. `walk` is compiled twice, once per handler, and each copy calls its handler's clause
directly.

You can write a row after the result type, `fn f(…) -> T with Log, Fail[i32]`, and the checker
holds the function to it.

## Control operations and their continuation

An operation declared `ctl` is a **control** operation. Its clause receives the rest of the
computation as a continuation `k` and decides whether and how to go on. `k(v)` resumes the body
with `v` as the operation's answer, and returns what the handler returns for the rest of the
body. The declaration says how often `k` may be resumed:

| declared | the clause |
|---|---|
| `ctl op(…) -> B` | resumes `k` at most once; if it does not, the rest of the body is cancelled |
| `must_resume ctl op(…) -> B` | resumes `k` exactly once |
| `ctl op(…) -> never` | receives no `k`: the operation is **abortive**, as `raise` is |

A control handler names the type of the body it handles and what it returns (`Watch, i32 -> i32`
below), and its `return(a)` clause receives the body's value. This handler resumes while the
values are small and abandons the body at the first large one:

```bc
include textio

effect Watch { ctl watch(x: i32) -> bool }

-- Resumes with `true` while the value is small; at the first large one, stops the body there.
handler until_large: Watch, i32 -> i32 = {
  return(a) = a;
  watch(x, k) = if x < 100 { k(true) } else { 0 - x }
}

fn walk(n: i32) -> i32 =
  let c = alloc(0);
  let mut s = 0;
  for i in 0..n { if watch(i * i) { s = s + 1 } };
  s + free(c)

main -> 1 =
  print_dec(with until_large { walk(5) });
  print_byte(b' ');
  print_dec(with until_large { walk(20) });
  print_byte(b'\n')
-- output: 5 -100
```

When the clause doesn't resume, the rest of `walk` is cancelled. The cell `c` it owns is freed,
and the run ends with nothing allocated.

A clause runs once per operation, so anything it needs across calls lives in the handler's
**state**: its parameters (`mut` ones can be assigned) and any capabilities its clauses use.

```bc
include textio

effect Ask { ctl ask() -> i32 }

-- Answers each `ask` with the cell's content, which it then increments.
handler asking(mut c: ref i32): Ask, i32 -> i32 = {
  return(a) = a + free(c);
  ask(k) = { let v = free(c); c = alloc(v + 1); k(v) }
}

main -> 1 =
  print_dec(with asking(alloc(5)) { let x = ask(); let y = ask(); x * 10 + y });
  print_byte(b'\n')
-- output: 63
```

The two `ask`s read 5 and 6, and the return clause adds the cell's last content, 7.

An abort unwinds: whatever the abandoned code owned is dropped, and any borrow it was inside
ends, so the place goes back to its owner. A value with no destructor (a closure that must be
called, a capability) can't be live where an abort may leave, and the checker tells you which one
it is.

Each operation goes to the innermost handler around it, decided at compile time.

## Several instances, and names

`Fail[i32]` and `Fail[u8]` are two **instances** of `Fail`, and a row can hold both. An
operation goes to the innermost handler of its instance, worked out from its argument's type, so
the order you nest the two handlers in doesn't matter. If an operation's instance is ambiguous
(`raise(1)` with two integer instances in scope), the checker asks you for an ascription,
`raise((1 : u8))`, or a name.

```bc
include textio
include fail

-- Raises a `u8` error for a large `n`.
fn small(n: i32) -> i32 with Fail[u8] = if n > 9 { raise(u8[2]) } else { n }

-- Raises its own `i32` error for a negative `n`, and passes on `small`'s.
fn check(n: i32) -> i32 with Fail[i32], Fail[u8] = if n < 0 { raise(n) } else { small(n) }

fn show(n: i32) -> 1 =
  let r = with to_result[i32, i32 + u8] { with to_result[u8, i32] { check(n) } };
  match r {
    inl (inl v) -> print_dec(v)
  | inl (inr b) -> print_lit("too large, code "); print_dec(to_i32(b))
  | inr e -> print_lit("negative: "); print_dec(e)
  };
  print_byte(b'\n')

main -> 1 = show(5); show(10); show(0 - 1)
-- output: 5
-- output: too large, code 2
-- output: negative: -1
```

Two handlers of the same instance are told apart by name: `with n = h(…) { … }` names a handler,
`n.op(v)` performs at it, and a row can name its entries, `with a: Log, b: Log`:

```bc
include textio

effect Log { fn note(x: i32) }

handler summed(mut s: i32): Log = { note(x) = { s = s + x; () } }

fn both(n: i32) -> 1 with a: Log, b: Log = a.note(n); b.note(n * 10)

main -> 1 =
  let c = alloc(0);
  let d = alloc(0);
  with a = summed(&mut c) { with b = summed(&mut d) { both(3) } };
  print_dec(free(c));
  print_byte(b' ');
  print_dec(free(d));
  print_byte(b'\n')
-- output: 3 30
```

A generic function means the same thing at every type. In `f[E]` with the row
`Fail[E], Fail[ParseError]`, each operation goes to the entry it names in `f`'s own types, even
when `f` is used at `E := ParseError`. A handler of `Fail[E]` inside `f` never accidentally
catches the caller's `Fail[ParseError]`.

## Blocks that perform effects

A closure passed as an argument is a **block**. Its type names no effects, and its operations go
to the handlers around the place it's written, never to a handler inside the function it's
passed to. The function is compiled once per block row, so one function serves pure blocks and
effectful ones without any annotation.

```bc
include textio
include fail

fn twice(f: !(i32 => i32), x: i32) -> i32 = f(f(x))

fn guarded(f: !(i32 => i32)) -> i32 = with default[1, i32](0) { f(1) }

main -> 1 =
  print_dec(twice(!{ x -> x + 5 }, 1));
  print_byte(b'\n');
  match with to_result[1, i32] { guarded(!{ x -> raise(()) }) } {
    inl v -> print_lit("guarded caught it\n")
  | inr u -> print_lit("the error went past guarded\n")
  }
-- output: 11
-- output: the error went past guarded
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

Here is a generic `retry` with exponential backoff, tested against a fake timer:

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
```

With five attempts, the third succeeds with 200 after waits of 10 and 20. With two, both fail
and the last error reaches the caller. `retry` never says which timer it uses: its caller picks
one, here a fake that just adds up the waits. Had `f` been a plain block parameter,
`f: !(i32 => A)`, the block's `raise` would go straight to the `to_result` in `attempt` and
nothing would be retried. Passing a named function works too: `retry(3, 10, call)` means
`retry(3, 10, !{ a -> call(a) })`.

`|>` stacks these stages. When `h` is a handler, `e |> h(…)` is `with h(…) { e }`, and when `h`
is a function whose first parameter is a computation parameter, it's `h(!{ () -> e }, …)`. A
chain reads in the order it wraps, innermost first: `step() |> timeout |> retry(3, 10) |> logged`.
For any other function, `e |> f(a)` is `f(e, a)` ([Iteration](iteration.md#pipelines)).
