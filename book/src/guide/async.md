# Async tasks

Async is just another effect. `await()` is an ordinary operation, a task is a computation paused
at one, and a scheduler is a handler. The one in `lib/async.bc` is written in the language itself,
with no runtime support. A function that awaits is an ordinary function with `Async` in its row.
There's no `async` keyword, and the same function runs inside a task or outside one. Tasks
compile to state machines, as Rust's `async fn`s do, with no garbage collector and no reference
counting.

The scheduler in `lib/async.bc` is cooperative and single-threaded.

## Spawning and running tasks

`include async` gives you:

| name | what it is |
|---|---|
| `effect Async { ctl await() }` | the one operation |
| `with spawn { e }` | runs `e` to its first `await` and answers the task, a `Task[A]` |
| `resume(t)` | runs a task to its next `await`: `inl` its value if it finished, else `inr` the rest |
| `cancel(t)` | abandons a task, running what it must finalise |
| `queue[A]()`, `push(q, t)` | a queue of tasks |
| `run_until_empty(q)` | resumes the queued tasks round robin; their values, in the order queued |

```bc
-- answer: inr (i32[111], inr (i32[22], inl ()))
include async

fn ticker(tag: i32, n: i32) -> i32 with Async =
  let mut acc = 0;
  for _ in 0..n { acc = acc * 10 + tag; await() };
  acc * 10 + tag

main -> List[i32] =
  let q = queue[i32]();
  let q = push(q, with spawn { ticker(1, 2) });
  let q = push(q, with spawn { ticker(2, 1) });
  run_until_empty(q)
```

The answer is the list `[111, 22]` (a `List` prints as nested sums). `ticker` doesn't name a
scheduler; it runs under whoever spawns it. A task is a value, so a program can also drive tasks
itself with `resume` and `cancel`, or write its own scheduler as a handler of `await`
(`corpus/async-timers.bc` is an event loop with timers and deadlines).

## Cancellation

A task is a linear value: it has to be either run to the end or cancelled. Cancelling frees
everything the task owns, so nothing leaks. Here the first of two lookups to finish wins, and the
other is cancelled along with the buffer it holds:

```bc
include async

-- A lookup that takes `steps` turns, holding a cell it owns.
fn lookup(key: i32, steps: i32) -> i32 with Async =
  let buf = alloc(key);
  for _ in 0..steps { await() };
  free(buf) * 10

-- The value of the first task to finish (`inl` for `a`, `inr` for `b`); the other is cancelled.
fn race[A](a: Task[A], b: Task[A], turns: i32) -> A + (A + 1) =
  if turns == 0 { cancel(a); cancel(b); inr (inr ()) } else {
    match resume(a) {
      inl v -> cancel(b); inl v
    | inr ra ->
        match resume(b) {
          inl w -> cancel(ra); inr (inl w)
        | inr rb -> race(ra, rb, turns - 1)
        }
    }
  }

main -> i32 + (i32 + 1) =
  let a = with spawn { lookup(3, 3) };
  let b = with spawn { lookup(4, 6) };
  with on_exhausted(!{ u -> inr (inr ()) }) { race(a, b, 10) }
-- answer: inl i32[30]
```

The run ends with `live 0`: cancelling the slow task freed its cell. (`race` is recursive, so its
call goes under `on_exhausted`; see [Recursion](data.md#recursion).)

## Borrows across `await`

A task may borrow its own data across an `await`, with no `Pin` and nothing written:

```bc
include async

fn task(n: i32) -> i32 with Async =
  let c = alloc(n);
  let v = borrow mut c { m ->
    let old = modify m { x -> (x + 1, x) };
    await();
    let now = modify m { x -> (x * 10, x) };
    old + now };
  v + free(c)

main -> List[i32] =
  let q = queue[i32]();
  let q = push(q, with spawn { task(1) });
  let q = push(q, with spawn { task(2) });
  run_until_empty(q)
-- answer: inr (i32[23], inr (i32[35], inl ()))
```

Each task holds a `mut` borrow of its own cell while it's suspended, and the compiler checks it
like any other borrow.

A task spawned with `spawn_in` inside a borrow block can also hold that outer borrow across its
`await`s, and it can use effects such as standard output that the surrounding block gives it
(`corpus/io-task.bc`, `corpus/async-scoped.bc`).

## Not yet

An event loop over real I/O, platform timers and wakers; an `imm` borrow held across `await`; two
tasks sharing one output stream; and threads. See [Status](../status.md).
