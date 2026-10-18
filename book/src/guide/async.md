# Async tasks

Async is an effect like the others. `await()` is an ordinary control operation, a task is a
computation suspended at it, and a scheduler is a handler: `lib/async.bc` is one, written in the
language, with no runtime support (SPEC §30). A function that awaits is an ordinary function with
`Async` in its row; nothing marks it `async`, and the same function runs inside a task or outside
one. Tasks compile to state machines, as Rust's `async fn` do, with no garbage collector and no
reference counting.

What is built is a cooperative, single-threaded scheduler for tasks the program spawns. There is
no event loop over real I/O yet, and no threads.

## Spawning and running tasks

`include async` declares

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

The answer is the list `[111, 22]` (a `List` prints as nested sums). `ticker` names no scheduler:
its row is `Async`, and it runs under whichever site spawns it. A task is a value, so a program
can also drive tasks itself with `resume` and `cancel`, or write a scheduler of its own as a
handler of `await` (`corpus/async-timers.bc` is an event loop with timers and deadlines).

## Cancellation

A task is a linear value: it is resumed to its end or cancelled, and cancelling runs the task's
finalisers, so nothing it owns leaks. Here the first of two lookups to finish wins, and the other
is cancelled with the buffer it holds:

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

`live 0`: the slow task's cell was freed by its cancel. (`race` is recursive, so its call is
under `on_exhausted`, [Recursion](data.md#recursion).)

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

Each task holds the `mut` borrow of its cell while it is suspended. This is the *relaxed lend*
of SPEC §29, and it is the one place where the guarantees rest on a stated assumption rather
than a proof: `PinLaw`, a hypothesis of the theorems, stated in Lean and not yet proved
(`docs/async-capabilities.md` §4 gives the evidence, and the corpus tries to break it). `bcc
check` reports each program that uses it, `assurance: PinLaw (R1 at L:C)`; every other program is
covered unconditionally.

A task spawned with `spawn_in` inside a borrow block may also hold that outer borrow across its
`await`s, and a task may perform other effects, such as writing to standard output, given to it
by the borrow block that bounds it (SPEC §32, §34; `corpus/io-task.bc`, `corpus/async-scoped.bc`).

## Not yet

- An event loop over real I/O, timers from the platform's clock, and wakers (#52).
- Spawning from a scheduler handle (`s.spawn { … }`), and an `imm` borrow or a segmented lend
  across `await` (L0) (SPEC §30 *Open*, §29).
- Two tasks sharing one output stream (SPEC §34 *Open*); threads and parallelism (#212, #22).
