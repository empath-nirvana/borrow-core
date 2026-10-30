# Async tasks

Async is just another effect. `await()` is an ordinary operation, a task is a computation paused
at one, and a scheduler is a handler. The one in `include async` is written in the language
itself, with no runtime support. A function that awaits is an ordinary function with `Async` in
its row. There's no `async` keyword, and the same function runs inside a task or outside one.
Tasks compile to state machines, as Rust's `async fn`s do, with no garbage collector and no
reference counting.

The library's scheduler is cooperative and single-threaded.

## Spawning and running tasks

`include async` gives you:

| name | what it is |
|---|---|
| `effect Async { ctl await(); ctl log(x: i32) }` | the operations: let other tasks run, and record an entry with the scheduler |
| `with spawn { e }` | runs `e` to its first `await` and answers the task, a `Task[A]` |
| `resume(t)` | runs a task to its next `await`: `inl` its value if it finished, else `inr` the rest |
| `cancel(t)` | abandons a task, running what it must finalise |
| `queue[A]()`, `push(q, t)` | a queue of tasks |
| `run_until_empty(q)` | resumes the queued tasks round robin; their values, in the order queued |
| `with spawn_logged { e }`, `lqueue[A]()`, `lpush(q, t)` | the same for tasks whose `log` entries are kept |
| `run_logged(q)` | runs logged tasks round robin; their values, and every entry logged, in order |
| `with spawn_in { e }`, `resume_in`, `cancel_in`, `queue_in`, `push_in` | a task that may hold a borrow from the scope it was spawned in across its `await`s |
| `run_in(q, rounds)` | runs such tasks round robin for at most `rounds` rounds, inside that scope |

The values come back as a `List`, so the examples below print one with a small helper.

```bc
include async
include textio

fn print_all(xs: List[i32]) -> 1 =
  with on_exhausted(!{ u -> false }) {
    fold(xs, true, !{ (first, x) -> if not(first) { print_lit(", ") }; print_dec(x); false })
  };
  print_byte(b'\n')

fn ticker(tag: i32, n: i32) -> i32 with Async =
  let mut acc = 0;
  for _ in 0..n { acc = acc * 10 + tag; await() };
  acc * 10 + tag

main -> 1 =
  let q = queue[i32]();
  let q = push(q, with spawn { ticker(1, 2) });
  let q = push(q, with spawn { ticker(2, 1) });
  print_all(run_until_empty(q))
-- output: 111, 22
```

`ticker` doesn't name a scheduler; it runs under whoever spawns it. A task is a value, so a
program can also drive tasks itself with `resume` and `cancel`, or write its own scheduler as a
handler of `await`.

A logged task records entries with `log(x)` as it runs, and `run_logged` answers them in the
order they were logged, interleaved across tasks:

```bc
include async
include textio

fn print_all(xs: List[i32]) -> 1 =
  with on_exhausted(!{ u -> false }) {
    fold(xs, true, !{ (first, x) -> if not(first) { print_lit(", ") }; print_dec(x); false })
  };
  print_byte(b'\n')

-- Logs each step it takes, and answers its tag.
fn worker(tag: i32, steps: i32) -> i32 with Async =
  for i in 0..steps { log(tag * 10 + i); await() };
  tag

main -> 1 =
  let q = lqueue[i32]();
  let q = lpush(q, with spawn_logged { worker(1, 2) });
  let q = lpush(q, with spawn_logged { worker(2, 3) });
  let (values, log) = run_logged(q);
  print_all(values);
  print_all(log)
-- output: 1, 2
-- output: 10, 20, 11, 21, 22
```

## Cancellation

A task is linear, with a cancel branch: it has to be either run to the end or cancelled. Cancelling
frees everything the task owns, so nothing leaks. Here the first of two lookups to finish wins, and
the other is cancelled along with the cell it holds:

```bc
include async
include textio

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

main -> 1 =
  let a = with spawn { lookup(3, 3) };
  let b = with spawn { lookup(4, 6) };
  match with on_exhausted(!{ u -> inr (inr ()) }) { race(a, b, 10) } {
    inl v -> print_lit("first: "); print_dec(v)
  | inr (inl w) -> print_lit("second: "); print_dec(w)
  | inr (inr u) -> print_lit("neither")
  };
  print_byte(b'\n')
-- output: first: 30
```

The run ends with nothing allocated: cancelling the slow task freed its cell. `race` calls
itself, so its call goes under `on_exhausted` ([Recursion](data.md#recursion)).

## Borrows across `await`

A task may borrow its own data across an `await`, with no `Pin` and nothing written:

```bc
include async
include textio

fn print_all(xs: List[i32]) -> 1 =
  with on_exhausted(!{ u -> false }) {
    fold(xs, true, !{ (first, x) -> if not(first) { print_lit(", ") }; print_dec(x); false })
  };
  print_byte(b'\n')

fn task(n: i32) -> i32 with Async =
  let c = alloc(n);
  let v = borrow mut c { m ->
    let old = modify m { x -> (x + 1, x) };
    await();
    let now = modify m { x -> (x * 10, x) };
    old + now };
  v + free(c)

main -> 1 =
  let q = queue[i32]();
  let q = push(q, with spawn { task(1) });
  let q = push(q, with spawn { task(2) });
  print_all(run_until_empty(q))
-- output: 23, 35
```

Each task holds a `mut` borrow of its own cell while it's suspended, and the compiler checks it
like any other borrow. A task spawned with `spawn_in` inside a borrow block can also hold that
outer borrow across its `await`s, and use effects such as standard output that the surrounding
block gives it.
