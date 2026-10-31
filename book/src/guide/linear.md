# Linear values

Every value has one of two kinds of type. An **unrestricted** type (a number, `bool`, `1`, a
`!` function, and tuples and sums of these) can be copied and forgotten freely. Every other
type is **linear**: a value of it is used exactly once. There is no third kind. This chapter
says what that means in practice; its examples use data declarations and handlers, which the
chapters after it introduce.

Most linear values don't feel that way, because most linear types have a **derived drop**: a way
to consume a value that the compiler works out from the type's structure. A cell's drop frees it
and then drops what it held; a tuple's or a record's drops each field; a task's cancels it. Where
a value goes unused, the checker inserts its derived drop at the end of its scope, and that drop
is the value's one use. You never write a drop, and there is no other kind: every drop in a
program is derived from a type.

```bc
include textio

data Note = { tag: i32, body: ref i32 }

main -> 1 =
  let n = Note { tag: 1, body: alloc(40) };
  let m = Note { tag: 2, body: alloc(2) };
  let Note { tag, body } = m;
  print_dec(free(body) + 40);
  print_byte(b'\n')
-- output: 42
```

`n` is never used, so the checker inserts `Note`'s derived drop where `main` ends: it frees the
cell in `body`, and the run ends with nothing allocated.

A shared borrow `imm 'a A` is linear too. Its derived drop ends the loan, and it also has a
**derived copy**: one shared borrow can be split into two, which is how the library's view
functions read a view twice. The checker doesn't insert copies, so a body that uses a borrow
twice is refused:

```bc,reject
fn twice<'a>(r: imm 'a i32) -> i32 = *r + *r

main -> i32 =
  let c = alloc(21);
  let n = twice(&c);
  n + free(c)
-- expect: 1:38: `r` is used twice here, and its type `imm 'a i32` is linear
```

Read the contents once instead: `let v = *r; v + v`.

## Linear types with no derived drop

Some linear types have no derived drop. Consuming a value of one means doing something the
program has to say: calling it, resuming it, closing it. They are:

- **Capabilities**: standard input, standard output and the other host streams. Your program
  never holds one: the platform's handlers keep them as their state ([Input and output](io.md)).
- **Continuations of `must_resume ctl` operations**, which a handler must resume.
- **One-shot functions** `A => B`, which can be disposed of only by calling them.
- **Declared types**: a data declaration whose field is marked `must_close`.

A value of one of these types has to be consumed on every path, and leaving one unused is an
error that names it:

```bc,reject
effect Ask { must_resume ctl ask() -> i32 }

handler skip: Ask, i32 -> i32 = {
  return(a) = a;
  ask(k) = 0
}

main -> i32 = with skip { ask() + 1 }
-- expect: 5:7: `k` is not consumed in its scope, and its type `U ((i32 -o F i32) & top)` is linear and has no derived drop
```

The clause has to call `k`. A one-shot function has to be called:

```bc,reject
fn adder(k: i32) -> i32 => i32 = { x -> x + k }

main -> i32 =
  let f = adder(5);
  5
-- expect: 4:7: `f` is not consumed in its scope, and its type `i32 => i32` is linear and has no derived drop
```

### Declared types

Marking a field `must_close` puts the whole type among the linear types with no derived drop.
Use it for a value whose silent disappearance would be a bug: a transaction that has to be
committed, a guard that has to be released. `must_close(commit)` also names the function that
consumes it, which the error messages point at:

```bc,reject
data Txn = { id: i32, must_close(commit) log: i32 }

fn begin(id: i32) -> Txn = Txn { id: id, log: 0 }

fn commit(t: Txn) -> i32 = match t { Txn { id, log } -> id * 100 + log }

main -> i32 =
  let t = begin(7);
  5
-- expect: 8:7: `t` is not consumed in its scope, and its type `i32 * i32 * tok` is linear and has no derived drop: `Txn` holds the field `log`, marked `must_close`; pass it to `commit` before its scope ends
```

Naming `commit` doesn't make anything call it: the program does, by writing the call. A `match`
on a declared value consumes it, so `commit` is an ordinary function, and so is anything else
that takes a `Txn` apart:

```bc
data Txn = { id: i32, must_close(commit) log: i32 }

fn begin(id: i32) -> Txn = Txn { id: id, log: 0 }

fn write(t: Txn, x: i32) -> Txn = match t { Txn { id, log } -> Txn { id: id, log: log + x } }

fn commit(t: Txn) -> i32 = match t { Txn { id, log } -> id * 100 + log }

main -> i32 =
  let t = begin(7);
  let t = write(t, 5);
  let t = write(t, 7);
  commit(t)
-- answer: i32[712]
```

A type that holds a declared value has no derived drop either, so a record that stores a guard
beside its data has to be consumed as well. A borrow of a declared value does have one: the loan
ends and the value is still there, so `&t` can be passed to functions that read its fields
before `t` is committed.

## Resources are handlers

A resource that has to be closed doesn't have to be a value you carry around. Hold it in a
handler's state, give the handler operations that use it, and let the handler close it when the
block ends. The platform serves standard output this way: the capability is the state of a
handler written once in the library, and your program performs `print_byte` and never sees it.

A program's own resource works the same. This handler holds a transaction, logs into it, and
commits it in its `return` clause:

```bc
include textio

data Txn = { id: i32, must_close(commit) log: i32 }

fn write(t: Txn, x: i32) -> Txn = match t { Txn { id, log } -> Txn { id: id, log: log + x } }

fn commit(t: Txn) -> i32 = match t { Txn { id, log } -> id * 100 + log }

effect Log { must_resume ctl log(x: i32) -> 1 }

-- Runs a block inside the transaction `t`, and commits it when the block answers.
handler in_txn(mut t: Txn): Log, i32 -> i32 = {
  return(a) = a + commit(t);
  log(x, k) = { t = write(t, x); k(()) }
}

main -> 1 =
  print_dec(with in_txn(Txn { id: 7, log: 0 }) { log(5); log(7); 0 });
  print_byte(b'\n')
-- output: 712
```

The block holds no transaction and owes no commit. `commit` runs once, in the handler, where
the program wrote it.

### `finally`

For cleanup of your own, put `finally { … }` after a `with`. The block runs when the `with` is
left, whether it answered or an error passed through it. It is written once and placed on both
exits; each placement is a call you wrote, checked like any other code, so it is not a drop.

```bc
include textio
include fail

data Guard = { must_close(release) lock: i32 }

fn release(g: Guard) -> 1 = match g { Guard { lock } -> () }

effect Step { fn step(x: i32) }

handler counted(mut n: i32): Step = { step(x) = { n = n + 1 } }

fn work(x: i32) -> i32 with Step, Fail[i32] =
  step(x);
  if x > 100 { raise(x) } else { x * 6 }

-- Runs `work` holding a guard, and releases it however `work` ends.
fn guarded(x: i32) -> i32 + i32 =
  let g = Guard { lock: x };
  with to_result[i32, i32] {
    with counted(0) { work(x) } finally { release(g) }
  }

fn show(r: i32 + i32) -> 1 with Stdout =
  match r { inl v -> print_dec(v) | inr e -> print_lit("raised "); print_dec(e) };
  print_byte(b'\n')

main -> 1 =
  show(guarded(7));
  show(guarded(500))
-- output: 42
-- output: raised 500
```

The second call raises inside `counted`, the error passes through it to `to_result`, and the
`finally` releases the guard on the way. Both runs end with nothing allocated. A `finally` block
can't do I/O yet.

## Values a program wants to forget

When you want a value to be droppable, there are three ways to get there, and each is something
the compiler derives or something you write.

**Keep the type's fields droppable.** A record or variant whose fields all have derived drops
has one too, built from theirs, and the checker inserts it (`Note` above).

**Give a task or a continuation a cancel branch.** A task can be run to the end or cancelled,
and cancelling it is its derived drop: it frees what the task owns. An unused task is cancelled
where its scope ends:

```bc
include async
include textio

-- A lookup that takes `steps` turns, holding a cell it owns.
fn lookup(key: i32, steps: i32) -> i32 with Async =
  let buf = alloc(key);
  for _ in 0..steps { await() };
  free(buf) * 10

main -> 1 =
  let a = with spawn { lookup(3, 3) };
  let b = with spawn { lookup(4, 6) };
  match resume(a) {
    inl v -> print_dec(v)
  | inr ra -> cancel(ra); print_lit("pending")
  };
  print_byte(b'\n')
-- output: pending
```

`with spawn` runs each lookup to its first `await`, so both have allocated their cell. `b` is
never resumed, and where `main` ends its derived drop cancels it, which frees that cell. The continuation of an
operation declared plain `ctl` has a cancel branch in the same way: a clause that doesn't call
`k` cancels the rest of the block, and when that cancel performs no operation it is `k`'s
derived drop ([Control operations](effects.md#control-operations-and-their-continuation)).

**Consume it with a function you write.** A declared value is consumed by any `match` on it, so
a function that takes it apart and answers nothing is a written way to let it go:

```bc
data Txn = { id: i32, must_close(commit) log: i32 }

fn commit(t: Txn) -> i32 = match t { Txn { id, log } -> id * 100 + log }

fn roll_back(t: Txn) -> 1 = match t { Txn { id, log } -> () }

main -> i32 =
  let a = Txn { id: 1, log: 5 };
  let b = Txn { id: 2, log: 9 };
  roll_back(a);
  commit(b)
-- answer: i32[209]
```

The call is in the program, where a reader can see it.

## What an abort does

When a `raise` leaves a computation, or a block is cancelled, the rest of it doesn't run. The
abort itself drops nothing. A value in scope that holds no owned cell (a number, a borrow, a `!`
function, data made of these) is **abandoned**: nothing runs for it, and that is safe because
there is nothing to free. A value that owns a cell is consumed by its derived drop, in a finaliser
the compiler places around the computation that may abort, so it is freed on the way out
([Errors](errors.md)).

A value with no derived drop has neither, so it can't be live across a computation that may
abort. Consume it before, or close it in a `finally`:

```bc,reject
include fail

data Guard = { must_close(release) lock: i32 }

fn release(g: Guard) -> 1 = match g { Guard { lock } -> () }

fn work(x: i32) -> i32 with Fail[i32] = if x > 100 { raise(x) } else { x * 6 }

fn guarded(x: i32) -> i32 + i32 =
  let g = Guard { lock: x };
  with to_result[i32, i32] {
    let y = work(x);
    release(g);
    y
  }

main -> i32 = match guarded(7) { inl v -> v | inr e -> 0 }
-- expect: 12:13: `g`, of type `i32 * tok`, is live across a computation that may abort, and its type is linear with no derived drop, and an abort abandons only a value that holds no owned cell: `Guard` holds the field `lock`, marked `must_close`; pass it to `release` before the computation that may abort, or close it in a `finally`
```

The `finally` version is the one in the previous section. Holding the value in a handler's
state doesn't carry it across an error either: an error that passes the handler would leave its
state behind, and the checker refuses that too.

## Compared with Rust

Rust's types are *affine*: any value may be used at most once, and any value may go unused. A
type can say what happens when it goes unused by implementing `Drop`, written by hand and free to
do anything, and leaking a value (`mem::forget`) is safe. There is no way for a type to insist on
being consumed; `#[must_use]` is a warning.

Here every type that isn't unrestricted is linear, and the difference shows in three places:

- **Drops are derived, never written.** A drop frees memory and closes codata by the type's
  structure, and does nothing else. Cleanup that does something more is a call the program
  writes, in a `finally`, a handler or a consuming function.
- **A type can have no drop.** `must_close`, `must_resume ctl` and one-shot functions are linear
  with no derived drop, and leaving one unused is a type error, not a lint.
- **An abort abandons, it doesn't drop.** What an abort passes over holds no owned cell, or is
  consumed by its derived drop in a finaliser the compiler places, or is refused. Rust unwinds by
  running `Drop` on whatever is in scope.

Most programs see little of this: a cell, a string or a record of them is dropped where its scope
ends, as in Rust.
