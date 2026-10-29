# Ownership and borrows

Every value is either **copyable** or **owned**. A copyable value holds no resource, and may be
used any number of times or not at all. An owned value holds memory (or a capability, or a
suspended computation), and is used exactly once: passed on, taken apart, or freed. Borrowing
lends an owned value for a while without giving it up. If you know Rust, this is its model, and
a program that type-checks has no use after free, no double free and no leak
([Safety guarantees](../safety.md)).

## Copyable and owned values

These types are copyable: the numbers, `bool`, `1`, `!` functions, and tuples and sums of
copyable types. Everything else is owned:

| type | what it owns |
|---|---|
| `ref A` | a heap cell holding an `A` |
| `array A`, `buf A`, `string` | a run of cells (next chapter) |
| `imm 'a A`, `mut 'a A` | a borrow, below |
| `A => B` | a closure that may hold owned values; called once |

`alloc(v)` puts `v` in a new heap cell, a `ref A`, and `free(c)` takes the value back out and frees
the cell. Using an owned value moves it, and a value that has moved can't be used again:

```bc
include textio

fn take_all(c: ref i32) -> i32 = free(c)

main -> 1 =
  let c = alloc(40);
  let d = c;
  print_dec(take_all(d) + 2);
  print_byte(b'\n')
-- output: 42
```

```bc,reject
fn take_all(c: ref i32) -> i32 = free(c)

main -> i32 =
  let c = alloc(1);
  let n = take_all(c);
  n + free(c)
-- expect: 5:3: `c` is used twice here, and its type `ref i32` is not persistent
```

The second use is an error, so there is no use after free and no double free. A value that is
never used is not an error: the compiler frees it where its scope ends, as Rust drops it.

```bc
include textio

main -> 1 =
  let unused = alloc(1);
  let c = alloc(41);
  print_dec(free(c) + 1);
  print_byte(b'\n')
-- output: 42
```

The run ends with `live 0`: both cells were freed. A value that can't be dropped this way,
because dropping it would need an argument (a capability, or a one-shot closure that must be
called), must be used, and leaving it unused is an error that names it.

## Borrowing for one call

`&x` lends `x` shared, and `&mut x` lends it exclusively, to one call. After the call, `x` is
usable again, changed if it was lent `&mut`. The function receives a borrow, `imm 'a A` or
`mut 'a A`, whose lifetime `'a` is a parameter of the function:

```bc
include textio

fn get<'a>(r: imm 'a i32) -> i32 = *r

fn bump<'a>(r: mut 'a i32) -> 1 = modify r { v -> v + 1 }

-- Adds `k`, and answers the old value.
fn add<'a>(m: mut 'a i32, k: i32) -> i32 = modify m { v -> (v + k, v) }

main -> 1 =
  let c = alloc(5);
  bump(&mut c);
  let old = add(&mut c, 10);
  let now = get(&c);
  print_dec(old);
  print_byte(b' ');
  print_dec(now);
  print_byte(b'\n')
-- output: 6 16
```

- `*r` reads through a borrow. It copies the contents, so it needs a copyable content type.
- `modify m { v -> e }` replaces the contents `v` of a `mut` borrow by `e`. When `e` is a pair
  `(new, result)`, the contents become `new` and `modify` answers `result`.

`&x` and `&mut x` work on a `let mut` variable too, with no heap cell: the compiler gives the
variable a slot in the stack frame for the call. Through a `mut` borrow of a record, a field is
assigned as on the record itself:

```bc
include textio

data Point = { x: i32, y: i32 }

fn nudge<'a>(p: mut 'a Point, dx: i32) -> 1 = p.x = p.x + dx

main -> 1 =
  let mut p = Point { x: 1, y: 2 };
  nudge(&mut p, 10);
  nudge(&mut p, 5);
  print_dec(p.x);
  print_byte(b'\n')
-- output: 16
```

## Borrow blocks

`borrow imm x { b -> … }` and `borrow mut x { m -> … }` lend `x` for a block of code rather than
one call. Inside the block, `x` itself is out of reach; after it, `x` is back. The block's value
is the block's result:

```bc
include textio

main -> 1 =
  let c = alloc(5);
  let k = 7;
  let old = borrow mut c { m ->
    let old = modify m { v -> (v + k, v) };
    modify m { v -> (v * 2, old) } };
  print_dec(old);
  print_byte(b' ');
  print_dec(free(c));
  print_byte(b'\n')
-- output: 5 24
```

The block introduces a lifetime of its own. It is unnamed unless a type written inside the block
mentions it, in which case it is written first: `borrow imm a { 'x, v -> … }`.

Inside the block, `m` is a value like any other: passing it to a function moves it. So a function
that takes a `mut` borrow and is meant to be called more than once hands it back,
`fn f<'a>(m: mut 'a A) -> mut 'a A * B`, and the caller binds it again, `let (m, r) = f(m);`.
The view functions of the next chapter work this way.

## What the checker refuses

The owner can't be used while it is lent:

```bc,reject
main -> i32 =
  let c = alloc(5);
  let n = borrow mut c { m -> free(c) };
  n
-- expect: 3:11: `c` is used twice here, and its type `ref i32` is not persistent
```

and a borrow can't outlive its lend: a call whose result mentions the lent place's lifetime
can't hand the place back.

```bc,reject
fn keep<'a>(r: imm 'a i32) -> imm 'a i32 = r

main -> i32 =
  let c = alloc(5);
  let r = keep(&c);
  free(c)
-- expect: 5:11: the call's result mentions the lifetime of the lent place, so the place cannot be handed back after it
```

Any number of `imm` borrows of a place may be live at once, and a `mut` borrow is exclusive, so
two `&mut` of one place are never live together. Lifetimes are lexical, as Rust's were before
non-lexical lifetimes: a borrow lasts for its call or its block.

## Recursive data is copied only when you say so

A list of integers holds no resource, so it can be copied, but copying it allocates every node,
so it's like a Rust type that is `Clone` but not `Copy`. Where a use would copy recursive data,
the copy is written `clone(x)`; without it, the second use is an error that says so:

```bc,reject
include list

main -> i32 =
  let xs = cons(1, cons(2, nil()));
  let a = with on_exhausted(!{ u -> 0 }) { fold(xs, 0, !{ (s, x) -> s + x }) };
  let b = with on_exhausted(!{ u -> 0 }) { fold(xs, 0, !{ (s, x) -> s + x }) };
  a + b
-- expect: 5:49: `xs` is used again at 6:49, so this use copies it, and its type `mu X. 1 + i32 * X` holds recursive data: the copy allocates every node. Write `clone(xs)` to copy it here, or do not use `xs` after this
```

Writing `fold(clone(xs), …)` in the first call makes it run. An `i32` or a pair of them is copied
as a few words, and needs nothing written. (`List`, `fold` and `on_exhausted` are the next
chapter's.)

## Lifetimes in signatures

A function that takes a borrow names its lifetime, `fn f<'a>(r: imm 'a A)`, and a result that
holds part of the borrow mentions it, as Rust's do. A view of an array element, for example, lives
as long as the view of the array it came from:

```text
fn get[A]<'a>(v: array_imm 'a A, i: i32) -> imm 'a A + 1
```

Lifetimes are not elided in signatures. Inside a body they are inferred, except where a borrow
block's lifetime must be named (above).

A lifetime parameter can be declared shorter than another, `fn f<'x, 'w < 'x>(…)`, for a result
that must not outlive a borrow it was made from. `main` runs under a lifetime of its own,
`'main`, which lasts for its whole body; a call that needs a lifetime its arguments don't give
gets the innermost one in scope, and `f['main](…)` passes `main`'s by name. A generic function
can require that a type argument outlive one of its lifetimes, as in Rust:
`fn hold[S]<'c>(s: S) -> … where S: 'c`.
