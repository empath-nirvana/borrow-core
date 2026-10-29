# Ownership and borrows

Every value is either **copyable** or **owned**. A copyable value holds no resource, and may be
used any number of times or not at all. An owned value holds memory (or a capability, or a
suspended computation), and is used exactly once: passed on, taken apart, or freed. Borrowing
lends an owned value for a while without giving it up. If you know Rust, this is its model. One
difference: data that holds no resources, like a list of integers, counts as copyable, but
copying a list or tree must be written `clone(x)` (below). The rules are
proved sound in Lean ([What is proved](../proved.md)), so a program that type-checks has no use
after free, no double free and no leak.

## Copyable and owned values

These types are copyable (the reference calls them *persistent*): the numbers, `bool`, `1`, `!`
functions, and pairs and sums of copyable types. Everything else is owned:

| type | what it owns |
|---|---|
| `ref A` | a heap cell holding an `A` |
| `array A`, `buf A`, `string` | a run of cells (next chapter) |
| `imm 'a A`, `mut 'a A` | a borrow, below |
| `A => B` | a closure that may hold owned values; called once |

`alloc(v)` puts `v` in a new heap cell, a `ref A`, and `free(c)` takes the value back out and frees
the cell. Using an owned value moves it, and a value that has moved cannot be used again:

```bc
fn take_all(c: ref i32) -> i32 = free(c)

main -> i32 =
  let c = alloc(40);
  let d = c;
  take_all(d) + 2
-- answer: i32[42]
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
main -> i32 =
  let unused = alloc(1);
  let c = alloc(41);
  free(c) + 1
-- answer: i32[42]
```

`live 0` after the answer says that both cells were freed. A value that cannot be dropped this
way, because dropping it would need an argument (a capability, or a one-shot closure that must
be called), must be used, and leaving it unused is an error that names it.

## Borrowing for one call

`&x` lends `x` shared, and `&mut x` lends it exclusively, to one call. After the call, `x` is
usable again, changed if it was lent `&mut`. The function receives a borrow, `imm 'a A` or
`mut 'a A`, whose lifetime `'a` is a parameter of the function:

```bc
fn get<'a>(r: imm 'a i32) -> i32 = *r

fn bump<'a>(r: mut 'a i32) -> 1 = modify r { v -> v + 1 }

-- Adds `k`, and answers the old value.
fn add<'a>(m: mut 'a i32, k: i32) -> i32 = modify m { v -> (v + k, v) }

main -> i32 * i32 =
  let c = alloc(5);
  bump(&mut c);
  let old = add(&mut c, 10);
  let now = get(&c);
  (now, old)
-- answer: (i32[16], i32[6])
```

- `*r` reads through a borrow. It copies the contents, so it needs a copyable content type.
- `modify m { v -> e }` replaces the contents `v` of a `mut` borrow by `e`. When `e` is a pair
  `(new, result)`, the contents become `new` and `modify` answers `result`.

`&x` and `&mut x` work on a `let mut` variable too, with no heap cell: the compiler gives the
variable a slot in the stack frame for the call.

```bc
fn bump<'a>(r: mut 'a i32) -> 1 = modify r { v -> v * 2 }

main -> i32 =
  let mut n = 21;
  bump(&mut n);
  n
-- answer: i32[42]
```

Write a lend as the whole call of a `let` or a statement: `let x = get(&c); (x, …)` rather than
`(get(&c), …)`.

## Borrow blocks

`borrow imm x { b -> … }` and `borrow mut x { m -> … }` lend `x` for a block of code rather than
one call. Inside the block, `x` itself is out of reach; after it, `x` is back. The block's value
is the block's result:

```bc
main -> i32 =
  let c = alloc(5);
  let k = 7;
  let n = borrow mut c { m ->
    let old = modify m { v -> (v + k, v) };
    modify m { v -> (v * 2, old) } };
  n * 100 + free(c)
-- answer: i32[524]
```

The block introduces a lifetime of its own. It is unnamed unless a type written inside the block
mentions it, in which case it is written first: `borrow imm a { 'x, v -> … }`.

Inside the block, `m` is a value like any other: passing it to a function moves it. So a function
that takes a `mut` borrow and is meant to be called more than once hands it back,
`fn f<'a>(m: mut 'a A) -> mut 'a A * B`, as the view functions of the next chapter do. (`&mut m`,
lending a borrow on again, is not available yet; nor is lending a second owner inside a borrow
block. Lend it before or after the block.)

## What the checker refuses

The owner cannot be used while it is lent:

```bc,reject
main -> i32 =
  let c = alloc(5);
  let n = borrow mut c { m -> free(c) };
  n
-- expect: 3:11: `c` is used twice here, and its type `ref i32` is not persistent
```

and a borrow cannot outlive its lend: a call whose result mentions the lent place's lifetime
cannot hand the place back.

```bc,reject
fn keep<'a>(r: imm 'a i32) -> imm 'a i32 = r

main -> i32 =
  let c = alloc(5);
  let r = keep(&c);
  free(c)
-- expect: 5:11: the call's result mentions the lifetime of the lent place, so the place cannot be handed back after it
```

There is no borrow checker separate from the type checker: an `imm` borrow is a value that is
used once like any owned value (`copy` splits it in two), and a `mut` borrow cannot be split at
all, so two `&mut` of one place are never live together. Lifetimes are lexical, as Rust's were
before non-lexical lifetimes: a borrow lasts for its call or its block.

## Recursive data is copied only when you say so

A list of integers holds no resource, so it is copyable, but copying it allocates every node.
Where a use would copy recursive data, the copy is written `clone(x)`; without it, the second use
is an error that says so:

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
block's lifetime must be named (above). The full rules, including `main`'s own lifetime `'main`
and lifetime bounds `where S: 'c`, are in [Cells and borrows in the
core](../elaboration/ownership-and-borrows.md#lifetime-parameters-bounds-and-mains-lifetime).
