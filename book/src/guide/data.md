# Data and generics

This chapter covers the data a program builds: recursive types such as lists and trees, arrays,
buffers and strings, and the generic code over them: `poly` families, operators at your own
types, and the hash map and set.

## Recursive types

`mu X. A` is a recursive type: `A` with `X` standing for the type itself. A list of integers is
empty, or a head and the rest:

```text
type IntList = mu X. 1 + (i32 * X)
```

`roll v` builds a value of a `mu` type from one layer, and `unroll v` exposes the layer, which a
`match` takes apart:

```bc
type Tree = mu X. 1 + (X * (i32 * X))

def empty : Tree = roll inl ()

fn branch(l: Tree, v: i32, r: Tree) -> Tree = roll inr (l, (v, r))

fn root(t: Tree) -> i32 =
  match unroll t {
    inl u -> 0
  | inr (l, p) -> let (v, r) = p; v
  }

main -> i32 = root(branch(empty, 7, branch(empty, 3, empty)))
-- answer: i32[7]
```

`def name : T = v` declares a constant. A type may take parameters, `type Pair[A] = A * A`, and
`include list` (`lib/list.bc`) gives the generic `List[A]`, with `nil()`, `cons(x, xs)` and the
recursive `map`, `filter` and `fold`.

There are no `data` declarations with named constructors yet (#489): a type is a `mu`, a sum and
pairs, and constructors are functions. The names `leaf`, `node`, `swap`, `total` and the
constant names of the core are reserved, and cannot name a function.

## Recursion

A function that calls itself runs with a budget of depth instead of an unbounded stack. When the
budget is spent, the recursion raises `Exhausted`, an error like any other, which a handler
around the call decides what to do with: `with on_exhausted(f) { … }` answers `f(())` instead,
and `with deep { … }` runs the recursion with its pending calls on the heap, with no limit but
memory. Both come from `include rec`. A recursive call that nothing handles is an error that says
so. The budget is 10000 levels.

A function may call itself, and functions may call one another: they form a recursive group, and
a **driver** runs it (SPEC §20, §21). The group is the fixed point of its *generator*, the members'
bodies with their calls of the group going to a self-reference, and each of those calls is a
direct call. The default driver, `bounded`, needs nothing written: it takes the fixed point as
native calls, carrying a budget of depth, and when the budget is spent it performs `exhausted()`,
an error like any other (`include rec`). So a recursive function's *row*, the effects it may perform
([Effects and handlers](effects.md)), has `Exhausted`, and something handles it:

```bc
include rec

type Tree = mu X. 1 + (X * (i32 * X))

def empty : Tree = roll inl ()
fn mk(l: Tree, v: i32, r: Tree) -> Tree = roll inr (l, (v, r))

fn build(d: i32) -> Tree = if d == 0 { empty } else { mk(build(d - 1), d, build(d - 1)) }

fn sum(t: Tree) -> i32 =
  match unroll t {
    inl u -> 0
  | inr (l, p) -> let (v, r) = p; sum(l) + v + sum(r)
  }

fn down(n: i32) -> i32 = if n == 0 { 0 } else { 1 + down(n - 1) }

main -> i32 * i32 =
  let s = with on_exhausted(!{ u -> 0 - 1 }) { sum(build(4)) };
  let d = with on_exhausted(!{ u -> 0 - 1 }) { down(20000) };
  (s, d)
-- answer: (i32[26], i32[4294967295])
```

`down(20000)` is deeper than the budget, so it performs `exhausted()`, which unwinds every level
(running what each level must finalise) and reaches `on_exhausted`. A recursion that must go
deeper runs under the heap driver, `with deep { down(20000) }`, which keeps its pending calls in
a buffer instead of on the stack, and is div.

A recursion may do what any function does. It may use a handler's capability: the capability is
passed down with each call and handed back with each answer, as to any function that uses one. It
may yield, or perform any operation, which goes to the handler around the call from outside. Its
members may answer different types: the fixed point is taken at the record of their functions.
A recursion whose body has a `while` or a `loop` is not provided yet: it is div, and its
`Exhausted` would be performed inside its loop, where no handler reaches.

A recursion may be **generic**. `lib/list.bc` (`include list`) gives `List[A]` with `nil`,
`cons`, and the recursive templates `map`, `filter` and `fold`. Each use at new types is an
instance of the whole recursion at those types, and a block given to one may itself perform
operations, which go to the handlers where the block is written:

```bc
include list

main -> List[bool] * i32 = with on_exhausted(!{ u -> (nil(), 0) }) {
  let xs = cons(3, cons(0 - 1, cons(4, nil())));
  (map(xs, !{ x -> x > 1 }), fold(cons(1, cons(2, nil())), 0, !{ (a, x) -> a + x }))
}
-- answer: (inr (inr (), inr (inl (), inr (inr (), inl ()))), i32[3])
```

The members of a generic recursion take the same type parameters, and a call of itself is at
them: a recursion that calls itself at other types is not provided.

A **layer** runs around each call a recursion makes of itself. It is a function of the call and
its argument, generic in their types, and `with L { … }` applies it to the recursions called in the
block, before their fixed point is taken: it transforms the generator, and the recursion knows
nothing of it.

```bc
include rec

effect Count { fn tick() -> i32 }

handler count(mut n: i32): Count = { tick() = { n = n + 1; n } }

fn counted[A, B](call: !(A => B), a: A) -> B = tick(); call(a)

fn fib(n: i32) -> i32 = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }

main -> i32 * i32 =
  let c = alloc(0);
  let f = with count(&mut c) { with counted { with on_exhausted(!{ u -> 0 - 1 }) { fib(10) } } };
  (f, free(c))
-- answer: (i32[55], i32[176])
```

`fib(10)` makes 176 calls of itself, each counted; the call from outside is not. Effects and
handlers (`effect`, `handler`, `with`) are [their own chapter](effects.md).

## Arrays

`array A` owns `n` cells, `n` known when the program runs. `array_new[A](n, f)` makes one, with
`f(i)` at index `i`. An array is owned, so it is lent to be read:

- `at(&a, i, d)` copies element `i`, or answers `d` when `i` is out of range;
- `borrow imm a { v -> … }` lends the whole array as a *view*, `array_imm 'a A`, and
  `borrow mut a { v -> … }` as a mutable one, `array_mut 'a A`;
- a `for` over a view visits each element's borrow, read with `*p`.

`include slice` (`lib/slice.bc`) has the view operations, as Rust's slice methods: `len`, `get`,
`set`, `swap_at`, `split_at`, `reverse`, `fill`, `find`, `binary_search`, `sort`, and their `_mut`
forms.

```bc
include slice

fn sum<'a>(v: array_imm 'a i32) -> i32 =
  let mut s = 0;
  for p in v { s = s + *p };
  s

fn scramble(i: i32) -> i32 = (i * 7) % 5

main -> i32 * (i32 * i32) =
  let a = array_new[i32](5, scramble);
  let s = borrow imm a { v -> sum(v) };
  borrow mut a { v -> let v = sort(v, cmp_i32, 0); discard_mut(v) };
  let lo = at(&a, 0, 0);
  let hi = at(&a, 4, 0);
  (s, (lo, hi))
-- answer: (i32[10], (i32[0], i32[4]))
```

A view-taking function hands its `array_mut` back, so a block that sorts in place ends with
`discard_mut(v)`, which ends the view. A view can be split at a run-time index into two views of
the same elements (`split_at`, `split_at_mut`), as Rust's `split_at_mut` is: `corpus/quicksort.bc`
sorts in place that way, with no allocation per element.

A `for` directly over the view of a borrow block whose body is in the same function is not
provided in every shape yet (#501): pass the view to a function, as `sum` above takes it.

## Buffers and strings

`buf A` is a growable array, `include buf`. `box buf[A](cap)` allocates one, `push(&mut b, x)`
appends, `pop(&mut b)` takes the last, and `len_of(b)` hands it back with its length. A buffer
lends its initialised prefix as a view, as an array does.

```bc
include buf
include slice

fn sum<'a>(v: array_imm 'a i32) -> i32 = let mut s = 0; for p in v { s = s + *p }; s

main -> i32 * i32 =
  let mut b = box buf[i32](2);
  for i in 0..5 { push(&mut b, i * i) };
  let n = borrow imm b { v -> sum(v) };
  let (b, len) = len_of(b);
  (n, len)
-- answer: (i32[30], i32[5])
```

`string` is a buffer of UTF-8 bytes, and `text 'a` a view of some (`include textio`, which brings
`include text` and the I/O helpers). `string_new(cap)` makes one; `push_lit(&mut s, "…")`,
`push_dec(&mut s, n)` and `push_char(&mut s, 'c')` append. A string literal `"…"` is data the
program owns no copy of. Text views are cut without copying (`split_once`, `trim`, `next_line`,
`fold_lines`), and `parse_i32` reads a number, raising on bad input ([Errors](errors.md)).

```bc
include textio

fn point(x: i32, y: i32) -> string =
  let mut s = string_new(16);
  push_lit(&mut s, "(");
  push_dec(&mut s, x);
  push_lit(&mut s, ", ");
  push_dec(&mut s, y);
  push_char(&mut s, ')');
  s

main -> i32 =
  let s = print_string(point(3, 0 - 4));
  print_byte(b'\n');
  let n = borrow imm s { t -> len(t) };
  n
-- output: (3, -4)
-- answer: i32[7]
```

## `poly` families

A generic function `fn f[T](…)` has one body for every `T`. A **family** has one body per type,
chosen by the type, as a Rust trait with one method is. It is declared by its signature with no
body, and each `poly f at H = …` gives its case at a type `H`:

```bc
poly weight[T](x: T) -> i32

poly weight at i32 = x
poly weight at bool = if x { 1 } else { 0 }
poly weight[A, B] at A * B = let (a, b) = x; weight(a) + weight(b)

main -> i32 = weight((40, (true, true)))
-- answer: i32[42]
```

A call picks the case from its argument's type, at compile time; a case may itself be generic,
as the one at `A * B` is, and calls the family at the parts. The rules keep the choice a function
of the type:

- **One case per type.** A second case at the same type is an error, never resolved by order.
- **The most specific case wins**, and two cases that overlap with neither more specific are an
  error.
- **A type with no case** is an error at the call that needs it.

There are no modules yet (#63), so a family's cases are global to the program.

### Operators at your own types

`+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>` and `>=` are families too. At the integer and float
types they are the machine instructions. At any other type, a program gives a case, `poly (+) at
H = …`, whose parameters are `a` and `b`:

```bc
type Complex = i32 * i32

poly (+) at Complex =
  let (ar, ai) = a;
  let (br, bi) = b;
  (ar + br, ai + bi)

poly (*) at Complex =
  let (ar, ai) = a;
  let (br, bi) = b;
  (ar * br - ai * bi, ar * bi + ai * br)

-- `x₁·y₁ + x₂·y₂`, at any type with `+` and `*`.
fn dot[T](x: T * T, y: T * T) -> T =
  let (x1, x2) = x;
  let (y1, y2) = y;
  x1 * y1 + x2 * y2

main -> i32 * Complex =
  let n = dot((1, 2), (3, 4));
  let z = dot[Complex](((1, 2), (1, 1)), ((3, 4), (0 - 1, 3)));
  (n, z)
-- answer: (i32[11], (i32[4294967287], i32[12]))
```

`dot` at `i32` is compiled with the machine's `mul` and `add`; at `Complex` with the cases above.
A different arithmetic is a different type, never a different scope. Because `Complex` is a name
for `i32 * i32`, its cases are the cases of every pair of `i32`s (newtypes wait for `data`
declarations, #489).

### Equality, hashing and order

`include key` (`lib/key.bc`) declares the families a map uses: `equal`, `hash` and `order`, each
taking its operands as views so that a key is read where it is stored. They have cases at the
integers, `1`, pairs, sums, arrays and buffers (so `bool`, `string` and `text` are covered),
compared structurally. `==` and `equal` are separate families: a float has `==`, IEEE 754's, and
no `equal`, so a float is not a map key.

## Maps and sets

`include map` (`lib/map.bc`) is a hash map, `Map[K, V]`, and a set, `Set[K]`. A map is a value: it
is lent to each operation, and an operation that changes it takes it `&mut`.

| call | answers |
|---|---|
| `map_new[K, V](cap)` | an empty map with room for `cap` entries before it grows |
| `map_insert(&mut m, k, v)` | `V + 1`: the value displaced, or `inr ()` |
| `map_lookup(&m, k)` | `V + 1`: a copy of the value (`V` copyable) |
| `map_contains(&m, k)` | `bool` |
| `map_remove(&mut m, k)` | `V + 1`: the value taken out |
| `map_len(&m)` | `i32` |
| `set_new[K](cap)`, `set_insert(&mut s, k)`, `set_contains(&s, k)`, `set_remove(&mut s, k)`, `set_len(&s)` | `set_insert` answers whether `k` was new |

```bc
include map

-- How often each digit occurs among the first `n` squares' last digits; the count for 6.
fn sixes(n: i32) -> i32 * i32 =
  let mut m = map_new[i32, i32](8);
  for i in 0..n {
    let d = (i * i) % 10;
    let old = map_insert(&mut m, d, 1);
    match old { inl c -> let o = map_insert(&mut m, d, c + 1); () | inr u -> () }
  };
  let got = map_lookup(&m, 6);
  let six = match got { inl c -> c | inr u -> 0 };
  let kinds = map_len(&m);
  (six, kinds)

main -> (i32 * i32) * bool =
  let mut s = set_new[i32](4);
  let a = set_insert(&mut s, 5);
  let b = set_insert(&mut s, 5);
  (sixes(20), a && not(b))
-- answer: ((i32[4], i32[6]), inr ())
```

For values that are not copyable, such as buffers, `borrow imm m { 'x, r -> … }` lends the map's
entries, and `map_get(r, k)` answers a view of a value in place and `map_iter(r)` visits every
entry (`corpus/map-views.bc`). While the map is lent it cannot change, so no view outlives a
growth of the table.

The map is open addressing with linear probing, grown by doubling. Its hash is deterministic, so
the order of iteration is the same on every run.
