# Data and generics

This chapter covers the data a program builds: recursive types such as lists and trees, the
folds that walk them, arrays, vectors and strings, and the generic code over them: `poly`
families, operators at your own types, and the hash map and set.

## Recursive data

A `data` declaration may mention itself. A binary tree is a leaf, or a node with two subtrees
and a value:

```bc
include textio

data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)

fn branch(l: Tree, v: i32, r: Tree) -> Tree = box Node(l, v, r)

-- The sum of the values; consumes the tree.
fn sum(t: Tree) -> i32 = fold_own t { Leaf -> 0 | box Node(l, v, r) -> l + v + r }

main -> 1 =
  let t = branch(branch(Leaf, 1, Leaf), 2, branch(Leaf, 3, Leaf));
  print_dec(sum(t));
  print_byte(b'\n')
-- output: 6
```

A node holds a tree, so it has to live on the heap, and you say so: `box Node(l, v, r)` allocates
it, where Rust would write `Box::new`. Nothing else allocates. Cases that hold no tree, like
`Leaf`, need no `box`.

`fold_own` walks the tree bottom up. In the `Node` arm, `l` and `r` are not subtrees but the
fold's answers for them, here their sums, and the pattern `box Node(…)` frees each node as the
fold passes it, so the run ends with nothing allocated.

## Folds

A fold walks recursive data bottom-up: each arm sees a node with its subtrees already folded.
There are three, one for each way of holding the data:

| fold | takes | use it to |
|---|---|---|
| `fold_imm t { … }` | a borrow, `imm 'a T` | read the data and keep it |
| `fold_own t { … }` | the data itself | consume it, freeing each node |
| `fold_reuse t { … }` | the data itself | rebuild it in place, reusing each node's memory |

```bc
include textio

data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)

fn branch(l: Tree, v: i32, r: Tree) -> Tree = box Node(l, v, r)

-- Reads the tree through a borrow: `v` is a view of the node's value.
fn sum<'a>(t: imm 'a Tree) -> i32 = fold_imm t { Leaf -> 0 | Node(l, v, r) -> l + *v + r }

-- The largest value; consumes the tree.
fn largest(t: Tree) -> i32 =
  fold_own t {
    Leaf -> 0
  | box Node(l, v, r) -> if l > v && l > r { l } else if r > v { r } else { v }
  }

main -> 1 =
  let t = branch(branch(Leaf, 1, Leaf), 7, branch(Leaf, 3, Leaf));
  let s = sum(&t);
  print_dec(s);
  print_byte(b' ');
  print_dec(largest(t));
  print_byte(b'\n')
-- output: 11 7
```

Folds work on generic data too:

```bc
include textio

data List[T] = Nil | Cons(head: T, tail: List[T])

fn cons[T](x: T, rest: List[T]) -> List[T] = box Cons(x, rest)

fn len[T]<'a>(l: imm 'a List[T]) -> i32 = fold_imm l { Nil -> 0 | Cons(_, rest) -> 1 + rest }

fn first[T](l: List[T]) -> Option[T] = match l { Nil -> None | box Cons(x, rest) -> Some(x) }

main -> 1 =
  let xs = cons(1, cons(2, cons(3, Nil)));
  let n = len(&xs);
  print_dec(n);
  print_byte(b' ');
  match first(xs) { Some(x) -> print_dec(x) | None -> print_lit("empty") };
  print_byte(b'\n')
-- output: 3 1
```

`first` keeps the head and drops the rest of the list, which the compiler frees.

## Collections of recursive data

`Vec[T]`, the prelude's growable vector ([below](#buffers-and-strings)), holds recursive data like
any other value, and a type may hold a vector of itself with no `box`: the vector's storage is
already on the heap. A rose tree, Rust's `struct Tree { val: i32, kids: Vec<Tree> }`, is

```bc
include textio
include rec

data Tree = Tree(val: i32, kids: Vec[Tree])

-- A node with no children: an empty vector, which allocates nothing.
fn tip(n: i32) -> Tree = Tree(n, box buf[Tree](0))

-- `t` added as the last child of `p`.
fn adopt(p: Tree, t: Tree) -> Tree =
  match p { Tree(n, kids) -> push(&mut kids, t); Tree(n, kids) }

-- The sum of the values, consuming the tree: each child taken out of its vector.
fn sum(t: Tree) -> i32 =
  match t {
    Tree(v, kids) ->
      let n = len_of(&kids);
      let mut s = v;
      for i in 0..n {
        let child = take(&mut kids, i);
        match child { Some(c) -> s = s + sum(c) | None -> () }
      };
      s
  }

main -> 1 =
  let t = adopt(adopt(tip(10), tip(1)), adopt(tip(2), tip(3)));
  print_dec(with on_exhausted(!{ u -> 0 - 1 }) { sum(t) });
  print_byte(b'\n')
-- output: 16
```

`take(&mut kids, i)` moves element `i` out, leaving an empty node in its place. `sum` calls
itself, which is what `on_exhausted` is for ([Recursion](#recursion), next). A node with a fixed
number of children can hold an array of itself in the same way,
`data Tree = Tip(i32) | Node(i32, array Tree)`, and a trie node is
`data Trie = Trie(bool, Vec[Option[Trie]])`.

## Recursion

A function that calls itself runs with a budget of depth, 10000 levels, instead of an unbounded
stack. When the budget runs out the recursion raises an error, `Exhausted`, which unwinds every
level, freeing what each held, like any other [error](errors.md). The compiler checks that
something handles it, and `include rec` has the two handlers:

- `with on_exhausted(f) { … }` answers `f(())` if the budget runs out, so `f` is a closure that
  ignores its argument: `!{ u -> 0 - 1 }` answers −1;
- `with deep { … }` keeps the pending calls on the heap instead of the stack, so the recursion is
  limited only by memory.

```bc
include textio
include rec

fn down(n: i32) -> i32 = if n == 0 { 0 } else { 1 + down(n - 1) }

main -> 1 =
  print_dec(with on_exhausted(!{ u -> 0 - 1 }) { down(500) });
  print_byte(b' ');
  print_dec(with on_exhausted(!{ u -> 0 - 1 }) { down(20000) });
  print_byte(b'\n')
-- output: 500 -1
```

`down(20000)` is deeper than the budget, so its answer is −1. `with deep { down(20000) }` would
run it to the end. A fold doesn't count as recursion and needs no handler.

Functions declared one after the other may call each other, as `even` calling `odd` and `odd`
calling `even`, and a recursion may be generic. Each use at new types is compiled as its own copy
of the recursion:

```bc
include textio
include rec

data List[T] = Nil | Cons(head: T, tail: List[T])

fn cons[T](x: T, rest: List[T]) -> List[T] = box Cons(x, rest)

fn map[A, B](l: List[A], f: !(A => B)) -> List[B] =
  match l { Nil -> Nil | box Cons(x, rest) -> cons(f(x), map(rest, f)) }

fn sum(l: List[i32]) -> i32 = fold_own l { Nil -> 0 | box Cons(x, rest) -> x + rest }

main -> 1 =
  let xs = cons(1, cons(2, cons(3, Nil)));
  let ys = with on_exhausted(!{ u -> Nil }) { map(xs, !{ x -> x * x }) };
  print_dec(sum(ys));
  print_byte(b'\n')
-- output: 14
```

`include list` has a ready-made generic `List[A]` with `nil()`, `cons(x, xs)`, `map`, `filter`
and `fold`.

### Layers

A **layer** wraps every call a recursion makes of itself, without touching the recursive
function. It is a generic function of the call and its argument, and `with L { … }` applies it to
the recursions in the block. Here a layer counts the calls of `fib`:

```bc
include textio
include rec

effect Count { fn tick() -> i32 }

handler count(mut n: i32): Count = { tick() = { n = n + 1; n } }

fn counted[A, B](call: !(A => B), a: A) -> B = tick(); call(a)

fn fib(n: i32) -> i32 = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }

main -> 1 =
  let c = alloc(0);
  let f = with count(&mut c) { with counted { with on_exhausted(!{ u -> 0 - 1 }) { fib(10) } } };
  print_dec(f);
  print_lit(" after ");
  print_dec(free(c));
  print_lit(" calls\n")
-- output: 55 after 176 calls
```

`fib(10)` makes 176 calls of itself, each counted; the first call, from outside, is not. The same
shape gives tracing or a step limit. Effects and handlers (`effect`, `handler`,
`with`) are [their own chapter](effects.md).

## Arrays

`array A` owns `n` cells, `n` known when the program runs. `array_new[A](n, f)` makes one, with
`f(i)` at index `i`. An array is owned, so it is lent to be read:

- `at(&a, i, d)` copies element `i`, or answers `d` when `i` is out of range;
- `borrow imm a { v -> … }` lends the whole array as a *view*, `array_imm 'a A`, and
  `borrow mut a { v -> … }` as a mutable one, `array_mut 'a A`;
- a `for` over a view visits each element's borrow, read with `*p`.

`include slice` has the view operations, as Rust's slice methods: `len`, `get`, `set`,
`swap_at`, `split_at`, `reverse`, `fill`, `find`, `binary_search`, `sort`, and their `_mut`
forms.

```bc
include textio
include slice

fn sum<'a>(v: array_imm 'a i32) -> i32 =
  let mut s = 0;
  for p in v { s = s + *p };
  s

fn scramble(i: i32) -> i32 = (i * 7) % 5

main -> 1 =
  let a = array_new[i32](5, scramble);
  let s = borrow imm a { v -> sum(v) };
  borrow mut a { v -> let v = sort(v, cmp_i32, 0); discard_mut(v) };
  let lo = at(&a, 0, 0);
  let hi = at(&a, 4, 0);
  print_dec(s);
  print_lit(", from ");
  print_dec(lo);
  print_lit(" to ");
  print_dec(hi);
  print_byte(b'\n')
-- output: 10, from 0 to 4
```

A function that changes a view hands its `array_mut` back, so a block that sorts in place ends
with `discard_mut(v)`, which ends the view. A view can be split at a run-time index into two
views of the same elements (`split_at`, `split_at_mut`), as Rust's `split_at_mut` is, so a
quicksort sorts each half in place with no allocation per element.

## Buffers and strings

`buf A` is a growable array, `include buf`, and `Vec[T]` is the prelude's name for one:
`data Vec[T] = Vec(buf T)`, and every buffer function works on a `Vec`. `box buf[A](cap)`
allocates one with room for `cap` elements (`box buf[A](0)` allocates nothing until the first
push), `push(&mut v, x)` appends, `pop(&mut v)` takes the last as an `Option`, `take(&mut v, i)`
moves element `i` out, and `len_of(&v)` is the length. A buffer lends its elements as a view, as an
array does, so `get`, `set` and the rest of `include slice` index it:

```bc
include textio
include slice

fn sum<'a>(v: array_imm 'a i32) -> i32 = let mut s = 0; for p in v { s = s + *p }; s

main -> 1 =
  let mut v: Vec[i32] = box buf[i32](2);
  for i in 0..5 { push(&mut v, i * i) };
  let n = len_of(&v);
  let s = borrow imm v { w -> sum(w) };
  borrow mut v { w -> let w = set(w, 0, 100); discard_mut(w) };
  let first = borrow imm v { w -> at(w, 0, 0) };
  print_dec(n);
  print_byte(b' ');
  print_dec(s);
  print_byte(b' ');
  print_dec(first);
  print_byte(b'\n')
-- output: 5 30 100
```

A buffer's spare capacity holds placeholder elements, so its element type must have one: numbers,
views, arrays, buffers, and data built from them do, but a heap cell `ref A` doesn't, and
`buf[ref i32]` is refused.

`string` is a buffer of UTF-8 bytes, and `text 'a` a view of some (`include textio`, which brings
`include text` and the I/O helpers). `box string(cap)` makes one; `push_lit(&mut s, "…")`,
`push_dec(&mut s, n)` and `push_char(&mut s, 'c')` append. A string literal `"…"` is data the
program owns no copy of. Text views are cut without copying (`split_once`, `trim`, `next_line`,
`fold_lines`), `eq_lit(t, "…")` compares one with a literal, and `parse_i32` reads a number,
raising on bad input ([Errors](errors.md)).

```bc
include textio

fn point(x: i32, y: i32) -> string =
  let mut s = box string(16);
  push_lit(&mut s, "(");
  push_dec(&mut s, x);
  push_lit(&mut s, ", ");
  push_dec(&mut s, y);
  push_char(&mut s, ')');
  s

main -> 1 =
  let s = point(3, 0 - 4);
  let n = len_of(&s);
  borrow imm s { t -> print_str(t) };
  print_lit(" is ");
  print_dec(n);
  print_lit(" bytes\n")
-- output: (3, -4) is 7 bytes
```

## `poly` families

A generic function `fn f[T](…)` has one body for every `T`. A **family** has one body per type,
chosen by the type, as a Rust trait with one method is. It is declared by its signature with no
body, and each `poly f at H = …` gives its case at a type `H`:

```bc
include textio

poly weight[T](x: T) -> i32

poly weight at i32 = x
poly weight at bool = if x { 1 } else { 0 }
poly weight[A, B] at A * B = let (a, b) = x; weight(a) + weight(b)

main -> 1 =
  print_dec(weight((40, (true, true))));
  print_byte(b'\n')
-- output: 42
```

A call picks the case from its argument's type, at compile time; a case may itself be generic,
as the one at `A * B` is, and calls the family at the parts. The rules keep the choice a function
of the type:

- **One case per type.** A second case at the same type is an error, never resolved by order.
- **The most specific case wins**, and two cases that overlap with neither more specific are an
  error.
- **A type with no case** is an error at the call that needs it.

A family's cases are global to the program.

### Operators at your own types

`+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>` and `>=` are families too. At the integer and float
types they are the machine instructions. At any other type, a program gives a case, `poly (+) at
H = …`, whose parameters are `a` and `b`:

```bc
include textio

data Complex = C(re: i32, im: i32)

poly (+) at Complex =
  match (a, b) { (C(ar, ai), C(br, bi)) -> C(ar + br, ai + bi) }

poly (*) at Complex =
  match (a, b) { (C(ar, ai), C(br, bi)) -> C(ar * br - ai * bi, ar * bi + ai * br) }

-- `x₁·y₁ + x₂·y₂`, at any type with `+` and `*`.
fn dot[T](x: T * T, y: T * T) -> T =
  let (x1, x2) = x;
  let (y1, y2) = y;
  x1 * y1 + x2 * y2

main -> 1 =
  print_dec(dot((1, 2), (3, 4)));
  print_byte(b'\n');
  match dot((C(1, 2), C(1, 1)), (C(3, 4), C(0 - 1, 3))) {
    C(re, im) -> print_dec(re); print_lit(" + "); print_dec(im); print_lit("i\n")
  }
-- output: 11
-- output: -9 + 12i
```

`dot` at `i32` is compiled with the machine's `mul` and `add`; at `Complex` with the cases above.
A different arithmetic is a different type, never a different scope. Give the type a `data`
declaration, as here: a `type` name is only an alias, so a case at `type Complex = i32 * i32`
would be a case at every pair of `i32`s.

### Equality, hashing and order

`include key` declares the families a map uses: `equal`, `hash` and `order`, each taking its
operands as views so that a key is read where it is stored. They have cases at the integers,
`1`, tuples, sums, arrays and buffers (so `bool`, `string` and `text` are covered), compared
structurally. `==` and `equal` are separate families: a float has `==`, IEEE 754's, and no
`equal`, so a float is not a map key.

## Maps and sets

`include map` is a hash map, `Map[K, V]`, and a set, `Set[K]`. A map is a value: it is lent to
each operation, and an operation that changes it takes it `&mut`.

| call | answers |
|---|---|
| `map_new[K, V](cap)` | an empty map with room for `cap` entries before it grows |
| `map_insert(&mut m, k, v)` | the value displaced, as an `Option` |
| `map_lookup(&m, k)` | a copy of the value (`V` copyable), as an `Option` |
| `map_contains(&m, k)` | `bool` |
| `map_remove(&mut m, k)` | the value taken out, as an `Option` |
| `map_len(&m)` | `i32` |
| `set_new[K](cap)`, `set_insert(&mut s, k)`, `set_contains(&s, k)`, `set_remove(&mut s, k)`, `set_len(&s)` | `set_insert` answers whether `k` was new |

Counting the letters of a word:

```bc
include textio
include map

-- How often each byte of `t` occurs.
fn tally<'t>(t: text 't) -> Map[u8, i32] =
  let mut counts = map_new[u8, i32](16);
  for p in t {
    let c = *p;
    let old = map_lookup(&counts, c);
    let n = match old { Some(n) -> n + 1 | None -> 1 };
    map_insert(&mut counts, c, n)
  };
  counts

main -> 1 =
  let counts = borrow imm "mississippi" { t -> tally(t) };
  let kinds = map_len(&counts);
  print_dec(kinds);
  print_lit(" letters:");
  borrow imm counts { 'x, r ->
    for e in map_iter(r) { let (k, v) = e; print_byte(b' '); print_byte(k); print_dec(*v) } };
  print_byte(b'\n')
-- output: 4 letters: s4 p2 m1 i4
```

`borrow imm m { 'x, r -> … }` lends the map's entries: `map_iter(r)` visits every entry, each
value as a view, and `map_get(r, k)` answers a view of one value in place, so values that aren't
copyable, such as vectors, are read without copying. While the map is lent it can't change. The
hash is deterministic, so the order of iteration is the same on every run.
