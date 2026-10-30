# Language reference

This page states the language's syntax and rules in one place, briefly. The guide chapters teach
the same material with longer examples; each section below links to the one it summarises. The
library's types and functions are in the [Standard library](stdlib.md), and what isn't built yet
is in [Status](status.md).

## Lexical structure

**Comments** run from `--` to the end of the line. There are no block comments.

**Names.** There are three kinds:

| kind | form | used for |
|---|---|---|
| lower-case | `[a-z_][A-Za-z0-9_']*` | variables, functions, fields, handlers, operations |
| upper-case | `[A-Z][A-Za-z0-9_]*` | types, type parameters, constructors, effects |
| lifetime | `'` then `[a-z][a-z0-9_]*` | lifetimes, `'a`, `'main` |

**Literals.**

| literal | type | examples |
|---|---|---|
| integer, decimal or hexadecimal | `i32`, or the integer type expected | `42`, `0x2A` |
| integer at a width | that width | `u8[200]`, `i64[5000000000]` |
| float: a fraction or an exponent | `f64`, or `f32` where expected | `1.5`, `2.5e-3`, `1e10` |
| byte | `u8` | `b'a'`, `b'\n'` |
| character | `i32`, its Unicode code point | `'a'`, `'é'`, `'\n'` |
| string | `lit`, read with the `text` functions | `"Hello\n"` |
| `true`, `false` | `bool` | |
| `()` | `1` | |

A byte literal holds a printable ASCII character or one of the escapes `\n`, `\t`, `\r`, `\0`,
`\\`, `\'`; a character literal takes the same escapes. A string literal is written on one line,
is UTF-8, and takes the escapes `\n`, `\t`, `\r`, `\0`, `\\`, `\"` and `\xNN` (the byte with
hexadecimal value `NN`). There are no negative literals: write `0 - 5`.

```bc
include textio

main -> 1 =
  let n = 0x2A;                -- 42
  let big = i64[5000000000];
  let c = 'é';                 -- 233
  print_dec(n);
  print_byte(b' ');
  print_dec64(big);
  print_byte(b' ');
  print_dec(c);
  print_lit(" \x41\"\n")
-- output: 42 5000000000 233 A"
```

**Reserved words.** These can't be used as names:

- the keywords of programs: `borrow`, `box`, `break`, `clone`, `continue`, `def`, `div`, `effect`,
  `else`, `fn`, `fold_imm`, `fold_own`, `fold_reuse`, `for`, `handler`, `if`, `imm`, `in`,
  `include`, `inl`, `inr`, `let`, `loop`, `main`, `match`, `modify`, `mut`, `poly`,
  `return`, `total`, `type`, `while`, `with`;
- the built-in types and operations: `alloc`, `array`, `array_imm`, `array_mut`, `array_new`,
  `f32`, `f64`, `free`, `host`, `i32`, `i64`, `ref`, `swap`, `u8`;
- words reserved for the compiler's internal forms: `abort`, `absurd`, `all`, `alloc_s`,
  `array_copy`, `array_empty`, `array_forget`, `array_free`, `array_get`, `array_len`,
  `array_replace`, `array_size`, `block`, `bounded_fix`, `boxed`, `case`, `copy`, `copy_bang`,
  `count_fold`, `count_try`, `delay`, `delay_in`, `delay_out`, `dom`, `extern`, `fam`, `fixd`,
  `forall`, `force`, `forget_bang`, `forget_imm`, `forget_mut`, `forget_unk`, `free_s`, `fun`,
  `handle_with`, `input`, `iter`, `leaf`, `mu`, `node`, `nu`, `nu_in`, `nu_out`, `output`,
  `perform`, `roll`, `run`, `shape`, `shorten_imm`, `shorten_mut`, `sized`, `stream`,
  `stream_in`, `stream_out`, `str`, `thunk`, `thunkv`, `top`, `unbang`, `unbox`, `unfold`,
  `unfold_s`, `unk`, `unroll`, `unwind`, `val`, `view`, every word beginning `slice_`,
  `withbor` or `withload`, `withswap`, and `writes`; and the upper-case `U`, `F` and `Fun`.

A few ordinary names mean something where a type or a declaration is expected, and are names
anywhere else: `data`, `at`, `where`, `ctl`, `bool`, `string`, `buf`, `text`, `text_mut`, `lit`,
`never` and `pull`.

## Declarations

A program is a sequence of declarations, with at most one `main`. A name is in scope from its
declaration on: a function or type is used after it is declared. Functions declared one after
the other may call each other ([Recursion](guide/data.md#recursion)).

| declaration | form |
|---|---|
| library module | `include textio` |
| function | `fn f[T, …]<'a, …>(x: A, …) -> B with E, … where T: 'a = body` |
| terminating function | `total fn f(…) -> B = body` |
| constant | `def name : A = e`, `def name[T, …] : A = e` |
| data type | `data N[T, …]<'a, …> = C₁(A, …) \| C₂(f: A, …) \| C₃` |
| record type | `data N[T, …]<'a, …> = { f: A, … }` |
| type alias | `type N[T, …]<'a, …> = A` |
| effect | `effect E[T, …] { fn op(x: A, …) -> B; ctl op(…) -> B; … }` |
| handler | `handler h(mut s: S): E = { op(x, …) = e; … }` |
| control handler | `handler h[T, …](p: A, …): E[…], A -> R with E₂ = { return(x) = e; op(x, …, k) = e; … }` |
| family | `poly f[T](x: A, …) -> B` |
| case of a family | `poly f[P, …] at H = body`, `poly (+) at H = body` |
| entry point | `main -> T = body` |

In a function, the type parameters `[T, …]` and the lifetime parameters `<'a, …>` are each
optional, as are the row `with …` and the bounds `where …`. A lifetime parameter may be bounded
by another, `<'x, 'w < 'x>`. With no parameters, a function is `fn f() -> B`. Every parameter's
type and the result type are written.

```bc
include textio

data Pair[A] = { fst: A, snd: A }
type Grid = i32 * i32

def origin : i32 = 0

fn swapped[A](p: Pair[A]) -> Pair[A] = match p { Pair { fst, snd } -> Pair { fst: snd, snd: fst } }

fn first<'a>(r: imm 'a Grid) -> i32 = let (x, y) = *r; x

total fn area(g: Grid) -> i32 = let (w, h) = g; w * h

main -> 1 =
  let p = swapped(Pair { fst: 1, snd: 2 });
  let c = alloc((3, 4));
  let x = first(&c);
  print_dec(p.fst + origin);
  print_byte(b' ');
  print_dec(x * 10 + area(free(c)));
  print_byte(b'\n')
-- output: 2 42
```

- `data` cases with fields hold them positionally, `C(A, B)`, or by name, `C(f: A, g: B)`; a
  record has one case, named after the type. A case that holds the type itself is built with
  `box` ([Data and generics](guide/data.md)).
- `type` names a type; the name and the type are interchangeable
  ([Tuples and sums](guide/basics.md#tuples-and-sums)).
- `effect`: an operation declared `fn` answers its caller; `ctl` receives the continuation and
  resumes it at most once, `must_resume ctl` exactly once, and `ctl op(…) -> never` never. `-> B`
  left out is `-> 1`. A handler of `fn` operations keeps its state in its `mut` parameter; a
  control handler names the body's type `A` and its answer `R`, and has a `return(x)` clause
  ([Effects and handlers](guide/effects.md)).
- `poly`: a family has one type parameter, the type that chooses the case; the operators `+`,
  `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`, `>=` are families
  ([`poly` families](guide/data.md#poly-families)).
- `include` brings a library module's declarations into scope ([Standard library](stdlib.md)).
  The prelude (`bool`, `true`, `false`, `not`, `Option`, `Vec`, `to_i32`, `to_u8`) is always in
  scope.

## Types

| type | what it is | guide |
|---|---|---|
| `i32`, `i64`, `u8` | integers, two's complement | [Numbers](guide/basics.md#numbers) |
| `f32`, `f64` | IEEE 754 floats | [Floats](guide/basics.md#floats) |
| `bool` | `true` or `false` | [Numbers](guide/basics.md#numbers) |
| `1` | the unit type; its value is `()` | |
| `0`, `never` | the empty type, which has no values | [Errors](guide/errors.md) |
| `A * B`, `A * B * C` | tuples | [Tuples and sums](guide/basics.md#tuples-and-sums) |
| `A + B` | `inl a` or `inr b` | [Tuples and sums](guide/basics.md#tuples-and-sums) |
| `N`, `N[A, …]`, `N[…]<'a, …>` | a `data` or `type` declaration, applied | [Data and generics](guide/data.md) |
| `ref A` | a heap cell holding an `A` | [Ownership](guide/ownership.md#copyable-and-owned-values) |
| `box A` | a `data` field on the heap: `ref A` | [Recursive data](guide/data.md#recursive-data) |
| `array A` | `n` cells, `n` fixed when it is made | [Arrays](guide/data.md#arrays) |
| `array_imm 'a A`, `array_mut 'a A` | a shared or exclusive view of an array's elements | [Arrays](guide/data.md#arrays) |
| `buf A`, `Vec[A]` | a growable array | [Buffers and strings](guide/data.md#buffers-and-strings) |
| `string` | a growable buffer of UTF-8 bytes | [Buffers and strings](guide/data.md#buffers-and-strings) |
| `text 'a`, `text_mut 'a` | a view of bytes, shared or exclusive | [Buffers and strings](guide/data.md#buffers-and-strings) |
| `lit` | a string literal | |
| `imm 'a A`, `mut 'a A` | a shared or exclusive borrow, for the lifetime `'a` | [Ownership](guide/ownership.md#borrowing-for-one-call) |
| `!(A => B)` | a function that may be called any number of times | [Functions as values](guide/basics.md#functions-as-values) |
| `A => B` | a closure called at most once | [Functions as values](guide/basics.md#functions-as-values) |
| `!(A => B with E, …)` | a computation parameter: the callee handles `E` | [Computation parameters](guide/effects.md#computation-parameters-and-) |
| `U (pull A B R)` | a stored generator yielding `A`, returning `B` | [Stored generators](guide/iteration.md#stored-generators) |

A function of several parameters has a tuple as its argument type: `fn f(x: i32, y: bool)` is a
`!(i32 * bool => B)`. `*` binds tighter than `+`, which binds tighter than `=>`, and all three
associate to the right: `A * B + C => D` is `((A * B) + C) => D`.

Copyable types are the numbers, `bool`, `1`, `!` functions, and tuples and sums of copyable
types; recursive data built from them is copied only by `clone(x)`. Every other type is owned
and used exactly once ([Ownership and borrows](guide/ownership.md)).

**Rows.** A function's row, the effects it performs, is inferred, and may be written after the
result type: `-> B with Fail[i32], Stdout`. An entry may be named, `with a: Log, b: Log`, and a
written row is checked ([Effects and handlers](guide/effects.md)).

**Lifetimes.** A lifetime is a parameter `'a` of a function, a `data` or a `type`, the lifetime
`'b` a borrow block names, `{ 'b, x -> … }`, or `'main`, which lasts for `main`'s body. They are
lexical, and never elided in signatures
([Lifetimes in signatures](guide/ownership.md#lifetimes-in-signatures)).

## Expressions and statements

A body is a sequence of statements separated by `;`, and its value is the last one's. A
statement is one of:

| statement | meaning |
|---|---|
| `let p = e;` `let p: A = e;` | bind the pattern `p`; later `let`s of a name shadow it |
| `let mut x = e;` | a variable that can be assigned |
| `let C(p, …) = e;` | take apart a value of a type with one case |
| `x = e` | assign a `let mut` variable |
| `x.f = e` | assign a field of a `let mut` record, or of one lent `mut` |
| `e` | any expression |

The expressions are:

| expression | meaning | guide |
|---|---|---|
| `f(a, b)`, `f[T, …](…)`, `f['main](…)` | a call; type and lifetime arguments are optional | [Generic functions](guide/basics.md#generic-functions) |
| `(a, b)`, `()` | tuples, the unit | [Tuples and sums](guide/basics.md#tuples-and-sums) |
| `inl e`, `inr e` | the sides of a sum | [Tuples and sums](guide/basics.md#tuples-and-sums) |
| `C`, `C(e, …)`, `N { f: e, … }`, `N { f, … }` | a `data` value; `{ f }` is `{ f: f }` | [Records and variants](guide/basics.md#records-and-variants) |
| `box C(e, …)` | a case allocated on the heap | [Recursive data](guide/data.md#recursive-data) |
| `box buf[A](n)`, `box string(n)` | a buffer or string with room for `n` | [Buffers and strings](guide/data.md#buffers-and-strings) |
| `e.f` | a field | [Records and variants](guide/basics.md#records-and-variants) |
| `(e : A)` | `e`, at the type `A` | |
| `if c { … } else if d { … } else { … }` | the `else` may be left out when the branch's value is `()` | [Mutable variables](guide/basics.md#mutable-variables-and-loops) |
| `match e { p -> … \| p -> … }` | the arms must cover every case | [Records and variants](guide/basics.md#records-and-variants) |
| `&x`, `&mut x` | lend the place `x` to the call it is an argument of | [Borrowing for one call](guide/ownership.md#borrowing-for-one-call) |
| `borrow imm x { r -> … }`, `borrow mut x { m -> … }` | lend `x` for a block; `{ 'b, r -> … }` names the lifetime | [Borrow blocks](guide/ownership.md#borrow-blocks) |
| `*r` | copy out the contents of a borrow | [Borrowing for one call](guide/ownership.md#borrowing-for-one-call) |
| `modify m { v -> e }` | replace the contents of a `mut` borrow; with `e = (new, r)`, answer `r` | [Borrowing for one call](guide/ownership.md#borrowing-for-one-call) |
| `alloc(e)`, `free(c)`, `swap(c, e)` | make a cell, take its contents out and free it, or exchange its contents (`(cell, old)`) | [Ownership](guide/ownership.md#copyable-and-owned-values) |
| `clone(x)` | copy recursive data | [Ownership](guide/ownership.md#recursive-data-is-copied-only-when-you-say-so) |
| `!{ p -> … }` | a closure called any number of times, which captures nothing | [Functions as values](guide/basics.md#functions-as-values) |
| `{ p -> … }` | a closure called once, which may capture anything | [Functions as values](guide/basics.md#functions-as-values) |
| `fold_imm e { p -> … \| … }`, `fold_own …`, `fold_reuse …` | fold recursive data bottom up | [Folds](guide/data.md#folds) |
| `with h(e, …) { … }`, `with n = h(…) { … }` | run a block under a handler | [Effects and handlers](guide/effects.md) |
| `n.op(e)` | perform `op` at the handler named `n` | [Several instances](guide/effects.md#several-instances-and-names) |
| `raise(e)` | raise an error (`include fail`) | [Errors](guide/errors.md) |
| `e \|> f(a, …)` | `f(e, a, …)`; into a handler, `with f(a, …) { e }` | [Pipelines](guide/iteration.md#pipelines) |
| `host[op](…)` | a machine instruction: bitwise, shifts, conversions | [Numbers](guide/basics.md#numbers) |

```bc
include textio

data Shape = Rect(w: i32, h: i32) | Circle(r: i32)
data Point = { x: i32, y: i32 }

fn area(s: Shape) -> i32 = match s { Rect(w, h) -> w * h | Circle(r) -> 3 * r * r }

fn kind(n: i32, b: u8) -> i32 =
  match (n, b) {
    (0, _) -> 0
  | (_, b'x') -> 1
  | _ -> 2
  }

main -> 1 =
  let mut p = Point { x: 1, y: 2 };
  p.x = p.x + 10;
  let Point { x, y } = p;
  let (a, b) = (area(Rect(2, 3)), area(Circle(1)));
  let mut best = a;
  if b > best { best = b };
  let sign = if x > y { 1 } else if x == y { 0 } else { 0 - 1 };
  print_dec(best);
  print_byte(b' ');
  print_dec(sign);
  print_byte(b' ');
  print_dec(kind(0, b'x') + kind(5, b'x') * 10 + kind(5, b'y') * 100);
  print_byte(b'\n')
-- output: 6 1 210
```

### Patterns

`let`, `match`, closures and borrow blocks take patterns:

| pattern | matches |
|---|---|
| `x` | anything, bound to `x` |
| `_` | anything |
| `()` | the unit |
| `(p, q, …)` | a tuple |
| `C`, `C(p, …)` | a case of a `data` type |
| `box C(p, …)` | a case on the heap, freeing its cell |
| `N { f: p, … }`, `N { f, … }` | a record; fields left out are ignored |
| `inl p`, `inr p` | the sides of a sum |
| `5`, `b'a'`, `'a'`, `true`, `false` | a literal |

`let` takes a pattern that can't fail: names, `_`, `()`, tuples, and constructors of a type with
one case. A `match` may match several values at once, `match (a, b) { (p, q) -> … }`. There are
no guards and no or-patterns.

## Loops

| loop | runs | guide |
|---|---|---|
| `for i in a..b { … }` | for `i` from `a` up to `b - 1` | [`for` over data](guide/iteration.md#for-over-data) |
| `for x in a { … }` | over an owned array: each element copied out, then the array dropped | [`for` over data](guide/iteration.md#for-over-data) |
| `for p in &a { … }`, `for p in &mut a { … }` | each element of `a` lent `imm` or `mut` | [`for` over data](guide/iteration.md#for-over-data) |
| `for p in v { … }` | each element of the view `v` lent | [`for` over data](guide/iteration.md#for-over-data) |
| `for x in g(…) { … }` | the body runs at each `yield` of the generator `g` | [Generators](guide/iteration.md#generators) |
| `for x in it { … }` | pulls from a stored generator until it returns | [Stored generators](guide/iteration.md#stored-generators) |
| `while c { … }` | while `c` is true | [Loops that may not end](guide/iteration.md#loops-that-may-not-end) |
| `loop { … }` | until a `break` | [Loops that may not end](guide/iteration.md#loops-that-may-not-end) |

In a loop's body, `break` leaves the loop, `break e` leaves it with the value `e`, `continue`
goes on to the next turn, and `return e` returns `e` from the enclosing function. `for … { … }
else { e }` gives the loop's value when its source ends without a `break`, and
`let r = for … { … };` binds the loop's value (or, over a generator, what the generator
returns). A `let mut` variable assigned in the body is carried from turn to turn and is there
after the loop.

A `for` over data always finishes. A function with a `while` or a `loop`, or that calls one, may
diverge, which is inferred; `total fn` asks the compiler to check that it can't, and
`div_fuel(e, n)` runs a diverging `e` for at most `n` steps
([Loops that may not end](guide/iteration.md#loops-that-may-not-end)).

```bc
include textio

main -> 1 =
  let a = array_new[i32](5, !{ i -> i * i });
  let first = for p in &a { let v = *p; if v > 5 { break v } } else { 0 };
  let mut odd = 0;
  for i in 0..10 { if i % 2 == 0 { continue }; odd = odd + i };
  let mut n = 1;
  while n < 100 { n = n * 3 };
  let mut k = 0;
  loop { k = k + 1; if k == 4 { break } };
  print_dec(first);
  print_byte(b' ');
  print_dec(odd);
  print_byte(b' ');
  print_dec(n);
  print_byte(b' ');
  print_dec(k);
  print_byte(b'\n')
-- output: 9 25 243 4
```

## Operators and precedence

From the tightest binding to the loosest:

| operators | associativity |
|---|---|
| calls `f(…)`, type arguments `f[T]`, fields `e.f` | left |
| prefix `*e`, `inl e`, `inr e`, `&x`, `&mut x` | |
| `*`  `/`  `%` | left |
| `+`  `-` | left |
| `==`  `!=`  `<`  `<=`  `>`  `>=` | none: `a < b < c` is an error |
| `&&` | left; the right side runs only if needed |
| `\|\|` | left; the right side runs only if needed |
| `\|>` | left; its right side is a call or a name |
| `a..b`, in a `for` | |

Arithmetic and comparisons work at the type of their operands: the machine instructions at the
integer and float types, and a program's `poly` cases at its own types
([Operators at your own types](guide/data.md#operators-at-your-own-types)). Integer arithmetic
wraps, comparisons are signed, and `/` and `%` truncate toward zero; dividing by zero raises an
error ([Division](guide/errors.md#division)). `not(b)` negates a `bool`. There are no unary
minus, compound assignment or bitwise operators; bitwise operations and shifts are
`host[and32](a, b)` and the like ([Numbers](guide/basics.md#numbers)).

```bc
include textio

fn twice(x: i32) -> i32 = x * 2

main -> 1 =
  let a = 1 + 2 * 3 - 8 / 2 % 3;
  let ok = a > 4 && not(a == 5) || false;
  let b = a |> twice;
  let o = if ok { 1 } else { 0 };
  print_dec(a);
  print_byte(b' ');
  print_dec(b);
  print_byte(b' ');
  print_dec(o);
  print_byte(b'\n')
-- output: 6 12 1
```

## `main`

`main -> T = body` is where the program starts. `main` performs standard input and output, the
clock and the arguments with nothing written; an operation no handler in the program serves goes
to the platform ([Input and output](guide/io.md)). An error that no handler catches is a compile
error, except division, which ends the program with status 1
([Division](guide/errors.md#division)).

When `main` finishes, `bcc` prints its result after the program's own output, and then
`live N`, the number of heap objects still allocated: `0`, unless the result itself holds some.
The result is printed in a raw form: an integer as its width and its bits read unsigned
(`i32[42]`, and `i32[4294967295]` for −1), `bool` as `inl ()` (false) or `inr ()` (true),
records and tuples as tuples of their fields, cases of a sum as `inl …` and `inr …`, a heap
object as `<loc>` and a function as `<fun>`. Most programs print what they mean to and return
`()`, with `main -> 1`.

```bc
main -> i32 * bool = (6 * 7, 1 < 2)
-- answer: (i32[42], inr ())
```
