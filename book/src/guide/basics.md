# Values, functions and numbers

This chapter covers the parts of the language that look like most others: functions, `let`,
`if`, numbers, records and variants, generics and closures. Ownership, the part that is
different, is the [next chapter](ownership.md).

## A program

A program is a list of declarations ending with `main`. `main -> T = e` says that `main` computes
a value of type `T`; `bcc run` prints that value, and then `live N`, the number of heap objects
still allocated. Every example in this book ends with `live 0`.

```bc
fn square(x: i32) -> i32 = x * x

main -> i32 = square(6) + square(2)
-- answer: i32[40]
```

`fn name(params) -> T = e` declares a function. Every parameter has its type written, and so does
the result. A function can call itself and any function declared before it, but not one
declared after it ([Recursion](data.md#recursion)).

A body is a sequence of statements separated by `;`, and its value is the value of the last one:

```bc
fn hyp2(a: i32, b: i32) -> i32 =
  let aa = a * a;
  let bb = b * b;
  aa + bb

main -> i32 =
  let x = hyp2(3, 4);
  let x = x + 1;
  x
-- answer: i32[26]
```

`let x = e;` binds a name, and a later `let` of the same name shadows it. A type can be written,
`let x: i64 = 5;`, and is needed where nothing else fixes it.

## Mutable variables and loops

`let mut x = e;` declares a variable that can be assigned, `x = e;`. `while c { … }` repeats its
body while `c` is true, and `if c { … } else { … }` chooses one branch; both arms of an `if` have
the same type. A statement whose value is `()` is followed by `;`.

```bc
-- The number of Collatz steps from `n` to 1.
fn collatz(n: i32) -> i32 =
  let mut x = n;
  let mut steps = 0;
  while x != 1 {
    if x % 2 == 0 { x = x / 2 } else { x = 3 * x + 1 };
    steps = steps + 1
  };
  steps

main -> i32 = collatz(27)
-- answer: i32[111]
```

A `while` may run forever, and the compiler knows it: a function with one is *div* (it may
diverge), which it infers. Loops over data, which always finish, are `for` loops
([Iteration](iteration.md)).

## Numbers

| type | values | literals |
|---|---|---|
| `i32`, `i64` | two's-complement integers | `42`, `0x2A` |
| `u8` | bytes | `b'a'`, `u8[200]` |
| `f32`, `f64` | IEEE 754 floats | `1.5`, `2.5e-3`, `1e10` |
| `bool` | `true`, `false` | |
| `1` | the unit `()` | |

An integer literal is an `i32` unless another integer type is expected. The operators are
`+ - * / %`, the comparisons `== != < <= > >=`, and `&&`, `||` and `not(b)` on `bool`; each works
at the type of its operands, so `x * 2` at an `i64` is a 64-bit multiplication. Comparisons are
signed. There is no unary minus: write `0 - x`.

`/` and `%` truncate toward zero. A division with no answer (by zero, or `MIN / -1`) raises an
error rather than trapping; [Errors](errors.md#division) shows how to handle it.

```bc
fn mean(xs: i64 * (i64 * i64)) -> i64 =
  let (a, (b, c)) = xs;
  (a + b + c) / 3

main -> i64 * (i32 * bool) =
  let big: i64 = 4000000000;
  let m = mean((big, (big, 1)));
  (m, (17 % 5, m < big && not(m == 0)))
-- answer: (i64[2666666667], (i32[2], inr ()))
```

`main`'s value is printed raw: integers unsigned, so `0 - 1` prints as `i32[4294967295]`, and
`bool` as `inl ()`/`inr ()` (see [Pairs and sums](#pairs-and-sums)). Print with `print_dec` for
anything nicer ([Input and output](io.md)).

A byte is a `u8`. Arithmetic on bytes is done at `i32` and narrowed back, and `to_i32(b)` and
`to_u8(n)` convert between the two:

```bc
main -> u8 * i32 =
  let c = b'a' + 2;
  (c, to_i32(c) - to_i32(b'a'))
-- answer: (u8[99], i32[2])
```

The bitwise operations and shifts have no operators yet: they are written as calls of the
machine instruction, `host[and32](x, 1)`, `host[shl64](n, 3)`, `host[shr_u32](x, 16)`
([Integers](../elaboration/integers.md) lists them).

### Floats

A literal with a fraction or an exponent is a float, an `f64` unless an `f32` is expected. `+ - * /`
and the comparisons work at floats as IEEE 754 defines them: a NaN compares unequal to
everything, itself included. `include float` brings the rest: `sqrt_f64`, `abs_f64`, `floor_f64`,
`round_f64`, conversions such as `f64_of_i32` and `i32_of_f64_sat`, and `print_f64`, which prints
the shortest decimal that reads back as the same float.

```bc
include float

fn hypot(x: f64, y: f64) -> f64 = sqrt_f64(x * x + y * y)

main -> i32 =
  let h = hypot(3.0, 4.0);
  print_f64(h / 3.0);
  print_byte(b'\n');
  i32_of_f64_sat(h * 10.0)
-- output: 1.6666666666666667
-- answer: i32[50]
```

`main`'s value prints a float as its bits (`f64[4617315517961601024]` for `5.0`), which is why
this one prints with `print_f64`. A float has no hash or total order of its own, so it cannot be
a map key directly; `lib/float.bc` has `total_cmp_f64` and `ord_f64` for when you need one.

## Records and variants

`data` declares a type of your own. A **record** has named fields, read and written with `.`:

```bc
data Point = { x: i32, y: i32 }

fn manhattan(p: Point) -> i32 = p.x + p.y

main -> i32 =
  let mut p = Point { x: 3, y: 4 };
  p.x = p.x * 10;
  manhattan(p)
-- answer: i32[34]
```

A **variant** is one of several cases, each with its own fields, and `match` takes it apart:

```bc
data Shape = Rect(w: i32, h: i32) | Circle(r: i32)

fn area(s: Shape) -> i32 =
  match s {
    Rect(w, h) -> w * h
  | Circle(r) -> 3 * r * r
  }

main -> i32 = area(Rect(3, 4)) + area(Circle(2))
-- answer: i32[24]
```

A `match` must cover every case, and it can match several values at once,
`match (state, byte) { (Locked, b'c') -> Open | … }`. Declarations can be generic,
`data Pair[A, B] = { fst: A, snd: B }`, and the prelude has `Option[T]`, with `Some(x)` and
`None`. Recursive types, such as lists and trees, are in [Data and generics](data.md).

## Pairs and sums

Underneath, every type is built from two pieces, and you can use them directly.

`(a, b)` is a pair, of type `A * B`. There are no wider tuples as such: `(a, b, c)` is the nested
pair `(a, (b, c))`, of type `A * (B * C)`. `let (x, y) = p;` takes a pair apart, and patterns
nest.

A sum `A + B` holds either an `A`, written `inl a`, or a `B`, written `inr b`. `match` takes one
apart, `inl` arm first:

```bc
type Size = (i32 * i32) + i32

fn cells(s: Size) -> i32 =
  match s {
    inl (w, h) -> w * h
  | inr n -> n
  }

main -> i32 =
  let a: Size = inl (3, 4);
  let b: Size = inr 2;
  cells(a) + cells(b)
-- answer: i32[14]
```

`type Size = …` gives a type a name; the name and its definition are interchangeable. `inl` and
`inr` need to know the whole sum, so they appear where a type is expected: an annotated `let`, an
argument, a result.

`bool` is the sum `1 + 1`, with `false` as `inl ()` and `true` as `inr ()`, and `Option[A]` is
`A + 1`. This is why `main`'s value prints sums and pairs: a record prints as its fields, nested
in pairs, and a variant as `inl`/`inr`.

## Generic functions

A function may take type parameters in brackets. They are inferred at each call from the
arguments, or written, `pick[i32](…)`:

```bc
fn swap_pair[A, B](p: A * B) -> B * A = let (a, b) = p; (b, a)

fn pick[A](c: bool, x: A, y: A) -> A = if c { x } else { y }

main -> (bool * i32) * i64 =
  let p = swap_pair((7, true));
  let n = pick[i64](false, 1, 2);
  (p, n)
-- answer: ((inr (), i32[7]), i64[2])
```

A generic function is compiled once for each type it is used at, as in Rust: there is no boxing
and no dictionary. What a generic function may do with a value of type `A` is checked at each
use: a body that copies an `A` works only where `A` can be copied (next chapter).

## Functions as values

A function can be passed to another. Its parameter's type says how often it may be called:

- `!(A => B)` is a function that can be called any number of times. A named function is one, and
  so is a closure `!{ x -> … }`, which can't capture local variables (pass them as arguments, or
  use a one-shot closure).
- `A => B` is a function called at most once. A closure `{ x -> … }` of this type may capture
  anything in scope, including local variables and owned values.

```bc
fn twice(f: !(i32 => i32), x: i32) -> i32 = f(f(x))

fn double(x: i32) -> i32 = x * 2

fn apply_once(f: i32 => i32, x: i32) -> i32 = f(x)

main -> i32 * (i32 * i32) =
  let k = 5;
  let a = twice(double, 3);
  let b = twice(!{ x -> x + 1 }, 0);
  let c = apply_once({ x -> x + k }, 1);
  (a, (b, c))
-- answer: (i32[12], (i32[2], i32[6]))
```

A closure's parameter types come from the parameter it is passed to, so a closure bound with
`let` needs its type written: `let f: !(i32 => i32) = !{ x -> x + 1 };`. A pattern can take the
argument apart, `!{ (a, b) -> a + b }`.

A function whose body performs effects, raises an error or waits, is passed the same way, and the
function it is passed to needs nothing extra to accept it: [Effects and
handlers](effects.md#blocks-that-perform-effects) explains how.
