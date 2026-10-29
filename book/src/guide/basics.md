# Values, functions and numbers

This chapter covers the parts of the language that look like most others: functions, `let`,
`if`, numbers, records and variants, generics and closures. Ownership, the part that is
different, is the [next chapter](ownership.md). The [Language reference](../language-reference.md)
has the whole syntax in one place.

## A program

A program is a list of declarations ending with `main`, where it starts:

```bc
include textio

fn square(x: i32) -> i32 = x * x

main -> 1 =
  print_dec(square(6) + square(2));
  print_byte(b'\n')
-- output: 40
```

`fn name(params) -> T = e` declares a function. Every parameter has its type written, and so does
the result. `main -> 1` returns nothing interesting: `1` is the unit type, whose one value is
`()`. A function calls the functions declared before it; functions that call themselves or each
other are in [Recursion](data.md#recursion).

A body is a sequence of statements separated by `;`, and its value is the value of the last one:

```bc
include textio

fn hyp2(a: i32, b: i32) -> i32 =
  let aa = a * a;
  let bb = b * b;
  aa + bb

main -> 1 =
  let x = hyp2(3, 4);
  let x = x + 1;
  print_dec(x);
  print_byte(b'\n')
-- output: 26
```

`let x = e;` binds a name, and a later `let` of the same name shadows it. A type can be written,
`let x: i64 = 5;`, and is needed where nothing else fixes it. A constant is declared at the top
level with `def`: `def max_depth : i32 = 64`.

## Mutable variables and loops

`let mut x = e;` declares a variable that can be assigned, `x = e;`. `while c { … }` repeats its
body while `c` is true, and `if c { … } else { … }` chooses one branch; both branches have the
same type. An `if` whose body is a statement needs no `else`: `if x > max { max = x }`.

```bc
include textio

-- The number of Collatz steps from `n` to 1.
fn collatz(n: i32) -> i32 =
  let mut x = n;
  let mut steps = 0;
  while x != 1 {
    if x % 2 == 0 { x = x / 2 } else { x = 3 * x + 1 };
    steps = steps + 1
  };
  steps

main -> 1 =
  print_dec(collatz(27));
  print_byte(b'\n')
-- output: 111
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
signed, and `0 - x` negates.

`/` and `%` truncate toward zero. A division with no answer (by zero, or `MIN / -1`) raises an
error rather than trapping; [Errors](errors.md#division) shows how to handle it.

```bc
include textio

fn mean(a: i64, b: i64, c: i64) -> i64 = (a + b + c) / 3

main -> 1 =
  let big: i64 = 4000000000;
  print_dec64(mean(big, big, 1));
  print_byte(b'\n');
  print_dec(17 % 5);
  print_byte(b'\n');
  print_dec((0 - 7) / 2);
  print_byte(b'\n')
-- output: 2666666667
-- output: 2
-- output: -3
```

`print_dec` prints an `i32` and `print_dec64` an `i64`.

A byte is a `u8`. Arithmetic on bytes is done at `i32` and narrowed back, and `to_i32(b)` and
`to_u8(n)` convert between the two:

```bc
include textio

main -> 1 =
  let c = b'a' + 2;
  print_byte(c);
  print_byte(b' ');
  print_dec(to_i32(c) - to_i32(b'a'));
  print_byte(b'\n')
-- output: c 2
```

The bitwise operations, shifts and integer conversions are written as calls of the machine
instruction, with the width as a suffix: `host[and32](x, 1)`, `host[shl64](n, 3)`.

| operations | at `i32` | at `i64` |
|---|---|---|
| and, or, exclusive or | `and32`, `or32`, `xor32` | `and64`, `or64`, `xor64` |
| shifts | `shl32`, `shr_s32` (signed), `shr_u32` (unsigned) | `shl64`, `shr_s64`, `shr_u64` |
| rotations | `rotl32`, `rotr32` | `rotl64`, `rotr64` |
| bit counts | `clz32`, `ctz32`, `popcnt32` | `clz64`, `ctz64`, `popcnt64` |
| unsigned comparisons | `lt_u32`, `le_u32`, `gt_u32`, `ge_u32` | `lt_u64`, … |

`host[extend_s](x)` widens an `i32` to an `i64` (`extend_u` for unsigned), and `host[wrap](n)`
keeps an `i64`'s low 32 bits.

### Floats

A literal with a fraction or an exponent is a float, an `f64` unless an `f32` is expected. `+ - * /`
and the comparisons work at floats as IEEE 754 defines them: a NaN compares unequal to
everything, itself included. `include float` brings the rest: `sqrt_f64`, `abs_f64`, `floor_f64`,
`round_f64`, conversions such as `f64_of_i32` and `i32_of_f64_sat`, and `print_f64`, which prints
the shortest decimal that reads back as the same float.

```bc
include float

fn hypot(x: f64, y: f64) -> f64 = sqrt_f64(x * x + y * y)

main -> 1 =
  let h = hypot(3.0, 4.0);
  print_f64(h / 3.0);
  print_byte(b'\n');
  print_dec(i32_of_f64_sat(h * 10.0));
  print_byte(b'\n')
-- output: 1.6666666666666667
-- output: 50
```

A float has no hash or total order of its own, so it can't be a map key directly; `include float`
has `total_cmp_f64` and `ord_f64` for when you need one.

## Records and variants

`data` declares a type of your own. A **record** has named fields, read and written with `.`:

```bc
include textio

data Point = { x: i32, y: i32 }

fn manhattan(p: Point) -> i32 = p.x + p.y

main -> 1 =
  let mut p = Point { x: 3, y: 4 };
  p.x = p.x * 10;
  print_dec(manhattan(p));
  print_byte(b'\n')
-- output: 34
```

A record pattern, `Point { x, y }`, takes a record apart in a `let` or a `match` and binds each
field to a variable of its name; `Point { x: a, y: b }` binds them to other names. Construction
has the same shorthand: `Point { x, y }` builds a record from variables named like its fields.

```bc
include textio

data Point = { x: i32, y: i32 }

-- The point reflected in the diagonal.
fn flip(p: Point) -> Point =
  match p { Point { x, y } -> Point { x: y, y: x } }

-- The point moved right by `dx`.
fn shift(p: Point, dx: i32) -> Point =
  let Point { x, y } = p;
  let x = x + dx;
  Point { x, y }

main -> 1 =
  let p = shift(flip(Point { x: 1, y: 2 }), 10);
  print_dec(p.x);
  print_byte(b' ');
  print_dec(p.y);
  print_byte(b'\n')
-- output: 12 1
```

A **variant** is one of several cases, each with its own fields, and `match` takes it apart:

```bc
include textio

data Shape = Rect(w: i32, h: i32) | Circle(r: i32)

fn area(s: Shape) -> i32 =
  match s {
    Rect(w, h) -> w * h
  | Circle(r) -> 3 * r * r
  }

main -> 1 =
  print_dec(area(Rect(3, 4)) + area(Circle(2)));
  print_byte(b'\n')
-- output: 24
```

A `match` must cover every case, and it can match several values at once,
`match (state, byte) { (Locked, b'c') -> Open | … }`. Declarations can be generic,
`data Pair[A, B] = { fst: A, snd: B }`, and the prelude has `Option[T]`, with `Some(x)` and
`None`. Recursive types, such as lists and trees, are in [Data and generics](data.md).

## Tuples and sums

`(a, b)` is a pair, of type `A * B`, and `(a, b, c)` a triple, of type `A * B * C`.
`let (x, y) = p;` takes one apart, and patterns nest.

A sum `A + B` holds either an `A`, written `inl a`, or a `B`, written `inr b`, and `match` takes
it apart. Library functions use sums for answers that may be missing: `A + 1` is an `A` or
nothing (`inr ()`), and an error handler answers `A + E`, the value or the error.

```bc
include textio

type Size = (i32 * i32) + i32

fn cells(s: Size) -> i32 =
  match s {
    inl (w, h) -> w * h
  | inr n -> n
  }

main -> 1 =
  let a: Size = inl (3, 4);
  let b: Size = inr 2;
  print_dec(cells(a) + cells(b));
  print_byte(b'\n')
-- output: 14
```

`type Size = …` gives a type a name; the name and its definition are interchangeable. `inl` and
`inr` need to know the whole sum, so they appear where a type is expected: an annotated `let`, an
argument, a result.

## Generic functions

A function may take type parameters in brackets. They are inferred at each call from the
arguments, or written, `pick[i32](…)`:

```bc
include textio

fn swap_pair[A, B](p: A * B) -> B * A = let (a, b) = p; (b, a)

fn pick[A](c: bool, x: A, y: A) -> A = if c { x } else { y }

main -> 1 =
  let (n, ok) = swap_pair((true, 7));
  let m = pick[i64](ok, 1, 2);
  print_dec(n);
  print_byte(b' ');
  print_dec64(m);
  print_byte(b'\n')
-- output: 7 1
```

A generic function is compiled once for each type it is used at, as in Rust: there is no boxing
and no dictionary. What a generic function may do with a value of type `A` is checked at each
use: a body that copies an `A` works only where `A` can be copied (next chapter).

## Functions as values

A function can be passed to another. Its parameter's type says how often it may be called:

- `!(A => B)` is a function that can be called any number of times. A named function is one, and
  so is a closure `!{ x -> … }`, which takes what it needs as arguments rather than capturing
  local variables.
- `A => B` is a function called at most once. A closure `{ x -> … }` of this type may capture
  anything in scope, including local variables and owned values.

```bc
include textio

fn twice(f: !(i32 => i32), x: i32) -> i32 = f(f(x))

fn double(x: i32) -> i32 = x * 2

fn apply_once(f: i32 => i32, x: i32) -> i32 = f(x)

main -> 1 =
  let k = 5;
  print_dec(twice(double, 3));
  print_byte(b' ');
  print_dec(twice(!{ x -> x + 1 }, 0));
  print_byte(b' ');
  print_dec(apply_once({ x -> x + k }, 1));
  print_byte(b'\n')
-- output: 12 2 6
```

A closure's parameter types come from the parameter it is passed to, so a closure bound with
`let` needs its type written: `let f: !(i32 => i32) = !{ x -> x + 1 };`. A pattern can take the
argument apart, `!{ (a, b) -> a + b }`.

A function whose body performs effects, raises an error or waits, is passed the same way, and the
function it is passed to needs nothing extra to accept it: [Effects and
handlers](effects.md#blocks-that-perform-effects) explains how. A callback that keeps state from
one call to the next is a handler with state ([Effects and handlers](effects.md)).
