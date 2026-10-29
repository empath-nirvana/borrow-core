# Errors

An error is raised with `raise(e)` and handled with `with h { … }` around the code that may raise
it. There is one model: no `Result` type threaded by hand, no `?`, no exceptions separate from
the rest of the language. `raise` is an operation of an ordinary effect, `Fail[E]`, and its
handlers are ordinary handlers ([Effects and handlers](effects.md) has the general mechanism).

## Raising and handling

`include fail` declares the effect and three handlers:

| handler | answers |
|---|---|
| `with to_result { e }` | `inl` the value of `e`, or `inr` the error |
| `with default(d) { e }` | the value of `e`, or `d` |
| `with map_err(f) { e }` | the value of `e`; an error `x` is raised again as `f(x)`, to the handler around it |

A function that raises says so after its result type, `with Fail[E]`, and a function that calls
one that raises raises too, with nothing written: its *row*, the effects it may perform, is
inferred. A call of a function that raises needs no `?`: the error goes on by itself to the
nearest handler.

```bc
include textio
include fail

-- The sum of the elements; a negative one raises its index.
fn checked<'a>(v: array_imm 'a i32) -> i32 with Fail[i32] =
  let mut s = 0;
  let mut i = 0;
  for p in v { let x = *p; if x < 0 { raise(i) }; s = s + x; i = i + 1 };
  s

-- A function that calls one that raises raises too: its row is inferred.
fn twice<'a>(v: array_imm 'a i32) -> i32 = checked(v) * 2

fn report(r: i32 + i32) -> 1 =
  match r {
    inl n -> print_lit("sum "); print_dec(n)
  | inr i -> print_lit("negative at "); print_dec(i)
  };
  print_byte(b'\n')

fn good(i: i32) -> i32 = i * 10
fn bad(i: i32) -> i32 = if i == 2 { 0 - 1 } else { i }

main -> 1 =
  let a = array_new[i32](3, good);
  let b = array_new[i32](3, bad);
  let x = borrow imm a { v -> with to_result { twice(v) } };
  let y = borrow imm b { v -> with to_result { twice(v) } };
  let z = borrow imm b { v -> with default(0) { twice(v) } };
  report(x);
  report(y);
  print_dec(z);
  print_byte(b'\n')
-- output: sum 60
-- output: negative at 2
-- output: 0
```

A `raise` that no handler can reach is a compile-time error naming the function that performs it
(`` `f` performs `Fail`, but no handler of `Fail` is in scope here ``): an error never escapes
`main` unnoticed. The one exception is division, below.

If you do write the row, the compiler holds you to it: performing an effect the row leaves out
is an error. A row may also give the error's type where nothing else does.

## What an error abandons

An error unwinds: what the abandoned code owned is freed by its destructors, and every borrow it
was inside ends, the place going back to its owner. Here the cell that `checked` holds when it
raises is freed by the unwind, and the run ends with nothing live:

```bc
include textio
include fail

-- Holds a cell while it checks `x`; an error abandons the cell.
fn checked(x: i32) -> i32 with Fail[i32] =
  let c = alloc(x * 10);
  if x < 0 { raise(x) };
  free(c)

main -> 1 =
  print_dec(with default(0) { checked(4) });
  print_byte(b' ');
  print_dec(with default(0) { checked(0 - 3) });
  print_byte(b'\n')
-- output: 40 0
```

A value with no destructor (a capability, a one-shot closure that must be called) can't be live
where an error may leave, and the checker names it. An error's payload is plain data, borrows or
`!` values.

The handler of `Fail` is a handler like any other, so it can be written for a purpose. `to_result`
itself is

```bc,ignore
effect Fail[E] { ctl raise(e: E) -> never }

handler to_result[E, A]: Fail[E], A -> A + E = {
  return(a) = inl a;
  raise(e) = inr e
}
```

`ctl raise(e: E) -> never` declares an operation that never returns to its caller (it answers
the empty type `never`), so the handler's clause receives only the error.

## Errors of several types

A function may raise errors of several types: `Fail[i32]` and `Fail[ParseError]` are two
*instances* of `Fail`, each handled by the innermost handler of its own instance, whatever the
order of the handlers. The library's parsers raise their own error types: `parse_i32` raises a
`ParseError` (`include text`), which says why the text isn't a number: `inl ()` when it has no
digits, `inr (inl b)` for a byte `b` that isn't a digit, and `inr (inr ())` for a number too large
for an `i32`.

```bc
include textio

-- The two numbers of `"a b"`, added.
fn parse_sum<'t>(t: text 't) -> i32 with Fail[ParseError] =
  match split_once(t, b' ') {
    inl (a, b) -> parse_i32(a) + parse_i32(b)
  | inr t -> parse_i32(t)
  }

fn show(s: string) -> 1 =
  let r = borrow imm s { t -> with to_result { parse_sum(t) } };
  match r {
    inl n -> print_dec(n)
  | inr (inl u) -> print_lit("no digits")
  | inr (inr (inl b)) -> print_lit("not a digit: "); print_byte(b)
  | inr (inr (inr u)) -> print_lit("too large")
  };
  print_byte(b'\n')

main -> 1 =
  show(string_of_lit("12 30"));
  show(string_of_lit("12 x7"))
-- output: 42
-- output: not a digit: x
```

[Several instances, and names](effects.md#several-instances-and-names) shows two instances in one
row, and two handlers of one instance told apart by name.

## Division

`a / b` and `a % b` at `i32`, `i64` and `u8` truncate toward zero, the remainder taking the
dividend's sign.

Dividing by zero, or `MIN / -1` at a signed width, raises `Fail[DivError]`. Its two values are
`div_by_zero` and `div_overflow`. It's an ordinary `Fail`, so `to_result`, `default` and
`map_err` handle it, and a function can raise its own `Fail[E]` and divide too. Dividing by a
nonzero literal can't fail and needs no handler. `checked_div` and `checked_rem` return an
`Option`-like sum instead, and `div_euclid` and `rem_euclid` are the Euclidean forms.

```bc
include textio

fn mean(sum: i32, n: i32) -> i32 = sum / n

main -> 1 =
  print_dec(with default(0) { mean(7, 0) });
  print_byte(b' ');
  match with to_result { mean(9, 3) } {
    inl m -> print_dec(m)
  | inr e -> print_lit("no mean")
  };
  print_byte(b' ');
  print_dec((0 - 7) / 2);
  print_byte(b'\n')
-- output: 0 3 -3
```

A division error that reaches `main` unhandled is not a compile-time error, so that arithmetic
reads as it does elsewhere: the program unwinds, writes `error: division by zero` on standard
error, and exits with status 1, after freeing what it held.

```bc,check
main -> i32 = let n = 0; 10 / n
```
