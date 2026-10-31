# Iteration

There are three kinds of loop. A `for` over data (a range of integers, an array, a view) runs
once per element and always finishes. A `while` or `loop` may run forever. A `for` over a
generator runs its body once for each value the generator yields. The compiler tells the first
kind apart from the other two, and that's how it knows which functions terminate.

## `for` over data

`for x in a..b` counts from `a` up to `b - 1`. A `for` over an array or a view visits its
elements, and the source's type decides how, much like Rust's `IntoIterator`:

- over an owned array, the elements are copied out and the array is dropped after the loop;
- over `&a`, each element is lent `imm` and you keep the array;
- over `&mut a`, each element is lent `mut`, so the loop can change it in place;
- over a view, each of its elements is lent.

```bc
include textio

fn tab(i: i32) -> i32 = (i + 1) * 10

main -> 1 =
  let mut a = array_new[i32](5, tab);
  let first = for x in &a { let v = *x; if v > 25 { break v } } else { 0 };
  let mut odd = 0;
  for i in 0..10 { if i % 2 == 0 { continue }; odd = odd + i };
  for p in &mut a { modify p { v -> v + 1 } };
  let mut sum = 0;
  for x in a { sum = sum + x };
  print_dec(first);
  print_byte(b' ');
  print_dec(odd);
  print_byte(b' ');
  print_dec(sum);
  print_byte(b'\n')
-- output: 30 25 155
```

- `break` leaves the loop, and `break v` leaves it with the loop's value `v`; `else { e }` after
  the loop gives the value when the source ends without a `break`.
- `continue` goes on to the next element.
- `return e` returns from the enclosing function.
- A `let mut` variable assigned in the body is carried from one turn to the next and is there
  after the loop.

Over an array of records lent `&mut`, a field is assigned directly:
`for p in &mut particles { p.x = p.x + p.v }`.

## Loops that may not end

`while c { … }` and `loop { … }` may run forever, so a function containing one is *div*: it may
diverge. You never write this; it's inferred, and it spreads like any other effect, so a function
that calls a div function is div too. If you want a guarantee that a function terminates, mark it
`total` and the compiler checks it:

```bc
include textio

total fn sum_to(n: i32) -> i32 =
  let mut s = 0;
  for i in 0..n { s = s + i };
  s

main -> 1 =
  print_dec(sum_to(10));
  print_byte(b'\n')
-- output: 45
```

A `total fn` with a `while` is rejected:

```bc,reject
total fn spin(n: i32) -> i32 =
  let mut i = 0;
  while i < n { i = i + 1 };
  i

main -> i32 = spin(3)
-- expect: 3:3: `spin` is declared `total`, but it has a `while` (SPEC §14)
```

`div_fuel(e, n)` runs a div computation for at most `n` steps: it answers `inl` the value if `e`
finished in time, and `inr ()` if not. Code that runs a loop this way is total again. Nobody knows
whether the Collatz loop always reaches 1, so `collatz` is div, but a bounded run of it is total:

```bc
include textio

fn collatz(n: i32) -> i32 =
  let mut x = n;
  let mut steps = 0;
  while x != 1 {
    if x % 2 == 0 { x = x / 2 } else { x = 3 * x + 1 };
    steps = steps + 1
  };
  steps

total fn collatz_within(n: i32, fuel: i32) -> Option[i32] =
  match div_fuel(collatz(n), fuel) { inl s -> Some(s) | inr u -> None }

fn show(r: Option[i32]) -> 1 =
  match r { Some(s) -> print_dec(s) | None -> print_lit("gave up") };
  print_byte(b'\n')

main -> 1 =
  show(collatz_within(27, 200));
  show(collatz_within(27, 50))
-- output: 111
-- output: gave up
```

A higher-order function written with a total callback in mind works with a div one too: the
compiler makes a copy of it for the div callback, and that copy is div. Functions don't come in
two colours.

## Generators

A generator is a function that yields a sequence of values and then returns. Yielding is an
ordinary effect, `Yield[T]`, from the library (`include yield`), with one operation,
`yield(x: T)`. A `for` over a call of such a function handles the effect: its body runs at each
`yield`, with the yielded value. `for x in lo..hi` is a counted loop rather than a generator, so
the examples below write a small `range` generator where they need one.

```bc
include textio
include yield

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn squares(lo: i32, hi: i32) -> 1 with Yield[i32] =
  for x in range(lo, hi) { yield(x * x) };
  ()

main -> 1 =
  for x in squares(1, 5) { print_dec(x); print_byte(b'\n') }
-- output: 1
-- output: 4
-- output: 9
-- output: 16
```

The `for` is a handler of `Yield` (see [Effects](effects.md)), and its body is the handler's
clause: each `yield` is a direct call of the body, so the program allocates nothing.

A `for` over a generator that loops is div; over one that doesn't, it's total. A `for` over data
whose body yields counts as a looping generator, so `squares` is div.

### Leaving early: `break` and `return`

`break` in a `for`'s body stops the generator, and anything the generator owns is dropped.
`return e` returns from the function around the loop. Inside a generator, `break` leaves the
innermost loop, and `return` ends the generator from any depth.

```bc
include textio
include yield

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

-- The first square above `k`.
fn first_square_above(k: i32) -> i32 =
  for x in range(1, 100) { if x * x > k { return x * x } };
  0

main -> 1 =
  let mut acc = 0;
  for x in range(1, 100) { if x > 4 { break }; acc = acc + x };
  print_dec(acc);
  print_byte(b' ');
  print_dec(first_square_above(50));
  print_byte(b'\n')
-- output: 10 64
```

### The value of a loop

A generator returns a value, and `let r = for x in g(…) { … };` keeps it, or keeps `e` after a
`break e`:

```bc
include textio
include yield

-- Yields the decimal digits of `n`, last first, and returns how many there were.
fn digits(n: i32) -> i32 with Yield[i32] =
  let mut x = n;
  let mut k = 0;
  while x > 0 { yield(x % 10); x = x / 10; k = k + 1 };
  k

main -> 1 =
  let k = for d in digits(4096) { print_dec(d) };
  print_lit(" has ");
  print_dec(k);
  print_lit(" digits\n")
-- output: 6904 has 4 digits
```

A generator that calls another passes on whatever the callee yields, then carries on with what it
returns: `let n = digits(x); yield(n)` inside a generator yields the digits and then their count.

### Stored generators

Pass a generator call where a stored generator is expected, as in `take(10, fib())` below or
`let g: U (pull i32 0 1) = fib();`, and you get the generator as a value instead of running it.
In `U (pull A B R)`, `A` is what it yields, `B` what it returns when it finishes (`0` for one that
never does), and `R` what closing it early gives back, usually `1`.
Nothing runs until you ask for the next item; each request runs it to its next `yield`, and
closing it cancels the rest. A `for` over a stored generator pulls from it until it returns. This
is how you write adapters like `take`:

```bc
include textio
include yield

fn fib() -> 0 with Yield[i32] =
  let mut a = 0;
  let mut b = 1;
  loop {
    yield(a);
    let c = a + b;
    a = b;
    b = c
  }

fn take(n: i32, it: U (pull i32 0 1)) -> 1 with Yield[i32] =
  let mut i = 0;
  for x in it {
    if i < n { yield(x); i = i + 1 } else { break }
  };
  ()

main -> 1 =
  for x in take(6, fib()) { print_dec(x); print_byte(b'\n') }
-- output: 0
-- output: 1
-- output: 1
-- output: 2
-- output: 3
-- output: 5
```

`include adapters` gives you the usual ones (`map`, `filter`, `take`, `skip`, `enumerate`,
`chain`, `flat_map`, `take_until`, `scan`, `zip`, `chunks`, `lines`, `batch`), all generic
generators over stored generators, so a pipeline is just calls:

```bc
include textio
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn times(p: i32 * i32) -> i32 = let (i, x) = p; i * x
fn even(x: i32) -> bool = x % 2 == 0

main -> 1 =
  let mut acc = 0;
  for y in take(filter(map(enumerate(range(10, 1000)), times), even), 5) { acc = acc + y };
  print_dec(acc);
  print_byte(b'\n')
-- output: 320
```

### Pipelines

`e |> f(a, …)` is `f(e, a, …)`: the value on the left becomes the first argument of the call on
the right, so a chain of adapters reads left to right. The adapters are listed in
[adapters](../stdlib.md#adapters).

```bc
include textio
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

main -> 1 =
  let mut b = 0;
  for y in range(0, 10) |> map(!{ x -> x * x }) |> filter(!{ x -> x > 5 }) |> take(3) {
    b = b + y
  };
  print_dec(b);
  print_byte(b'\n')
-- output: 50
```

`|>` into a handler is `with`: `e |> to_result` is `with to_result { e }`
([Effects and handlers](effects.md#computation-parameters-and-)).

## Borrows and loops

A borrow block around a loop is free: the loop body can use the borrow at every step. What the
loop carries from one step to the next can't hold the borrow, though, so a generator that takes
the borrow as an argument can't run in a `for` inside the block; the checker says which iterator
holds it. This is the language's rule, not a gap to be filled: what crosses a step or a `yield`
is owned, and borrows live within one step. Give the generator the data it owns (a literal is
persistent, so it can simply be passed), have it hand the data back when it finishes, or iterate
by index with a counted `for`.
