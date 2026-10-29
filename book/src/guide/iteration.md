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
- over a view, each of its elements is lent.

```bc
fn tab(i: i32) -> i32 = (i + 1) * 10

main -> i32 * (i32 * i32) =
  let a = array_new[i32](5, tab);
  let first = for x in &a { let v = *x; if v > 25 { break v } else { () } } else { 0 };
  let mut odd = 0;
  for i in 0..10 { if i % 2 == 0 { continue } else { () }; odd = odd + i };
  let mut sum = 0;
  for x in a { sum = sum + x };
  (first, (odd, sum))
-- answer: (i32[30], (i32[25], i32[150]))
```

- `break` leaves the loop, and `break v` leaves it with the loop's value `v`; `else { e }` after
  the loop gives the value when the source ends without a `break`.
- `continue` goes on to the next element.
- `return e` returns from the enclosing function.
- A `let mut` variable assigned in the body is carried from one turn to the next and is there
  after the loop.

## Loops that may not end

`while c { … }` and `loop { … }` may run forever, so a function containing one is *div*: it may
diverge. You never write this; it's inferred, and it spreads like any other effect, so a function
that calls a div function is div too. If you want a guarantee that a function terminates, mark it
`total` and the compiler checks it:

```bc
total fn sum_to(n: i32) -> i32 =
  let mut s = 0;
  for i in 0..n { s = s + i };
  s

main -> i32 = sum_to(10)
-- answer: i32[45]
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

`div_fuel` runs a div computation for a bounded number of steps, and code that does that is
total again ([Divergence](../elaboration/divergence.md) has the details).

A higher-order function written with a total callback in mind works with a div one too: the
compiler makes a copy of it for the div callback, and that copy is div. Functions don't come in
two colours.

## Generators

A generator is a function that yields a sequence of values and then returns. Yielding is an
ordinary effect, `Yield[T]`, from the library (`include yield`), with one operation,
`yield(x: T)`. A `for` over a call of such a function handles the effect: its body runs at each
`yield`, with the yielded value.

```bc
-- answer: i32[355]
include yield

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn squares(lo: i32, hi: i32) -> 1 with Yield[i32] =
  for x in range(lo, hi) { yield(x * x) };
  ()

main -> i32 =
  let mut acc = 0;
  for x in squares(1, 11) { if x > 20 { acc = acc + x } else { () } };
  acc
```

The `for` is a handler of `Yield` (see [Effects](effects.md)), and its body is the handler's
clause. Each `yield` compiles to a direct call of the body, so the program above allocates
nothing and makes no indirect call.

A `for` over a generator that loops is div; over one that doesn't, it's total. A `for` over data
whose body yields counts as a looping generator, so `squares` below is div:

```bc
-- answer: i32[30]
include yield

fn squares(n: i32) -> 1 with Yield[i32] =
  for i in 0..n { yield(i * i) };
  ()

main -> i32 =
  let mut acc = 0;
  for x in squares(5) { acc = acc + x };
  acc
```

The same loop over `&a` is rejected, because the lend of `a` would be held across a `yield`.

### Leaving early: `break` and `return`

`break` in a `for`'s body stops the generator, and anything the generator owns is dropped.
`return e` returns from the function around the loop. Inside a generator, `break` leaves the
innermost loop, and `return e` returns from the generator from any depth.

```bc
-- answer: i32[67]
include yield

fn below(n: i32, lim: i32) -> 1 with Yield[i32] =
  let mut i = 0;
  while true {
    let mut j = 0;
    while j < i {
      if i * j > lim { return } else { () };
      yield(j);
      j = j + 1
    };
    if i == n { break } else { () };
    i = i + 1
  };
  ()

fn first_above(k: i32) -> i32 =
  for x in below(10, 100) { if x > k { return x * 10 } else { () } };
  0

main -> i32 =
  let mut acc = 0;
  for x in below(10, 12) { if x > 2 { break } else { acc = acc + x } };
  acc + first_above(5)
```

### The value of a loop

A generator returns a value. `let r = for x in g(…) { … }; …` keeps it, or keeps `e` after a
`break e`:

```bc
-- answer: i32[70012]
include yield

fn upto(n: i32) -> i32 with Yield[i32] =
  let mut i = 0;
  while i < n { yield(i); i = i + 1 };
  n

main -> i32 =
  let mut acc = 0;
  let r = for x in upto(4) { acc = acc + x };
  let s = for x in upto(10) { if x == 7 { break 70000 } else { () } };
  acc + r + s + 2
```

### Calling a generator

A generator that calls another passes on whatever the callee yields, then carries on with what
it returns.

```bc
-- answer: i32[1256]
include yield

fn two() -> i32 with Yield[i32] =
  yield(1);
  yield(2);
  5

fn around() -> i32 with Yield[i32] =
  yield(0);
  let n = two();
  yield(n);
  n + 1

main -> i32 =
  let mut acc = 0;
  let r = for x in around() { acc = acc * 10 + x };
  acc * 10 + r
```

### Stored generators

Pass a generator call where a stored generator is expected, as in `take(10, fib())` below or
`let g: U (pull i32 0 1) = fib();`, and you get the generator as a value instead of running it.
In `U (pull A B R)`, `A` is what it yields, `B` what it returns when it finishes (`0` for one that
never does), and `R` what closing it early gives back, usually `1`.
Nothing runs until you ask for the next item; each request runs it to its next `yield`, and
closing it cancels the rest. A `for` over a stored generator pulls from it until it returns. This
is how you write adapters like `take`:

```bc
-- answer: i32[88]
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

main -> i32 =
  let mut acc = 0;
  for x in take(10, fib()) { acc = acc + x };
  acc
```

`include adapters` gives you the usual ones (`map`, `filter`, `take`, `skip`, `enumerate`,
`chain`, `flat_map`, `take_until`, `scan`, `zip`, `chunks`, `lines`, `batch`), all generic
generators over stored generators, so a pipeline is just calls:

```bc
-- answer: i32[320]
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn times(p: i32 * i32) -> i32 = let (i, x) = p; i * x
fn even(x: i32) -> bool = host[and32] (x, 1) == 0

main -> i32 =
  let mut acc = 0;
  for y in take(filter(map(enumerate(range(10, 1000)), times), even), 5) { acc = acc + y };
  acc
```

### Pipelines

`e |> f(a, …)` is `f(e, a, …)`: the value on the left becomes the first argument of the call on
the right, so a chain of adapters reads left to right.

```bc
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

main -> i32 =
  let mut b = 0;
  for y in range(0, 10) |> map(!{ x -> x * x }) |> filter(!{ x -> x > 5 }) |> take(3) {
    b = b + y
  };
  b
-- answer: i32[50]
```

`|>` into a handler is `with`: `e |> to_result` is `with to_result { e }`
([Effects and handlers](effects.md#computation-parameters-and-)).

Generators compile to state machines, and a simple `for` over a generator turns each `yield`
into a direct call of the loop body. None of the programs on this page allocate.

## Borrows and loops

A borrow block around a loop lends the place again at each step, at no run-time cost. What the
loop carries from one step to the next can't hold the borrow: an iterator that holds it is
rejected with a message that says so
([Divergence](../elaboration/divergence.md#borrows-around-a-loop)).

## Not yet

A generator can't yet hold a borrow, or a capability such as stdin or a handler's state, across
a `yield`; the body of the `for` can use them freely. The [Status](../status.md) page lists the
remaining gaps.
