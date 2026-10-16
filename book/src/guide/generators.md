# Generators

A generator is a function that yields a sequence of values, then returns. Yielding is an
ordinary effect, `Yield[T]`, declared in the library (`include yield`) with one operation,
`yield(x: T)`, and a function that performs it says so in its row. A `for` over a call of such a
function handles the effect: its body runs at each `yield`, with the yielded value.

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

The `for` is a handler of `Yield` with a static name of its own (see [Effects](effects.md)):
the loop's variables travel through the operation, so the body is the handler's clause, and it
resumes the generator at its end. When the body does nothing else, each `yield` compiles to a
direct call of the body: the program above allocates nothing and dispatches no call.

A generator's `while` and `loop` are loops of a div body (see [Divergence](divergence.md)),
whose every turn may yield: one turn per observation, so every observation terminates. A `for`
over a generator that loops is div; over one that does not, it is total.

A `for` over data whose body yields is such a loop too: a counted loop's step is one total
computation, which cannot hold the generator's continuation, so the loop goes over the source's
cursor one turn per element, and it is div:

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

Over `&a` it is rejected: the lend of `a` would be held across a `yield` (#172).

## Leaving early: `break` and `return`

`break` in a `for`'s body stops the generator: what it holds is finalised, its owned values
dropped, as a cancelled continuation's are. `return e` returns from the function around the
loop. Inside a generator, `break` leaves its innermost loop, and `return e` returns from the
generator with `e` from any depth of its loops.

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

## The value of a loop

A generator returns a value. `let r = for x in g(…) { … }; …` keeps it, or, after `break e`,
keeps `e`:

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

## Calling a generator

A generator that calls another passes on what it yields, and goes on with what it returns: the
callee's `yield` reaches the handler the caller's reaches. A call of a function that loops runs
its loop inside the generator, one turn per observation.

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

## Stored generators

A call of a generator where a value of type `U (pull A B R)` is expected (an argument at a
parameter of that type, or a binding with that type written) is the generator stored: its
handler keeps the continuation instead of resuming it. Nothing runs until it is observed, each
observation runs it to its next `yield`, and closing it cancels the rest. It is codata,
`pull A B R = νX. F((A ⊗ U X) ⊕ (B ⊕ U X)) & F R`: an observation gives an `A` with the rest,
returns `B`, or skips a turn that yielded nothing. A `for` over a stored generator observes it
until it returns.

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

The adapters of `include adapters` (`map`, `filter`, `take`, `skip`, `enumerate`, `chain`,
`flat_map`, `take_until`, `scan`, `zip`, `chunks`, `lines`, `batch`) are generic generators over
stored generators, so a pipeline is written as calls:

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

## What a generator cannot do yet

`yield` may be cancelled (`break`, or closing a stored generator), and what a generator holds
across it is then dropped. A capability, such as the input or the output, has no destructor and
must be handed back, so a generator cannot hold one across a `yield`: a generator over the input
is not provided yet. A body of a loop may use them; the loop's variables are passed through the
operation. A block that yields to the `for` over its generator would be passed those variables
and hand them back at each call, which is not built yet (SPEC §29 *Open*).
