# Iteration

There are three kinds of loop. A `for` over data (a range of integers, an array, a view) runs
once per element and always finishes. A `while` or `loop` may run forever. A `for` over a
generator runs its body at each value the generator yields. The compiler tells the first kind
from the other two, and that is how it knows which functions terminate.

## `for` over data

`for x in a..b` counts from `a` up to `b - 1`. A `for` over an array or a view visits its
elements, chosen by the source's type as Rust's `IntoIterator` chooses: an owned array's elements
are copied out and the array is dropped after the loop; `&a` lends each element `imm` and hands
the array back; a view lends each of its elements.

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

`while c { … }` and `loop { … }` may run forever, so a function with one is *div*: it may
diverge. Divergence is inferred, never written, and it is an effect like the others: a function
that calls a div function is div. Marking a function `total` asks the compiler to check that it
terminates:

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

A div computation can be run for a bounded number of
steps by `div_fuel`, and code that does so is total again ([Divergence](../elaboration/divergence.md)
has the details, and what a closed total program is proved to do).

A higher-order function written for a total callback serves a div one too: given a div function,
the compiler makes a copy of it at the callback's type, and the copy is div. So functions do not
come in two colors.

## Generators

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

A generator's `while` and `loop` are loops of a div body (see [Divergence](../elaboration/divergence.md)),
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

### Leaving early: `break` and `return`

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

### The value of a loop

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

### Calling a generator

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

### Stored generators

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

### Pipelines

`e |> f(a, …)` is `f(e, a, …)`: the value on the left is the first argument of the call on the
right, so a chain of adapters reads left to right. A generator's call piped into an adapter is
stored there, as above.

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

A `for` over a call of a generator whose body does nothing else compiles each `yield` to a direct
call of the loop's body, and a generator's loops are the kernel's `iterate`: the programs above
allocate nothing.

## Borrows and loops

A borrow lasts for one computation, and a loop runs one step at a time, so a borrow block around
a loop lends the place again at each step, at no run-time cost. What the loop carries from one
step to the next must not hold the borrow: an iterator that holds it is rejected with a message
that says so ([Divergence](../elaboration/divergence.md#borrows-around-a-loop)). Holding a
borrow across the turns of a generator (the *spanning lend*) is not provided (#172): a `for` over
`&a` whose body yields is rejected for that reason.

## Not yet

- A generator cannot use a capability (the input, the output, a handler's state) across a
  `yield`: `yield` may be cancelled, by `break` or by closing a stored generator, and a
  capability has no destructor to run then. A `for` over a generator that performs `Stdin`, say,
  is refused with a message saying so. The *body* of the `for` may use capabilities, and a block
  given to a function may yield to a `for` it is written inside (SPEC §32).
- The spanning lend: a borrow held across a generator's turns (#172), above.
- A `for` over the view of a borrow block written inline in some shapes (#501), a `for` that
  lends a variable inside an `if` arm (#502), and a recursive call inside a counted `for` that
  threads an array (#492) are refused; each issue has the shape and the workaround.
