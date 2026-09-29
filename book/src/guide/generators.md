# Generators

A generator is a function that yields a sequence of values and then finishes. `gen fn` declares
one: its result type is what it yields, and after a comma what it finishes with (`1` when left
out). Calling it runs nothing; each observation runs its body up to the next `yield`.

```bc
-- answer: i32[355]
gen fn range(lo: i32, hi: i32) -> i32 =
  let mut i = lo;
  while i < hi { yield i; i = i + 1 };
  ()

gen fn squares(it: U (gen i32 1 1)) -> i32 =
  for x in it { yield x * x };
  ()

gen fn above(n: i32, it: U (gen i32 1 1)) -> i32 =
  for x in it { if n < x { yield x } else { () } };
  ()

main -> i32 =
  let mut acc = 0;
  for x in above(20, squares(range(1, 11))) { acc = acc + x };
  acc
```

A generator is codata, `gen A B R = νX. F((A ⊗ U X) ⊕ (B ⊕ U X)) & F R` (SPEC §14): an
observation yields an `A` with the rest, finishes with `B`, or skips a step (a turn of a loop
that yielded nothing), and closing it early hands back `R`, what it holds that has no
destructor. Every observation terminates; a consumer decides how many to make. There is no new
type former: `gen` is an abbreviation over the core's one codata former.

## Leaving early: `break` and `return`

`break` leaves the innermost loop from anywhere in its body, and `return e` finishes the whole
generator with `e` from any depth of its loops. Each loop that is left closes its iterator.

```bc
-- answer: i32[13]
gen fn below(n: i32, lim: i32) -> i32 =
  let mut i = 0;
  while true {
    let mut j = 0;
    while j < i {
      if i * j > lim { return } else { () };
      yield j;
      j = j + 1
    };
    if i == n { break } else { () };
    i = i + 1
  };
  ()

main -> i32 =
  let mut acc = 0;
  for x in below(10, 12) { acc = acc + x };
  acc
```

`return` is a generator's: in `fn` and `main` bodies it is the core's `return`. `break` also
leaves a `for` in `main` or any other function.

## The value of a loop

A generator finishes with a value. `let r = for x in g { … }; …` keeps it, or, after
`break e`, keeps `e`:

```bc
-- answer: i32[1006]
gen fn upto(n: i32) -> i32, i32 =
  let mut i = 0;
  while i < n { yield i; i = i + 1 };
  n

gen fn firstbig(it: U (gen i32 i32 1), lim: i32) -> i32, i32 =
  let r = for x in it {
    if x > lim { break x } else { yield x }
  };
  r + 1000

main -> i32 =
  let s = for x in firstbig(upto(10), 5) { () };
  s
```

## Calling a loop from a generator

A generator may call a function that loops (a div function, see
[Divergence](divergence.md)) as it would call any other. The loop runs inside the generator, one
turn per observation, so every observation still terminates: a consumer that stops early stops
the loop too.

```bc
-- stdin: abc
-- stdin: de
-- answer: i32[32]
fn line_len(c: In) -> In * i32 =
  let mut n = 0;
  for b in bytes(&mut c) { if b == 10 { break } else { n = n + 1 } };
  (c, n)

gen fn lens(c: In, k: i32) -> i32, In =
  let mut i = 0;
  while i < k {
    let n = line_len(&mut c);
    yield n;
    i = i + 1
  };
  c

main -> i32 =
  let mut s = 0;
  for n in lens(&mut stdin, 2) { s = s * 10 + n };
  s
```

## Delegating: `yield from`

`yield from g` yields everything the generator `g` yields, and its value is what `g` finishes
with:

```bc
-- answer: i32[1256]
gen fn two() -> i32, i32 =
  yield 1;
  yield 2;
  5

gen fn around() -> i32, i32 =
  yield 0;
  let n = yield from two();
  yield n;
  n + 1

main -> i32 =
  let mut acc = 0;
  let r = for x in around() { acc = acc * 10 + x };
  acc * 10 + r
```

## Generators in place, and callbacks that yield

`gen { … }` is a generator written where it is used. It captures what it uses and runs nothing
until it is observed:

```bc
-- answer: i32[31]
main -> i32 =
  let k = 7;
  let mut acc = 0;
  for x in gen { yield 1; let mut i = 0; while i < 3 { yield k + i; i = i + 1 }; () } {
    acc = acc + x
  };
  acc + 6
```

A callback may yield. The function it is passed to was written for a callback that returns a
value; it is specialized into a generator (as it is specialized into a loop for a callback that
may diverge, see [Divergence](divergence.md)), and its call yields everything the callbacks
yield. No function is written twice:

```bc
-- answer: i32[1111]
fn twice(f: !(i32 => 1), x: i32) -> 1 =
  f(x);
  f(x + 1)

main -> i32 =
  let mut acc = 0;
  for x in gen { twice(!{ y -> yield y; yield y * 100 }, 5) } { acc = acc + x };
  acc
```
