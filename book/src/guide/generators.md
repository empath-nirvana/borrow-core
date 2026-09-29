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
