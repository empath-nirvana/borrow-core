# Recipes

Short, complete programs for the things you usually try first in a new language. Each one runs
as it is: save it as a `.bc` file and run it with `bcc run`. The `-- stdin:` lines under a program
are the input it was run with, and the `-- output:` lines are what it printed.

## Sum the numbers on standard input

```bc
include textio

main -> 1 =
  let s = read_input();
  let sum = borrow imm s { t -> fold_i32s(t, !{ (x, acc) -> acc + x }, 0) };
  print_dec(sum);
  print_byte(b'\n')
-- stdin: 1 2
-- stdin: 3
-- stdin: -4 10
-- output: 12
```

`read_input()` reads all of standard input into a string, and `borrow imm s { t -> … }` lends it
as a text view `t`. `fold_i32s` walks every integer written in the text, in order, and folds it
into a running value: a run of digits is a number, a `-` just before it makes it negative, and
every other byte separates numbers, so spaces, newlines and commas all work. The closure
`!{ (x, acc) -> acc + x }` gets each number and the sum so far.

## Parse numbers and report bad input

```bc
include textio

data Tally = { line: i32, sum: i32, bad: Vec[i32] }

-- One more line: added to the sum if it is a number, its line number kept if not.
fn add_line<'a>(l: text 'a, t: Tally) -> Tally =
  match t {
    Tally { line, sum, bad } ->
      let line = line + 1;
      match with to_result { parse_i32(trim(l)) } {
        inl x -> Tally { line, sum: sum + x, bad }
      | inr e -> push(&mut bad, line); Tally { line, sum, bad }
      }
  }

fn report<'a>(bad: array_imm 'a i32) -> 1 =
  for n in bad { print_lit("line "); print_dec(*n); print_lit(" is not a number\n") }

main -> 1 =
  let s = read_input();
  let start = Tally { line: 0, sum: 0, bad: box buf[i32](0) };
  let t = borrow imm s { v -> fold_lines(v, !{ (l, t) -> add_line(l, t) }, start) };
  match t {
    Tally { line, sum, bad } ->
      borrow imm bad { v -> report(v) };
      print_lit("sum ");
      print_dec(sum);
      print_byte(b'\n')
  }
-- stdin:  12
-- stdin: four
-- stdin: 30
-- stdin: 3x
-- output: line 2 is not a number
-- output: line 4 is not a number
-- output: sum 42
```

`parse_i32` raises a `ParseError` when the text isn't a number, and `with to_result { … }` turns
that into a value: `inl` the number, or `inr` the error ([Errors](guide/errors.md)). `fold_lines`
hands each line to `add_line` with the state so far, a `Tally` record that counts lines, keeps the
sum and collects the numbers of the bad lines in a `Vec`. `match t { Tally { line, sum, bad } -> … }`
takes a record apart into variables named after its fields, and `Tally { line, sum, bad }` builds
one back from variables of the same names. The report is printed once the fold has finished.

## Count things with a map

```bc
include textio
include map

-- One more sighting of `x`.
fn seen(x: i32, counts: Map[i32, i32]) -> Map[i32, i32] =
  let mut counts = counts;
  let old = map_lookup(&counts, x);
  let n = match old { Some(n) -> n + 1 | None -> 1 };
  map_insert(&mut counts, x, n);
  counts

main -> 1 =
  let s = read_input();
  let counts = borrow imm s { t -> fold_i32s(t, !{ (x, m) -> seen(x, m) }, map_new[i32, i32](16)) };
  let mut best = 0;
  let mut most = 0;
  borrow imm counts { 'x, r ->
    for e in map_iter(r) { let (x, v) = e; let n = *v; if n > most { best = x; most = n } } };
  let distinct = map_len(&counts);
  print_dec(distinct);
  print_lit(" different numbers; ");
  print_dec(best);
  print_lit(" appears most, ");
  print_dec(most);
  print_lit(" times\n")
-- stdin: 3 1 4 1 5 9 2 6 5 3 5
-- output: 7 different numbers; 5 appears most, 3 times
```

`map_lookup` answers a copy of the count stored for a key, as an `Option`, and `map_insert` stores
the new one; both take the map lent, `&counts` to read it and `&mut counts` to change it. To visit
every entry, `borrow imm counts { 'x, r -> … }` lends the map and `map_iter(r)` yields each key
with a view of its value, read with `*v`. The iteration order comes from the hash, and it's the
same on every run. [Maps and sets](guide/data.md#maps-and-sets) lists the rest of the map's
operations.

## Build a string

```bc
include textio

-- `[a, b, c]`, written into a new string.
fn show_list<'a>(v: array_imm 'a i32) -> string =
  let mut s = box string(32);
  push_char(&mut s, '[');
  let mut first = true;
  for p in v {
    if not(first) { push_lit(&mut s, ", ") };
    push_dec(&mut s, *p);
    first = false
  };
  push_char(&mut s, ']');
  s

fn square(i: i32) -> i32 = (i + 1) * (i + 1)

main -> 1 =
  let a = array_new[i32](5, square);
  let s = borrow imm a { v -> show_list(v) };
  let n = len_of(&s);
  let s = print_string(s);
  print_lit(" (");
  print_dec(n);
  print_lit(" bytes)\n")
-- output: [1, 4, 9, 16, 25] (17 bytes)
```

`box string(32)` allocates an empty string with room for 32 bytes; it grows when it needs to.
`push_char`, `push_lit` and `push_dec` append a character, a literal and a number. The function
hands the finished string back to its caller, which owns it from then on. `print_string(s)`
prints it and hands it back, and the string is freed when `main` ends.

## Read the command-line arguments

```bc
include textio

-- Greets each name given on the command line, or the world if none is.
main -> 1 =
  let mut n = 0;
  let mut more = true;
  while more {
    let (name, got) = next_arg(box string(16));
    if got {
      n = n + 1;
      print_lit("Hello, ");
      let name = print_string(name);
      print_lit("!\n")
    } else { more = false }
  };
  if n == 0 { print_lit("Hello, world!\n") }
-- output: Hello, world!
```

`next_arg` appends the next argument to the string it's given, and answers it with whether there
was one. The arguments come after the file name:

```text
$ bcc run hello.bc Ada Grace
Hello, Ada!
Hello, Grace!
()
live 0
```

In the interpreter they come after `--`: `bcc interp hello.bc -- Ada Grace`.

## Update a record's `Vec` through `&mut`

```bc
include textio

data Scores = { best: i32, history: Vec[i32] }

-- Records one score: appended to `history`, and kept as `best` if it is the highest yet.
fn record<'a>(s: mut 'a Scores, x: i32) -> 1 =
  modify s { sc ->
    match sc {
      Scores { best, history } ->
        push(&mut history, x);
        let best = if x > best { x } else { best };
        Scores { best, history }
    } }

fn print_all<'a>(v: array_imm 'a i32) -> 1 =
  for p in v { print_byte(b' '); print_dec(*p) }

main -> 1 =
  let mut s = Scores { best: 0, history: box buf[i32](4) };
  record(&mut s, 12);
  record(&mut s, 40);
  record(&mut s, 27);
  let best = s.best;
  print_lit("best ");
  print_dec(best);
  print_lit(", history:");
  match s { Scores { best, history } -> borrow imm history { v -> print_all(v) } };
  print_byte(b'\n')
-- output: best 40, history: 12 40 27
```

`record` gets the scores lent `mut` and changes them in place. `modify s { sc -> … }` takes the
record out of the borrow, and the record the block ends with is put back: here the same `Vec`
with one more element pushed, and the new best. A copyable field is read directly, as in
`let best = s.best;`. To read the `Vec`, `main` takes the record apart and lends the vector to
`print_all` as a view.

## A recursive function over a tree

```bc
include textio
include rec

fn max(a: i32, b: i32) -> i32 = if a > b { a } else { b }

data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)

-- `t` with `x` added, smaller values to the left.
fn insert(t: Tree, x: i32) -> Tree =
  match t {
    Leaf -> box Node(Leaf, x, Leaf)
  | box Node(l, v, r) ->
      if x < v { box Node(insert(l, x), v, r) } else { box Node(l, v, insert(r, x)) }
  }

-- The height, read through a borrow.
fn height<'a>(t: imm 'a Tree) -> i32 =
  fold_imm t { Leaf -> 0 | Node(l, v, r) -> 1 + max(l, r) }

-- Prints the values in order, consuming the tree.
fn print_sorted(t: Tree) -> 1 =
  match t {
    Leaf -> ()
  | box Node(l, v, r) -> print_sorted(l); print_byte(b' '); print_dec(v); print_sorted(r)
  }

fn build(xs: array i32) -> Tree =
  let mut t = Leaf;
  for x in xs { t = insert(t, x) };
  t

main -> 1 =
  let t = with on_exhausted(!{ u -> Leaf }) { build(array_new[i32](7, !{ i -> (i * 5) % 7 })) };
  let h = height(&t);
  print_lit("height ");
  print_dec(h);
  print_lit(", sorted:");
  with on_exhausted(!{ u -> () }) { print_sorted(t) };
  print_byte(b'\n')
-- output: height 5, sorted: 0 1 2 3 4 5 6
```

A binary search tree, built by inserting the values one at a time. `insert` takes the tree and
gives back a new one: the pattern `box Node(l, v, r)` frees the old node, and `box Node(…)`
allocates its replacement. `height` only reads the tree, so it takes a borrow and uses
`fold_imm`, which hands each node its subtrees' heights. `print_sorted` consumes the tree as it
prints it, so nothing is left to free. A function that calls itself needs a handler for running
out of depth; `on_exhausted` gives the value to use if it does
([Recursion](guide/data.md#recursion)).

## A tree whose children are a `Vec`

```bc
include textio
include rec

-- A directory: the bytes of its own files, and its subdirectories.
data Dir = Dir(size: i32, subdirs: Vec[Dir])

fn files(n: i32) -> Dir = Dir(n, box buf[Dir](0))

fn with_sub(d: Dir, sub: Dir) -> Dir =
  match d { Dir(n, subs) -> push(&mut subs, sub); Dir(n, subs) }

-- The size of `d` and everything under it, and the number of directories; consumes `d`.
fn du(d: Dir) -> i32 * i32 =
  match d {
    Dir(size, subs) ->
      let mut bytes = size;
      let mut dirs = 1;
      let n = len_of(&subs);
      for i in 0..n {
        match pop(&mut subs) {
          Some(sub) -> let (b, k) = du(sub); bytes = bytes + b; dirs = dirs + k
        | None -> ()
        }
      };
      (bytes, dirs)
  }

main -> 1 =
  let src = with_sub(with_sub(files(120), files(300)), files(45));
  let root = with_sub(with_sub(files(10), src), files(2048));
  let (bytes, dirs) = with on_exhausted(!{ u -> (0, 0) }) { du(root) };
  print_dec(bytes);
  print_lit(" bytes in ");
  print_dec(dirs);
  print_lit(" directories\n")
-- output: 2523 bytes in 5 directories
```

Each directory holds its subdirectories in a `Vec[Dir]`; the vector's storage is on the heap
already, so no `box` is needed. `du` takes a directory apart, pops each subdirectory off its
vector, adds up what the recursive call returns, and answers a pair: the bytes and the number of
directories. Each directory is freed once it has been counted.

## Test I/O with a fake handler

```bc
include textio

-- The code under test: it writes to whatever serves `Stdout`.
fn fizzbuzz(n: i32) -> 1 with Stdout =
  for i in 1..n + 1 {
    if i % 15 == 0 { print_lit("FizzBuzz") }
    else if i % 3 == 0 { print_lit("Fizz") }
    else if i % 5 == 0 { print_lit("Buzz") }
    else { print_dec(i) };
    print_byte(b' ')
  }

-- A fake standard output that keeps what is written.
handler collect(mut out: string): Stdout = {
  print_byte(b) = { push_byte(&mut out, b) };
  print_bytes(v) = { push_str(&mut out, v) }
}

-- Runs `fizzbuzz(n)` with its output captured, and compares it with `want`.
fn check(name: lit, n: i32, want: lit) -> 1 =
  let c = alloc(box string(64));
  with collect(&mut c) { fizzbuzz(n) };
  let got = free(c);
  let ok = borrow imm got { t -> eq_lit(t, want) };
  if ok { print_lit("ok   ") } else { print_lit("FAIL ") };
  print_lit(name);
  print_byte(b'\n')

main -> 1 =
  check("first five", 5, "1 2 Fizz 4 Buzz ");
  check("fifteen", 15, "1 2 Fizz 4 Buzz Fizz 7 8 Fizz Buzz 11 Fizz 13 14 FizzBuzz ")
-- output: ok   first five
-- output: ok   fifteen
```

`fizzbuzz` writes to `Stdout`, and its signature says so. In a test, `with collect(&mut c) { … }`
serves `Stdout` with a handler that appends each byte to a string, instead of the real standard
output; `fizzbuzz` itself doesn't change. Afterwards the cell `c` holds everything that was
written, and `eq_lit` compares it with the expected text. A string literal's type is `lit`, which
is how `check` takes the name and the expected output. A fake clock or scripted input is written
the same way ([Serving an effect yourself](guide/io.md#serving-an-effect-yourself)).

## Time something

```bc,check
include textio

fn collatz(n: i32) -> i32 =
  let mut x = n;
  let mut steps = 0;
  while x != 1 {
    if x % 2 == 0 { x = x / 2 } else { x = 3 * x + 1 };
    steps = steps + 1
  };
  steps

-- The number below `n` with the longest Collatz run.
fn longest(n: i32) -> i32 =
  let mut best = 1;
  let mut most = 0;
  let mut i = 1;
  while i < n {
    let s = collatz(i);
    if s > most { best = i; most = s };
    i = i + 1
  };
  best

main -> 1 =
  let t0 = now();
  let x = longest(100000);
  let t1 = now();
  print_dec(x);
  print_lit(" has the longest run; that took ");
  print_dec64((t1 - t0) / 1000000);
  print_lit(" ms\n")
```

```text
$ bcc run --native collatz.bc
77031 has the longest run; that took 16 ms
()
live 0
```

`now()` is a monotonic clock in nanoseconds, as an `i64`, so the difference of two readings is
the time between them, and dividing by 1000000 gives milliseconds. `print_dec64` prints an `i64`.
The time you see will differ from run to run.

## A generator pipeline

```bc
include textio
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

-- Whether `n` is prime, trying the divisors up to its square root.
fn is_prime(n: i32) -> bool =
  let mut ok = true;
  for d in 2..n {
    if d * d > n { break };
    match checked_rem(n, d) { inl r -> if r == 0 { ok = false; break } | inr e -> () }
  };
  ok

fn print_all<'a>(v: array_imm 'a i32) -> 1 =
  for p in v { print_byte(b' '); print_dec(*p) }

main -> 1 =
  let mut found: Vec[i32] = box buf[i32](8);
  for x in range(2, 1000) |> filter(is_prime) |> map(!{ p -> p * p }) |> take(6) {
    push(&mut found, x)
  };
  print_lit("squares of the first six primes:");
  borrow imm found { v -> print_all(v) };
  print_byte(b'\n')
-- output: squares of the first six primes: 4 9 25 49 121 169
```

`range` is a generator: it yields each number in turn ([Generators](guide/iteration.md#generators)).
`|>` passes the value on its left as the first argument of the call on its right, so the pipeline
reads in order: the numbers from 2, the primes among them, their squares, the first six. Nothing
is computed ahead: `take(6)` stops the pipeline after the sixth value, so `range` never gets near
1000. The loop collects the values in a `Vec`, and they're printed after it.
`is_prime` uses `checked_rem`, which answers the remainder as a sum instead of raising on a zero
divisor, so it's a plain function that `filter` can take.
