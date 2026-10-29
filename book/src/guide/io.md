# Input and output

Standard input, standard output, standard error, the clock and the command-line arguments are
each an effect, and their operations are called like ordinary functions. `main` gets them for
free. Any other function gets them from its caller, and its row (the list of effects it
performs) says which ones it uses. You usually don't write the row, since it's inferred, but you
can (`with Stdout`).

That gives you two things. A function's signature tells you what it can touch. And a test can
serve the same effect with a handler of its own, say a fake stdout that collects into a string.

## The effects

`lib/sys.bc` declares the system interface:

| effect | operations |
|---|---|
| `Stdout` | `print_byte(b: u8)`, `print_bytes(v: array_imm 'b u8)` |
| `Stderr` | `eprint_byte(b: u8)`, `eprint_bytes(v: array_imm 'b u8)` |
| `Stdin` | `input_byte() -> u8 + 1` (`inr ()` at the end), `input_into(v: array_mut 'b u8) -> array_mut 'b u8 * i32` |
| `Clock` | `now() -> i64` (nanoseconds, monotonic), `sleep(ns: i64)` |
| `Args` | `arg_byte() -> u8 + 1`: the arguments' bytes, each argument followed by `0` |

The operations work on bytes and byte views, one system call each. Text and numbers are library
code on top: `include io` (`lib/io.bc`) adds `print_dec`, `eprint_dec`, `print_dec64` and `ns_of_ms`,
and `include textio` (`lib/textio.bc`) adds `print_lit("…")`, `print_str(t)`, `print_string(s)`
(which hands the string back), `eprint_lit`, `read_input()` (the whole input as a string) and
`next_arg(s)` (the next argument appended to a string, and whether there was one).

```bc
include textio

main -> 1 = print_lit("Hello, world!\n")
-- output: Hello, world!
-- answer: ()
```

## `main` holds the capabilities

In `main`, any of these operations that no `with` handles goes to the platform: the WASI handlers
in `lib/wasi.bc`, which call the host's `fd_write`, `fd_read`, `clock_time_get` and `args_get`.
Every other function just performs its effects, and whoever calls it provides them. This one can
write to standard output and nothing else:

```bc
include textio

-- A report, written to whatever serves `Stdout`.
fn report(lines: i32, bytes: i32) -> 1 with Stdout =
  print_lit("lines ");
  print_dec(lines);
  print_lit(", bytes ");
  print_dec(bytes);
  print_byte(b'\n')

main -> i32 =
  let s = read_input();
  let r = borrow imm s { 'a, t ->
    let (t, u) = array_copy['a, u8] t;
    (fold_lines(t, !{ (l, n) -> n + 1 }, 0), len(u)) };
  let (lines, bytes) = r;
  report(lines, bytes);
  lines
-- stdin: one
-- stdin: two
-- stdin: three
-- output: lines 3, bytes 14
-- answer: i32[3]
```

`with Stdout` is optional here: the row is inferred from `print_lit`. If you write it, the
checker holds you to it, and a function that performs an effect its row leaves out is rejected.
A function with no effects does no I/O. That's guaranteed, not a convention
([What is proved](../proved.md)).

None of this costs anything at run time. An operation is a direct call of the platform's clause,
which calls the host function on the stream's handle, just like a C program calling `write`.

## Serving an effect yourself

A handler of `Stdout` is an ordinary declaration. A test, or a program that wants the output in
a string, can run `report` under a handler of its own. `report` itself doesn't change:

```bc
include textio

fn report(lines: i32, bytes: i32) -> 1 with Stdout =
  print_lit("lines ");
  print_dec(lines);
  print_lit(", bytes ");
  print_dec(bytes);
  print_byte(b'\n')

-- A fake standard output: the bytes written, kept in a string.
handler collect(mut out: string): Stdout = {
  print_byte(b) = { let (s, u) = push_byte(out, b); out = s };
  print_bytes(v) = { let (s, u) = push_str(out, v); out = s }
}

-- The length of what `report` writes, without writing it.
fn report_len(lines: i32, bytes: i32) -> i32 =
  let c = alloc(string_new(16));
  with collect(&mut c) { report(lines, bytes) };
  let s = free(c);
  let n = borrow imm s { t -> len(t) };
  n

main -> i32 = print_lit("measured\n"); report_len(3, 14)
-- output: measured
-- answer: i32[18]
```

`with collect(&mut c) { … }` runs the block with `collect` serving `Stdout`. Its state is lent
from the cell `c`, so afterwards `c` holds everything that was written. A fake clock or scripted
input works the same way (`corpus/io-laws.bc`, `corpus/reconcile-clock.bc`).

## Reading input

`input_byte()` returns the next byte, or `inr ()` at the end. A loop over it runs as long as the
input does, so it's a `while`:

```bc
include io

-- Upper-cases its input until the input ends; the number of bytes.
fn shout() -> i32 =
  let mut n = 0;
  let mut more = true;
  while more {
    match input_byte() {
      inl b -> if b >= b'a' && b <= b'z' { print_byte(b - 32) } else { print_byte(b) }; n = n + 1
    | inr u -> more = false
    }
  };
  n

main -> i32 = shout()
-- stdin: Hi there
-- output: HI THERE
-- answer: i32[9]
```

`read_input()` reads the whole input into a string at once. The text functions then cut it into
lines and fields without copying (`fold_lines`, `next_line`, `split_once`, `trim`).

## The clock and the arguments

`now()` is the monotonic clock in nanoseconds, as an `i64`. `sleep(ns)` waits at least that
long. Times saturate rather than wrap.

```bc
include io

main -> bool =
  let t0 = now();
  sleep(ns_of_ms(2));
  let t1 = now();
  t1 - t0 >= ns_of_ms(2)
-- answer: inr ()
```

The arguments come as one stream of bytes. `next_arg` reads the next one into a string:

```bc,check
include textio

-- Writes each argument on a line of its own, numbered; the number of arguments.
fn echo() -> i32 =
  let mut n = 0;
  let mut more = true;
  while more {
    let (s, got) = next_arg(string_new(16));
    if got {
      n = n + 1;
      print_dec(n);
      print_byte(b' ');
      let s = print_string(s);
      print_byte(b'\n')
    } else { more = false }
  };
  n

main -> i32 = echo()
```

`bcc run prog.bc alpha beta` passes `alpha` and `beta`; `bcc interp prog.bc -- alpha beta` does
the same in the interpreter.

## Capabilities by name

The standard streams are also values: `stdin`, `stdout` and `stderr` are cells that `main`
holds. A function can take one as an argument instead of performing the effect, and `main` lends
it with `&mut`: `write_lit(&mut stdout, "…")`, `putb(&mut stdout, b)`, or
`for b in bytes(&mut stdin) { … }`. The effects above are built on these cells, so the two styles
are one mechanism. A `main` that names a stream's cell can't also perform its effect.
[Standard I/O as capabilities](../elaboration/standard-io.md) covers the cell style.

## Not yet

Files, the environment, the network and randomness will be effects of the same kind, but they
aren't built yet, and WASI is the only platform so far. Two tasks can't share one output stream.
The [Status](../status.md) page has the full list.
