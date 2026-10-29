# Input and output

Standard input, standard output, standard error, the clock and the command-line arguments are
each an effect, and their operations are called like ordinary functions. `main` gets them for
free. Any other function gets them from its caller, and its row (the list of effects it
performs) says which ones it uses. You usually don't write the row, since it's inferred, but you
can (`with Stdout`).

That gives you two things. A function's signature tells you what it can touch. And a test can
serve the same effect with a handler of its own, say a fake stdout that collects into a string.

## The effects

| effect | operations |
|---|---|
| `Stdout` | `print_byte(b: u8)`, `print_bytes(v: array_imm 'b u8)` |
| `Stderr` | `eprint_byte(b: u8)`, `eprint_bytes(v: array_imm 'b u8)` |
| `Stdin` | `input_byte() -> u8 + 1` (`inr ()` at the end), `input_into(v: array_mut 'b u8) -> array_mut 'b u8 * i32` |
| `Clock` | `now() -> i64` (nanoseconds, monotonic), `sleep(ns: i64)` |
| `Args` | `arg_byte() -> u8 + 1`: the arguments' bytes, each argument followed by `0` |

The operations work on bytes and byte views. Text and numbers are library code on top:

- `include io` adds `print_dec`, `print_dec64`, `eprint_dec` and `ns_of_ms`;
- `include textio` adds `print_lit("…")`, `print_str(t)` for a text view, `eprint_lit`,
  `read_input()` (the whole input as a string), `next_arg(s)` (the next argument appended to a
  string, and whether there was one) and `print_string(s)`, which prints an owned string and
  hands it back so you can keep using it.

```bc
include textio

main -> 1 = print_lit("Hello, world!\n")
-- output: Hello, world!
```

## Functions that do I/O

In `main`, an operation that no `with` handles goes to the platform: the operating system's
streams, clock and arguments, under WebAssembly and natively alike. Every other function just
performs its effects, and whoever calls it provides them. This one can write to standard output
and nothing else:

```bc
include textio

-- A report, written to whatever serves `Stdout`.
fn report(lines: i32, bytes: i32) -> 1 with Stdout =
  print_lit("lines ");
  print_dec(lines);
  print_lit(", bytes ");
  print_dec(bytes);
  print_byte(b'\n')

main -> 1 =
  let s = read_input();
  let bytes = len_of(&s);
  let lines = borrow imm s { t -> fold_lines(t, !{ (l, n) -> n + 1 }, 0) };
  report(lines, bytes)
-- stdin: one
-- stdin: two
-- stdin: three
-- output: lines 3, bytes 14
```

`with Stdout` is optional here: the row is inferred from `print_lit`. If you write it, the
checker holds you to it, and a function that performs an effect its row leaves out is rejected.
A function with no effects does no I/O. That's guaranteed, not a convention
([Safety guarantees](../safety.md)).

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
  print_byte(b) = { push_byte(&mut out, b) };
  print_bytes(v) = { push_str(&mut out, v) }
}

main -> 1 =
  let c = alloc(box string(16));
  with collect(&mut c) { report(3, 14) };
  let s = free(c);
  print_lit("report wrote ");
  print_dec(len_of(&s));
  print_lit(" bytes\n")
-- output: report wrote 18 bytes
```

`with collect(&mut c) { … }` runs the block with `collect` serving `Stdout`. Its state is lent
from the cell `c`, so afterwards `c` holds everything that was written. A fake clock or scripted
input works the same way.

## Reading input

`input_byte()` returns the next byte, or `inr ()` at the end. A loop over it runs as long as the
input does, so it's a `while`:

```bc
include textio

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

main -> 1 =
  let n = shout();
  print_dec(n);
  print_lit(" bytes\n")
-- stdin: Hi there
-- output: HI THERE
-- output: 9 bytes
```

For text, `read_input()` reads the whole input into a string, and the text functions cut it into
lines and fields without copying: `fold_lines`, `next_line`, `split_once`, `trim`. Here each line
is a number, and a line that isn't one is skipped and counted:

```bc
include textio

-- One line added to the running sum, or counted as skipped if it isn't a number.
fn add_line<'a>(line: text 'a, acc: i32 * i32) -> i32 * i32 =
  let (sum, skipped) = acc;
  match with to_result { parse_i32(line) } {
    inl n -> (sum + n, skipped)
  | inr e -> (sum, skipped + 1)
  }

main -> 1 =
  let s = read_input();
  let r = borrow imm s { t -> fold_lines(t, !{ (l, acc) -> add_line(l, acc) }, (0, 0)) };
  let (sum, skipped) = r;
  print_dec(sum);
  print_lit(" (");
  print_dec(skipped);
  print_lit(" skipped)\n")
-- stdin: 10
-- stdin: 20
-- stdin: abc
-- stdin: 12
-- output: 42 (1 skipped)
```

`eprint_lit` and `eprint_dec` write to standard error the same way.

## The clock and the arguments

`now()` is the monotonic clock in nanoseconds, as an `i64`. `sleep(ns)` waits at least that
long. Times saturate rather than wrap.

```bc
include textio

main -> 1 =
  let t0 = now();
  sleep(ns_of_ms(2));
  let t1 = now();
  if t1 - t0 >= ns_of_ms(2) { print_lit("slept\n") } else { print_lit("woke early\n") }
-- output: slept
```

The arguments come as one stream of bytes. `next_arg` reads the next one into a string:

```bc,check
include textio

-- Writes each argument on a line of its own, numbered; the number of arguments.
fn echo() -> i32 =
  let mut n = 0;
  let mut more = true;
  while more {
    let (s, got) = next_arg(box string(16));
    if got {
      n = n + 1;
      print_dec(n);
      print_byte(b' ');
      let s = print_string(s);
      print_byte(b'\n')
    } else { more = false }
  };
  n

main -> 1 = let n = echo(); ()
```

`bcc run prog.bc alpha beta` passes `alpha` and `beta`; `bcc interp prog.bc -- alpha beta` does
the same in the interpreter.
