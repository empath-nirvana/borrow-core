# Input and output

A program reaches the outside world through effects: standard input, standard output, standard
error, the clock and the command-line arguments are each an effect whose operations a function
calls like functions. `main` is the one place they are available without being asked for. Every
other function is given them by its row, the list of effects it performs, which is inferred and
may be written (`with Stdout`). So a function's signature says what it can touch, and a test can
serve the same effect with a handler of its own.

## The effects

`lib/sys.bc` declares the system interface (SPEC §34):

| effect | operations |
|---|---|
| `Stdout` | `print_byte(b: u8)`, `print_bytes(v: array_imm 'b u8)` |
| `Stderr` | `eprint_byte(b: u8)`, `eprint_bytes(v: array_imm 'b u8)` |
| `Stdin` | `input_byte() -> u8 + 1` (`inr ()` at the end), `input_into(v: array_mut 'b u8) -> array_mut 'b u8 * i32` |
| `Clock` | `now() -> i64` (nanoseconds, monotonic), `sleep(ns: i64)` |
| `Args` | `arg_byte() -> u8 + 1`: the arguments' bytes, each argument followed by `0` |

The operations are bytes and byte views, one system call each. Text and numbers are library code
over them: `include io` (`lib/io.bc`) adds `print_dec`, `eprint_dec`, `print_dec64` and `ns_of_ms`,
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

In `main`, an operation of the interface that no `with` handles is served by the platform: the
WASI handlers of `lib/wasi.bc`, which call the host's `fd_write`, `fd_read`, `clock_time_get` and
`args_get`. Another function performs the effects its body performs, and its caller gives them
to it. The function below can write to standard output and do nothing else:

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

`with Stdout` is optional here: the row is inferred from `print_lit`. Written, it is a promise the
checker holds the function to, and a function whose written row leaves out an effect it performs
is rejected. A function given no effect does no I/O, and that is a theorem about the program, not
a convention: a value owned outside a computation keeps its value through every run of it.

Nothing is allocated or dispatched for this. An operation is a direct call of the platform's
clause, which is a direct call of the host function on the stream's handle, as in a C program
that calls `write` (SPEC §34 *Lowering*).

## Serving an effect yourself

A handler of `Stdout` is an ordinary declaration, so a test, or a program that wants the output
in a string, serves `report` with one of its own. Nothing in `report` changes:

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

`with collect(&mut c) { … }` runs the block with `collect` serving `Stdout`, its state lent from
the cell `c`, which holds what was written afterwards. A fake clock or a scripted input is the same
(`corpus/io-laws.bc`, `corpus/reconcile-clock.bc`).

## Reading input

`input_byte()` answers the next byte or `inr ()` at the end; a loop over it may run as long as
the input does, so it is a `while`:

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

`read_input()` reads the whole input into a string at once, in chunks of `input_into`, and text
functions then cut it into lines and fields without copying (`fold_lines`, `next_line`,
`split_once`, `trim`).

## The clock and the arguments

`now()` is the monotonic clock in nanoseconds, as an `i64`, and `sleep(ns)` waits at least that
long; times saturate rather than wrap.

```bc
include io

main -> bool =
  let t0 = now();
  sleep(ns_of_ms(2));
  let t1 = now();
  t1 - t0 >= ns_of_ms(2)
-- answer: inr ()
```

The arguments are one stream of bytes. `next_arg` reads one into a string:

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

The standard streams are also values, `stdin`, `stdout` and `stderr`, cells that `main` holds
(SPEC §11). A function can take one as an argument instead of performing the effect, and `main`
lends it with `&mut`: `write_lit(&mut stdout, "…")`, `putb(&mut stdout, b)`, or
`for b in bytes(&mut stdin) { … }`. The effects above are written over these cells, and the two
styles are one mechanism; a `main` that names a stream's cell cannot also perform its effect.
[Standard I/O as capabilities](../elaboration/standard-io.md) describes the cell style.

## Not yet

- Files, the environment, the network, randomness and the exit status are designed as further
  effects of the same kind but not built (SPEC §11, §34 *Open*); I/O errors are not modelled (a
  read error is the end of the input).
- Two tasks cannot both write to one stream: a task is given the capability for its scope
  ([Async tasks](async.md)).
- A program that includes the I/O library but whose `main` performs no I/O checks and then fails
  to run (#515).
- Only the WASI platform exists; a POSIX one is designed (SPEC §34).
