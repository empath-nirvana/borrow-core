# Command-line tools

A program talks to the world through **capabilities**: values it is given, one per effect.
Standard input, standard output and standard error are three of them, `stdin`, `stdout` and
`stderr` (SPEC §11). In `main` they are in scope by name. Everywhere else a function that does
I/O takes the capability it uses, so its type says what it can touch.

Here is `cat`:

```bc
main : F 1 =
  for b in bytes stdin {
    return (putb (&mut stdout, b))
  };
  return ()
-- stdin: hello, world
-- stdin: second line
-- output: hello, world
-- output: second line
-- answer: ()
```

`bytes stdin` is the input as a stream of bytes. `for` runs its body on each byte until the
stream ends, however long the input is. `putb (&mut stdout, b)` writes one byte: `&mut stdout` lends the
output to that one call, which hands it back. After the value, `bcc` prints `live 0`: every cell
was freed.

## The library

These come with every program whose `main` uses the capabilities. They are ordinary code
(`lib/io.bc`), not primitives:

| name | type | |
|---|---|---|
| `getb` | `ref input => ref input * (u8 + 1)` | the next byte, or `inr ()` at the end |
| `putb` | `ref output * u8 => ref output * 1` | write a byte |
| `put_dec` | `ref output * i32 => ref output * 1` | write a number in decimal |
| `write_bytes` | `ref output * array_imm 'b u8 => ref output * 1` | write a byte view in one call |
| `read_bytes` | `ref input * array_mut 'b u8 => ref input * (array_mut 'b u8 * i32)` | read into a byte view, and how many |
| `bytes` | `ref input => U (iter u8 (ref input) (ref input))` | the input as a stream |

Each helper takes a capability and hands it back first, which is what `&mut c` expects. Underneath
are the operations `read_byte`, `write_byte`, `write_all` and `read_into`, on `mut` borrows of
the capabilities; the helpers do the borrowing so programs do not. A byte is a `u8`: compare it
with a literal (`b == 10`, `b == b'\n'`), and widen it with `to_i32(b)` to compute with it.
Text, buffers and literals are libraries of their own (`include textio`, SPEC §17).

## State across a loop

A `for` carries the variables of `main` that its body, or the code after it, reads. Rebind one
in the body and the next byte sees the new value. The loop's state is built from their types,
which are inferred; an annotation, `n : T <- …`, is allowed but not needed.

```bc
def inc : i32 => i32 = thunkv fun (n : i32) -> return ((unbang host[add32]) (n, i32[1]))

-- The number of lines of the input.
main : F 1 =
  lines : i32 <- return i32[0];
  for b in bytes stdin {
    lines : i32 <- case (unbang host[eq32]) ((unbang host[extend8_u]) b, i32[10]) {
      inl other -> return lines
    | inr newline -> return (inc lines)
    };
    return ()
  };
  _ <- return (put_dec (&mut stdout, lines));
  return (putb (&mut stdout, u8[10]))
-- stdin: one
-- stdin: two
-- stdin: three
-- output: 3
-- answer: ()
```

The code after the loop runs once, when the input ends. Here it prints the count; `main`'s
value is what the last `putb` hands back, `()`.

## Loops in helpers

A `for` may appear in any function, not only in `main`. A helper that loops over its input
takes the capability and hands it back with its result, and `main` goes on when it returns:

```bc
def count_bytes : In => In * i32 =
  thunkv fun (c : In) ->
    n : i32 <- return i32[0];
    for b in bytes c {
      n : i32 <- return ((unbang host[add32]) (n, i32[1]));
      return ()
    };
    return (c, n)

main : F 1 =
  n <- return (count_bytes (&mut stdin));
  _ <- return (put_dec (&mut stdout, n));
  return (putb (&mut stdout, u8[10]))
-- stdin: hello
-- output: 6
-- answer: ()
```

A loop over the input may never end, so `count_bytes` is *div*, and so is `main`, which calls it.
Nothing marks either: the compiler infers it, and a function declared `total` that loops is
rejected. [Divergence](divergence.md) says more.

## Helpers, and what their types say

A helper names the capabilities it uses in its type. This one can write to an output and do
nothing else:

```bc
def hexd : i32 => u8 =
  thunkv fun (n : i32) ->
    case (unbang host[lt_u32]) (n, i32[10]) {
      inl u -> return ((unbang host[wrap8]) ((unbang host[add32]) (n, i32[87])))
    | inr u -> return ((unbang host[wrap8]) ((unbang host[add32]) (n, i32[48])))
    }

-- A byte as two hex digits.
def put_hex : Out * u8 => Out * 1 =
  thunkv fun (p : Out * u8) ->
    let (o, c) = p;
    b <- return ((unbang host[extend8_u]) c);
    _ <- return (putb (&mut o, hexd ((unbang host[shr_u32]) (b, i32[4]))));
    return (putb (o, hexd ((unbang host[and32]) (b, i32[15]))))

main : F 1 =
  for b in bytes stdin {
    return (put_hex (&mut stdout, b))
  };
  return (putb (&mut stdout, u8[10]))
-- stdin: Hi
-- output: 48690a
-- answer: ()
```

`stdout` and `stderr` have the same type, `ref output`: a writer is given an output stream, and
its caller chooses which. A function given no capability does no I/O. That is a theorem, not a
convention: a cell owned outside a computation keeps its value through every run of it
(`wpTSD_frame_own`), so a function that does not hold an output cannot change the stream in it.

Capabilities belong to `main`. A `def` that names one is rejected:

```bc,reject
def leak : 1 => ref output = thunkv fun (u : 1) -> return stdout

main : F 1 = return (putb (&mut stdout, i32[10]))
-- expect: 1:59: unknown variable `stdout`
```

and a lent capability must come back through a binding (a `let` is one: the call's result after
the capability is what it binds), not a `case`'s scrutinee:

```bc,reject
main : F 1 =
  case putb (&mut stdout, i32[104]) { inl u -> return () | inr u -> return () }
-- expect: 2:14: `&mut stdout` lends a place to one call: it may appear only in the head `M` of `y <- M; N` (SPEC §11)
```

## What the sugar means

`main`'s ambient capabilities, `&mut c` and `for` are sugar. The frontend turns them into ordinary
core before checking, and the checker never sees them. `bcc desugar tool.bc` prints what it
checks:

- the library and an `extern` for each capability `main` uses;
- `main : F A` becomes `main : F (Caps * A)`, handing the capabilities back where each path
  ends; when `main` loops, `main : F (U (loop (Caps * A) (Caps * 1)))`, a loop the runtime
  drives;
- `x <- f (&mut c, v); N` becomes `r <- f (c, v); let (c, x) = r; N`;
- the `for` becomes a loop by `unfold` over the stream, the other capabilities and the threaded
  variables;
- a function that loops returns its loop, `A => U (loop B R)`, and a call of it in direct style
  is the delay bind `div_bind` ([Divergence](divergence.md)).

The same program can be written without sugar, declaring the externs and passing the
capabilities by hand:

```bc,check
extern stdout : ref output
extern write_byte : !(all 'a < top. mut 'a output * i32 => mut 'a output)

main : F (ref output * 1) =
  q <- return (withbor2['x, top, output, 1] stdout
         (thunkv Fun 'x < dom. return (thunkv fun (m : mut 'x output) ->
            m1 <- return ((unbang write_byte) ['x] (m, i32[104]));
            m2 <- return ((unbang write_byte) ['x] (m1, i32[10]));
            return (boxed['x] ()))));
  let (o, u) = q;
  return (o, ())
```

`corpus/sugar/` pairs each sugared program with its core form, and the gate checks that both
erase to the same term.

## The corpus

Tools run by the interpreter and by wasmtime against a golden output, none with a bound on its
input:

| program | what it shows |
|---|---|
| `io-cat.bc` | the loop above; it also copies a 4860-byte input |
| `io-hex.bc` | a helper that takes only an output |
| `io-upper.bc` | a filter |
| `io-wc.bc` | several counts threaded through a loop in a helper |
| `io-lines.bc` | a helper that loops over the input and returns to `main`, which then writes |
| `io-sections.bc` | two div helpers sequenced, one a loop written in core |
| `io-for-then.bc` | a `for` followed by another loop |
| `io-fuel.bc` | div functions run from total ones with a bound, and the input read on after a cut |
| `io-aoc.bc` | every line read into one array, lent mutably per line (§9) |
| `io-head.bc` | a stream closed early, handing the capability back, then read on |
| `io-guess.bc` | a scripted guessing game, writing to standard error as well |

## Running

    bcc run tool.bc < input          compiled to Wasm, run by wasmtime: interactive, unbuffered
    bcc interp tool.bc < input       the model: reads all of the input first
    bcc desugar tool.bc              the core program the sugar stands for
    bcc trusted tool.bc              the trusted boundaries

`bcc run` gives each capability a cell holding its file descriptor and lowers the operations to
WASI `fd_read` and `fd_write` (in a plain LLVM/libc build, `read(2)` and `write(2)`). `bcc interp`
runs the *model*: streams are byte lists in memory, and the operations are ordinary core terms.
It is slow: each step of the model walks the whole term, so it takes about ten milliseconds a
byte on `io-cat.bc`.

## Text

`include textio` brings in buffers, text and literals (SPEC §17). A string is a growable byte
buffer, `box string(cap)` allocates one, and appends take it and hand it back. A literal `"…"` is
data the program owns no copy of; `'c'` is a character. `write_string` writes a string in one
call:

```bc
include textio

fn point(x: i32, y: i32) -> string =
  let mut s = box string(16);
  push_lit(&mut s, "x="); push_dec(&mut s, x);
  push_lit(&mut s, ", y="); push_dec(&mut s, y);
  push_char(&mut s, '\n');
  s

main -> i32 =
  let s = write_string(&mut stdout, point(12, 0 - 7));
  let (s, n) = len_of(s);
  n
-- output: x=12, y=-7
-- answer: i32[11]
```

A string lends its bytes as a view, with no copy: `borrow imm s { v -> … }`. A view is cut at
run-time indices into views of the same bytes (`split_once`, `trim`, the lines of `fold_lines`),
so reading lines, fields and tokens allocates nothing per line. The block hands back what it
lends, so `write_str(&mut stdout, v)` inside it leaves `stdout` in scope after it.

## What is proved, and what is trusted

- The model of each operation meets its extern's type (`readByte_meets`, `writeByte_meets`,
  `writeAll_meets`, `readInto_meets`), proved in Lean.
- For every implementation of the externs that meets their types, every run of the program's
  `run_io` wrapper from empty memory, under every allocator, continues to its outputs at empty
  memory (`externs_every_run`). A program that runs until its input ends is covered one prefix
  at a time: observed at most `n` times, for every `n` (`externs_loop_every_run`). The model is
  one such implementation, and `bcc interp` runs the very term the theorem is about
  (`IORun.every_run`, `IORun.loop_every_run`).
- The host implementations (WASI calls in the runtime) are assumed to behave as the model. The
  flat IR's interpreter runs the same lowering against scripted streams, checking every memory
  access, and the corpus compares every stage with the model.

`bcc trusted` lists each extern a program uses, with its contract, its host implementation and
its level. Adequacy's "empty memory" is about the model's cells: file descriptors are not memory,
and nothing is claimed about them.

## Not yet

- A `for` has no early exit; `io-guess.bc` keeps a flag instead, and `io-sections.bc` writes its
  line reader as a loop in core. A `for` over a finite source, allowed in total code, is not
  provided (#59); neither are `|>` pipelines.
- A line reader over the stream: an observation must terminate, so a line of unbounded length is
  a loop of its own. Keep the line in a buffer in the loop's state (`corpus/fields.bc`), or read
  the whole input with `read_all` and split it into line views.
- I/O errors are not modeled: a read error is the end of the input.
- Command-line arguments, environment variables, the exit status, files and the network are
  designed as more capabilities of the same kind (SPEC §11) but not built.
