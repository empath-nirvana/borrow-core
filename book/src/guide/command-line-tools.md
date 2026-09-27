# Command-line tools

A program talks to the world through **capabilities**: values it is given, one per effect. There
is no ambient I/O. Standard input, standard output and standard error are three capabilities,
declared as externs, and two operations act on them (SPEC §11):

```text
extern stdin      : ref input
extern stdout     : ref output
extern stderr     : ref output
extern read_byte  : !(all 'a < top. mut 'a input => mut 'a input * (i32 + 1))
extern write_byte : !(all 'a < top. mut 'a output * i32 => mut 'a output)
```

A capability is a cell whose content is opaque: `input` and `output` have no rules, so a program
can move them, keep them in cells and hand them to the operations, but cannot copy, inspect or
drop them. The operations take a `mut` borrow of the cell and give it back. `read_byte` answers
the next byte, or `inr ()` at the end of the input; `write_byte` writes the low 8 bits of an
integer.

A program declares the externs it uses. Its `main` hands the capabilities back after its result:
`main : F (Caps * A)`, with `Caps` its capabilities in declaration order.

## Writing

`write_byte` needs a borrow of the output. `withbor2` lends one for a callback, and returns the
cell with the callback's result:

```bc
extern stdout : ref output
extern write_byte : !(all 'a < top. mut 'a output * i32 => mut 'a output)

main : F (ref output * 1) =
  q <- return (withbor2['x, top, output, 1] stdout
         (thunkv Fun 'x < dom. return (thunkv fun (m : mut 'x output) ->
            m1 <- return ((unbang write_byte) ['x] (m, i32[104]));
            m2 <- return ((unbang write_byte) ['x] (m1, i32[105]));
            m3 <- return ((unbang write_byte) ['x] (m2, i32[10]));
            return (boxed['x] ()))));
  let (o, u) = q;
  return (o, ())
-- output: hi
-- answer: ()
```

The program writes `hi` and a newline; then `bcc` prints the result and `live 0`.

## Helpers, and what their types say

A `def` may use the operations: they are persistent externs and carry no authority. It may not
use a capability. A helper that reads takes the input; one that writes takes the output:

```bc
extern stdin : ref input
extern stdout : ref output
extern read_byte : !(all 'a < top. mut 'a input => mut 'a input * (i32 + 1))
extern write_byte : !(all 'a < top. mut 'a output * i32 => mut 'a output)

type In = ref input
type Out = ref output

-- The next byte, or `inr ()` at the end: it can only read.
def getb : In => In * (i32 + 1) =
  thunkv fun (c : In) ->
    return (withbor2['x, top, input, i32 + 1] c
      (thunkv Fun 'x < dom. return (thunkv fun (m : mut 'x input) ->
         r <- return ((unbang read_byte) ['x] m);
         let (m2, b) = r;
         return (boxed['x] b))))

-- One byte out: it can only write.
def putb : Out * i32 => Out =
  thunkv fun (p : Out * i32) ->
    let (c, b) = p;
    q <- return (withbor2['x, top, output, 1] c
      (thunkv Fun 'x < dom. return (thunkv fun (m : mut 'x output) ->
         m2 <- return ((unbang write_byte) ['x] (m, b));
         return (boxed['x] ()))));
    let (c2, u) = q;
    return c2

-- The first two bytes of the input, swapped.
main : F ((In * Out) * 1) =
  q1 <- return (getb stdin);
  let (i1, x) = q1;
  q2 <- return (getb i1);
  let (i2, y) = q2;
  o <- return (stdout);
  o1 : Out <- case y { inl b -> return (putb (o, b)) | inr u -> return o };
  o2 : Out <- case x { inl b -> return (putb (o1, b)) | inr u -> return o1 };
  return ((i2, putb (o2, i32[10])), ())
-- stdin: ab
-- output: ba
-- answer: ()
```

`getb`'s type, `ref input => ref input * (i32 + 1)`, is the whole of what it can do to the
world: read the input it is given. A function given no capability does no I/O, and that is a
theorem, not a convention: a cell owned by a computation's frame keeps its value through every
run of the computation (`wpTSD_frame_own`), so a function that does not hold the output cannot
change the stream in it.

The checker enforces the rest. A `def` that names a capability is rejected:

```bc,reject
extern stdout : ref output

def leak : 1 => ref output = thunkv fun (u : 1) -> return stdout

main : F (ref output * 1) = return (stdout, ())
-- expect: 3:59: the capability `stdout` is not in scope: a `def` may use only persistent externs; take the capability as an argument (SPEC §11)
```

and so is a capability used twice, or one `main` does not hand back:

```bc,reject
extern stdout : ref output

main : F ((ref output * ref output) * 1) = return ((stdout, stdout), ())
-- expect: 3:52: `stdout` is used twice here, and its type `ref output` is not persistent
```

## Borrowed capabilities

A helper can take a borrow instead of the cell, and its type then says it needs a lent stream
for as long as it runs:

```bc,check
extern write_byte : !(all 'a < top. mut 'a output * i32 => mut 'a output)

def hexd : i32 => i32 =
  thunkv fun (n : i32) ->
    case (unbang host[lt_u32]) (n, i32[10]) {
      inl u -> return ((unbang host[add32]) (n, i32[87]))
    | inr u -> return ((unbang host[add32]) (n, i32[48]))
    }

-- A byte as two hex digits, to a borrowed output.
def put_hex : all 'a < top. mut 'a output * i32 => mut 'a output =
  thunkv Fun 'a < top. return (thunkv fun (p : mut 'a output * i32) ->
    let (m, b) = p;
    m1 <- return ((unbang write_byte) ['a] (m, hexd ((unbang host[shr_u32]) (b, i32[4]))));
    return ((unbang write_byte) ['a] (m1, hexd ((unbang host[and32]) (b, i32[15])))))
```

`stdout` and `stderr` have the same type, `ref output`: a writer is given an output stream, and
the caller chooses which. `corpus/io-guess.bc` points one decimal printer at both.

## Loops

Recursion is structured, so a loop over the input is a step function applied a bounded number
of times, and a step after the end of the input does nothing. The corpus doubles a `!` step with
`twice`, as the array programs do; `corpus/io-cat.bc` copies up to 4095 bytes in 2^12 steps:

```bc,ignore
def twice : !(S => S) => !(S => S) =
  thunkv fun (f : !(S => S)) -> return (!thunkv fun (s : S) -> return ((unbang f) ((unbang f) s)))
```

The corpus has seven tools, each run by the interpreter and by wasmtime against a golden output:

| program | what it shows |
|---|---|
| `io-cat.bc` | copying, with helpers that take only the input or only the output |
| `io-hex.bc` | a helper over a borrowed output (`put_hex`) |
| `io-upper.bc` | a filter |
| `io-wc.bc` | counting, and a decimal printer |
| `io-aoc.bc` | every line read into one buffer, an array lent mutably per line (§9) |
| `io-head.bc` | the input as an iterator that owns the capability, closed early, handing it back |
| `io-guess.bc` | a scripted guessing game, writing to standard error as well |

## Running

    bcc run tool.bc < input          compiled to Wasm, run by wasmtime: interactive, unbuffered
    bcc interp tool.bc < input       the model: reads all of the input first
    bcc trusted tool.bc              the trusted boundaries

`bcc run` gives each capability a cell holding its file descriptor and lowers the operations to
WASI `fd_read` and `fd_write` (in a plain LLVM/libc build, `read(2)` and `write(2)`). `bcc interp`
runs the *model*: the checker wraps `main` into `run_io`, which makes the capabilities from the
input bytes, runs `main`, and takes the capabilities back. The model's streams are byte lists in
memory, and its operations are ordinary core terms.

## What is proved, and what is trusted

- The model of each operation meets its extern's type (`readByte_meets`, `writeByte_meets`):
  proved in Lean, assurance level 7.
- For every implementation of the externs that meets their types, every run of `run_io` from
  empty memory, under every allocator, continues to the outputs at empty memory
  (`externs_every_run`); the model is one such implementation (`io_every_run`), and
  `bcc interp` runs exactly the term the theorem is about (`IORun.every_run`).
- The host implementations (WASI calls in the runtime) are assumed to behave as the model. They
  are interpreter-checked (level 2): the flat IR's interpreter runs the same lowering against
  scripted streams, checking every memory access, and the corpus compares every stage with the
  model's output.

`bcc trusted` lists each extern a program declares with its contract, its host implementation
and its level. Adequacy's "empty memory" is about the model's cells: file descriptors are not
memory, and nothing is claimed about them.

## Not yet

Command-line arguments, environment variables, the exit status, files and the network are
designed as more capabilities of the same kind (SPEC §11) but not built; a file source would be
`io-head.bc` over a file's `input`. Inside `main` only, printing without naming `stdout` is
planned as sugar that elaborates to the capability-passing form.
