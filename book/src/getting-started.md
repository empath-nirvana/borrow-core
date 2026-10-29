# Getting started

## Installing

borrow-core is built with Lean 4. You need:

- **elan**, the Lean toolchain manager. The toolchain version is pinned in `lean-toolchain`, and
  elan installs it on first use.
- **wasmtime**, to run compiled programs. `bcc run` calls `wasmtime -W tail-call=y`, so any
  version with tail-call support works.
- **clang**, only if you want native builds (`bcc run --native`).

On macOS, `brew bundle` in the repository installs elan and wasmtime (and `mdbook`, for building
this book). Then clone the repository, fetch the prebuilt Mathlib cache, and build the compiler:

```sh
git clone https://github.com/empath-nirvana/borrow-core
cd borrow-core
lake exe cache get
lake build bcc
```

The compiler is at `.lake/build/bin/bcc`, and `lake exe bcc …` runs it too. `lake build` on its
own builds the proofs as well, which takes longer.

## A first program

Save this as `hello.bc`:

```bc
include textio

-- The sum of the squares below `n`.
fn squares(n: i32) -> i32 =
  let mut s = 0;
  for i in 0..n { s = s + i * i };
  s

main -> i32 =
  print_lit("hello\n");
  squares(4)
-- output: hello
-- answer: i32[14]
```

and run it:

```text
$ bcc run hello.bc
hello
i32[14]
live 0
```

`fn` declares a function, and `main -> i32` says the program computes an `i32`, which `bcc`
prints after the program's own output. Then comes `live N`, the number of objects still
allocated at the end: `live 0` means nothing leaked. `include textio` brings in the text and
I/O library, and `print_lit` writes a string literal to standard output. `main` is the one
function that can do I/O without being given it.

The same program runs natively, or in the reference interpreter:

```text
$ bcc run --native hello.bc
hello
i32[14]
live 0
$ bcc interp hello.bc
hello
i32[14]
live 0
```

`bcc check` type-checks without running, and prints the type of each declaration:

```text
$ bcc check hello.bc
…
def squares : !(i32 => i32)
…
loop 6:3: `for` is total, bounded by len(0..n)
…
```

`bcc check` also prints notes on how each part compiles; you can ignore them for now. The types
are those of the core the program is translated into, which
[How it elaborates](elaboration/overview.md) explains.

## The `bcc` commands

| command | what it does |
|---|---|
| `bcc check file.bc` | type-check: print each declaration's type and notes, or the first error |
| `bcc run file.bc [arg…]` | compile `main` to WebAssembly and run it under wasmtime |
| `bcc run --native file.bc [arg…]` | compile through LLVM and clang, and run natively |
| `bcc interp file.bc [-- arg…]` | run `main` in the reference interpreter |
| `bcc compile file.bc -o out.wat` | write the WebAssembly text (`--target native` for LLVM IR) |
| `bcc desugar file.bc` | print the core program the surface program translates to |
| `bcc trusted file.bc` | list the externs `main` reaches, and what each takes on trust |
| `bcc parse file.bc`, `bcc print file.bc` | parse and round-trip; print in the canonical spelling |

A program reads standard input and writes standard output as usual, and takes arguments after
the file name: `bcc run tool.bc a b < input`. `make run hello.bc` builds `bcc` if needed and
then runs the program.

The [next chapter](guide/basics.md) starts the language from here.

## Where to find more programs

`corpus/` holds the programs the test suite runs, each with a comment saying what it computes.
`corpus/aoc/` and `corpus/leetcode/` are ports of Advent of Code and LeetCode solutions.
`corpus/reject/` holds programs the checker must reject, which is a quick way to see the errors
it gives.
