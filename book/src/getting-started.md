# Getting started

## Installing

The compiler, `bcc`, is written in Lean 4 and built from source. You need:

- **elan**, the Lean toolchain manager. It installs the pinned toolchain on first use.
- **wasmtime**, to run compiled programs. Any version with tail-call support works.
- **clang**, only if you want native builds.

On macOS, `brew bundle` in the repository installs elan and wasmtime (and `mdbook`, for building
this book). Then clone the repository and build the compiler:

```sh
git clone https://github.com/empath-nirvana/borrow-core
cd borrow-core
lake exe cache get      # downloads prebuilt Mathlib, which the proofs use, instead of compiling it
lake build bcc
```

The compiler is at `.lake/build/bin/bcc`.

## A first program

Save this as `hello.bc`:

```bc
include textio

-- The sum of the squares below `n`.
fn squares(n: i32) -> i32 =
  let mut s = 0;
  for i in 0..n { s = s + i * i };
  s

main -> 1 =
  print_lit("squares below 4: ");
  print_dec(squares(4));
  print_byte(b'\n')
-- output: squares below 4: 14
```

and run it:

```text
$ bcc run hello.bc
squares below 4: 14
()
live 0
```

`fn` declares a function, and `main` is where the program starts. `include textio` brings in
the text and I/O library: `print_lit` writes a string literal, `print_dec` a number in decimal,
and `print_byte` one byte. `main -> 1` says that `main` returns nothing interesting: `1` is the
unit type, whose one value is `()`.

The last two lines come from `bcc`, not from the program. `()` is the value `main` returned, and
`live 0` is the number of heap objects still allocated when it finished: `live 0` means nothing
leaked. Every program in this book ends that way; the examples show only the program's own
output.

If something is wrong, `bcc run` prints the error, with its line and column, instead of running
the program.

## The `bcc` commands

| command | what it does |
|---|---|
| `bcc run file.bc [arg…]` | compile to WebAssembly and run it under wasmtime |
| `bcc run --native file.bc [arg…]` | compile through LLVM and clang, and run natively |
| `bcc interp file.bc [-- arg…]` | run in the reference interpreter, without compiling |
| `bcc compile file.bc -o out.wat` | write the WebAssembly text |
| `bcc compile --target native file.bc -o out.ll` | write the LLVM IR |

A program reads standard input and writes standard output as usual, and takes arguments after
the file name: `bcc run tool.bc a b < input`.

The [next chapter](guide/basics.md) starts the language from here. [Recipes](recipes.md) has
short programs for everyday tasks, and the [Language reference](language-reference.md) and
[Standard library](stdlib.md) are for looking things up. For larger programs, see the
Advent of Code and LeetCode ports in
[`corpus/aoc/`](https://github.com/empath-nirvana/borrow-core/tree/main/corpus/aoc) and
[`corpus/leetcode/`](https://github.com/empath-nirvana/borrow-core/tree/main/corpus/leetcode).
