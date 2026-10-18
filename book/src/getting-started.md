# Getting started

## Installing

borrow-core is a Lean 4 project. You need:

- **elan**, the Lean toolchain manager. The toolchain version is pinned in `lean-toolchain`,
  and elan installs it on first use.
- **wasmtime**, to run compiled programs. `bcc run` calls `wasmtime -W tail-call=y`, so any
  version with tail-call support works.

Clone the repository, fetch the prebuilt Mathlib cache, and build:

```sh
git clone https://github.com/empath-nirvana/borrow-core
cd borrow-core
lake exe cache get
lake build
```

`lake build` builds the proofs and the `bcc` executable. The executable is at
`.lake/build/bin/bcc`; `lake exe bcc …` runs it.

## The `bcc` commands

| command | what it does |
|---|---|
| `bcc check file.bc` | type-check: print each declaration's type, what the elaboration decided, or the first error |
| `bcc run file.bc [arg…]` | check, compile `main` to WebAssembly, run it under wasmtime |
| `bcc interp file.bc [-- arg…]` | check, then run `main` in the Lean interpreter, the reference semantics |
| `bcc compile file.bc -o out.wat` | check, and write the WebAssembly text |
| `bcc desugar file.bc` | print the core program the surface program elaborates to |
| `bcc trusted file.bc` | list the externs `main` reaches, with their contracts and assurance levels |
| `bcc parse file.bc`, `bcc print file.bc` | parse and round-trip; print in the canonical spelling |

`interp` and `run` print the value of `main`, then `live N`: the number of objects still
allocated after the value has been dropped. `live 0` means nothing leaked. A program reads
standard input and writes standard output as usual: `bcc run tool.bc < input`.

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

Check it:

```text
$ lake exe bcc check hello.bc
…
def squares : !(i32 => i32)
def print_lit__wasi_stdout_cell : !(ref output * i32 * !(i32 => u8) => ref output * 1)
extern stdout : ref output
main : F (ref output * i32)
loop 6:3: `for` is total, bounded by len(0..n)
lowering 9:1: main: `Stdout` is served by the platform's `wasi_stdout` on the cell `stdout`, which each operation lends
call 10:3: print_lit → `print_lit__wasi_stdout_cell`, passing the capabilities
assurance: unconditional
```

It prints the core type of every declaration (the library's included, elided here), then what
the elaboration decided: that the loop is total, that `main`'s output is served by the platform,
and which function each call reaches. `assurance: unconditional` says that the theorems cover
the program with no hypothesis ([What is proved](proved.md)). The types are those of the core the
program elaborates to, which [How it elaborates](elaboration/overview.md) explains.

and run it:

```text
$ lake exe bcc run hello.bc
hello
i32[14]
live 0
```

`fn` declares a function and `main -> i32` says that the program computes an `i32`, which `bcc`
prints after the program's own output. `include textio` brings in the text and I/O library, and
`print_lit` writes a string literal to standard output: `main` is the one function that may do
I/O without being given it. The [next chapter](guide/basics.md) starts the language from there.

## Where to find more programs

`corpus/` holds the programs the test suite runs, each with a comment saying what it computes
and why its answer tells a correct implementation from a plausible wrong one: `corpus/aoc/` and
`corpus/leetcode/` are ports of Advent of Code and LeetCode solutions. `corpus/reject/` holds
programs the checker must reject, `corpus/fail/` programs the parser must reject, and
`corpus/reports/` what `bcc check` prints about the effect programs.
