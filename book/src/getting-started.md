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
| `bcc parse file.bc` | parse, print, re-parse, and compare |
| `bcc print file.bc` | print the program in the canonical ASCII spelling |
| `bcc check file.bc` | type-check: print each declaration's type, or the first error |
| `bcc interp file.bc` | check, then run `main` in the Lean interpreter |
| `bcc run file.bc` | check, compile `main` to WebAssembly, run it under wasmtime |
| `bcc compile file.bc -o out.wat` | check, and write the WebAssembly text |

`interp` and `run` print the value of `main`, then `live N`: the number of objects still
allocated after the value has been dropped. `live 0` means nothing leaked.

## A first program

Save this as `hello.bc`:

```bc
-- A value is bound with `<-`, and a computation ends with `return`.
main : F i32 =
  x <- return i32[40];
  return ((unbang host[add32]) (x, i32[2]))
-- answer: i32[42]
```

Check it:

```text
$ lake exe bcc check hello.bc
main : F i32
```

and run it:

```text
$ lake exe bcc run hello.bc
i32[42]
live 0
```

`main : F i32` says that `main` is a computation that returns an `i32`. `i32[40]` is an integer
literal, and `host[add32]` is WebAssembly's `i32.add`, which `unbang` takes out of its `!` so it
can be applied to a pair. The [next chapter](guide/values-and-computations.md) explains each of
these.

## Where to find more programs

`corpus/` holds the programs the test suite runs, each with a comment saying what it computes
and why its answer tells a correct implementation from a plausible wrong one. `corpus/reject/`
holds programs the checker must reject, and `corpus/fail/` programs the parser must reject.
