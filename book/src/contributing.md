# Contributing

The project's working rules are in `CLAUDE.md` and `docs/decisions.md`; this chapter collects
them.

## Spec first

{{#include ../../CLAUDE.md:spec-first}}

## Definition of done

A feature is done when it compiles ([Design decisions](decisions.md), 17). A feature issue carries
this checklist (`.github/ISSUE_TEMPLATE/feature.md`):

{{#include ../../.github/ISSUE_TEMPLATE/feature.md:13:}}

## Experiments and the library

The library is `Paper/`, `Support/`, `Examples/` and `Core/`, with the parser and checker in
`Frontend/` and the compiler in `Backend/`. `experiments/` holds probes toward future entries, as
separate Lean libraries that the library never imports. An experiment that works becomes a
`SPEC.md` entry, and the entry is then implemented in the library. `experiments/README.md` lists
each experiment and what it found.

## Growth discipline

{{#include ../../CLAUDE.md:growth}}

## Hygiene

- No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe` in the
  library, `Frontend/` or `Backend/`.
- Every result's axioms are within `propext`, `Classical.choice` and `Quot.sound`.
- Comments say what the code is, not how it got here.

## Tests

CI (`.github/workflows/ci.yml`) runs on every push and pull request:

| script | checks |
|---|---|
| `lake build` | the proofs, the checker and the compiler |
| `scripts/check-hygiene.sh` | forbidden keywords and axioms |
| `scripts/parse-corpus.sh` | every corpus file parses and round-trips; each `corpus/fail/` file fails with its expected message |
| `scripts/check-corpus.sh` | every corpus file checks; each `corpus/reject/` file is rejected with its expected message |
| `scripts/compile-corpus.sh` | every corpus `main` gives the same value compiled and interpreted, with `live 0` |
| `scripts/book-doctest.sh` | every program in this book, as below |
| `mdbook build book` | this book |

A corpus program's `main` should have a **falsifier observable**: an answer that plausible wrong
implementations cannot produce. `a - b` with `a ≠ b` catches swapped operands, and two stores read
back in order catch a store that ignores its index.

## Doc-tests

Every fenced block in `book/src/` whose info string starts with `bc` is a program, and
`scripts/book-doctest.sh` runs it according to its attributes, as `rustdoc` does for Rust:

| info string | the program must |
|---|---|
| `bc` | check, and print the value on its `-- answer:` line and then `live 0`, under both `bcc interp` and `bcc run` |
| `bc,check` | check (a library, or a program that cannot run yet) |
| `bc,reject` | parse, and be rejected by the checker with exactly the message on its `-- expect:` line |
| `bc,ignore` | nothing: it is not run |

The line and column in an `-- expect:` line count from the block's first line. Failures are
reported at the block's opening fence, `book/src/<file>.md:<line>`. To run the doc-tests
locally after `lake build`:

```sh
scripts/book-doctest.sh            # uses .lake/build/bin/bcc
BCC=path/to/bcc scripts/book-doctest.sh
```

`bcc run` needs wasmtime on `PATH`; without it, `bc` blocks run under the interpreter only.
Use `text` for fragments that are not whole programs, and `bc,ignore` for syntax that is planned
but not accepted yet.

To build the book, install [mdBook](https://rust-lang.github.io/mdBook/) and run
`mdbook build book` (output in `book/book/`) or `mdbook serve book`. CI uploads the built book as
the `book` artifact of each run.

Guide chapters change with the features they describe: a feature's pull request updates its
chapter, or replaces a planned chapter with a real one.
