# Contributing

This chapter collects the project's working rules. Work is tracked in GitHub issues and merged
by pull request. The reasoning behind the design is in
[`docs/decisions.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/decisions.md).

## Spec first

See [`CLAUDE.md`](../../CLAUDE.md) (the part marked `spec-first`).

## Definition of done

A feature is done when it compiles and runs, not when it type-checks. A feature issue carries
this checklist (`.github/ISSUE_TEMPLATE/feature.md`):

See [`.github/ISSUE_TEMPLATE/feature.md`](../../.github/ISSUE_TEMPLATE/feature.md) (from line 13).

## Experiments and the library

The library is `Paper/`, `Support/`, `Examples/` and `Core/`, with the parser and checker in
`Frontend/` and the compiler in `Backend/`. `experiments/` holds probes toward future entries, as
separate Lean libraries that the library never imports. An experiment that works becomes a
`SPEC.md` entry, and the entry is then implemented in the library. `experiments/README.md` lists
each experiment and what it found.

## Growth discipline

See [`CLAUDE.md`](../../CLAUDE.md) (the part marked `growth`).

## Hygiene

- No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe` in the
  library, `Frontend/` or `Backend/`.
- Every result's axioms are within `propext`, `Classical.choice` and `Quot.sound`.
- Comments say what the code is, not how it got here.

## Tests

There is no hosted CI. The sanity gate, `make gate` (`scripts/ci-local.sh`), is run locally
before a pull request is opened. It runs the build, the hygiene and axiom checks, the judgment
freeze and the Backend2 fence, and these:

| script | checks |
|---|---|
| `lake build` | the proofs, the checker and the compiler |
| `scripts/check-hygiene.sh` | forbidden keywords and axioms |
| `scripts/parse-corpus.sh` | every corpus file parses and round-trips; each `corpus/fail/` file fails with its expected message |
| `scripts/check-corpus.sh` | every corpus file checks; each `corpus/reject/` file is rejected with its expected message |
| `scripts/check-type-eq.sh` | every type comparison goes through the one `[α]` helper |
| `scripts/alpha-check.py` | every corpus program elaborates to the same term under a renaming of its binders |
| `scripts/compile-corpus.sh --final` | every corpus `main` prints its golden `.out`, the interpreter's output, in WebAssembly, with `live 0` |
| `scripts/compile-backend2.sh --final` | the same, compiled by the new backend |

`make gate-full` runs every check besides: every compiled stage and the counts, the native
target, the kernel programs, the static tables, the generated and renamed programs,
`scripts/book-doctest.sh` (every program in this book, as below) and `mdbook build book`.

Other targets:

```sh
make gate-full   # every check
make gate-fast   # while iterating: only the sanity gate's steps your changes since origin/main reach
make goldens     # rewrite the corpus goldens (.out) and their keys from the reference interpreter
make keys        # record the keys of the goldens the reference interpreter verifies
make verify-goldens  # re-check every golden against the reference interpreter
scripts/new-worktree.sh <branch>  # a worktree from origin/main, reusing this checkout's build
```

Every corpus program's `.out` and every book block's `-- answer:` is a golden: what the reference
interpreter (`bcc interp`) prints. The gate checks every compiled stage against the goldens. It
runs the interpreter itself, which is slow on the largest programs, only on programs and blocks
whose recorded key (`<name>.key`, `book/keys/`) is missing or no longer the current one: the key
covers the elaborated term, the input and the interpreter's source (`scripts/source-stage.sh`).
Record the keys of goldens it verified with `make keys`; `make verify-goldens` reruns it on
every program and block.

A corpus program's `main` should have a **falsifier observable**: an answer that plausible wrong
implementations cannot produce. `a - b` with `a ≠ b` catches swapped operands, and two stores read
back in order catch a store that ignores its index. Write a single program's golden with
`scripts/compile-corpus.sh --write-goldens corpus/<name>.bc`.

## Doc-tests

Every fenced block in `book/src/` whose info string starts with `bc` is a program, and
`scripts/book-doctest.sh` runs it according to its attributes, as `rustdoc` does for Rust:

| info string | the program must |
|---|---|
| `bc` | check, and print the value on its `-- answer:` line and then `live 0`, under both `bcc interp` and `bcc run` |
| `bc,check` | check (a library, or a program that cannot run yet) |
| `bc,reject` | parse, and be rejected by the checker with exactly the message on its `-- expect:` line |
| `bc,ignore` | nothing: it is not run |

A `bc` block's expected standard output goes in `-- output:` lines, one per line, and its
standard input in `-- stdin:` lines. The line and column in an `-- expect:` line count from the
block's first line. Failures are
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
`mdbook build book` (output in `book/book/`) or `mdbook serve book`.

Guide chapters change with the features they describe: a feature's pull request updates its
chapter and its line on the [Status](../../book/src/status.md) page.
