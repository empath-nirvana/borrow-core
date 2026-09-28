# borrow-core

A systems language with Rust-style ownership and borrowing, whose safety is proved in Lean
and which compiles to WebAssembly. It grows from the Lean mechanization of Wagner, Gierczak,
Marshall, Li and Ahmed, *From Linearity to Borrowing* (PACMPL 9:OOPSLA2:415, 2025;
bolo-formalization commit `1658da9`), under a written specification, [`SPEC.md`](SPEC.md).

```
main : F 1 =
  for b in bytes stdin {
    return (putb (&stdout, b))
  };
  return ()
```

That is `cat`, from `corpus/io-cat.bc`. The core syntax is call-by-push-value written out in
full. A surface syntax is being built over it by typed elaboration (issue #54,
[`docs/typed-elaboration.md`](docs/typed-elaboration.md)).

## What is proved

These are proved about the core calculus (`Core/`) in Lean, with no `sorry` and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`:

- **The Fundamental Property** (`fundamentalC`): every well-typed term is in the semantic
  relation, borrows included.
- **Every run is safe** (`adequacyD`, `adequacyD_safe`; SPEC §13): take a closed well-typed
  program and *every* allocator that returns free locations. Then no run of the program gets
  stuck, and every run can continue to its result with all memory freed. The paper's statement,
  that some run succeeds, follows as a corollary.
- **Totality** (`total_every_run`, `total_no_infinite_run`; §14): a program whose type has no
  divergence terminates on every run. Divergence is an effect that is inferred, and `total def`
  checks its absence.
- **I/O through capabilities** (`externs_every_run`, `io_loop_every_run`; §11): the end-to-end
  theorem holds for every implementation of a program's externs that meets their contracts. It
  also holds for programs that loop until their input ends.

The checker is certifying: accepting a program produces its typing derivation. `bcc trusted`
lists what a program takes on trust, namely its externs and their contracts.

## The language, today

Each feature below is a numbered entry in `SPEC.md`, and [`docs/decisions.md`](docs/decisions.md)
records why it was added:

- ownership, and `Imm`/`Mut` borrows with lifetimes (the paper's calculus), in a
  call-by-push-value core;
- records, places and family borrows;
- recursive types with folds, and general codata `νX. C` (iterators, streams, loops);
- integers and arrays;
- persistent `!` values and implicit destructors;
- stdin, stdout and stderr as linear capabilities;
- divergence as an inferred effect.

The compiler lowers checked programs to WebAssembly through a closure IR and a flat IR. Values
are unboxed by type, and closures are defunctionalized into sized stack values. The allocations
and indirect calls of every corpus program are counted, and the gate fails if a count rises.

## Layout

| path | what |
|---|---|
| [`docs/Home.md`](docs/Home.md) | start here: overview, pipeline, glossary, decisions, prior art |
| [`SPEC.md`](SPEC.md) | the language: the paper's calculus (§1), then numbered entries |
| `Core/` | the CBPV core, its semantic relation and the theorems above ([`Core/README.md`](Core/README.md)) |
| `Paper/`, `Support/` | the paper's mechanization, the baseline that `Core` embeds (`Paper/INDEX.md`) |
| `Frontend/` | the parser, typed elaboration, the certifying checker and the `bcc` executable ([`Frontend/README.md`](Frontend/README.md)) |
| `Backend/` | the compiler to WebAssembly ([`Backend/README.md`](Backend/README.md)) |
| `lib/` | library code in the language (`io.bc`, `div.bc`) |
| `corpus/` | test programs with goldens: accepted, rejected, sugar pairs, allocation counts |
| `book/` | the guide and reference, an mdBook whose programs are doc-tested |
| `experiments/` | probes toward future entries ([`experiments/README.md`](experiments/README.md)) |
| `Examples/` | programs exercising the early entries |

## Building and running

You need Lean (installed with `elan`) and `wasmtime`. `mdbook` is optional, for building the book.

```sh
lake exe cache get
lake build
scripts/ci-local.sh             # the gate: build, hygiene and axioms, corpus, sugar, book
```

`lake exe bcc <command>` runs the compiler:

| command | does |
|---|---|
| `check <file>` | parse, elaborate and type-check |
| `interp <file>` | run in the reference interpreter (`--stage clos` or `--stage flat` for the IRs) |
| `run <file>` | compile to WebAssembly and run under `wasmtime` |
| `compile <file> -o <out>` | compile to a `.wasm` file |
| `desugar <file>` | print the core a surface program elaborates to |
| `tir <file>` | print the typed IR |
| `trusted <file>` | list the externs a program depends on |

`lake exe bcc-counts <file>` reports a program's allocations and indirect calls.

## How work happens

Work is tracked in GitHub issues and merged by pull request. There is no hosted CI: the gate is
`scripts/ci-local.sh` passing. New language features follow the growth discipline in
[`CLAUDE.md`](CLAUDE.md), in this order:

1. a probe in `experiments/`;
2. a `SPEC.md` entry;
3. the library, the compiler and a running corpus program, together.
