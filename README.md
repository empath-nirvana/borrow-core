# borrow-core

A systems language with Rust-style ownership and borrowing, whose safety is proved in Lean
and which compiles to WebAssembly. It grows from the Lean mechanization of Wagner, Gierczak,
Marshall, Li and Ahmed, *From Linearity to Borrowing* (PACMPL 9:OOPSLA2:415, 2025;
bolo-formalization commit `1658da9`), under a written specification, [`SPEC.md`](SPEC.md).

```
fn is_space(b: u8) -> bool = b == 32 || b == 10 || b == 9

fn count(c: In) -> In * (i32 * (i32 * i32)) =
  let mut lines = 0;
  let mut words = 0;
  let mut chars = 0;
  let mut in_word = false;
  for b in bytes(&mut c) {
    chars = chars + 1;
    if b == 10 { lines = lines + 1 };
    if is_space(b) { in_word = false }
    else { if not(in_word) { words = words + 1 }; in_word = true }
  };
  (c, (lines, (words, chars)))

main -> i32 * (i32 * i32) =
  let (lines, (words, chars)) = count(&mut stdin);
  put_dec(&mut stdout, lines); putb(&mut stdout, 32);
  put_dec(&mut stdout, words); putb(&mut stdout, 32);
  put_dec(&mut stdout, chars); putb(&mut stdout, 10);
  (lines, (words, chars))
```

That is `wc`, from `corpus/surface/io-wc.bc`. The program reads stdin through a borrowed
capability, so `count`'s type shows that it does I/O. `count` has a `for` over the input, so it
may not terminate: it is inferred to be div, and so is `main`, which calls it. It compiles to
WebAssembly that allocates twice and makes no indirect calls (`corpus/counts.expected`). The
surface syntax elaborates into a call-by-push-value core, and the checker proves that core well
typed; `bcc desugar` prints it. The surface is still growing (issue #54,
[`docs/typed-elaboration.md`](docs/typed-elaboration.md)).

## What is proved

These are proved about the core calculus (`Core/`) in Lean, with no `sorry` and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`:

- **The Fundamental Property** (`fundamentalC`, `fundamentalD`): every well-typed term is in the
  semantic relation, borrows and effect handlers included. What the relation gives depends on
  the type:
  - at `F A`, total correctness: every run terminates with a value of `A`, and the memory it
    leaves is described by the type;
  - at `F_Σ A`, the effectful returner of SPEC §19: the computation performs finitely many of the
    operations in `Σ`, each at its protocol, and then answers a value of `A` (`ewpTS`, a least
    fixed point);
  - at `νX. C` (loops, streams, generators): each observation terminates; the whole may be
    observed without end.
- **Every run is safe** (`adequacyD`, `adequacyD_safe`; SPEC §13): take a closed well-typed
  program of type `F 1` and *every* allocator that returns free locations. Then no run of the
  program gets stuck, and every run can continue to its result with all memory freed. The
  paper's statement, that some run succeeds, follows as a corollary. This covers programs that
  handle their effects internally; a program with an unhandled operation is not typed at `F 1`.
- **Totality** (`total_every_run`, `total_no_infinite_run`; §14): a closed program of type `F A`
  terminates on every run, handled effects included. Divergence is an effect that is inferred:
  a program that may not terminate has a loop in its type, and `total def` checks its absence.
- **I/O through capabilities** (`externs_every_run`, `io_loop_every_run`; §11): the end-to-end
  theorem holds for every implementation of a program's externs that meets their contracts. It
  also holds for programs that loop until their input ends, one observation at a time.

The checker is certifying: accepting a program produces its typing derivation
(`checkProgram_sound`). `bcc trusted` lists what a program takes on trust, namely its externs and
their contracts. The compiler is tested, not proved (below).

## The language, today

Each feature below is a numbered entry in `SPEC.md`, and [`docs/decisions.md`](docs/decisions.md)
records why it was added:

- ownership, and `Imm`/`Mut` borrows with lifetimes (the paper's calculus), in a
  call-by-push-value core (§1–§4);
- records, places and family borrows (§5);
- recursive types with folds, and general codata `νX. C` (iterators, streams, loops) (§6, §7);
- the affine closure, codata whose `call` takes an argument: called any number of times through a
  `mut` borrow, then closed, its captured state hidden by its type (`lib/aff.bc`, §22);
- integers, bytes, arrays, and slice borrows that split and write a borrowed array (§8, §9);
- persistent `!` values and implicit destructors (§10, §12);
- stdin, stdout and stderr as linear capabilities (§11);
- divergence as an inferred effect (§14);
- generators, `gen fn` with `yield`, each body one state machine (§15);
- counted loops and `for` over data and iterators (§16);
- growable buffers, UTF-8 text and string literals (§17);
- effects and handlers in the surface, defined by elaboration into capability passing (§18);
- effects and handlers in the kernel (§19): `perform`, `raise`, `hnd`, the finaliser frame
  `ubind` and the cancel catchers `ccatch` and `cfin`; the effectful returner `F_Σ A`; answering
  and control operations, with linear, affine or unrestricted continuations; unwinding through
  borrows, which ends each lend it passes; and cancelling a stored continuation, which runs its
  finalisers and re-raises at the canceller the first error a finaliser raises to a handler
  outside the cancelled region.

Recursion is the fixed point of a generator (decision 24, SPEC §20, §21): a function calls itself,
and functions call one another, as written; the group is the bounded fixed point of its generator,
each call a direct call of the self-reference, run by a driver chosen at the call site. Its
environment (the capabilities it uses) is passed with each call, and layers (`with L { … }`) are
transformers of the generator. The default, `bounded`, is the kernel's `bounded_fix`: a native recursion with a budget of
depth whose end performs `Exhausted` (`lib/rec.bc`), an abortive effect a handler catches. The
heap driver `deep` keeps the pending calls as first-order frames in one growable buffer and is
div. Pending: the layer `memo`, which needs a map (#211).

The kernel's effects are not yet reachable from the surface: §19's programs are Lean terms
(`Core/EffPrograms.lean`), compiled with `bcc kernel`. Moving the surface onto them is in
progress (#188), as is `Yield` inside generators (#159).

The compiler lowers checked programs to WebAssembly through a closure IR and a flat IR. Values
are unboxed by type, and closures are defunctionalized into sized stack values. Fixed points
are compiled natively, and loops and owned folds run in constant stack (owned folds by pointer
reversal). Handlers have no runtime handler stack and no handler search:

- an abortive operation (`raise`) is a branch after each call that may raise
  (`Backend/Clos/Unwind.lean`);
- a tail-resumptive operation whose handler is known is a direct call of its clause (#207);
- other control operations and stored continuations are state machines with one flat tagged
  state, nested through calls, as Rust's `async` is (`Backend/Clos/Capture.lean`).

This lowering is tested, not verified: every kernel program gives the same answer at every stage
and in WebAssembly, with nothing left allocated (`scripts/compile-kernel.sh`). The allocations and
indirect calls of every corpus program and kernel program are counted, and the gate fails if a
count rises.

## Layout

| path | what |
|---|---|
| [`docs/Home.md`](docs/Home.md) | start here: overview, pipeline, glossary, decisions, prior art |
| [`SPEC.md`](SPEC.md) | the language: the paper's calculus (§1), then numbered entries |
| `Core/` | the CBPV core, its semantic relation and the theorems above ([`Core/README.md`](Core/README.md)) |
| `Paper/`, `Support/` | the paper's mechanization, the baseline that `Core` embeds (`Paper/INDEX.md`) |
| `Frontend/` | the parser, typed elaboration, the certifying checker and the `bcc` executable ([`Frontend/README.md`](Frontend/README.md)) |
| `Backend/` | the compiler to WebAssembly, and the kernel programs it compiles (`Backend/Kernel.lean`) ([`Backend/README.md`](Backend/README.md)) |
| `lib/` | library code in the language: `prelude.bc`, `io.bc` and `textio.bc` (standard I/O), `div.bc` (the delay bind and fuel), `lend.bc` (per-observation lends), `gen.bc` and `adapters.bc` (generators and their adapters), `iters.bc` (sized iterators), `slice.bc`, `buf.bc` and `text.bc` (slices, buffers, UTF-8 text) |
| `corpus/` | test programs with goldens: accepted, rejected, sugar pairs, allocation counts (`counts.expected`, `kernel-counts.expected`) |
| `book/` | the guide and reference, an mdBook whose programs are doc-tested |
| `experiments/` | probes toward future entries ([`experiments/README.md`](experiments/README.md)) |
| `Examples/` | programs exercising the early entries |

## Building and running

You need Lean (installed with `elan`) and `wasmtime`. `mdbook` is optional, for building the book.

```sh
lake exe cache get
lake build
make gate        # the gate (scripts/ci-local.sh): build, hygiene and axioms, corpus, kernel programs, sugar, book
make gate-full   # the gate, re-verifying every golden against the reference interpreter (--source)
make gate-fast   # while iterating: only the steps the changes since origin/main reach (--changed)
make goldens     # rewrite the corpus goldens (`.out`) from the reference interpreter
scripts/new-worktree.sh <branch>  # a worktree from origin/main, its build cloned from this checkout's
```

Every corpus program's `.out` and every book block's `-- answer:` is a golden: what the reference
interpreter (`bcc interp`, `Support`'s) prints. `make gate` checks every compiled stage (the
closure IR, the flat IR and WebAssembly) against the goldens, with `live 0` and the counts, and
runs the reference interpreter, which takes minutes on the largest programs, only on the programs
and blocks that are new or changed since the merge base with origin/main. `make gate-full` runs
it on all of them. It is required, and `make gate` turns it on by itself, when `Paper/`,
`Support/` or `Backend/` changed; run it by hand after a `Frontend/` or `lib/` change that changes
what programs mean.

`bcc` reads the library modules (`lib/*.bc`) when it starts, from the `lib/` of the checkout it
was built in (or `$BCC_LIB`), so editing the library needs no rebuild.

`lake exe bcc <command>` runs the compiler:

| command | does |
|---|---|
| `parse <file>` | parse, and check that printing and re-parsing gives the same AST |
| `print <file>` | print in the canonical ASCII spelling |
| `check <file>` | parse, elaborate and type-check |
| `interp <file>` | run in the reference interpreter (`--stage clos` or `--stage flat` for the IRs) |
| `run <file>` | compile to WebAssembly and run under `wasmtime` |
| `compile <file> -o <out.wat>` | compile to WebAssembly text |
| `desugar <file>` | print the core a surface program elaborates to |
| `tir <file>` | print the typed IR |
| `erase <file>` | print the erasure of the checked `main` |
| `trusted <file>` | list the externs a program depends on, with their contracts and assurance levels |
| `kernel list`, `kernel interp <name>`, `kernel run <name>`, `kernel compile <name> -o <out.wat>` | the kernel programs of `Backend/Kernel.lean`, which the surface cannot spell (SPEC §19) |

`lake exe bcc-counts <file>` reports a program's allocations, indirect calls and deep copies
(`--kernel <name>` for a kernel program).

## How work happens

Work is tracked in GitHub issues and merged by pull request. There is no hosted CI: the gate is
`make gate` (`scripts/ci-local.sh`) passing. New language features follow the growth discipline in
[`CLAUDE.md`](CLAUDE.md), in this order:

1. a probe in `experiments/`;
2. a `SPEC.md` entry;
3. the library, the compiler and a running corpus program, together.
