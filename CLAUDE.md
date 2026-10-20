# Standing instructions

## Spec first

<!-- ANCHOR: spec-first -->
`SPEC.md` is the specification; `Paper/`, `Support/` and `Examples/` implement it (§1–§2),
and `Core/` implements §3–§7. The task is
to implement what the spec states, the way the paper mechanization transcribes what the paper
prints. Code an entry adds or changes is tagged `[spec §N]`.

- No change to the library without a spec entry that states it. If an implementation needs
  something the entry does not state, stop and change the entry first.
- Experiments live in `experiments/`. The library (`Paper/`, `Support/`, `Examples/`, `Core/`)
  never imports them; work from an experiment lands in the library only after its spec entry is
  written.
- Every entry says what it adds, which baseline theorems it must preserve, and what is open.
  The changelog records each version.
<!-- ANCHOR_END: spec-first -->

## Changing Core

<!-- ANCHOR: changing-core -->
Core is the language's kernel, not a transcription. "Spec first" fixes the order of work (entry,
then code), not how much may change. When a program the language should run needs a kernel
change, make the kernel change: types, rules, the relation, the lifetime carrier and the machine
may all be rewritten. What must hold afterwards:

- the fundamental property and adequacy, restated over the new relation if it changes;
- every borrow guarantee;
- every corpus and kernel program, with the same output (a changed count is explained).

The rules of the paper transcription (`bolo-formalization`: follow the printed proof, never edit
a printed statement, no new mathematics) do not apply here. The growth rules below are cost
guidance for choosing between designs, not bans.
<!-- ANCHOR_END: changing-core -->

## The elaborator never does the kernel's work

<!-- ANCHOR: elaborator-scope -->
The elaborator turns surface programs into core terms that the kernel checks. It may do
ergonomics, inference and sugar: inserting `&`, inferring an annotation, expanding a form into
existing core terms. It must never do the borrow calculus's work, and must never work around it.

- **In scope:** sugar into existing core terms, inference, hygiene (resolution to binders),
  ergonomic insertions the kernel then checks, and error messages.
- **Hard stop:** stop and report `STOP: KERNEL WORK` before writing an elaboration rule that
  - decides what the kernel should decide (aliasing, mutation, ownership, lend extents, escape);
  - threads, copies or rebuilds state so that a program the borrow rules would refuse, or could
    not express, gets through;
  - refuses a program on borrow grounds itself instead of letting the kernel's rules refuse it.
- **When the kernel cannot express a program it should run,** change the kernel (Changing Core).
  An elaborator workaround is never the fix.
<!-- ANCHOR_END: elaborator-scope -->

## Growth discipline

<!-- ANCHOR: growth -->
The proof burden of the previous language grew until it was unmaintainable
(`docs/l-lang-kernel-and-lit.md` §2). Three rules (`docs/decisions.md` 19–21):

- **No new index on `CDerives`.** Put a new coordinate in a type former or in the model.
- **Generalize by deleting.** A general former lands in the same change that turns the fixed
  formers it replaces into abbreviations.
- **Do not invert `CDerives` casually.** Inversion lemmas, substitution over derivations, checker
  completeness or lowering proofs that invert typing need their cost stated in the issue or PR.

Prefer computation-type formers and derived forms over new value-type formers: a `VTy` former
costs about 100 match arms across `Core/`, a `CTy` former about 20, a `CDerives` rule one
compatibility lemma.
<!-- ANCHOR_END: growth -->

## The gate: local CI

GitHub Actions does not run for this repository (the workflow is manual-only). The gate for every
PR is `make gate` (`scripts/ci-local.sh`), which runs every check CI would. Run it before opening
or merging a PR and paste its final summary into the PR body. Never report a PR as passing
without it.

Goldens are the oracle. Every corpus program has a `<name>.out` and every book `bc` block an
`-- answer:`: the output of `Support`'s interpreter (`bcc interp`), the reference semantics.
`make gate` checks the build, hygiene, axioms, parse, check, sugar, kernel programs,
counts, `live 0`, and the clos, flat and wasm stages against every golden; it runs the
interpreter itself (minutes on the largest programs) only on the corpus programs and book blocks
that are new or changed since the merge base with origin/main. `make gate-full`
(`scripts/ci-local.sh --source`) runs it on every one, re-verifying every golden. `make gate-full`
is required, and `make gate` turns it on by itself, when `Paper/`, `Support/` (the interpreter and
the machine) or `Backend/` changed. Run it by hand too after a `Frontend/` or `lib/` change that
changes what programs mean. `make goldens` (`scripts/compile-corpus.sh --write-goldens [file…]`)
writes corpus goldens, only ever from the interpreter.

While iterating, `make gate-fast` (`scripts/ci-local.sh --changed`) runs only the steps the
changes since origin/main reach: a change to no `.lean` file skips the build of the library, the
hygiene and the axioms. It never runs the interpreter. It is for the edit loop only; the full gate
is the merge requirement.

## Working loop

- While iterating, check only what you touched: `lake build <Module>`; `bcc check`,
  `bcc interp --stage clos|flat` or `bcc run` on the one program; the one script on the one file
  (`scripts/compile-corpus.sh corpus/foo.bc`, `scripts/check-corpus.sh corpus/foo.bc`,
  `scripts/book-doctest.sh book/src/guide/foo.md[:line]`).
- At milestones, `make gate-fast`.
- Run `make gate` when the PR is ready, or whenever you judge you need it, as for a change whose
  reach you cannot scope to a few files. Never run it out of habit after each edit.
- Run long commands in the background and keep working meanwhile.

Start a worktree with `scripts/new-worktree.sh <branch>`: it branches from origin/main and clones
the main checkout's `.lake` copy-on-write, so the first build is incremental, not cold. The
library modules `lib/*.bc` are read when `bcc` starts, so editing them rebuilds no Lean.

## Hygiene

- No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`, `unsafe` in
  `Paper/`, `Support/`, `Examples/` or `Core/`.
- Every result's `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
- `lake build` clean; `scripts/check-hygiene.sh` and the axiom check passing
  (`lake env lean scripts/AxiomCheck.lean`).
- Comments say what the code is, not how it got here.
