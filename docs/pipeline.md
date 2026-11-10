# Pipeline

```
file.bc ──parse──▶ AST ──check──▶ Expr + proof of CDerives ──compile──▶ .wat ──wasmtime──▶ result
```

| stage | code | command |
|---|---|---|
| parse | `Frontend/Lexer.lean`, `Frontend/Parser.lean` | `lake exe bcc parse file.bc`, `lake exe bcc print file.bc` |
| elaborate | `Frontend/Elab/Effects.lean` (handlers, SPEC §18), `Frontend/Sugar.lean`, `Frontend/Elab/` (`docs/typed-elaboration.md`) | `lake exe bcc desugar file.bc` |
| check | `Frontend/Check/`: returns the typed term (`Check/TExpr.lean`), whose erasure is compiled | `lake exe bcc check file.bc`, `lake exe bcc erase file.bc`, `lake exe bcc trusted file.bc` |
| compile | `Backend2/` (LIR → word IR → Wasm AST → WAT), the default; with `--backend old`, `Backend/` (closure IR → flat IR → Wasm AST → WAT) until N7 | `lake exe bcc compile [--backend old] file.bc -o out.wat` |
| run | wasmtime, with tail calls | `lake exe bcc run [--backend old] file.bc` |
| interpret | `Support`'s interpreter, or a backend stage's: Backend2's `lir` and `flat`, or the old backend's `clos` and `flat` | `lake exe bcc interp [--stage source\|lir\|flat] file.bc`, `lake exe bcc interp --backend old --stage clos\|flat file.bc` |
| count | `Backend/Counts.lean`: allocations, indirect calls and deep copies | `lake exe bcc-counts [--backend old] file.bc` |

The check stage also inserts the consume of every owned value that a path leaves unused (SPEC
§12), so the `Expr` it hands on consumes each value exactly once, and the compiler lowers the
inserted calls as ordinary code.

Every command that runs a program prints the value, then `live N`, the number of objects still
allocated. `live 0` is the leak check.

**Kernel programs.** Some programs of `Core/` cannot be spelled in the surface, such as SPEC §19's
handlers that capture the continuation. They are listed in `Backend/Kernel.lean` and enter the
pipeline at the old backend's compile stage: `lake exe bcc kernel list` names them, and `bcc kernel interp
[--stage source|clos|flat] <name>`, `bcc kernel compile <name> -o out.wat` and `bcc kernel run
<name>` run them as the commands above run a file. `lake exe bcc-counts --kernel <name>` counts
one.

## Scripts

| script | checks |
|---|---|
| `scripts/parse-corpus.sh` | every corpus file parses and round-trips; each `corpus/fail/` file fails with its expected message |
| `scripts/check-corpus.sh` | every corpus file checks; each `corpus/reject/` file is rejected with its expected message |
| `scripts/compile-backend2.sh` | Backend2, the default: every corpus `main` prints its golden at the lir, flat, wasm and native stages, with `live 0`; its counts are at most its entry in `corpus/counts-backend2.expected`; `--final` runs wasm only, without counts |
| `scripts/compile-corpus.sh` | the old backend (`--backend old`): every corpus `main` prints its golden `<name>.out` (the reference interpreter's output) at the clos, flat and wasm stages, with `live 0`, and at the source stage when that runs (below); its counts are at most its entry in `corpus/counts.expected`; `--final` runs wasm only, without counts; `--write-goldens` writes the goldens from the reference interpreter |
| `scripts/compile-kernel.sh` | the old backend: every kernel program gives the same value at every stage and in WebAssembly, with `live 0`; its counts are at most its entry in `corpus/kernel-counts.expected` |
| `scripts/compile-scaling.sh` | compile time against program size, by Backend2 (`--backend old` for the old backend); with `--guard`, the 8× program compiles within a bound times the 1× program's time |
| `scripts/check-sugar.sh` | for every `corpus/sugar/` pair, the sugared program and its hand-written core form check and erase to the same term |
| `scripts/book-doctest.sh` | every `bc` block in `book/src/` checks and prints its `-- answer:` with `live 0` compiled (by Backend2; `--backend old` for the old backend), and interpreted when the source stage runs, or is rejected with its `-- expect:` message |
| `scripts/check-hygiene.sh` | no `sorry`, `axiom`, `native_decide`, `partial` and the like; every declaration's axioms within the standard three |
| `scripts/AxiomCheck.lean` | prints the axioms of the theorems `SPEC.md` names (`lake env lean scripts/AxiomCheck.lean`) |

`scripts/ci-local.sh` (`make gate`) is the sanity gate, run before opening a pull request: after
`lake build`, at once, the hygiene and axiom checks, the judgment freeze, the Backend2 fence,
`check-type-eq.sh`, `parse-corpus.sh`, `check-corpus.sh`, `alpha-check.py`, and the corpus in WebAssembly on each backend
(`compile-backend2.sh --final` on Backend2, `compile-corpus.sh --final` on the old backend: no intermediate-IR interpreter and no
counts, except to name the first differing stage of a program whose WebAssembly run is wrong).
`scripts/ci-local.sh --full` (`make gate-full`) runs every script, the corpus at every stage
with its counts, and `mdbook build book` when `mdbook` is installed. `scripts/ci-local.sh
--changed` (`make gate-fast`) runs only the sanity gate's steps that the changes since origin/main
reach (none of the Lean steps unless a `.lean` file changed): it is for iteration. There is no hosted CI;
`.github/workflows/ci.yml` runs only when started by hand. `compile-corpus.sh`, `check-corpus.sh`
and `book-doctest.sh` also take the files to check (`book/src/<file>.md:<line>` for one block).

**Goldens and the source stage.** The reference semantics is `Support`'s interpreter (`bcc
interp`, the source stage). Every corpus program's `<name>.out` and every book block's
`-- answer:` and `-- output:` lines record what it prints, and the clos, flat and wasm stages are
always checked against them. The interpreter takes minutes on the largest programs, so the gate
runs it only where a golden is unverified (`scripts/source-stage.sh`). A verified golden is
recorded with its key, `bcc interp --key` (`Reference/Key.lean`): a sha256 over the elaborated
term the interpreter runs (every library definition it reaches included), the program's input and
arguments, the fuel, and the interpreter digest (`scripts/interp-digest.sh`: the source of every
file in `Reference.Source`'s import closure, `Reference/Driver.lean`, `Reference/Key.lean` and
`lean-toolchain`). A corpus program's key is `<name>.key`, with the hash of its golden; a book
chapter's, `book/keys/<chapter>.md.keys`, a line for each verified block. A golden is unverified
when no key is recorded or the recorded one is not the current one: a change to a library
function reruns exactly the programs whose term it changes, and a change to the interpreter every
program. Computing the keys elaborates each program and runs nothing. `make gate` and `make
gate-full` both follow this rule, and list the programs and blocks they reran; `make
verify-goldens` (`BCC_SOURCE=1`, or `--source` for a single script) runs the interpreter on every
program and block and re-verifies every golden. `make keys` (`--write-keys`) records the keys of
the goldens it verifies. `make gate-fast` never runs the interpreter; it lists the unverified
programs. `make goldens` (`scripts/compile-corpus.sh --write-goldens [file…]`) writes corpus
goldens and their keys, only ever from the interpreter; `corpus/deep-list.bc` (`-- check:
no-source`), too large for it, keeps a golden written by hand, and has no key.

## Writing a corpus program

A corpus program lives in `corpus/`, and its `main` should have a **falsifier observable**: an
answer that plausible wrong implementations cannot produce. For example, `a - b` with `a ≠ b`
catches swapped operands, and two stores read back in order catch index-blindness. A rejected
program lives in `corpus/reject/` with an `-- expect:` line giving its error. A new program's golden is
written by `scripts/compile-corpus.sh --write-goldens corpus/<name>.bc`, and checked by
`scripts/compile-corpus.sh corpus/<name>.bc` (which runs the source stage on it, since it is new).
