# Pipeline

```
file.bc ──parse──▶ AST ──check──▶ Expr + proof of CDerives ──compile──▶ .wat ──wasmtime──▶ result
```

| stage | code | command |
|---|---|---|
| parse | `Frontend/Lexer.lean`, `Frontend/Parser.lean` | `lake exe bcc parse file.bc`, `lake exe bcc print file.bc` |
| elaborate | `Frontend/Elab/Effects.lean` (handlers, SPEC §18), `Frontend/Sugar.lean`, `Frontend/Elab/` (the typed IR, `docs/typed-elaboration.md`) | `lake exe bcc desugar file.bc`, `lake exe bcc tir file.bc` |
| check | `Frontend/Check/` | `lake exe bcc check file.bc`, `lake exe bcc erase file.bc`, `lake exe bcc trusted file.bc` |
| compile | `Backend/` (closure IR → flat IR → Wasm AST → WAT) | `lake exe bcc compile file.bc -o out.wat` |
| run | wasmtime, with tail calls | `lake exe bcc run file.bc` |
| interpret | `Support`'s interpreter, or a backend stage's | `lake exe bcc interp [--stage source\|clos\|flat] file.bc` |
| count | `Backend/Counts.lean`: allocations, indirect calls and deep copies | `lake exe bcc-counts file.bc` |

The check stage also inserts the destructor of every owned value that a path leaves unused (SPEC
§12), so the `Expr` it hands on consumes each value exactly once, and the compiler lowers the
inserted calls as ordinary code.

Every command that runs a program prints the value, then `live N`, the number of objects still
allocated. `live 0` is the leak check.

**Kernel programs.** Some programs of `Core/` cannot be spelled in the surface, such as SPEC §19's
handlers that capture the continuation. They are listed in `Backend/Kernel.lean` and enter the
pipeline at the compile stage: `lake exe bcc kernel list` names them, and `bcc kernel interp
[--stage source|clos|flat] <name>`, `bcc kernel compile <name> -o out.wat` and `bcc kernel run
<name>` run them as the commands above run a file. `lake exe bcc-counts --kernel <name>` counts
one.

## Scripts

| script | checks |
|---|---|
| `scripts/parse-corpus.sh` | every corpus file parses and round-trips; each `corpus/fail/` file fails with its expected message |
| `scripts/check-corpus.sh` | every corpus file checks; each `corpus/reject/` file is rejected with its expected message |
| `scripts/check-elab.sh` | every checked corpus program and sugar pair has a fully typed IR that lowers back to the elaborated program; each `corpus/tir/*.tir` matches `bcc tir` |
| `scripts/compile-corpus.sh` | every corpus `main` gives the same value compiled and interpreted, with `live 0`; its counts are at most its entry in `corpus/counts.expected` |
| `scripts/compile-kernel.sh` | every kernel program gives the same value at every stage and in WebAssembly, with `live 0`; its counts are at most its entry in `corpus/kernel-counts.expected` |
| `scripts/compile-scaling.sh` | compile time against program size; with `--guard`, the 8× program compiles within a bound times the 1× program's time |
| `scripts/check-sugar.sh` | for every `corpus/sugar/` pair, the sugared program and its hand-written core form check and erase to the same term |
| `scripts/book-doctest.sh` | every `bc` block in `book/src/` checks and prints its `-- answer:` with `live 0`, or is rejected with its `-- expect:` message |
| `scripts/check-hygiene.sh` | no `sorry`, `axiom`, `native_decide`, `partial` and the like; every declaration's axioms within the standard three |
| `scripts/AxiomCheck.lean` | prints the axioms of the theorems `SPEC.md` names (`lake env lean scripts/AxiomCheck.lean`) |

`scripts/ci-local.sh` runs all of them, after `lake build`, and `mdbook build book` when `mdbook`
is installed, the independent ones at once. It is the gate: run it before opening or merging a
pull request. `scripts/ci-local.sh --changed` runs only the steps that the changes since
origin/main reach (none of the Lean steps unless a `.lean` file changed): it is for iteration,
and does not replace the full gate. There is no hosted
CI; `.github/workflows/ci.yml` runs only when started by hand.

## Writing a corpus program

A corpus program lives in `corpus/`, and its `main` should have a **falsifier observable**: an
answer that plausible wrong implementations cannot produce. For example, `a - b` with `a ≠ b`
catches swapped operands, and two stores read back in order catch index-blindness. A rejected
program lives in `corpus/reject/` with an `-- expect:` line giving its error.
