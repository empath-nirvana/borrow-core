# Pipeline

```
file.bc ──parse──▶ AST ──check──▶ Expr + proof of CDerives ──compile──▶ .wat ──wasmtime──▶ result
```

| stage | code | command |
|---|---|---|
| parse | `Frontend/Lexer.lean`, `Frontend/Parser.lean` | `lake exe bcc parse file.bc` |
| check | `Frontend/Check/` | `lake exe bcc check file.bc` |
| compile | `Backend/` (closure IR → flat IR → Wasm AST → WAT) | `lake exe bcc compile file.bc -o out.wat` |
| run | wasmtime, with tail calls | `lake exe bcc run file.bc` |
| interpret | `Support`'s interpreter, or a backend stage's | `lake exe bcc interp [--stage source\|clos\|flat] file.bc` |

The check stage also inserts the destructor of every owned value that a path leaves unused (SPEC
§12), so the `Expr` it hands on consumes each value exactly once, and the compiler lowers the
inserted calls as ordinary code.

Every command that runs a program prints the value, then `live N`, the number of objects still
allocated. `live 0` is the leak check.

## Scripts

| script | checks |
|---|---|
| `scripts/parse-corpus.sh` | every corpus file parses and round-trips; each `corpus/fail/` file fails with its expected message |
| `scripts/check-corpus.sh` | every corpus file checks; each `corpus/reject/` file is rejected with its expected message |
| `scripts/compile-corpus.sh` | every corpus `main` gives the same value compiled and interpreted, with `live 0` |
| `scripts/check-hygiene.sh` | no `sorry`, `axiom`, `native_decide`, `partial` and the like; every declaration's axioms within the standard three |

CI runs all of them on every push and pull request (`.github/workflows/ci.yml`).

## Writing a corpus program

A corpus program lives in `corpus/`, and its `main` should have a **falsifier observable**: an
answer that plausible wrong implementations cannot produce. For example, `a - b` with `a ≠ b`
catches swapped operands, and two stores read back in order catch index-blindness. A rejected
program lives in `corpus/reject/` with an `-- expect:` line giving its error.
