# P11 Handler correctness

## Statement

A handler means what its clauses say: initiality of the handler as a model, plus the unary laws (return, operation, forwarding, the tail-resumptive law, graded algebraicity).

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Plotkin–Pretnar; Kammar–Plotkin (effect-dependent laws).

## Design space

- **Initiality only,** or **initiality plus laws.**
- **Fusion,** which is binary and out of the first pass.

## Evidence

`ewp_handle` (Core σ=[]); every law in EffModelRel (SIB).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

These are the laws that justify the erased lowering.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
