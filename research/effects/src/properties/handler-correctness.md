# P11 Handler correctness

## Statement

A handler means what its clauses say: initiality of the handler as a model, plus the unary laws (return, operation, forwarding, the tail-resumptive law, graded algebraicity).

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.P11` (§6), unary, a conjunct of the end state; the equational laws are `Targets.Laws` (§3, T2), with hiding stated under a simulation of answering handlers' states and fusion at a composite-handler parameter (OQ-49). In Lean: `Targets.P11` (`HandleCompat ∧ RedLaws`) is PROVED AT σ=[] (`p11_core`), OPEN at W; `RedLaws` holds at every world whose operation tables are monotone (`redLaws_of_mono`). `Targets.Laws` is stated and OPEN (binary, out of the first pass).

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
