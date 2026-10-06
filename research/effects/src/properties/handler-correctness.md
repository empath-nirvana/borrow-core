# P11 Handler correctness

## Statement

A handler means what its clauses say: initiality of the handler as a model, plus the unary laws (return, operation, forwarding, the tail-resumptive law, graded algebraicity).

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §1.5, §3.7: A's S4 `HandlerSem`, in done: the handler's return, operation and unwind steps, deep resume and cancel of a captured continuation, and finalisation, each in every context up to administrative steps. At the world, P11 (`HandleCompat ∧ RedLaws`) is the proof device's, beside done. The equational laws are A₂ `HandlerLaws` (binary, at A's contextual approximation) and, over Core, `Laws` (hiding under a simulation of answering handlers' states, fusion at a composite-handler parameter, OQ-49). In Lean: S4 at our instance is OPEN (`handlerSem_ourInst` is not built). `P11 coreW` is PROVED AT σ=[] (`p11_core`), and `RedLaws` holds at every world whose operation tables are monotone (`redLaws_of_mono`). The binary laws are stated and OPEN (out of the first pass).

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
