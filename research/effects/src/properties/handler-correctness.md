# P11 Handler correctness

## Statement

A handler means what its clauses say: initiality of the handler as a model, plus the unary laws (return, operation, forwarding, the tail-resumptive law, graded algebraicity, η).

**Where each law is stated.**
- **In done, S4 `HandlerSem`** (reductions up to store-keeping steps): return, the resuming and the abortive catch, deep resume, cancel, and the two finaliser laws. Forwarding is the structural fact `KontLaws` (a handler frame of `l` catches `l` only). Algebraicity in reduction form is built into S3 (`StopsIn` holds under bind frames).
- **Beside done, `A.UnaryLaws`** (`experiments/Targets/Targets/A/UnaryLaws.lean`), STATED, not proved: the tail-resumptive law `TailLaw`, algebraicity graded by continuation class `AlgLaw` (resuming operations; the abortive case is S4's finaliser conjuncts), and η with a frame that holds the continuation `EtaHold` (effects TR D13.7, T13.8 (b)); `EtaLin` is η's typing-restricted alternative (TR L13.5), and `etaLin_of_etaHold` is PROVED. They are unary at the run level (P11/I5 menu form F.3): two configurations with the same complete runs' answers and traces, in every evaluation context of a configuration a typed closed program reaches. `TailLaw`'s hygiene is three explicit hypotheses: the clause's operations are not caught by `K`'s frames, not by the handler (which Core's `[handle]` premise `n ∉ Σ` appears to supply; not checked), and `K` holds no finaliser unless the clause's operations are all linear. Each fails at an instance whose handler or bind ignores its clauses (`not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy`, `not_etaLin_toy`, PROVED). They are **not** conjuncts of S4 or of done; whether they join done is a menu choice (P11/I5 menu axes H, F, K), for the user.
- **Binary:** A₂ `HandlerLaws` (tail and algebraicity among them; no η), and over Core `Laws` (`LawTail`, `LawAlg`, `CapEta` for η in renaming form). Stated, OPEN, out of the first pass.

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
