# The effect calculus: specification

The specification of borrow-core's effect calculus, written before any kernel work. It is one
calculus: effects as models and comodels of one signature, interpreted by one protocol table,
over one Kripke world on BoLo's resource model, with its equational theory and metatheory.
Every open question is boxed and numbered in [99-open-questions.md](99-open-questions.md).

Tracking issue: #290. Input: [the effects audit](../effects-audit.md) (#288).

## Contents

| file | contents | owns |
|---|---|---|
| [00-structure.md](00-structure.md) | the objects and notation, every id, the SPEC entries, the index of open questions, the named restrictions, the section contract | O-*, E-* (index), R-* |
| [01-scope.md](01-scope.md) | what the calculus is; what is in it by design; what is outside the proofs; the user's decisions at their strength; tier 1 and tier 2 as properties of the calculus; the "not an approximation" checklist | C-1 to C-12 |
| [02-signatures.md](02-signatures.md) | signatures, qualifiers as grades, names, rows as sums, interpretation, theories, renaming; the form of models and comodels; sum, tensor and threads | K-SIG, K-ROW, K-NAME, K-INT, K-THEORY, K-REN, K-MODEL, K-COMODEL |
| [03-statics.md](03-statics.md) | the types and typing rules: operations, sequencing, finalisers, handlers, continuations, capabilities, `withswap`, the row-generic borrows, `bounded_fix`, effectful codata, divergence, host capabilities, grades, stored continuations; the full constructs behind every named restriction (scoped operations, handling around div, carriers, borrowed answers, allocation, row abstraction, shallow handlers, finalisers at a resuming row, owned abortive payloads, the relevant qualifier, effectful co-operations, self-referential signatures, folds at a row, generative instances, the excluded negative recursion) | K-FTY, K-OP, K-RAISE, K-LET, K-THEN, K-HND, K-KONT, K-GEN, K-CAP, K-SWAP, K-BOR, K-FIX, K-NU, K-DIV, K-HOST, K-GRADE, K-SCOPE, K-HDIV, K-CARRIER, K-BORANS, K-ALLOC, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-FOLDΣ, K-GENNAME, K-NEGREC |
| [04-dynamics.md](04-dynamics.md) | the machine: contexts, head steps, cancellation, runs, determinism; the paths of a captured continuation; the erasure obligations | K-CTX, K-STEP, K-CANCEL, K-RUN |
| [05-model.md](05-model.md) | the world `W = (ρ, ls, σ)` and its order, arising, `wpG` and the stop condition, tables and `TableOK`, `ewp` and the partial-correctness `ewpP` (under OQ-15 (b)), the relation, models and comodels semantically; the model lemmas; the probes of OQ-9, OQ-44 and OQ-58 | D-*, T-MONO, T-NIL, T-STOP, T-ARISE, T-FRAME, T-SUMOK, T-MODEL, T-COMODEL, T-DEF |
| [06-laws.md](06-laws.md) | the equalities the laws are stated in; the base laws (β, η, the monad laws of `to`); algebraicity, handler laws, theory laws (exceptions, state, generators, asynchrony, nondeterminism, folds), sum and tensor, the effect-dependent laws of rows (discard, copy, commute), running against a comodel, linear laws, β/η/hiding, names, borrows and lowering | O-EQ, L-*, T-SI1, T-SI2 |
| [07-metatheory.md](07-metatheory.md) | compatibility, the fundamental property at `W`, adequacy, effect safety, leak freedom, finalisation, linear use, T1 and its lifting, preservation, determinism, renaming, the binary results | T-COMPAT, T-FP, T-ADEQ, T-SAFE, T-LEAK, T-FIN, T-LIN, T-T1, T-T2, T-PRES, T-DET, T-REN, T-NAH, T-ABS, T-TOTAL, T-2RUN, T-BINFP, T-SOUND |
| [08-correspondence.md](08-correspondence.md) | every id against the code and its fate; the SPEC entries, each drafted, and the decisions affected; the surface elaboration; the lowering; threads; the completeness check | T-CONS, T-ELAB, T-LOWER, E-* |
| [99-open-questions.md](99-open-questions.md) | the register: every open question boxed, with its tags, cross-references, what it blocks, what settles it and its default; the table of every question; indexes by tag, by the absence of a default, and by the audit's and the critic's numbering | OQ-* |

## Reading order

00, then 01. 02 to 05 define the calculus; 06 and 07 state what holds of it; 08 relates it to
the code; 99 lists what is open. An id is defined in the file that owns it and only cited
elsewhere.

## Open questions

The register is [99-open-questions.md](99-open-questions.md). Questions tagged
**[user decision]** need the user; **[settle by proof]** and **[settle by literature]** are
settled by a named Lean statement, a configuration, or a source read. The audit's Q1-Q7 are
OQ-1 to OQ-7. The first unknown is OQ-9, whose first probe is one Lean configuration at
`[handle]` + cancel over an open 6.64 frame (05 §12.1); beside it runs OQ-58's probe, whether Core
is the `σ = []` instance at `U` (05 T-NIL). Every default that narrows the calculus is a named
restriction (00 §7.2), and the full construct behind each restriction of a construct is written in
03 §9. Two restrictions defer constructs the user decided, a handler spanning observations of a
div computation (R-HDIV, U5) and allocation as an effect (R-ALLOCORACLE, U20): both constructs are
in the calculus, and only their lift waits on a proof (OQ-67, OQ-68). The questions with no default, whose blocked work does not start until they are settled, are
OQ-8 (the re-index), OQ-58 (Core as the `σ = []` instance) and OQ-59 (handling inside a
scope); 99 §3 lists them with the rest of the indexes.
