# Glossary

**BoCa, BoLo** — the paper's calculus and its separation logic. The baseline of `SPEC.md` §1.

**Adequacy** — a closed well-typed program runs to its result and leaves memory empty.

**Block** — an unboxed struct allocated at once as several cells; its handle is the family of its
leaf references (§5).

**CBPV (call-by-push-value)** — a calculus with value types (`1`, `⊗`, `⊕`, `U C`, …) and
computation types (`F A`, `⊸`, `&`, `∀`, …), related by the shifts `U` (thunk) and `F`
(returner).

**`CDerives`** — the typing judgment of the core (`Core/Fundamental.lean`). The checker is derived
from it: every checker step applies one of its rules.

**`close`** — the observation on codata that releases its state; required, because no rule
forgets a thunk.

**Delay (`D A`)** — codata that either returns an `A` or asks to be observed again. Loops that may
not terminate have this type (§7).

**Erasure** — the untyped term (`Expr`) a checked program denotes; what the machine runs and the
compiler compiles.

**Falsifier observable** — a corpus program's answer, chosen so that plausible wrong
implementations produce a different one.

**Family borrow** — borrowing several disjoint places at one lifetime (`withbor_f2`,
`withbor_s`), derived from nested `withbor` and lifetime shortening (§5).

**Fold rules** — `fold_imm` (over a borrow), `fold_own` (consuming), `fold_reuse` (in place,
reusing the consumed cells): recursion over `μ` types as typing rules (§6).

**Fundamental Property** — every well-typed term is semantically typed; the core soundness
theorem.

**Host** — the implementation of the integer operations; every theorem holds for every host (§8).

**Lifetime** — a lexical scope, introduced by a borrow's callback. Lifetimes nest.

**Persistent** — a type whose values hold no resource (`1`, `!A`, `i32`, …); its variables are
copied and dropped freely (§10).

**Place** — a location that can be borrowed: a cell, or a leaf of a block.

**Stream (`Stream A`)** — codata yielding `A`s, with `close` (§7).

**Typed world** — the Kripke world of the logical relation that the Fundamental Property is
proved in.

**Witness** — the resource an `imm`/`mut` cell holds for what it borrows; why a same-lifetime view
through a pointer is not available.
