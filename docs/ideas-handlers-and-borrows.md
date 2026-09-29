# Ideas: handlers, classified by what they do with the continuation

Brainstorm, not design. Nothing here is decided or proved. A tentative slogan, recorded
2026-09-29.

## The slogan

> **A stateful handler is a borrow presented through an interface.**

A tail-resumptive handler with state lends that state to a scope, runs each operation against it,
and resumes at once; at the end of the scope it hands the state back. That is a borrow block
(`withbor`) whose operations are functions over the borrow. Spike #100 already found that a borrow
block is a handler with no operations that resumes once, in tail position.

It is one kind of handler, not all of them. Handlers differ in what they do with the continuation
`k`, and each kind appears to land on a mechanism the language already has:

| what the handler does with `k` | examples | mechanism |
|---|---|---|
| resumes once, immediately | state, I/O, maps, logging, clock, allocator, mocks | a borrow |
| resumes once, then does more work | `finally`, transactions, timing a region | a borrow with an epilogue |
| never resumes | exceptions, early exit, cancellation | unwinding (drop the continuation: destructors run, borrows end) |
| stores `k` and resumes once, later | generators, async, coroutines | codata (`k` is the one-shot `U X`) |
| resumes many times | backtracking, nondeterminism | copying `k`; only when what it holds is persistent (`!`) |

Rows 1 and 2 together are what Ahman and Bauer call a **runner**: co-operations run against a
resource and resume exactly once, with initialisation and finalisation around the computation
("Runners in Action", ESOP 2020). A borrow with an epilogue is a runner. On this reading, runners
are not something to add to the language: linearity and borrows already are runners, which is why
they looked unnecessary earlier.

With linearity, the kind of handler is not only a compilation strategy (as in Koka or Effekt), but
also decides what the handler may touch:
- a lend for the first two rows;
- a suspended computation holding resources for the fourth (see `experiments/LoopBorrow`, O1);
- persistent data only for the fifth.

## A second slogan: control effects are value effects with a shift

> **A control effect is a value effect whose continuation is shifted to a value; the grade on that
> value says which control effect it is.**

- **Value effects (rows 1–2).** The operation returns a value and the computation continues; the
  continuation is never reified.
- **Control effects (rows 3–5).** At the operation, the rest of the computation becomes a value
  `U k` (CBPV's `U` shift, which CPS makes explicit; a generator's rest `U X` is one). What
  distinguishes the rows is only how `U k` may be used:

| row | `U k` is | grade |
|---|---|---|
| exceptions, early exit | dropped (destructors run) | 0 |
| generators, async | used once, possibly later | 1 |
| backtracking | used many times; only if `k` is persistent | ω |

**Caveats:**
- Row 2 (a runner with finalisation) wraps code around the continuation without reifying it, so it
  belongs on the value side.
- Exceptions also read with no shift at all, as a positive `A + E` result (data). The grade-0
  reading and the sum reading are two views of the same thing.

## Status

Untested. It came out of the effects/coeffects discussion: Andrew Wagner's remark that
borrowing and effect handling are deeply related, the strict spike's classification (#101) and
the prior-art surveys (#103, #92). If it holds, it is a candidate for the "one picture" of a design
charter. A check would state row 1 precisely: a stateful tail-resumptive handler, compiled as a
borrow block plus direct calls, gives the same runs as its handler semantics. Then check each row
against real effects.
