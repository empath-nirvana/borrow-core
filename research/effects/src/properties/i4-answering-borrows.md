# P6 I4: answering effects are borrows

## Statement

A handler of an answering (tail-resumptive) effect lends a capability to its body for the body's extent. Performing an operation is a call on a reborrow of it.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.I4a` (§5); the rejections I4.b are stated and outside the first pass; the relation to `hnd` with answering clauses is `Targets.I4Typing` (unary: a typed control form has a typed borrow form, on the spine where capability passing is defined) and `Targets.I4c` (binary), both beside done. In Lean: `Targets.I4a` is PROVED AT A RESTRICTION, for Core's typing at abortive rows (`i4a_tier1`), with the lend's variable fresh for `Δ`'s bounds and `Γ`'s live types (DESIGN §Corrections C4); OPEN at the end state. `Targets.I4Typing` and `Targets.I4c` are stated and OPEN.

## Why it matters

Survey A5's reborrow encoding and decision 1; Effekt and System C; Jane Street's `handled_effect`.

## Design space

- **One mechanism:** an answering handler is a tail-resumptive `[handle]`.
- **Two mechanisms under one protocol** (OQ-1).

## Evidence

`translate_typed`, `handle_is_shift`, `effect_safety` in `experiments/HandlersAsBorrows` (PAPER); `Core/Handlers.lean` (run facts only).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

If it holds, zero-cost lowering for answering effects comes for free.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
