# P6 I4: answering effects are borrows

## Statement

A handler of an answering (tail-resumptive) effect lends a capability to its body for the body's extent. Performing an operation is a call on a reborrow of it.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

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
