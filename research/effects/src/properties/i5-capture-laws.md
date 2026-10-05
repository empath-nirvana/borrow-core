# P7 I5: the capture laws

## Statement

- **β for capture:** freezing then resuming is the identity.
- **η for capture:** the forwarding handler is the identity.
- **Hiding:** a body cannot observe a handler's state except through its operations. This is the anti-frame read relationally.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Plotkin–Pretnar; the effects TR §13 (the adjunction, by hand).

## Design space

- **Unary forms** over the kernel's wp.
- **Binary forms:** optional unless safety needs them.

## Evidence

Proved in EffModelRel (SIB). P13.14 is computed by hand (PAPER).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Hiding is the relational content of 6.66.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
