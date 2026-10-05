# P12 Abstraction safety

## Statement

There is no accidental handling: a handler cannot intercept effects of code it was handed abstractly, and handler state is representation-independent.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Zhang–Myers 2019 (tunnelling); Biernacki et al. 2018 and 2019; capabilities (System C).

## Design space

- **Binary,** via parametricity.
- **By construction,** via lexical capabilities and second-class values.

## Evidence

None in Core. Decision 57 site freshness is checked by the elaborator.

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

It is a binary property, so its scope needs a decision.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
