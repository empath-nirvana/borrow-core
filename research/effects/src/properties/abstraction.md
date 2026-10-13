# P12 Abstraction safety

## Statement

There is no accidental handling: a handler cannot intercept effects of code it was handed abstractly, and handler state is representation-independent.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §1.6, §1.7: in done, E6 (`Tunnel`, unary): a function that handles a label of its own, written once, serves a callback at every row without that label, and the callback's own raise of another label escapes it (Zhang–Myers Example 1, in the shape `∀α. (N → [N]α) → [N]α`, `PolyUseLacks`). The binary form is A₂'s `Abstraction` (`Tunnel`, `RepInd`, `Encap`), out of the first pass, and its form over Core is stated in `Targets/Instance/Binary.lean`. In Lean: E6 needs effect polymorphism, at every instance (`not_tunnel_of_monoCallback`, PROVED); E6 at our instance is OPEN; the binary forms are stated and OPEN. Their proof device, T3 from a binary fundamental lemma, is named-only.

## Why it matters

Zhang–Myers 2019 (tunnelling); Biernacki et al. 2018 and 2019; capabilities (System C).

## Design space

- **Binary,** via parametricity.
- **By construction,** via lexical capabilities and second-class values.

## Evidence

None in Core. Decision 57 site freshness: decided; to be checked by the elaborator (not built).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

It is a binary property, so its scope needs a decision.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
