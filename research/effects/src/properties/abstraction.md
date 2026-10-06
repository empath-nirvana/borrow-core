# P12 Abstraction safety

## Statement

There is no accidental handling: a handler cannot intercept effects of code it was handed abstractly, and handler state is representation-independent.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.Abstraction` (§3, T3): `Tunnel` (Zhang–Myers Example 1 over a row-polymorphic `f`), `RepInd`, `Encap`. Binary, out of the first pass. In Lean: `Targets.Abstraction` with `Tunnel`, `RepInd` and `Encap` (`experiments/Targets/Targets/Statements/Abstraction.lean`), stated and elaborating; OPEN (binary, out of the first pass). Its proof device, T3 from a binary fundamental lemma, is named-only.

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
