---
name: Feature
about: A language feature, from spec entry to compiled corpus program
labels: ''
---

## What

<!-- The feature, in a sentence or two. Link the design discussion or experiment if any. -->

## Definition of done

- [ ] **Spec**: a `SPEC.md` entry (or change) says what the feature is.
- [ ] **Core**: rules in `Core/`, with `fundamentalC` and `adequacyC` extended; no `sorry`; axioms within `[propext, Classical.choice, Quot.sound]`.
- [ ] **Checker**: `bcc check` produces derivations for it (incompleteness, if any, recorded in `Frontend/README.md`).
- [ ] **Backend**: lowered by the compiler.
- [ ] **Corpus**: a program with a falsifier observable, giving the same answer under `bcc interp` and `bcc run`, with `live 0`.
- [ ] **Local CI** (`scripts/ci-local.sh`) passes: build, hygiene, axioms, parse/check/compile corpus, book doc-tests.
