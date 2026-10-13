# System A: the effect system on its own

> "we need an effect system that satisfies the effect algebra and a borrow calculus that satisfies BoLo's guarantees and the rules for their interaction." (user, 2026-10-05)

System A is judged on its own terms, with no borrows in sight. Its properties are stated over **any** calculus with effects, in the literature's terms rather than Core's. Our calculus is one instance.

**What System A must say precisely:**
- **Effects:** a signature is a set of operations, each with arities and a continuation qualifier.
- **Rows:** a row is a sum of signatures with an optional row variable. Row variables are in the kernel (decision 62). The row algebra must meet the Yoshioka conditions (see [P2](properties/effect-safety.md)).
- **Handlers:** a handler is a model of a signature. Handlers are deep.
- **Continuations:** a continuation is linear or affine. Discarding it is an explicit cancel. Multi-shot is ignored.

**Two kinds of property, and done needs both** ([`experiments/Targets/RESTRUCTURE.md`](../../../experiments/Targets/RESTRUCTURE.md) §1.2). In Lean, `Targets/A/*` states them over an abstract `EffectSystem`:
- **(S) soundness**, upper bounds that say nothing goes wrong:
  - S0, the machine's shape and the let law;
  - S1, the row algebra;
  - S2, safety, and termination at data answers;
  - S3, effect safety;
  - S4, the handler laws, deep, in every context;
  - S5, cancellation as SPEC §19 builds it;
  - S6, linear and affine use of continuations, observed from the run.
- **(E) expressiveness**, lower bounds that say what must be accepted and run: E1–E10. Each is a concrete program with its answer and observable trace, or a schema of effect polymorphism (one typing of a higher-order value serves its callback at every row):
  - E1, no colouring;
  - E2, higher-order polymorphism;
  - E3, loops and the runtime's driver;
  - E4, deep handlers;
  - E5, nested handlers;
  - E6, tunnelling;
  - E7 and E8, the cancel and unwind policies;
  - E9, stored continuations;
  - E10, the reconciler.

A decided feature enters A only through an (E) property that needs it. An abstract Lean lemma shows that an instance without the feature fails the property: for example, every instance in which a context type fixes one callback row fails E1, E2, E6 and E10. The targets are read in good faith, as the literature's theorems are.

**Its properties:**
- [P2 Effect safety](properties/effect-safety.md): S1, S3; E6.
- [P8 Continuation linearity](properties/continuation-linearity.md): S6.
- [P11 Handler correctness](properties/handler-correctness.md): S4; the binary laws (A₂), out of the first pass.
- [P12 Abstraction safety](properties/abstraction.md): E6 (unary, in done); the binary form (A₂), scope undecided.
- [P13 Zero-cost lowering](properties/zero-cost.md): A₃, over a fixed target and fixed references, out of the first pass.

The effect algebra itself is also a System A property (S1). Its equational laws are the binary ones, which are out of the first pass.

**Borrow-derived routes are optional.** "There might be a way to get some effect properties we want by leaning on borrow properties but it's not necessary." (user, 2026-10-05) Where one exists, it is recorded in that property's chapter as a possible realisation, never as a requirement or an assumption. The ones known so far:
- effect safety and no accidental handling, from handlers as lends (HandlersAsBorrows, second-class capabilities);
- finalisation exactly once, from linearity.
