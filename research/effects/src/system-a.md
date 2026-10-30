# System A: the effect system on its own

> "we need an effect system that satisfies the effect algebra and a borrow calculus that satisfies BoLo's guarantees and the rules for their interaction." (user, 2026-10-05)

System A is judged on its own terms, with no borrows in sight. Its properties are stated over **any** calculus with effects, in the literature's terms rather than Core's. Our calculus is one instance.

**What System A must say precisely:**
- **Effects:** a signature is a set of operations, each with arities and a continuation qualifier.
- **Rows:** a row is a sum of signatures with an optional row variable. Row variables are in the kernel (decision 62). The row algebra must meet the Yoshioka conditions (see [P2](properties/effect-safety.md)).
- **Handlers:** a handler is a model of a signature. Handlers are deep.
- **Continuations:** a continuation is must-resume or cancellable. Discarding it is an explicit cancel. Multi-shot is ignored.

**Its properties:**
- [P2 Effect safety](properties/effect-safety.md)
- [P8 Continuation linearity](properties/continuation-linearity.md)
- [P11 Handler correctness](properties/handler-correctness.md): initiality and the unary laws.
- [P12 Abstraction safety](properties/abstraction.md): binary; scope undecided.
- [P13 Zero-cost lowering](properties/zero-cost.md)

The effect algebra itself is also a System A property. Its laws are the binary ones, which are out of the first pass.

**Borrow-derived routes are optional.** "There might be a way to get some effect properties we want by leaning on borrow properties but it's not necessary." (user, 2026-10-05) Where one exists, it is recorded in that property's chapter as a possible realisation, never as a requirement or an assumption. The ones known so far:
- effect safety and no accidental handling, from handlers as lends (HandlersAsBorrows, second-class capabilities);
- finalisation exactly once, from linearity.
