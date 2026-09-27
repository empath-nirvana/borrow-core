# Effects

**Planned: #18.**

Effects are to be **borrowed capabilities**. A handler provides a capability as a borrow, with the
same callback shape as `withbor`, and the code that uses the effect receives the capability as an
argument. Effect safety would then follow from borrow soundness, with no new judgment. Divergence,
allocation and I/O are candidate capabilities.

The design decisions that constrain it ([Design decisions](../../decisions.md), 15 and 16):

- Shallow handlers are primitive and deep handlers are derived: a suspended computation is
  codata, one observation is a shallow handler, and a deep handler is a fold or a loop.
- Monads stay in the core. The surface is direct style.
