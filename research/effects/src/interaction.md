# Where the two systems meet

The interaction is the only place System A and System B touch. It consists of rules for how suspensions, handlers and drops behave in the resource world, plus one combined theorem.

**The combined theorem ([P1](properties/soundness.md)).** The composite satisfies System A's properties and System B's guarantees together. In Lean ([`experiments/Targets/RESTRUCTURE.md`](../../../experiments/Targets/RESTRUCTURE.md) §3.5) it is `I.Combined RF J M Adm c`, which holds:
- A's properties at our instance, at every admissible effect context;
- B's guarantees (`B.Guarantees`);
- how rows are read in the world (`Bounds`), and what the world reaches (`Interface`);
- what the composite's typing must contain (`Pins`, with I4);
- the composite's programs and rejections (`Accepts`, `Rejects`).

Tier 1 and tier 2 are the same theorem over different typing rules.

**The interface:**
- [I1](properties/i1-suspension-value.md): a suspension is a value of the resource world.
- [I2](properties/i2-capture-resume.md): capture and resume preserve the invariant, including spanning lends. This is a preservation statement. Read through [freeze as a binder](foundations/freeze-binder.md), it is equivariance.
- [I3](properties/i3-drop.md): drop finalises exactly once.
- [I4](properties/i4-answering-borrows.md): answering effects are borrows. This is one place where the two systems may overlap.
- [I5](properties/i5-capture-laws.md): the capture laws β, η and hiding.

**Side conditions** that make the interface provable:
- [P9 Lifetime soundness](properties/lifetimes.md)
- [P10 Exclusivity across the handler](properties/exclusivity.md)
- [P14 Well-bracketing conservativity](properties/conservativity.md)

**No option of OQ-8 or OQ-9 is picked.** A conjunct of done may read the world only where every option can meet it. The world-level forms of I1, I2, I3 and I5, P11, and the conservativity statements each fix an option, so they form the **proof device**, beside done: a route to done's world conjuncts, not a requirement.

**Overlap or orthogonality is a question, not a premise.** Realising System A out of System B's primitives may make some interface rules free. Keeping the systems separate is what lets that be asked properly.
