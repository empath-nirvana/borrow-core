# Introduction

This notebook is a research project, not a spec. Its job is to map the space of effect systems that can sit on the BoLo borrow calculus: which properties we want, what each costs, which options exist, and what the evidence says. The spec and its trade-offs are decided afterwards, from this map.

borrow-core already works, and it does a lot with effects (see [What works today](foundations/kernel-today.md)). The question is what end state we are building towards, and how to judge progress against it.

**How to read it.**
- [The register](register.md) is the global view. It has one row per property, with its status and what it depends on.
- Each property has its own chapter, laid out the same way: statement, why it matters, the design space, the evidence we have, the experiments, the trade-offs, and the open questions.
- [Design space](design-space/axes.md) lists the axes the properties are traded along.
- [Track log](tracks/log.md) records every experiment and which property it serves.

**Status words.**
- **stated:** a precise statement exists. Its Lean target is noted when it exists.
- **evidence:** some Lean bears on it, at a world short of the target.
- **proved at σ=[]:** proved at Core's relation today.
- **proved at W:** proved at the full world.
- **blocked:** a machine-checked obstruction exists, as an elaborating `def … : Prop` or a discharged configuration that arises.
- **open:** nothing yet.

**Worlds.** Every result names where it holds:
- **Core σ=[]:** the kernel relation at the empty lend stack.
- **W:** the full Kripke world.
- **GE:** a GhostEnd relation.
- **SIB:** the EffModelRel sibling calculus.
- **PAPER:** a paper-level encoding.
- **probe:** a draft definition in `experiments/`.

**Shared context.** Agents working on any track read [`docs/effects-state/BRIEF.md`](../../../docs/effects-state/BRIEF.md) first.
