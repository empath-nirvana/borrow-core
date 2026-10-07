# Summary

[Introduction](intro.md)
[How this notebook works](method.md)
[The register](register.md)
[Synthesis: coherent designs](synthesis.md)

# Ground rules

- [Decided constraints](decisions.md)

# Foundations

- [What works today](foundations/kernel-today.md)
- [The BoLo machinery](foundations/bolo.md)
- [Freeze as a binder](foundations/freeze-binder.md)
- [Linearity, not affinity](foundations/linearity.md)
- [Second-class values](foundations/second-class.md)
- [Well-bracketed control and T1](foundations/well-bracketing.md)

# System A: the effect system

- [The effect system on its own](system-a.md)
  - [P2 Effect safety](properties/effect-safety.md)
  - [P8 Continuation linearity](properties/continuation-linearity.md)
  - [P11 Handler correctness](properties/handler-correctness.md)
  - [P12 Abstraction safety](properties/abstraction.md)
  - [P13 Zero-cost lowering](properties/zero-cost.md)
  - [Multi-shot (side question, not a goal)](side/multi-shot.md)

# System B: the borrow calculus

- [BoLo's guarantees](system-b.md)

# The interaction

- [Where the two systems meet](interaction.md)
  - [P1 The combined theorem](properties/soundness.md)
  - [P3 I1: a suspension is a value](properties/i1-suspension-value.md)
  - [P4 I2: capture and resume preserve the invariant](properties/i2-capture-resume.md)
  - [P5 I3: drop finalises exactly once](properties/i3-drop.md)
  - [P6 I4: answering effects are borrows](properties/i4-answering-borrows.md)
  - [P7 I5: the capture laws](properties/i5-capture-laws.md)
  - [P9 Lifetime soundness](properties/lifetimes.md)
  - [P10 Exclusivity across the handler](properties/exclusivity.md)
  - [P14 Well-bracketing conservativity](properties/conservativity.md)

# Prior art (menus)

- [P2 Effect safety and the row algebra](prior-art/p2-effect-safety.md)
- [P8/P5 Linearity, drop and finalisation](prior-art/p8-p5-linearity-drop.md)
- [I2 Capture and resume](prior-art/i2-capture-resume.md)
- [P10/P9 Exclusivity and lifetimes](prior-art/p10-p9-exclusivity-lifetimes.md)
- [P11/I5 Handler correctness and the capture laws](prior-art/p11-i5-laws.md)
- [P12 Abstraction safety](prior-art/p12-abstraction.md)
- [Rows vs capabilities](prior-art/rows-vs-capabilities.md)
- [P13 Zero-cost lowering](prior-art/p13-zero-cost.md)
- [P14, I1, I4 Interaction](prior-art/p14-i1-i4-interaction.md)

# Design space

- [Axes and options](design-space/axes.md)

# Tracks

- [Track log](tracks/log.md)
- [WorldW batch 1: open frames](tracks/worldw-batch1.md)

# Sources

- [Literature](literature.md)
