# Well-bracketed control and T1

A program is well-bracketed if every called function returns before its caller resumes (Timany, Guéneau & Birkedal 2024). BoLo's proofs assume it.

In our kernel, two conjuncts of `wpG`'s stop carry that assumption together:
- **T1** (`Core/EffDefs.lean:40`): at every stop, the open Imm (6.64) frames and the record list are the same as at entry.
- **`↭`** (`ResU.UpdV ρ π`, conjunct 37): forbids a run ending with a new `mut` cell, so a Mut (6.65) lend cannot span a stop. T1 alone does not stop it, because a 6.65 lend leaves the frame and record lists unchanged.

This is checked in Lean (the targets library's `Restricted/RunEnd.lean`, using LoopBorrow's `not_upd_of_new_mut`).

- **Tier 1** keeps T1, and is well-bracketed by construction.
- **Tier 2** gives up T1, and changes the update relation at a stop, for lends that span a suspension. What is then given up, and for which operation classes, is P14.
