# Well-bracketed control and T1

A program is well-bracketed if every called function returns before its caller resumes (Timany, Guéneau & Birkedal 2024). BoLo's proofs assume it.

In our kernel that assumption is T1, the lexical stop at `Core/EffDefs.lean:40`. At every stop, the open frames and the record list are the same as at entry, so no internal lend spans a suspension.

- **Tier 1** keeps T1, and is well-bracketed by construction.
- **Tier 2** gives T1 up for lends that span a suspension. What is then given up, and for which operation classes, is P14.
