# The BoLo machinery

The full table is [`docs/effects-state/06-bolo-machinery.md`](../../../../docs/effects-state/06-bolo-machinery.md).

- **The resource algebra:** `Life = ℕᵒᵈ` and ⦇ρ⦈.
- **↭:** 6.48 (framing) and 6.49 (transitivity).
- **И freshness** (6.108–6.112).
- **The typed world** `TW` with `TI`/`TW.inv`. These are the resources that arise.
- **Frames:** Imm Frame 6.64, Mut Frame 6.65, Anti Frame 6.66, and the reborrow rule 6.150 (whose chooser `RebChooseTW` is ours).
- **Outlives** 6.60, the borrow constants 6.172–6.176, and the fundamental property 6.151.

**The first rule.** The effect calculus changes these definitions where effects interact with them. Every borrow guarantee is re-proved for effectful programs.
