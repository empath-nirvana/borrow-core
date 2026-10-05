# WorldW batch 1: open frames

**Question.** Do open 6.64, 6.65 and 6.66 frames, and a 6.150 record, handed on at a relativised stop close on resume, cancel and drop? And when a handler sits between two lenders (OQ-9, OQ-3)?

**Where:** branch `probe-open-frames` @4e464b5, `experiments/WorldW/` (README, DESIGN, CHECKPOINT). It builds clean, and its 39 results use only the allowed axioms.

**Proved (probe):**
- the resource-level hand-on and exit for 6.64, 6.65 and 6.150;
- coherence of the relaxed update relation, after two corrections, with H16 and the pin (sufficiency only);
- Core embeds into the draft (`ewpTS_ewpW`). The converse, T1 for tier-1 programs, is open;
- distinguishing OQ-3 (a) from (b) needs D-ORD.

**Unfinished:** the main probes `OpenFrame64`, `OpenFrame65`, `OpenFrame66`, `OpenRecord150` and `HandlerBetweenLenders*`.

**Verification.** It failed on overclaims in the prose, not in the Lean. These are now corrected (branch commit after 4e464b5). Still open:
- whether `OpenFrame66` fails;
- whether H16 and the pin are necessary;
- exclusivity at a stop (`HoldsChain`);
- the between-lenders probes.

**For the register:** evidence for P4 and P10 at the probe world.
