# WorldW batch 1: open frames

**Question.** Do open 6.64, 6.65 and 6.66 frames, and a 6.150 record, handed on at a relativised stop close on resume, cancel and drop? And when a handler sits between two lenders (OQ-9, OQ-3)?

**Where:** branch `probe-open-frames` @4e464b5, `experiments/WorldW/` (README, DESIGN, CHECKPOINT). It builds clean, and its 39 results use only the allowed axioms.

**Proved (probe):**
- the resource-level hand-on and exit for 6.64, 6.65 and 6.150;
- coherence of the relaxed update relation, after two corrections;
- Core as the empty-stack instance (`wpGW_nil`);
- distinguishing OQ-3 (a) from (b) needs D-ORD.

**Unfinished:** the main probes `OpenFrame64`, `OpenFrame65`, `OpenFrame66`, `OpenRecord150` and `HandlerBetweenLenders*`.

**Verification failed.** The write-up overclaims: that 6.66 needs an invariant at stops, and that H16 and the pin are necessary. These need restating as sufficiency, or proving.

**For the register:** evidence for P4 and P10 at the probe world.
