# How this notebook works

**One track per property.** A track researches and experiments on one property: its literature, then a probe, then a proof. It runs in its own worktree and `experiments/` directory, and its brief carries only that property's slice plus the shared brief. When a track runs into something that belongs to another property, it records a dependency in [the register](register.md). It does not wander off to fix it.

**Deep, not broad.** Each track is a small, self-contained unit:
- a deep designer;
- adversarial review of the statements before anything is built;
- one deep builder;
- adversarial verification;
- an entry in the [track log](tracks/log.md).

**Choosing the next track.** The choice follows an explicit rule, never "whatever looks tractable":
1. Among properties whose statement is agreed, pick the one the most other properties depend on.
2. Break ties by risk: the larger unknown goes first.

**What counts as done.** A property is done when its Lean target holds at W with no `sorry`, as a conjunct of the end state `EndStateAt J₂ W` ([`experiments/Targets/DESIGN.md`](../../../experiments/Targets/DESIGN.md) §1.0), at the same world and typing system as every other conjunct. Done names its world `W` and passes the step-index audit of `W`'s definition (§4.4), because no step-indexing is a property of a definition, not of the laws. Targets beside done (the freeze binder, conservativity at every type) are recorded but do not decide it. Prose results are evidence, not status.

**What an obstruction is.** An obstruction is reported only as an elaborating `def … : Prop`, or as a Lean configuration with every hypothesis discharged whose counterexample arises in `TW`. Otherwise the report says "not derived, and no obstruction verified".

**No GitHub issues.** No issues are filed until the user has agreed the spec. Open questions live in the chapters, never as issues.
