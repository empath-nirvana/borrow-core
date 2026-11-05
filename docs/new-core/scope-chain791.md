# Scope: #791 over the chain relation per task, plus the pool

Branch `chain-791`, from `origin/tree-core` (35fc7c0e).

## Target

`OrDiverges` for #791's hardest case, proved over Core's step-indexed chain relation per task
(`erwp`, `cerwp`, the Mut Frame and Anti-Frame across stops), with tasks related by the pool
invariant (`PoolTJ`'s design, #817):

- a task holds a `mut` reborrow of a boxed field of its borrowed record, two levels deep, across
  a `park`;
- another task opens and ends its own lend meanwhile;
- the first task is resumed, and everything ends with memory empty;
- separately, the same with the parked task cancelled.

The new constants of `goal-791` (`Row.Suspend`, the field reborrow) are data. No new judgment.

## Kill criteria (fixed in advance)

- **A.** A needed chain theorem does not exist, has a `sorry` or axiom, or proves less than
  claimed: stop, and name it and what it would take.
- **B.** The graft scenario (a task opens a lend `α` and suspends; the handler opens its own lend
  `β` and resumes the continuation inside `β`) is not provable as a program over the chain
  relation: build the reachable configuration where the chain relation fails, and stop.
- **C.** A build step fails: stop with the configuration and the exact step. No added hypotheses,
  no fences without the user's approval; conditions are accepted only as decidable conditions on
  types or rules.
- Anything unexpected is stated as an elaborating `def … : Prop` and reported, not explored.

## Status and next step

See the end of this file; it is kept current at each clean commit.
