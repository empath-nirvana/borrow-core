# Roadmap

## Async and generators under decision 71

T1 is the permanent rule (decision 71, SPEC §19): owned across suspensions, borrowed within. No
borrow is held across an `await`, a `yield`, a resuming operation or a loop's tick. Lifting it is
closed ([`docs/tombstones/lends-across-suspensions.md`](tombstones/lends-across-suspensions.md)),
so the async and generator work goes on inside the rule:

- **The surface `await` (#750, unit B)** is built under the rule. A task owns what it keeps across
  an `await`, ends each borrow before it, or is lent a place from outside its scheduler
  (`spawn_in`/`run_in`, SPEC §32). R1 (SPEC §29) stays as it is, frozen; nothing in unit B widens
  it or `PinLaw`.
- **Generators** own their data or iterate by index. A generator over a text or an array takes
  the owned value (or a persistent one, such as a literal) and hands it back when it finishes, or
  is given an index and lent the source within one step; a `for` over data stays a counted loop
  (SPEC §16). LoopLend's per-observation lend (SPEC §14) is kept for borrow blocks over loops.
- **I/O for `Net` (#597)** uses owned buffers: a read or write moves the buffer into the
  operation and gets it back with the result, so no borrow of the buffer is held while the
  operation is pending.

Each program that the rule refuses is rewritten in one of these idioms, or kept in
`corpus/reject/` with a message that names the fix.
