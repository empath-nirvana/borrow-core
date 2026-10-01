# Pipelines

**Planned: #17** (with #59 and #48).

What exists today:

- `for x in V { … }` over counts, arrays, views, sized iterators and generators, with `break`,
  `continue`, `return` and `else` (SPEC §16; see [Generators](../generators.md) and
  [Divergence](../divergence.md)).
- Iterator adapters as library code, not new type formers: `map`, `filter`, `take`, `skip`,
  `enumerate`, `chain`, `flat_map`, `zip`, `scan` and others are generic generators in
  `lib/adapters.bc` (SPEC §15), and sized iterators are in `lib/iters.bc`.
- A prelude in scope in every program, and `include` for the other library modules
  (`include buf`, `include text`, …).

A chain of adapters is written today as nested applications, such as `take(map(it, f), 3)`. The
plan is a `|>` pipeline for such chains, read left to right, as syntactic sugar over those
applications. The spelling is not final.

Sugar desugars to core before checking, so it adds nothing to the trusted base.
