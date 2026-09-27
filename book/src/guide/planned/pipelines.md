# Pipelines and `for`

**Planned: #59** (with #48 and #17).

Today a chain of stream or iterator operations is written as nested applications, and consuming
an iterator is written as an explicit sequence of `.1` observations (see
[Codata](../codata.md)). The plan:

- `|>` pipelines for chains of iterator and stream operations.
- `for x in it { … }`, sugar for a `for_each` consumer over an iterator. This is the one
  concession to loop syntax: recursion stays structured (folds, `delay` loops, codata), and
  there is no general direct recursion ([Design decisions](../../decisions.md), 24).
- A minimal `include`/prelude, so programs can share a standard library written in the core
  syntax: the iterator adapters (`map`, `filter`, `take`, …) as library code over `iter`, not new
  type formers.

Sugar desugars to the core syntax before checking, so it adds nothing to the trusted base.
