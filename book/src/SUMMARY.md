# Summary

[Introduction](introduction.md)

- [Getting started](getting-started.md)

# The language

- [Values, functions and numbers](guide/basics.md)
- [Ownership and borrows](guide/ownership.md)
- [Data and generics](guide/data.md)
- [Errors](guide/errors.md)
- [Input and output](guide/io.md)
- [Iteration](guide/iteration.md)
- [Effects and handlers](guide/effects.md)
- [Async tasks](guide/async.md)

# How it elaborates

- [The core, and `bcc desugar`](elaboration/overview.md)
  - [Values and computations](elaboration/values-and-computations.md)
  - [Cells and borrows](elaboration/ownership-and-borrows.md)
  - [Blocks and families](elaboration/blocks-and-families.md)
  - [Recursive data and folds](elaboration/recursive-data.md)
  - [Codata: iterators, streams, delay](elaboration/codata.md)
  - [Integers and host operations](elaboration/integers.md)
  - [Arrays](elaboration/arrays.md)
  - [Implicit destructors](elaboration/implicit-destructors.md)
  - [Standard I/O as capabilities](elaboration/standard-io.md)
  - [Divergence](elaboration/divergence.md)

# Reference

- [Reading the reference](reference/README.md)
- [Lexical structure](reference/lexical.md)
- [Lifetimes](reference/lifetimes.md)
- [Types and shapes](reference/types.md)
- [Terms](reference/terms.md)
- [Linearity](reference/linearity.md)
- [Constants and signatures](reference/constants.md)
- [Declarations and programs](reference/declarations.md)
- [Checker errors](reference/errors.md)

# About the project

- [Status](status.md)
- [What is proved](proved.md)
- [Contributing](contributing.md)
- [Design decisions](decisions.md)
- [Glossary](glossary.md)
