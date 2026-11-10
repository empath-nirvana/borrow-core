# borrow-core documentation

Start here. To learn the language, read the book in [`book/`](../book/src/SUMMARY.md), whose
examples are doc-tested. [`SPEC.md`](../SPEC.md) is the precise definition of the language and
the authority on what it is. The core syntax, the elaboration chapters, the theorems and the
contributing rules are in [`internals/`](internals/README.md). The pages below are the design and
research notes behind them.

| page | what it covers |
|---|---|
| [Overview](overview.md) | what the language is, what is proved, and what is trusted |
| [Roadmap](roadmap.md) | where the work goes next, with the issue for each item |
| [Pipeline](pipeline.md) | from a `.bc` file to WebAssembly or native code: the `bcc` commands and the scripts |
| [Glossary](glossary.md) | the terms used across the spec, the code and the docs |
| [Design decisions](decisions.md) | what was chosen, and why, newest last |
| [Theory index](theory-index.md) | every experiment and theoretical note: its question, its answer, its Lean names, and the open problems |

## Reference

- [Core syntax](syntax-core.md): the textual form the parser and the checker accept.
- [Typed elaboration](typed-elaboration.md): how the surface is elaborated to the core on
  inferred types.
- [`Core/README.md`](../Core/README.md), [`Frontend/README.md`](../Frontend/README.md),
  [`Backend/README.md`](../Backend/README.md): each part of the code, in detail.
- [Adjudications](adjudications.md): where the transcription of the paper (`Paper/`) needs an
  argument to read its printed text.
- [Kernel usage](kernel-usage.md): which kernel rules, constants and type formers the checked
  corpus produces, and which the backend reads.

## The kernel

- [The new Core: target structure](new-core/structure.md): the target theorem and how the
  relation is built.
- [The chain interpretation](new-core/chain-interpretation.md): the relation on `main`, with
  borrows held across a suspension, what is proved and what is open.
- [Where proof ends and assertion begins](new-core/assert-boundary.md): the analysis behind the
  named assertion `HandlerLawN`, and how to shrink it (#838).
- [Conditions](new-core/conditions.md), [evidence](new-core/evidence.md) and
  [configurations](new-core/configurations.md): the numbered conditions and gaps, the Lean names
  for each, and the configurations checked against the assertion.
- The working tables of #835: [qualifier](new-core/scope-835-qualifier.md),
  [tables](new-core/scope-835-tables.md) and [Kripke stops](new-core/scope-835-kripke-stop.md).
- Open scopes: [borrowed payloads to handlers](new-core/scope-844-borrowed-payloads.md) (#844;
  Tier 1 is built, Tier 2 is open), [per-code closure types](new-core/scope-855-per-code-types.md)
  (#855, decision 76) and [pipes](new-core/scope-pipes.md): `|>` push and `>|` pull, the connector
  and the unit split (#907, #918–#925).

## Designs

- [Data declarations](data-declarations.md): records, variants, blocks, folds and the match
  compiler (#489), built as SPEC §42, §60 and §61.
- [Strings and slices](strings-slices-design.md): slices, buffers, UTF-8 text and literals, end
  to end, with the status of each stage.
- [Loops](loops.md): one loop model for `for`, `while` and `loop` and their exits (#545).
- [Recursion as an effect](rec-effect/README.md): bounded recursion and its handlers, with a design
  corpus (SPEC §21).
- [Effect polymorphism](effect-polymorphism.md): functions over effectful computations (#161):
  computation parameters, rows and `|>`, built as SPEC §33; stored callbacks are not built.
- [Async with capabilities](async-capabilities.md): tasks that borrow their own data across
  `await` with no `Pin` (#52), built as SPEC §29 with the named assumption `PinLaw`.
- [The compiler](compiler.md): compiling from what the checker establishes (#555), and
  [N1's plan](n1-plan.md), which describes Backend2's typed IR as built (N1, SPEC §43).
- [Ergonomics](ergonomics.md): the surface's verbosity in real programs, and the sugar planned for
  it (#577, #583).
- [Expressiveness](expressiveness.md): what can't be expressed yet, why, and every way to unblock
  it (#587).
- [A Kubernetes operator](operator/README.md): the north-star program, sketched in the language as
  it should be.

## Research

- Prior art: [memory model](prior-art-memory-model.md),
  [borrow splitting](prior-art-borrow-splitting.md),
  [effects, coeffects and borrowing](prior-art-effects-coeffects.md),
  [borrows as optics](prior-art-optics.md),
  [session types, par and modes](prior-art-sessions.md),
  [what Rust's designers wish they had done](prior-art-rust-wishlists.md),
  [borrows across suspension points](prior-art-suspension-borrows.md).
- [Research reports](research/README.md): mutation paradigms, graded and adjoint types, modes and
  capabilities, dependent types, session types, Bend.
- [The effects research book](../research/effects/src/SUMMARY.md).
- [l_lang kernel and literature](l-lang-kernel-and-lit.md): the previous language's μ/ν techniques
  and the anatomy of its proof burden, behind the growth discipline in `CLAUDE.md`.

## History

Finished scopes, superseded designs and spikes, kept as the record. Each starts with a line
saying what superseded it.

- In place, because the spec or the code cites them:
  - unit scopes [#746, the derived copy](scope/746-imm-copy.md) and
    [#760, native facts](scope/760-native-facts.md);
  - the tree track and #835:
    [#781](new-core/scope-781.md), [#782](new-core/scope-782.md), [#804](new-core/scope-804.md),
    [#806](new-core/scope-806.md), [#791's goal](new-core/goal-791.md),
    [#831's interface](new-core/scope-831-interface.md) and [map](new-core/scope-831-map.md),
    [`imm` frames](new-core/scope-835-iframes.md), [`mut` frames](new-core/scope-835-mframes.md),
    [lend exits](new-core/scope-835-lendexit.md), [public transitions](new-core/scope-835-public.md),
    [the restriction](new-core/scope-835-restriction.md);
  - the effect calculus as a [technical report](effects-tr/README.md) (#245), the
    [effect model](effect-model.md) (#235) and [effects scoping](effects-scoping.md) (#18);
  - [draft 0 of the surface](surface-cbpv.md), [`FnMut` as `Clo`](fnmut.md),
    [strict outlives](outlives-strictness.md), [recursion](scope-recursion.md) and
    [deep freeze](scope-deep-freeze.md) scopes,
    [second-class closures and System C](second-class-and-system-c.md);
  - the backend's designs before [the compiler](compiler.md): the
    [pipeline architecture](pipeline-architecture.md) (#552) and
    [effect lowering](effect-lowering.md) (#541);
  - the [consolidation audit](consolidation-audit.md), the
    [generics inventory](generics-inventory.md),
    [ideas on handlers](ideas-handlers-and-borrows.md),
    [the void tombstone](tombstones/lends-across-suspensions.md), and the
    [expressiveness probes](expressiveness-probes/).
- In [`archive/`](archive/): the effects state dossier, the remaining unit scopes (#743, #746
  step 4b, #750a, #808), #795, #835's handlers and the chain spike, the properties wish list,
  ideas on pointers and lifetimes, and the l_lang salvage.
- In git history only: `new-core/scope-791-rule.md` and `scope-791-loctype.md`, at `9ba78899`.
