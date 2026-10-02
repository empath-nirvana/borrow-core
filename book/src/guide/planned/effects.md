# Effects

**Stage S1 has landed: [Effects and handlers](../effects.md). The rest is planned: #18.**

The design is `docs/effects-scoping.md`, and its stages are decision 48's:

- S1: answering operations and `Fail`, rows inferred (#152, #153, #154);
- S2: named capabilities and platform bundles (#155, #156);
- S3: recursion, drivers, layers and `|>` (#157, #158): recursion as the fixed point of a
  generator, its drivers `bounded` and `deep`, and layers as transformers of the generator have
  landed ([Recursion](../recursive-data.md#recursion)); `memo` and `|>` are planned;
- S4: `Yield`, projections and stored callbacks (#159, #160, #161);
- S5: with #52, suspension with input and cancellation (#162).

A handler is defined by its elaboration into core terms: a capability lent by `withbor`, a
resume-once clause a call on it, abort a sum exit, suspension codata, finalisation the implicit
destructors. Effect rows never enter the core.
