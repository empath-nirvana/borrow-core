# Axes and options

| axis | options | status |
|---|---|---|
| effect representation | rows with row variables; capabilities; modal | rows with row variables (decided). They encode into modal effects. |
| handler binding | dynamic; lexical | open; lexical gives P12 by construction |
| instances | static names; generative | static as built; generative is deferred |
| deep or shallow | deep; shallow | deep (decided) |
| continuation classes | tail-resumptive, abortive, one-shot; multi-shot | multi-shot is ignored |
| discard | silent weakening (the affine reading of other systems); linear with a cancel | cancel as built (§19); the core is linear |
| `resume` and capabilities | second-class; first-class with boxing | open (see [Second-class values](../foundations/second-class.md)) |
| a stored continuation's bound | a `[gen]` rule; an outlives rule at `U C` | OQ-28 |
| lends across a stop | carried open in σ; ghost-end (end and re-lend) | OQ-9 |
| future-world quantifier | at the binder clauses; at `U`/`contShare`/`KapRel` | OQ-8 |
| does a handler site open a lifetime | yes; no | OQ-3 |
| higher-order operations | algebraic only; scoped | algebraic only for now |
| lowering correctness | a theorem; laws and counts | OQ-23 |
