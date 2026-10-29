# Reading the reference

The reference chapters are the core syntax specification,
[`docs/syntax-core.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/syntax-core.md),
included section by section, with short notes on how to read it. The specification of the
language itself is
[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md).

Every term form is one typing rule of the core judgment `CDerives`, one constant, or one derived
rule (a Lean theorem concluding a `CDerives` judgment). The tables cite the Lean for each form:

See [`docs/syntax-core.md`](../../syntax-core.md) (the part marked `citations`).

Where the checker goes beyond or falls short of the specification, `Frontend/README.md` lists
it: the parser's choices where the syntax is ambiguous, and the checker's known incompleteness.
When "section N" appears below, it refers to a section of `docs/syntax-core.md`.

The reference covers the core. The surface language of the guide elaborates into it; its forms
are specified by the entries of `SPEC.md` that the guide cites, and `bcc desugar` shows the core
form of any program ([How it elaborates](../elaboration/overview.md)).
