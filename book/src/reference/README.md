# Reading the reference

The reference chapters are the core syntax specification,
[`docs/syntax-core.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/syntax-core.md),
included section by section, with short notes on how to read it. The specification of the
language itself is
[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md).

Every term form is one typing rule of the core judgment `CDerives`, one constant, or one derived
rule (a Lean theorem concluding a `CDerives` judgment). The tables cite the Lean for each form:

{{#include ../../../docs/syntax-core.md:citations}}

Where the checker goes beyond or falls short of the specification, `Frontend/README.md` lists
it: the parser's choices where the syntax is ambiguous, and the checker's known incompleteness.
When "section N" appears below, it refers to a section of `docs/syntax-core.md`.
