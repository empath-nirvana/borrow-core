# Terms

{{#include ../../../docs/syntax-core.md:terms}}

## Effects

The kernel's effect computations (SPEC §19) are, in the core text: `perform[n.i] V` and
`abort[n.i] V`, an operation `i` performed or aborted at the handler named `n`;
`handle_with[n](hr, hc) M`, the handler site `n` around `M`, with the return clause `hr` and the
tuple of operation clauses `hc`, each a value written in place (the elaboration writes a site's
clauses so) or a variable; and the binding `x <- M unwind (D); N`, whose finaliser `D` runs
when the rest is abandoned. The unwinding borrows (`withbor1u`, `withbor2u`, `withbor3u`,
`withloadu`, `slice_borrow_mut_u`, …) take the callback's row as their last bracket argument.
`Frontend/README.md`, item 18, gives the grammar, and `corpus/core-effects-*.bc` are programs
written in it. The rows of computation types are in [Types and shapes](types.md).
