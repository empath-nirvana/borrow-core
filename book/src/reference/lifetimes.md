# Lifetimes

{{#include ../../../docs/syntax-core.md:lifetimes}}

The checker decides `⊑` and `⊏` between lifetimes with the structural rules only: reflexivity,
`top` on the right, a variable through its bound, and `/\`/`\/` on either side. It does not use
distributivity.
