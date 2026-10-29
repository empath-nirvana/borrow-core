# Lifetimes

See [`docs/syntax-core.md`](../../syntax-core.md) (the part marked `lifetimes`).

The checker decides `⊑` and `⊏` between lifetimes with the structural rules only: reflexivity,
`top` on the right, a variable through its bound, and `/\`/`\/` on either side. It does not use
distributivity.
