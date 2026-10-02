# Sketches: the `aff-*` programs under K1, E1 and B1

Unchecked. Each file is its `corpus/` program as it would read with

* **K1**, the box rule of the outlives judgment non-strict (`[@b] T ⊐ @a` from `@a ⊑ @b`);
* **E1**, `main` run under an implicit lifetime of its own, and a lifetime argument that the call
  does not determine filled with `dom`;
* **B1**, a lifetime bound `where S: 'c` on a generic function, elaborated as the bound `'c < ⊓q̄`
  on the template's own lifetime, `q̄` the lifetimes of the instance's type argument `S`.

`aff.bc` is the library's `lib/aff.bc` with the bounded constructor `aff_new_boxed` beside
`aff_new`. `docs/outlives-strictness.md` §5 counts the scopes and `boxed[…]` annotations each
sketch removes. `../k1/` holds the four programs that need K1 alone, checked against
`../../k1.patch`.
