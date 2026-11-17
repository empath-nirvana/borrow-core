# Chain fragment retirement: client and assumption audit

Baseline: `c1d16d42` (2026-11-14). Scope: the unused chain type-former fragment assembly,
not tree-carrier algebra, the chain interpretation, or judgment consolidation (#798).
SPEC §62 states the deletion and the results it must preserve.

## What the fragment actually restricted

`JdgInFrag Γ j` inspected context/result types, through `VTy.inFrag`/`CTy.inFrag` and their
ν-body variants. It did not inspect an expression or derivation. In particular, it could
not exclude use of `effHandleV`, `effHandleVB`, or `reify` in the interior of a derivation.
It was not the no-value-handler judgment that was separately built and rolled back.

`fundamentalN_of : MissingN → FundamentalN` ignored the fragment premise by calling
`fundamentalN_all`. `fundamentalN_of_handlerLaw` supplied `MissingN` from `HandlerLawN`.
Neither adapter provided a handler-free fundamental theorem.

## Client inventory before deletion

Source search covered all Lean files in the repository, including experiments and scripts.
The compiled environment audit imported `Core` and `Frontend.Check.Externs`, inspected used
constants in **both types and proof/definition bodies**, and reported each client's type and
`Lean.collectAxioms` result (the operation underlying `#print axioms`).

| Interface | Handwritten clients | Disposition |
| --- | --- | --- |
| `FundamentalN` | `constN_w2`, `constN_w3`, `constN_wF`, `constN_sm`, `constNAt_of`, `constsN_of`; the two adapters | Entire unused assembly group removed |
| `ConstsN` | `constsN_of` | Removed with the group |
| `fundamentalN_of` | `fundamentalN_of_handlerLaw` | Both removed |
| Four fragment-dependent `constN_*` lemmas | `constNAt_of` | Both caller and callees removed |
| `constNAt_of` | Itself (recursion), `constsN_of` | Both removed |
| `constsN_of`, `fundamentalN_of_handlerLaw` | No other Lean clients | Removed |
| Type-former predicates, `JdgInFrag`, `Const791.InFrag`, `jdgInFrag_lolli` | Only the group above and each other | Removed, with generated auxiliaries |

The generic constant lemmas did take a supplied `FundamentalN` rather than `HandlerLawN`.
Replacing their hypothesis with the unrestricted theorem would have strengthened their
interface. That migration was **not** performed: no retained client depended on them, so
the whole closed group was deleted. This is removal of unused helper APIs, not a claim that
the two hypotheses are equivalent.

The environment scan found 49 referencing declarations, including generated equations and
match/congruence auxiliaries. Every one belonged to the deleted group or its auxiliaries.
Nine removed theorem names were removed from the §62 axiom registry; checks for retained
theorems remain in that registry.

## Results kept intact

The active path already used `fundamentalN_all → constNAt_all → goal791N`, with its existing
`MissingN`/`HandlerLawN` hypotheses. It required no fragment-client migration.

The direct finaliser proofs (`dRelease_sem`, `dFree_sem`, `dArrFree_sem`), constant
compatibility lemmas, concrete lend/reborrow/slice instances, and the callback-performing
instance remain. `constN_wl` and `constN_wl_inst` remain: these need no finaliser or handler
assumption and have live callers.

Verification compared `#check @name` (including explicit hypotheses) and `#print axioms`
before and after for 27 retained declarations: the fundamental theorem, general constant
and adequacy theorems, nil cases, checked ordinary/pinned/chain paths, and direct compatibility,
finaliser and concrete-instance proofs. Comparing axioms alone would miss a stronger explicit
hypothesis. All 27 signature/axiom reports were byte-for-byte identical. The post-deletion
environment audit found no remaining reference to the retired names. The normal gate separately checks build, registered axioms, hygiene and corpus
behavior; passing it does not discharge `HandlerLawN`.

Validation completed: `lake build Core Frontend.Check.Externs` passed; `make gate` reported
`ci-local: ALL PASSED (367s)`; `git diff --check` passed. No corpus outputs or counts changed.
