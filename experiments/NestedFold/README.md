# NestedFold: the owned fold by induction on the class `P` (#719, U0 of #595)

`lake build NestedFold`. Imports `Core`; nothing imports it.

## Question

Does the generic owned traversal spec close by induction on the class `P` (#595's design §4.2,
which replaces `FShape`), with the measure (cells, value size, binder rank) and an environment of
handles, one per binder?

## Verdict: yes, and it is in the library

The answer was yes, with one induction on the position `A ∈ P`, one case per former, and no case
tree over combinations of formers. The proof is now the library's (#722, SPEC §61):

| here | in `Core/` |
|---|---|
| the class `P`, binders, `reach_ok` | `Core/FoldClass.lean` (`P`, `PBody`, keys `Bnd`, `keysIn`, `keys_ok`) |
| the generated traversal, the dispatch | `Core/FoldOwnGTerm.lean` (`tE`, `selfG`, `foldOwnGV`), with the algebras passed at run time |
| `countLoop_inv`, `arr_spec`, `trav_spec`, `hs_all`, `fold_spec` | `Core/FoldOwnG.lean`, and `foldOwnG_compatX`, the rule's soundness |
| `HasDtorMu`, `dtor_spec` | `HasDtor.mu` and `dtor_wf` in `Core/Dtor.lean` |
| the test types `μX. I32 ⊗ Array X`, `μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)` | `corpus/storage-array.bc` and the kernel program `nested-fold` (`Core/NestedPrograms.lean`) |

Two things changed on the way. The algebras are a run-time tuple, so the traversal's handle is not
a closed value and the closed-algebra condition is gone. An array's slot is emptied by `swap`
rather than freed, and the emptied array is `drop`ped at the end, so a backend frees its buffer
once.

## What is left here

`Probe.lean`, the design pass's probe: `μX. I32 ⊗ Array X` is outside `FShape`; the iso-recursive
mismatch of a nested-`μ` mutual group (`tyBinA ≠ tyB`); the factorial size of that encoding
(`#guard`). The mutual groups are U5 of #595.

## Report items

- **Obstruction claims**: none.
- **Unused hypotheses**: none.
