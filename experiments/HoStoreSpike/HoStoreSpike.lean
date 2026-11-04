import HoStoreSpike.Example

/-!
# Higher-order store over the tree carrier (spike, #790)

A throwaway spike. `Tower`: the approximation tower, semantic types reading the store typing at
the step index, and cell invariants one step later (`semH`). `Reread`: re-reading at every later
tree and lower index, for every lawful store typing. `Formers`: `1`, `Imm`, `Mut` at any type,
thunks of any predicate family, guarded fixed points. `D2`: `InvKept`/`UpdX.inv` at types.
`Example`: a cell holding a thunk that holds a borrow, after the graft, re-read.
-/
