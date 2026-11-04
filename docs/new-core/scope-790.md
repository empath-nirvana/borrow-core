# Scope: `Mut` at any semantic type over the tree relation (#790)

Part of #771. Builds the spike that answered yes (`hostore-spike` @ `1b76d6d3`,
`experiments/HoStoreSpike/`) into `Core/`/`Support/`. Depends on `scope-782.md` (E1 is this
issue). **Paused** in favour of #791, which changes the record type (`RecC`: a record plus its
template) this work sits on. Resume from `tree-core` after #791 lands.

## 1. Kernel target

`STy.mut a τ` (`Core/TreeSem.lean`) takes any `STy` payload `τ` (closures, thunks, stored
continuations), not only a store code `KTy`. The store layer is the spike's approximation tower
(`ATy n`, `HTy`, `HStore`, `semH Ψ n`): at index `n` a type reads the store typing only through
its approximation at `n`, so no Löb argument is needed. On it:

- cells are re-read along tree growth, uniformly over every lawful store typing (`RR.exists_H`);
- `STy.mut_reread` and `RC.mut_extends` hold at the general payload;
- the `twp` rules that read and write cells (`Core/TreeHeap.lean`) are re-proved over it.

No statement may fix a payload type, a nesting depth or a store-typing shape.

## 2. Hardest case (stays in)

A `mut` cell holding a stored continuation that itself holds a borrow, re-read across a graft (a
proper tree extension, not `TWd.Ext.refl`), then loaded and resumed. The general results must
cover it, and a closed instance must exercise it at a proper extension. The spike's
`hard_case_inhabited` is this case at `TWd.Ext.refl` and with a thunk of `Imm @β 1`, not a
continuation, and stops before the load and the resume. `round7_codes`
(`Core/TreeSemKEx.lean`) is to be generalised to a non-code payload as one instance.

## 3. State

**Done:** reading only. Worktree `~/repos/borrow-core-tree790`, branch `tree-790` from
`origin/tree-core` (`666485be`). No Lean changes.

**What was read, and what it shows:**

- `twp_load`/`twp_store` (`Core/TreeHeap.lean`) are at `own` cells only. There is no `mut`-cell
  load or store and no swap rule at `twp` today. "Re-proved over it" therefore means: (i) the
  `own` rules carried over to the new world unchanged in substance, the store typing not being
  read at an `own` cell (`Cov.own`); (ii) the rules at a `mut` cell are **new**, and the load at
  a `mut` cell is where the payload's type is read back (`RC.mut_contentH`).
- `TWd.Θ : CodeTy` is read at index-free `sem`: in `WInv`, `RRw`, `RecsRR`/`SRecsRR`,
  `KeepRel`, `UpdA (sem w'.Θ)`, `InvKeptA w₀.Θ w'.Θ` inside `EndT`, and the template choice
  `TWd.tc : TRes → KTy → Val → TRes`.
- The spike's merge estimate says `WInv`/`twp` gain the index. The brief says `twp`/`EndT` keep
  their statements, and to stop if they would have to change.

## 4. Open question (not decided, not verified)

**Whether `twp`/`EndT` can keep their statements.** The cell invariant at `semH Ψ n` reads its
type at `n - 1`. `twp F Q n w …` asks `WInv w₀ fρ μ` at the start world and `WInv w' fρ' μ'` at
the end, neither at an index. Three readings were considered:

1. index-free `sem` of an `HStore` (cell content of its type at every index): a store at index
   `n` would need the value at every index;
2. the index as a field of `TWd` (or of `Θ`), so the text of `twp`/`EndT` is unchanged: nothing
   in `twp`'s statement ties the world's index to `n`, so a run started at an extension whose
   index is below `n` would get nothing from a load;
3. `WInv` at an index, read at `n` at the start and at `n - j` at the end, as the spike
   estimated. This changes the statement of `twp` and `EndT`.

I have not derived that (1) and (2) fail and have not verified that any obstruction is real. Before
resuming, either build (2) far enough to state the `mut` load rule, or state the failure as an
elaborating `def … : Prop` / a Lean configuration with every hypothesis discharged. If only (3)
works, that is the brief's stop condition, and it goes to the user before any code.

## 5. Next step, precisely

1. On the post-#791 `tree-core`, port `Tower.lean` and `Reread.lean` of the spike into
   `Support/Model/Tree/World/HStore.lean` (no dependence on `TWd`; generic in `LocTy`, as in the
   spike). This is independent of the question in §4 and of `RecC`.
2. Settle §4 with a Lean artefact: state `twp_load_mut` (load at a `mut` cell, postcondition the
   payload's `STy` at `n - 1`) against readings (2) and (3).
3. Then switch `TWd.Θ` to `HStore`, `sem` to `semH`, and carry #782's `STy`/`SCmp`/κ files;
   `STy.code` becomes the embedding of codes into `HTy` (not built in the spike: "`KTy` has not
   been embedded into `HTy`").

## 6. Interaction with record templates (#791)

- Records carry a code (`FrameRecT.T : KTy`, `World/Records.lean`), and the chain positions
  (`RefPosT`, `MutPosT`, `ChainT`, `GPosT`) and `KTy.immReborrow` case on `KTy`'s formers.
  `TWd.tc` and the canonical images are also indexed by `KTy`. If `RecC` pairs a record with a
  template over `KTy`, `KTy` stays the type of a record's lent value, and `Mut`'s generalisation
  is a change of the **store typing** (`TWd.Θ`) only. A record lending a cell whose payload is
  not a code (a `mut` of a thunk) would then need its template read at an `HTy`, which `KTy`
  cannot name: check whether #791's `RecC` fixes the template to a code.
- `RecsRR`/`SRecsRR`/`KeepRel` take `Θ' : CodeTy` only to read `RR (sem Θ')`. Under `semH` they
  take the store typing and an index. #791's re-reading of a record and its template should be
  generic in the `LocTy` it reads cells at (as `RR`, `Cov`, `UpdX` already are), so that the
  index can be added without re-proving it.
- The spike's forced change applies to records too: at a lower index a world is a re-reading of
  itself (`reread_is_update`). The records' re-reading at an index drop (`RecsRR` at
  `semH Ψ (n-1)`) is not in the spike and is the unverified risk the spike names ("step proofs
  that hold the world resource equal across an index drop").
