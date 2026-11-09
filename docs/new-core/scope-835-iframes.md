# #835: the `imm` frames, reborrows and anti-frames across Kripke stops

*History: a unit of #835, merged with #839. The code (`Core/Chain/`) is now its reference, and `chain-interpretation.md` the design. The text below is kept as the record.*

This unit restates the 12 Fi producers (`imm` frames and reborrows) and the 4 Fa producers
(anti-frames) of `scope-835-kripke-stop.md` §2 at `erwpK`, the stop choosing its floor
(`Core/Chain/SI/ErwpK.lean`), as `scope-835-mframes.md` did for the 13 `mut` frames. Each `erwp`
statement stays, word for word, and is proved again from its restated frame at one world.

The Lean:

| Class | Generic frame and the typed world | Instances and `Unit` corollaries |
|---|---|---|
| `imm` frames | `Core/Chain/SI/IFrameK.lean` | `Core/Chain/IFrameK835N.lean` |
| anti-frames | `Core/Chain/SI/AFrameK.lean` | `Core/Chain/AFrameK835N.lean` |
| reborrows | `Core/Chain/SI/RFrameK.lean` | `Core/Chain/RFrameK835N.lean` |

## 1. The two lemmas the classes needed

**The `imm` fold** (`LocTy.ExtP.immFoldAt`). The world of an `imm` lend of `r` at `A` adds the
record `(r, A)` and no key (`KW.lendImm`: `Θ.addImm (r, A)`, the view unchanged, the floor `A`).

```lean
theorem LocTy.ExtP.immFoldAt (hfA : f ≤ A) (h : Θ.ExtP f Θ' ρo) (hfr : Θ.Fresh A)
    (hI : ∀ x ∈ Θ.imm, x.2 ≠ A) (hc : ∀ a, a < A → CellIn ρi a → CellIn ρo a) (r : FrameRec) :
    (Θ.addImm (r, A)).ExtP f (Θ'.addImm (r, A)) ρi
```

It is `LocTy.ExtP.foldAt` with the key part dropped and the record kept: a key read at the
borrowed share is above `A` (`Fresh A`), so above `f`, where `ExtP` keeps it; the record `(r, A)` is
in both worlds; any other record is kept above `f` by `ExtP`'s filter clause, and below it by the
borrow cells' domination (`hc`), which reaches it since no record is at `A`. Its premises are
`FoldInv A` and `hc`. `extP_ifoldFrameAt` discharges `hc` at the fold's shares (`iFoldV`): a borrow
cell of `ρ_k ⊆ X` shorter-lived than `A` is not `Xᵢ`'s cell at `ℓ`, which is at `A`, so it is a cell
of `Xᵢ/ℓ` and of the lender's share.

**The share transfer** (`LocTy.ExtP.share`), `extF_fold`'s shape:

```lean
theorem LocTy.ExtP.share (h : Θ.ExtP lo Θ' ρo)
    (hc : ∀ a, a ≤ lo → CellIn ρi a → CellIn ρo a) : Θ.ExtP lo Θ' ρi
```

Above the floor `ExtP` reads no share; at or below it, a key or record relevant to `ρi` is relevant
to `ρo`. `CellIn.split` (a borrow cell of a composite is one of a part's, no longer-lived) supplies
the domination at each class's shares:

- **anti-frames** (`seal_cellIn`): the callback's share `ℓ ↦ own(w) ● σ′ ● R` is dominated by the
  sealed share `R ● ℓ ↦ mut(β, w, σ′)` at every lifetime: `σ′`'s cells lie above `β`, the sealed
  cell's lifetime;
- **reborrows** (`reb_cellIn`): the borrowed share `ρ_k ⊆ ψ ● χ|excl` is dominated by the lender's
  `ψ ● ρᵢ` below `β`, since every cell of a reborrow's image is at `β` or longer-lived
  (`reb_at_ge`, read off `reb_β`'s three clauses).

## 2. The frames

Each class is one strong induction on the index, with three cases, each the existing one:

- **a return**: the post read at the world the borrowed run chose;
- **a stop**: the lender's stop chooses its floor and owes its continuation at the worlds `y` its
  entry allows; a twin condition gives the borrowed entry's order at the borrowed share and the
  frame's invariant at `y`; the frame is re-entered at `y`. A cancellable stop's cancel obligation
  is the lender's, read at `y`;
- **a raise**: no continuation is owed, so no world is read.

| Class | Generic | Twin | Cancel | Raise |
|---|---|---|---|---|
| `imm` | `erwpK_I_frameGen` | `OpTabK.IFoldTwin` | `ICanK` | `IRaiseFold` |
| anti-frame | `erwpK_M_antiFrameGen` | `OpTabK.SealTwin` | `ASealCan` | `ASealRaise` |
| reborrow | `erwpK_rebGenK` | `OpTabK.RebTwin` | `RebCanK` | `RebRaiseFold` |

| `erwp` producer | at `erwpK` | its `erwp` statement from it |
|---|---|---|
| `erwp_I_frame` | `erwpK_I_frame` | `erwp_I_frame_of_K` |
| `erwp_I_frameR` | `erwpK_I_frameR` | `erwp_I_frameR_of_K` |
| `erwp_I_frameRR` | `erwpK_I_frameRR` | `erwp_I_frameRR_of_K` |
| `erwp_I_frameT` | `erwpK_I_frameT` | `erwp_I_frameT_of_K` |
| `erwp_I_frameF` | `erwpK_I_frameF` | `erwp_I_frameF_of_K` |
| `erwp_I_frame_cancelRun` | `erwpK_I_frame_cancelRun` | `erwp_I_frame_cancelRun_of_K` |
| `erwp_rebGen` | `erwpK_rebGen` | `erwp_rebGen_of_K` |
| `erwp_rebGen_cancelRun` | `erwpK_rebGen_cancelRun` | `erwp_rebGen_cancelRun_of_K` |
| `erwp_reborrow` | `erwpK_reborrow` | `erwp_reborrow_of_K` |
| `erwp_reborrow_cancelRun` | `erwpK_reborrow_cancelRun` | `erwp_reborrow_cancelRun_of_K` |
| `erwp_reborrowT` | `erwpK_reborrowT` | `erwp_reborrowT_of_K` |
| `erwp_reborrowDeep` | `erwpK_reborrowDeep` | `erwp_reborrowDeep_of_K` |
| `erwp_M_antiFrame` | `erwpK_M_antiFrame` | `erwp_M_antiFrame_of_K` |
| `erwp_M_antiFrameC` | `erwpK_M_antiFrameC` | `erwp_M_antiFrameC_of_K` |
| `erwp_M_antiFrameCR` | `erwpK_M_antiFrameCR` | `erwp_M_antiFrameCR_of_K` |
| `erwp_M_antiFrame_cancelRunCR` | `erwpK_M_antiFrame_cancelRunCR` | `erwp_M_antiFrame_cancelRunCR_of_K` |

The `_of_K` statements are the originals' text (checked by comparing their source text). The
originals and their proofs are unchanged.

## 3. The typed world

| Class | Discharge at `KW` | The inner world | The lender's floor | Invariant |
|---|---|---|---|---|
| `imm` | `ifoldTwin_owed` (`kw_owed_ifoldAt`) | `x.lendImm r A` | `min f x.lo` | `FoldInv A` |
| anti-frame | `sealTwin_owed` (`kw_owed_seal`) | `x` | `f` | `KW.SealInv` |
| reborrow | `rebTwin_owed` (`kw_owed_reb`) | `x` | `min f (↓β)` | `True` |

- **`imm`.** As `foldTwin_owed`: `ExtP` by the `imm` fold, the view consistent with the borrowed
  share (`consistentX_ifold`, an `imm` cell is consistent with every view), `FoldInv A` at the
  resumption world from `KW.Owed`. `KW.Owed`'s `FoldInv` clause at the lend's world: a floor `g` at
  which `Θ.addImm (r, A)` has `FoldInv` is not `A` (`LocTy.FoldInv.of_addImm`).
- **Anti-frames.** The seal changes the share, not the world: the callback and the anti-frame owe
  at the same world and floor. The invariant `KW.SealInv` (a valid location typing, the cell's
  key, the view at the cell's lifetime) gives `Φ ℓ = (β, F)` at the resumption world
  (`kw_seal_view`), which the anti-frame reads to open the cell again; `KW.Owed` at the sealed
  share keeps the key (`ExtR` at the sealed cell) and the view (`consistentX_get` at it).
- **Reborrows.** The same world; the lender's stop takes a floor below `β`, where the share
  transfer holds.
- The `imm` frames' and reborrows' stops are at the borrowed run's names (`IFoldTwin.schedPart`,
  `RebTwin.schedPart`), as `FoldTwin.schedPart` for the `mut` frames: under (S1) they owe along
  `KW.Owed`.

The KW instances: `erwpK_I_frameT_KW`, `erwpK_M_antiFrameCR_KW`, `erwpK_reborrowT_KW`.

## 4. Added premises

| Premise | Where | Discharged |
|---|---|---|
| validity of `π` and `π/ℓ ● ρ_ℓ ● ρ_P̂(v)` | `rwpG_I_frameGV`'s `hpost` | in its proof (`h10`, `hvFY`); `rwpG_I_frameG` is its corollary, statement unchanged |
| validity of the sealed resource | `rwpG_M_antiFrameGV`, `AFPostGV` | in its proof (`hvπ'`); `rwpG_M_antiFrameG` is its corollary, statement unchanged |
| validity of `w` and `Y` | `rwpG_rebGV`, `rwpG_rebDeepGV` | in their proofs (`hvfp`, `hvY59`); `rwpG_rebG`, `rwpG_rebDeepG` are corollaries, statements unchanged |
| `Pv` handed to the reborrow's `hpost` | `RebEntryGP` | `True` from `RebEntryG` (`RebEntryG.toP`), validity at both entries (`rebEntryGV_top`, `rebEntryGV_deep`) |
| `Φ ℓ = (β, F)` and `Φ` downward closed, at worlds where `Inv` holds | `erwpK_M_antiFrameGen` | at `Unit` the original `hF`, `hΦ`; at `KW` `KW.SealInv` |

Each validity is what the typed discharge's consistency step reads; at `Unit` each twin condition
holds of a twin with every world allowed (`ifoldTwin_lift`, `sealTwin_lift`, `rebTwin_lift`).

## 5. Not in this unit

- **The tables at `KW`.** Each KW instance takes the entries' orders (`hTw`: the borrowed entries
  owe along `KW.Owed` at the inner world, the lender's at its own) and the cancel conditions
  (`ICanK`, `ASealCan`, `RebCanK`) as premises. `scope-835-tables.md` §7 discharges them from the
  typed tables; `ICanK` and `ASealCan` there read `Inv` at the resumption world.
- **`erwp_M_antiFrame_cancelRun`** is a consumer (`scope-835-kripke-stop.md` §2) and is not
  restated; the `Unit` corollary of `erwp_M_antiFrameC` reads it (`asealCan_claimT`).
- **The typed lend lemmas' choice of `A` and `β`** at `KW`: `LocTy.exists_foldInv` for `A`; the
  reborrow's `β` needs no invariant.

## 6. Estimate

One agent run is about 1 unit.

| Item | Units |
|---|---|
| The 13 `mut` frames | done |
| The `imm` fold, the share transfer and their 16 frames | done |
| The remaining mechanical producers (31 on the path), handlers included | 1 |
| `tabN`/`entN` at `KW` (the `Sched` split), the cancel conditions at `KW` for all four classes, the two list frames, `SchedOKN` at `erwpK` | 1–2 |
| Re-pointing the 111 typed and compatibility lemmas | 2–3 |
| E10, `effHandleV`/`VB`, `reify`; `Goal791SchedN` with `Restrict835` | 1 |
| **Total** | **5–7** |

## 7. Bookkeeping

- **Restated declarations:** `rwpG_I_frameG`, `rwpG_M_antiFrameG`, `rwpG_rebG` and `rwpG_rebDeepG`
  are now corollaries of their `…V` forms, with their statements unchanged. No change to
  `ErwpK.lean` or `MFrameK.lean`.
- **Unspent hypotheses:** none. Each restated frame's premises are used, and each is discharged
  at one world.
- **Unused uniqueness or functionality results:** none.
- **Untranscribed in the run-up:** the typed tables at `KW` and the cancel conditions there, the
  list frames.
