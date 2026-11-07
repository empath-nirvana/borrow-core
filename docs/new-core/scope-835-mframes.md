# #835: the `mut` lend frames across Kripke stops

This unit restates the 13 `mut` lend frames of `scope-835-kripke-stop.md` §2's Fm class at
`erwpK`, the stop choosing its floor (`Core/Chain/SI/ErwpK.lean`). Each `erwp` statement stays,
word for word, and is proved again from its restated frame at one world.

The Lean is in `Core/Chain/SI/MFrameK.lean` (the frame, its tables, the raise cases, the
constant world, the typed world) and `Core/Chain/MFrameK835N.lean` (the 13 instances and their
`Unit` corollaries).

## 1. The frames

Every variant is the same strong induction on the index, with three cases, each the existing one.
`erwpK_M_frameGen` is that induction over any inner raise table `RI` and outer raise table `RO`,
with the lender's stops guarded by `G` (`opTableG`'s guard, or `True`):

- **a return**: 6.65's end, the post read at the world the borrowed run chose;
- **a stop**: the borrow folded into the continuation's share. The lender's stop chooses its floor,
  and owes its continuation at the worlds `y` its entry allows there. `OpTabK.FoldTwin` gives the
  borrowed entry's order at the borrowed share, and the frame's invariant at `y`. The frame is
  re-entered at `y` at the index the resume is at. A cancellable stop's cancel obligation is the
  lender's by `hcan`, read at `y`;
- **a raise** (a `raise` or a cancel's `raise`): no continuation is owed, so no world is read. The
  case is the existing one, now a lemma (`RaiseFold`).

| `erwp` frame | at `erwpK` | its `erwp` statement from it | raise case |
|---|---|---|---|
| `erwp_M_frame` | `erwpK_M_frame` | `erwp_M_frame_of_K` | none (`raiseFold_absurd`) |
| `erwp_M_frameR` | `erwpK_M_frameR` | `erwp_M_frameR_of_K` | `raiseFold_claim` |
| `erwp_M_frameT` | `erwpK_M_frameT` | `erwp_M_frameT_of_K` | none |
| `erwp_M_frame_cancelRun` | `erwpK_M_frame_cancelRun` | `erwp_M_frame_cancelRun_of_K` | `cancelFold_claim` |
| `erwp_M_frameCR` | `erwpK_M_frameCR` | `erwp_M_frameCR_of_K` | `raiseFold_claim` |
| `erwp_M_frame_cancelRunCR` | `erwpK_M_frame_cancelRunCR` | `erwp_M_frame_cancelRunCR_of_K` | `cancelFold_claim` |
| `erwp_M_frameRR` | `erwpK_M_frameRR` | `erwp_M_frameRR_of_K` | `raiseFold_claimR` |
| `erwp_M_frameCRR` | `erwpK_M_frameCRR` | `erwp_M_frameCRR_of_K` | `raiseFold_claimR` |
| `erwp_M_frame_cancelRunCRR` | `erwpK_M_frame_cancelRunCRR` | `erwp_M_frame_cancelRunCRR_of_K` | `cancelFold_claimR` |
| `erwp_M_frameCRG` | `erwpK_M_frameCRG` | `erwp_M_frameCRG_of_K` | `raiseFold_claim` |
| `erwp_M_frame_cancelRunCRG` | `erwpK_M_frame_cancelRunCRG` | `erwp_M_frame_cancelRunCRG_of_K` | `cancelFold_claim` |
| `erwp_M_frameF` | `erwpK_M_frameF` | `erwp_M_frameF_of_K` | none |
| `erwp_M_frameTF` | `erwpK_M_frameTF` | `erwp_M_frameTF_of_K` | none |

The `_of_K` statements are the originals' text (checked by comparing their source text).
The originals and their proofs are unchanged.

The tables at a world index are `opTableRK`, `opTableGK`, `opTableGRK`, `cancelTabK`, `cancelTabRK`
and `cancelTabGRK`. Each has its `Unit` embedding (`*_lift`), and `erwp_eq_erwpK_of` rewrites an
`erwp` at a table as `erwpK` at one world.

## 2. The premises of the restated frames

At a world index the borrowed run and the lender stop at different tables (`Ti`, `To`): the
borrowed run's entries owe at the lend's world, the lender's at its own.

| Premise | What it is | At one world | At `KW` |
|---|---|---|---|
| `hT : ∀ x, (Ti x).LendOKCR A` | `OpTabN.LendOKCR` at every world | `OpTabN.LendOKCR.lift` (from `LendOK`, `LendOKR`, `LendOKC` by `toCR`) | the typed tables unit |
| `hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) ℓ A` | the twin, and the fold at the floor-choosing stop | `foldTwin_lift` of the original twin, `Inv = True` | `foldTwin_owed` (§3) |
| `hcan : CanFold Inv Ti To ℓ A F` | the original `hcan`, its cancel obligations read at the resumption world | `canFold_lift` | the typed tables unit (`tabR_can` and the like at a world) |
| `hab`, `hlin` | no abortive entry, every entry must-resume | from `LendOK`/`LendOKR`/`LendOKC` | the typed tables unit |
| `hR` | the original's raise case | a lemma, no world | the same lemma |

`rwpG_M_frameGV` is `rwpG_M_frameG` with the borrowed run's post resource and the lender's read
valid. `rwpG_M_frameG` is now its corollary, with its statement unchanged. The validity is what the
inner view clause needs (§3).

## 3. The typed world

`foldTwin_owed` discharges `FoldTwin` at `KW`:
- the lender's entries owe along `KW.Owed` at the lender's world `x`;
- the borrowed run's owe along `KW.Owed` at the lend's world `x.lend ℓ A F` (`Θ + (ℓ, A)`, the view
  at `ℓ` set to `A`, the floor `A`; its view is `Φ.set ℓ A F`, `KW.lend_view`);
- the frame's invariant is `FoldInv A`.

`erwpK_M_frameCR_KW` is the frame at `KW` with these orders.

A borrowed stop at a floor `f ≤ A` is the lender's stop at `min f x.lo` (`kw_owed_foldAt`):
- **`ExtP` across the fold at any floor `f ≤ A`** (`LocTy.ExtP.foldAt`, `extP_foldFrameAt`). This
  is `LocTy.ExtP.fold`'s proof with the floor read below the lend. A floor below `A` arises when a
  lend `B < A` is live inside the callback.
- **The lend's view is consistent with the borrowed share** (`consistentX_fold`). The borrowed share
  is part of `Z = Z/ℓ ● ℓ ↦ mut(A, v, χ)`; `Z/ℓ` and `χ` are parts of the lender's share; the view
  at `ℓ` is `A`. Both `Z` and the lender's share must be valid, which `rwpG_M_frameGV` supplies.
- **The lend's world is valid** (`LocTy.ok_add`).
- **`FoldInv A` at the resumption world**, from `KW.Owed`.

**`KW.Owed` keeps `FoldInv g` at every `g ≥ f`.** Before this unit it kept `FoldInv f` alone. Under
lends at `A > B` the stop chooses `B`; the frame at `A` re-enters at the resumption world and needs
`FoldInv A` there. `owed_keeps_foldInv_above` is the configuration, with every hypothesis
discharged: a world with an `imm` record at `B` and `FoldInv A`, extended by a key at `C < B`, is
owed under the old clause, where `FoldInv B` is vacuous; at that world `FoldInv A` fails, and
`KW.Owed` does not owe it. `KW.owed_self`, `KW.owed_of_post`, `KW.Owed.trans`, `KW.Owed.foldInv`
and `kw_owed_fold` keep their statements.

**The frame reads no floor of the resumption world beyond its own bound**
(`scope-835-lendexit.md` §3 asked this). The lender's stop at `y` chooses `min f y.lo ≤ y.lo`. So
a post that lowers the floor costs the frame nothing, and `KW.Post` is unchanged here.

**The lend's starting world.** The frame's invariant must hold where the lend is taken.
`LocTy.exists_foldInv` gives, below any bound, a lifetime with `FoldInv`: fresh, and below every
`imm` record. The typed lend lemmas pick `A` that way when they are re-pointed.

## 4. Stops outside `Sched`

A Mut Frame builds no stop outside `Sched`. The lender's stop is at the key of the borrowed stop
(`FoldTwin`'s `en′` is at the same key). `OpTabK.FoldTwin.schedPart` states this:
- when the borrowed table's resuming entries are at names in `Sched` (the restriction's (S1),
  `Row.SchedOnly`), `FoldTwin` holds of the part of the lender's table at those names and its
  raises (`OpTabK.schedPart`);
- that part allows no stop the table does not (`opTableK_schedPart_le`).

So every stop the 13 frames give the lender owes along `KW.Owed`, and none along `KW.OwedR`. The
per-producer check `scope-835-lendexit.md` §5 left to the frames units is done for the Fm class by
this lemma, since all 13 are instances of `erwpK_M_frameGen`.

## 5. Not in this unit

- **`erwp_M_frameListCRN`, `erwp_M_frameListRN`** (`FamCancel836N`). These are list inductions over
  `erwp_M_frameCRR`/`erwp_M_frameRR` at typed tables (`tabR`, `claimL` at `Θ`, `Θ.view c`). Their
  frame step is restated here. Their statements read the typed tables at a world, which is the
  tables unit. Not attempted.
- **The anti-frames** (`erwp_M_antiFrame*`, the Fa class). They need the share transfer, a later
  unit.
- **`CanFold` and `LendOKCR` at `KW`.** They need the typed tables (`tabN`, `tabR`, `tabG`) at `KW`,
  which is the tables unit.

## 6. Estimate

One agent run is about 1 unit.

| Item | Units |
|---|---|
| The 13 `mut` frames | done |
| The `imm` fold analogue, the anti-frame share transfer and their 16 frames | 1–2 |
| The remaining mechanical producers (31 on the path), handlers included | 1 |
| `tabN`/`entN` at `KW` (the `Sched` split), `CanFold` and `LendOKCR` at `KW`, the two list frames, `SchedOKN` at `erwpK` | 1–2 |
| Re-pointing the 111 typed and compatibility lemmas | 2–3 |
| E10, `effHandleV`/`VB`, `reify`; `Goal791SchedN` with `Restrict835` | 1 |
| **Total** | **6–9** |

The previous estimate was 7–10.
- The frames row (1–2) is done.
- The list frames move to the tables row, which grows from 1 to 1–2.
- `CanFold` at `KW` is the existing cancel-table lemmas read at a world. It is mechanical, but every
  one of them is touched.

## 7. Bookkeeping

- **Restated declarations:** `KW.Owed` (the `FoldInv` clause at every floor at or above the
  stop's, §3, with a configuration). `rwpG_M_frameG` is now a corollary of `rwpG_M_frameGV`, with
  its statement unchanged.
- **Unspent hypotheses:** none. Each restated frame's premises are used, and each is discharged at
  one world.
- **Unused uniqueness or functionality results:** none.
- **Untranscribed in the run-up:** the typed tables at `KW` (`CanFold`, `LendOKCR` and the entries'
  orders there), the list frames, the `imm` fold analogue and the anti-frame transfer.
