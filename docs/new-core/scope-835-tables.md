# #835: the typed tables at the world `KW`

This unit builds a row's table at the typed world, read through `erwpK`. It also discharges the Mut
Frame's table premises there and restates the scheduler's contract and the two list frames at
`erwpK`. The Lean is in `Core/Chain/TabK835N.lean` (the tables, the frame's premises, the
scheduler) and `Core/Chain/FrameListK835N.lean` (the list frames). It builds on
`scope-835-mframes.md` and `scope-835-lendexit.md`.

## 1. The tables

`tabNK S g C δ x`, `finNK`, and the lender's twin `tabRK R S g C δ x` / `finRK` are `tabN`, `finN`,
`tabR` and `finR` at a world:

- **The payload** is read at the stop's world `x` (`vN A δ x.Θ`).
- **The answer, the cancel obligation and the order** are read at the resumption world `y`. The
  answer is `vN B δ y.Θ ∧ ConsistentX y.c`.
- **A cancel obligation** is a cancel run at `erwpK` (`cancelOblK`, `cancelOblRK`). Its posts are at
  the run's own world (`KW.PostK`). Its location family and floor are those of `g y`.
- **The order of an entry at `m`** is `KW.OwedS S m`:
  - if `m` is a scheduler name, the entry owes along `KW.Owed` (`ExtP` at the floor the stop
    chose);
  - otherwise it owes along `KW.OwedR` (`ExtR`, no floor).

  `tabNK_wk_sched` and `tabNK_wk_owedR` state both cases. For the second, `contShareK_owedR_lo` and
  `contShareK_owedR_U` apply as they stand.
- **The world map `g`.** An entry of a table built with `g` owes its continuation at `g y`, and its
  cancel runs use `g y`'s view and floor.
  - The lender's tables take `g = id`.
  - The borrowed run's tables inside a Mut Frame are indexed by the lender's worlds. They take the
    lend's world, `g = (·.lend ℓ α F)`, which is how `erwpK_M_frameCR_KW` reads them.

**The cancel row of a scheduler entry.** Every entry of that cancel row owes along `KW.Owed`,
whatever its name (`finSched S m n = S m ∨ S n`). The reasons:

- The scheduler cancels a stopped continuation through `K†`, which removes its handler frames
  (`Kont.dead`, `Paper/S3_Dynamics/Definitions.lean`). So that cancel run's stops reach only the
  scheduler, at a table inside its own (`SchedOKNLe.fin`). No value reads them at `U`.
- That cancel run runs inside the continuation, under the lends live there. So its stops get only
  `ExtP` at the lend's floor from the fold.
- Wherever the scheduler's cancel tables are at scheduler names, which `SchedOKNLe.fin` gives at
  `Goal791SchedN`, this order coincides with the plain split.

The plain split (an entry's order read off its own name alone) would ask the lender's twin to owe
`ExtR` at a non-scheduler entry of such a cancel row. That entry is stopped at under the live lend.
I have not derived `CanFold` under the plain split and have not verified that any obstruction is
real. No cancel row is restricted, and no typing side condition is added.

## 2. Posts keep the floor

`lendexit` §3 offered two options. This unit takes the first: the typed world's post order is
equality (`KW.PostK x y := y = x`).

- `tabLe_postK` gives `erwpK_shift`'s `hTV` for every table.
- `erwpK_shift_postK` is `erwpK_shift` at `KW.PostK`, with every premise discharged.
- `KW.PostK.post` relates it to `KW.Post`.

This keeps more statements than dropping `KW.Owed`'s floor bound would:

- `KW.Owed` is unchanged, so `not_owed_post_lower`, `owed_keeps_foldInv_above`, `kw_owed_foldAt`
  and `foldTwin_owed` keep their statements and proofs.
- `KW.Post` is unchanged, so `not_tabLe_post_lower` stays a true statement about it: the reason the
  typed instance does not use it.

## 3. The Mut Frame's premises at `KW`

| Premise | At `KW` |
|---|---|
| `hT : ∀ x, (Ti x).LendOKCR A` | `tabNK_lendOKCR`: the layers' clauses of `CTy.SuspendC`, the answer at every resumption world |
| the twin across the fold (`erwpK_M_frameCR_KW`'s `hTw`) | `tabNK_foldTwin`: the payload and answer agree (`'x` is read by no layer's types, `vN_extend_of_not_free`); the lend's order gives the callback's entry by `KW.Owed.owedS`; the lender's entry owes along `KW.Owed` because the row's resuming layers are at scheduler names (`CTy.SchedOnly`, (S1) on the row type; `CTy.schedOnly_effOf` from `Row.SchedOnly`) |
| `hcan : CanFold …` | `tabRK_canK`, `tabR_can` at `KW`: by induction on how deep cancel rows nest, the callback's cancel run is framed by `erwpK_M_frame_cancelRunCR` at the cancel row's tables, with `FoldTwin` from `foldTwin_owed` and the cancel row the scheduler's (`finSched`) |

`erwpK_M_frameCR_tab` is the frame at the typed tables, with every premise discharged.

**One premise changed: `CanFold` reads `Inv` at the resumption world.**

- `CanFold` and `erwpK_M_frameGen`'s `hcan` now take `Inv y` for the resumption world `y`.
  - Old: `∀ y k ls K …, cancelOKK en y … → cancelOKK en' y …`.
  - New: `∀ y, Inv y → ∀ k ls K …, …`.
- The frame already had `Inv y` at that point. It came from `FoldTwin` and was discarded.
- At `KW`, the cancel run's frame is entered at `y` and needs `FoldInv A` there.
- The premise is weaker, so every existing instance still holds: `canFold_of_lin` is unchanged, and
  `canFold_lift` ignores the new hypothesis.
- No `_of_K` statement changes.

## 4. The list frames

`erwpK_M_frameList` is the list induction of `erwp_M_frameListCRN` and `erwp_M_frameListRN` at
`erwpK` over any world index. The run is at the world `x`. Its location family `Φ Θ c` and its
tables `TbL Θ c I` are read at the location typing and view the earlier frames reached, and at the
cells not yet lent. Each step is a frame, `hstep` (`KFrame` with the invariant `· = x`). The rest of
the proof is the original's: the fresh lifetime, the claims, `vN_local`, and the innermost callback.

`erwp_M_frameListCRN_of_K` and `erwp_M_frameListRN_of_K` prove the original statements from it at
one world. A source comparison confirms the text matches word for word. Their steps are the
originals' (`erwp_M_frameCRR` with `tabR_canR` and `tabR_le`; `erwp_M_frameRR` with
`OpTabN.Sub.le`).

**The step at `KW`** is §7.3. `erwpK_M_frameList`'s step has the invariant `· = x`: the frame
re-enters only at the run's own world. At `KW` a lender's entry owes its continuation at every
world `KW.Owed` allows, so that step is met at one world only, and the list at `KW` is its own
induction (`erwpK_M_frameListKW`), the step's invariant `FoldInv αⱼ` at the lends' world.

## 5. The scheduler's contract at `erwpK`

- `KapRelK` is the continuation a clause receives: the stopped run's Kripke stop, at a floor below
  the bound that the clause does not know.
- `SchedOKNLeK` / `SchedOKNK` are `SchedOKNLe` / `SchedOKN` at every world, with `wcl` separated
  out because `OpTabK.Down` has no such field.
- `SchedOKNKW` is the instance at `KW`.
- `schedOKNLe_iff_K` and `schedOKN_iff_K` show that `SchedOKN` is `SchedOKNK` at one world, at any
  floor.

`hs_schedOKN` at `KW` and the scheduler's `[handle]` at `erwpK` are the handlers unit.

## 6. Bookkeeping

- **Restated declarations:** `CanFold` and `erwpK_M_frameGen`'s `hcan` (§3). No other existing
  statement or definition changes. `vN`, `cN`, `KW.Post` and `KW.Owed` are unchanged.
- **Unspent hypotheses:** none. `tabRK_canK`'s `hLt` and `hFam` are used, and so is
  `erwpK_M_frameList`'s `mb`, which bounds the chosen lifetime.
- **Untranscribed in the run-up:** `cN` at `KW` and the re-pointing. §7 lists what the wiring
  unit left.

## 7. The tables wired to every frame class

The Lean is in `Core/Chain/TabKW835N.lean` (the guarded twin, the anti-frame, the guarded Mut
Frame, the reborrow, the Imm Frame) and `Core/Chain/FrameListKW835N.lean` (the list frames).

### 7.1 The lender's guarded twin

`tabGK R G S g F δ x` / `finGK` are `tabG` / `finG` at a world: `tabRK`'s entries, every
capturable one's cancel run at its cancel row's own guarded table (`cancelOblGK`: `cancelTabGRK` at
`g y`'s floor and view, ending at `R`). The lookups are `tab_lookupNGK` (a `tabNK` entry and the
`tabGK` entry at its key) and `tab_lookupGK` (a `tabGK` entry and the `tabRK` entry at its key).

### 7.2 Each class at the typed tables

| Frame | At the typed tables | Twin | Cancel transfer |
|---|---|---|---|
| Mut Frame, plain twin | `erwpK_M_frameCR_tab` (§3) | `tabNK_foldTwin` | `tabRK_canK` |
| Mut Frame, guarded twin (inside an anti-frame) | `erwpK_M_frameCRG_tab` | `tabNK_foldTwinG` | `tabGK_canK` |
| Mut Anti-Frame | `erwpK_M_antiFrameCR_tab` | `tabGK_sealTw` | `tabRK_canAK` |
| reborrow | `erwpK_rebGen_tab` | `tabNK_rebTw` | `tabNK_rebCanK` |
| Imm Frame, must-resume rows | `erwpK_I_frame_tab` | `tabNK_ifoldTwin` | `icanK_of_lin` |
| the `n`-cell Mut Frame | `erwpK_M_frameListKW` (§7.3) | `tabRK_foldTwinR` | `tabRK_canRK` |

- Every twin's lender entry owes along `KW.Owed` because the row's resuming layers are at scheduler
  names (`CTy.SchedOnly`, (S1)), and the entries of a scheduler entry's cancel row owe along
  `KW.Owed` whatever their names (`finSched`).
- Every cancel transfer is by induction on how deep cancel rows nest. Its step is the class's own
  cancel-run frame at the cancel row's tables at `KW` (`erwpK_M_frame_cancelRunCR`, `…CRG`,
  `…CRR`, `erwpK_M_antiFrame_cancelRunCR`, `erwpK_rebGen_cancelRun`), entered at the resumption
  world, where the frame's invariant holds.
- The remaining premises of each lemma are the original's premises on the claims, the guard and
  the reborrow's entry (`hG`, `hRin`, `hRout`; `hE`, `hreb`, `hOk`), and the typing side
  (`SuspendC`, `LtLife`, `SchedOnly`). None is about the tables.

**Two cancel conditions read `Inv` at the resumption world.** `ICanK` and `ASealCan` now take
`Inv y` for the resumption world `y`, as `CanFold` does (§3):
- old: `… → en.q ≠ .lin → ∀ y k ls …`; new: `… → en.q ≠ .lin → ∀ y, Inv y → ∀ k ls …`;
- the generic frames had `Inv y` there and discarded it; `tabRK_canAK` enters the anti-frame's
  cancel run at `y` and needs `KW.SealInv` there;
- the premise is weaker, so `icanK_of_lin`, `icanK_lift`, `asealCan_of_lin`, `asealCan_lift` and
  `asealCan_claimT` hold with their statements; no `_of_K` statement changes.

`RebCanK` is unchanged: the reborrow's invariant is `True`.

**The Imm Frame's cancellable layers are not wired.** `erwpK_I_frame_tab` takes rows whose every
layer is must-resume (`CTy.LinOnly`), the shape of `erwp_I_frame` (`ILendOK`). For a cancellable
layer the callback's cancel obligation is a cancel run at the lend's world, whose view holds the
record `(r, A)` in `Φ.imm` (`KW.lendImm`), while `erwpK_I_frame_cancelRun` runs the cancel run at
the lender's view. At one world the two are joined by `rwpG_tieEntry` (the record is in the frame's
list), but `erwp_tieEntry` / `erwp_tieEntryR` hold only at abortive tables. I have not derived the
cancellable case and have not verified that any obstruction is real. No typed constant performs a
resuming operation under an `imm` lend today (the `imm` slice frames are at `Row.Unwind` rows), so
this is off every constant's path.

### 7.3 The list frames

- **The world map.** The run is indexed by the outermost lender's worlds. `KW.LendMap g`: `g` is
  the identity or a lend after a `KW.LendMap`. Frame `j`'s lender owes at `g y`, its callback at
  `(g y).lend ℓⱼ αⱼ Fⱼ`, and its location family is `g y`'s view (`KW.lend_view`).
- **The table** (`tabListK A δ F S Θ g I`): the row's lender's twin under `g`, at `g`'s floor,
  ending at the claim of the cells `I` at `Θ`.
- **The step** (`erwpK_M_frameCRR_listKW`): `erwpK_M_frameCRR` with `LendOKCR`
  (`tabRK_lendOKCR`), the twin under `g` (`foldTwin_owedG`, `tabRK_foldTwinR`) and `CanFold`
  (`tabRK_canRK`, `tabR_canR` at `KW`). The claim joins the inner frames' by `tabRK_finLe`
  (`tabR_le` at `KW`, along `OpTabK.FinLe`).
- **The list** (`erwpK_M_frameListKW`) is `erwpK_M_frameList`'s induction with the world map
  carried. Each lifetime is chosen by `LocTy.exists_foldInv` (fresh and below every `imm` record),
  so the step's invariant holds where the lend is taken. The innermost callback is a premise at
  every `KW.LendMap` extension, as `hH` is in the original.
- `erwp_M_frameListRN` (abortive tables) is not restated at the typed tables: its stops are raises,
  which read no world.

### 7.4 Not in this unit

- `cN` and `vN` at `KW`, and the re-pointing of the typed lemmas: the typed compatibility lemmas
  (`withbor2S_compat`, `withbor3S_compat`, `withborFS_compat`, `withloadS_compat`, the slice
  lemmas) still read the frames at `erwp`.
- The handlers: `hs_schedOKN` at `KW` and the scheduler's `[handle]` at `erwpK`.
- The Imm Frame's cancellable layers (§7.2).

## 8. The field frame, the scheduler's `[handle]` and the finaliser's raise at `KW`

The Lean is in `Core/Chain/TabKW835N2.lean`; the producers it discharges are in
`Core/Chain/MechK835N4.lean` and `Core/Chain/HandleK835N.lean`.

**An entry's order at a part of the share.** `KW.Owed` and `KW.OwedR` read `ConsistentX` at the
continuation's share, and consistency passes to a part of a share only when the share is valid
(`consistentX_left`). So the producers that put a frame into the continuation's share read the
entry's order at the joint share with its validity, which every resource a run returns has
(`rwpG_validK`): `KW.OwedS.left`.

| Premise | Producer | At `KW` |
|---|---|---|
| order at the run's share, twin's cancel with the frame | `erwpK_frameGR` (`wF`) | `KW.OwedS.left`, `tabGK_canF`; together `erwpK_frameGR_tab` |
| the cancel row's frame | `erwpK_frame_cancelRunGR` | the step of `tabGK_canF` |
| the scheduler's order at `κ`'s share, every owed world valid | `erwpK_handle_schedKW` | `tabNK_wkLeft`, `tabNK_wkOK`; together `erwpK_handle_schedKW_tab` |
| the abortive payload across `D ()`'s stops (`hTk`) | `erwpK_ubindRaiseF` | `tabNK_raiseOwed` (`ExtR` at the share, `vN_extR` at its part) |
| the abortive payload at `D ()`'s post (`hTVr`) | `erwpK_ubindRaiseF` | `tabNK_raisePost` |

**Premise shapes changed.**
- `hTk` of `erwpK_ubindRaiseF` reads the payload at a part of the share the stop's order is read
  at (old: at every resource, which `𝒱⟦A⟧` along `ExtR` at the share does not give).
- `hRk` of `erwpK_frameL` receives the order at the joint share (old: at the run's share).
- The share-shrinking premises of `erwpK_frame_plain` (`hkl`, `hFk`), `erwpK_frameL`,
  `erwpK_ubindRaiseF`, `erwpK_cfin_run`, `erwpK_ubind_cancelRunF` and `cancelOblNK_ubind` (`hwk`)
  receive the joint share's validity (old: without it), so `KW.OwedS.left` discharges them.

Each premise is weaker or equal; at `Unit` each is trivial, and no `_of_K` statement changed.

**The handler at a world.** `erwpK_handleLe_le` carries an invariant `Inv` on worlds (at `KW`, a valid
location typing), read off every world the handled table's entries and the cancel tables' entries
owe a continuation at; the location family is downward closed there. A clause gets the stopped
run's Kripke stop (`KapRelK`) at the floor the stop chose.

**Not in this unit.** `hs_schedOKN` at `KW` (the pool's clauses at `KapRelK`); E5 at `KW`
(`tabNK` closed under a plain context, which `iterate`'s `hK`/`hKi` read).
