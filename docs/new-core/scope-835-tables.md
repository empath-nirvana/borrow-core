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

**Not built: the step at `KW`.** It needs:

- the lender's twin `tabRK` at an incoming claim inside the callback (`tabR_canR`, `tabR_le` at
  `KW`);
- a location family `Φ Θ c y` that follows the lends the frames took. Inside the frames the run is
  indexed by the outermost lender's world.

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
- **Untranscribed in the run-up:**
  - the list frames' step at `KW` (§4);
  - the `imm` fold and the anti-frames (another unit);
  - `cN` at `KW` and the re-pointing.
