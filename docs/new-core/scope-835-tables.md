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

**Not in this unit.** `hs_schedOKN` at `KW` (the pool's clauses at `KapRelK`). E5 at `KW` is §9.

## 9. A row's table over a world index

The Lean is in `Core/Chain/RowFamK835N.lean` (the family, its two instances, the interface, E5),
`Core/Chain/ThenK835N.lean` (`[then]`'s producers) and `Core/Chain/IterKW835N.lean` (the loop at
`KW`).

### 9.1 The interface

A row's table, its cancel obligations and its entries are defined once over any world index `ι`,
from a record saying how they read a world (`RowRd ι M`):

| Field | Reading | One world (`rdU δ Θ c`) | Typed world (`rdKW g δ`) |
|---|---|---|---|
| `Θ`, `c` | where values and views are read | `Θ`, `c` | `x.Θ`, `x.c` |
| `wk μ m x f y ρ` | an entry at `m` under the mode `μ` owes at `y` | `True` | `(g x).OwedS μ m f (g y) ρ` |
| `M`, `sub`, `le` | the mode, a cancel row's mode, the order | `Unit` | scheduler names, `finSched`, inclusion |
| `V`, `Φ`, `fl` | the runs' post order, location family, floor | `True`, `Θ.view c`, `0` | `KW.PostK`, `(g z)`'s view and floor |
| `Inv` | the worlds the runs are read at | `True` | `(g z).Θ.Down` |

- **The family.** `tabF R μ C x`, `finF R μ C` and `R.ent` are `tabN`/`finN`/`entN`'s mutual
  recursion on `CTy`, an entry at `m` under `μ` and its cancel row under `sub μ m`; the cancel run
  is `R.canc T = erwpK R.V R.Φ (cancelTabK (R.fl ·) (T ·)) False`.
- **The instances.** `tabF_KW`/`finF_KW`: `tabF (rdKW g δ) S F x = tabNK S g F δ x`, and
  `finF` is `finNK`. `tabF_unit`/`finF_unit`: `tabF (rdU δ Θ c) () F x = liftTabK (tabN F δ Θ c)`,
  and `finF` is `finN` lifted (`canc_unit`: `cancelOblN` is the one-world `canc`).
- **What the interface needs** (`RowRd.OK`): every owed world satisfies `Inv`, where `Φ` is
  downward closed; an entry's order passes to a part of a valid share (`wkLeft`); `le` is a
  preorder, `sub` monotone with `μ ≤ sub μ m`; an entry under a higher mode owes at fewer worlds
  (`wk_anti`); posts are at the run's own world (`Veq`). `rdKW_ok`, `rdU_ok`.
- **`RowRd.PayExt`**: a value at a part of a stop's share is one at every world the stop owes. It is
  Core's `errOk_local` (`cfin_cancel` carries the kept error along `Ext`). `rdKW_payExt` (`g = id`,
  by `KW.OwedS.extR`, `LocTy.ExtR.left`, `vN_extR`), `rdU_payExt`.
- **The lemmas** are `tabN`'s, proved once: `tabF_effOf_find`, `tabF_effOf_some_find`,
  `tabF_rowOf`, `tabF_find_sig`, `tabF_rowOf_find`, `tabF_at`, `finF_eq_ite`, `entF_fin_cancel`,
  `entF_fin_of`, `errOkF_of_sub` (across modes), `errOkF_le`, `errOkF_ext`, `tabF_downI`,
  `tabF_wkLeft`, `tabF_wcl`, `entF_le_of_leF`, `finF_mono`, `tabF_rowLe_entry`, `tabF_plain₀`,
  `entF_plain`, `tabF_ctxClosed`.

**Why the modes.** At `KW` an entry's order depends on its name and on whether it sits in a
scheduler entry's cancel row (§1). A finaliser `D` is typed at its own row, under the scheduler
names `S`; the cancel run it is part of is the cancel row's, under `finSched S m₀ ⊇ S`. An entry
under the larger set owes along `KW.Owed` at least wherever it would under `S`, and `KW.Owed`
implies `KW.OwedR`, so a stop of `D` is a stop of the cancel run (`wk_anti`). At one world there
is one mode and nothing to read.

**Why `Inv`.** A run at a world needs that world's location family downward closed
(`rwpG_bind`, `rwpG_le`). At `KW` that holds where the location typing is downward closed, which
every owed world's is (`KW.Owed`/`KW.OwedR` give `Θ.OK`), but not at every `KW`. So the tables'
closure in the index and under a plain context are read at those worlds: `OpTabK.DownI`,
`OpTabK.CtxClosedI` (with `opTableK_downI`, `cancelTabK_downI`). At one world `Inv = True`, and
`OpTabK.Down.downI`, `OpTabK.CtxClosed.ctxClosedI` recover the unguarded forms.

### 9.2 `[then]`'s producers

| Original (`Then835N`) | Over the family | `_of_K` |
|---|---|---|
| `cfin_cancelN` | `cfin_cancelK` | `cfin_cancelN_of_K` |
| `cfin_runN` | `cfin_runK` | `cfin_runN_of_K` |
| `then_cancelN` | `then_cancelK` | `then_cancelN_of_K` |
| `seq_raise_runN` | `seq_raise_runK` | `seq_raise_runN_of_K` |
| `erwp_frame_then` | `erwpK_frame_then` | `erwp_frame_then_of_K` |

Each is the original's induction on the index and recursion on the cancel row. A script comparing
source text (`scratch-archive/rule791/cmp_ofK55.py`) confirms that each `_of_K` statement is the
original's word for word. What a world adds:

- **the joint share.** A producer puts a frame (the kept error, the pending raise, `[then]`'s
  context) beside a stop's continuation. The new stop owes at the joint share; the inner stop's
  order is read at its part (`wkLeft`, the joint share valid by `rwpG_validK`).
- **what rides is carried to the resumption world.** The kept error (`errOkF_ext`) and the
  pending raise's payload by `PayExt`; `[then]`'s frame by `hFe`, now read along the stop's order
  at a valid joint share:
  - old: `hFe : ∀ ls ls' ρ σ ρ', CompS ρ σ ρ' → extF ls ls' ρ' → Fr ls σ → Fr ls' σ`;
  - new: `hFe : ∀ μ' m x f y ls ls' ρ σ ρ', CompS ρ σ ρ' → Valid ρ' → R.wk μ' m x f y ρ' →
    extF ls ls' ρ' → Fr x ls σ → Fr y ls' σ`.

  At one world the new premise is the old one (the `_of_K` proofs pass it through). At `KW`,
  `gNFrame_carryKW` discharges it for `[then]`'s context `𝒢⟦Γ₂⟧ ∧ ConsistentX`.
- **modes.** `cfin_cancelK`, `cfin_runK` and `then_cancelK` cross from a mode to any higher one;
  `then_cancelK`'s recursion reads `D` under its own mode below the cancel row's.
- **`D` and the continuation** are read at every world satisfying `Inv`.

`erwpK_frame_then_tabKW` is `erwpK_frame_then` at `tabNK` under the scheduler names `S`, the
reading's premises discharged. What it leaves is `erwp_frame_then`'s premises at every world whose
location typing is downward closed, plus `hFe`.

### 9.3 E5 and the loop at `KW`

- **E5** (`tabNK_ctxClosed`): `(tabNK S g G δ x).CtxClosedI (fun z => (g z).Θ.Down) K` for a
  context with no handler that catches no cancel, by `tabF_ctxClosed`. That is `tabF_plain₀`,
  which is `cancelOblN_plain₀`'s recursion on the cancel row with `cancelK_plainI` (the cancel run
  under a plain context at `erwpK`, read at `Inv` worlds) for its step.
- **Closure in the index** (`tabNK_downI`).
- **The tick's invariant** (`tabNK_tickInv`): at the lender's tables (`g = id`), `𝒱⟦A⟧ ∧
  ConsistentX` at the stop's world, at the stop's whole share, is the same at every world the
  entry owes. The order is `ExtR` at the share (`KW.OwedS.extR`), along which `vN_extR` keeps the
  value, and the order makes the new view consistent with the share (`KW.OwedS.consistent`).
  `tabNK_tick` is `erwpK_iterateCI`'s `htick` at `tabNK` with `iterate_compatN`'s invariant.
- **The loop** (`erwpK_iterate_tabKW`): `erwpK_iterateCI` at `KW` at a row holding `Div`, with
  every table premise discharged. It leaves `erwp_iterateCI`'s turn, close path and answer, each
  read at every world whose location typing is downward closed.

**One statement changed: `erwpK_iterateCI` reads its runs at `Inv` worlds.**
- Old: `hΦ : ∀ x, (Φ x).Down`, `hTD : ∀ x, (T x).Down`, `hK`/`hKi : ∀ x, (T x).CtxClosed _`,
  `hturn`/`hclose` at every `y`, conclusion `∀ n, n ≤ N → ∀ x s ls ρ, …`.
- New: an invariant `Inv`, with `hΦ : ∀ x, Inv x → (Φ x).Down` and
  `hVI : ∀ x y, V x y → Inv x → Inv y`; `hTD : ∀ x, (T x).DownI Inv` (which also says every owed
  world satisfies `Inv`); `hK`/`hKi : ∀ x, (T x).CtxClosedI Inv _`; `hturn`/`hclose` at
  every `y` with `Inv y`; conclusion `∀ n, n ≤ N → ∀ x, Inv x → ∀ s ls ρ, …`.
- The old statement is the case `Inv = True`. `erwp_iterateCI_of_K` keeps its statement; its
  proof passes `Inv = True`. The new step is `erwpK_bind_leI`, `erwpK_bind_le` read at `Inv` worlds.
- No other existing statement or definition changed. `OpTabK.DownI`, `OpTabK.CtxClosedI` and
  `opTableK_downI` live in `MechK835N5.lean`, beside the loop that reads them.

### 9.4 How `cN` reads the family

`cN`'s `F_Σ` clause at `C = .eff m i q A B fin rc C'` is `erwp` at
`opTableN (extTabN m i (entN …) (tabN C' δ Θ c))`, and that table is `tabN C δ Θ c`. At `KW` the
re-pointed clause is

```lean
erwpK KW.PostK (fun z => z.Θ.view z.c) (fun z => opTableK z.lo (tabF (rdKW id δ) S C z))
  (fun z => retN C δ z.Θ) x n ls e ρ
```

that is, `tabNK S id C δ` by `tabF_KW`, with `S` the program's scheduler names (`Restrict835`).
Every lemma over the family then applies at `μ = S`, `R = rdKW id δ`:
- `then_compatN` at `KW` is `erwpK_frame_then_tabKW` with `Fr` the context and `gNFrame_carryKW`;
- `iterate_compatN` at `KW` is `erwpK_iterate_tabKW`;
- the lemmas that read `tabN`'s shape (`tabN_effOf_find`, `tabN_rowOf`, `tabN_rowLe_entry`,
  `finN_mono`) are read through their `tabF` forms.

At one world, `tabF_unit` and `erwp_tabF_unit` turn each statement back into today's.

### 9.5 Bookkeeping

- **Unspent hypotheses:** none. `RowRd.OK.le_refl` is read by `erwpK_frame_then`
  (`then_cancelK`'s `μ ≤ μ′` at one mode), `Veq` by the value cases, `PayExt` by
  `cfin_cancelK`, `cfin_runK` and `seq_raise_runK`.
- **Unused uniqueness/functionality results:** none.
- **Not in this unit:** `cN`/`vN` at `KW` and the re-pointing, `hs_schedOKN` at `KW`, E10, the
  Capture family, the Imm Frame's cancellable layers.

## 10. `cN` at `KW` and the typed layer re-pointed: the plan

### 10.1 How `cN` changes

**The relation takes the scheduler names.** `vN`'s `U` clause reads `cN`, and `cN` at `KW` reads
the scheduler names `S` through each entry's order (`KW.OwedS S m`). So every member of the mutual
block takes `S`: a thunk's computation is read at the program's scheduler names. No fixed `S` does:
`S = ∅` makes a lend callback's `await` owe along `KW.OwedR`, which the Mut Frame's fold cannot
give (`Kappa835N.not_extRFoldTransfer`); a larger `S` makes an ordinary handler's `κ` owe along
`KW.Owed`, which `U` does not read (`flooredExit`). `vN`'s clauses do not change: `U` reads `ExtR`
at the share with no floor (`scope-835-lendexit.md` §2).

**The tables read the new values.** The `F_Σ` clause's table reads payloads and answers at the
new `vN`, not at today's: a payload `U C` (the scheduler's task, a callback) must be a thunk of the
new `cN`. So the table is `tabF (rdKWv (vNW S) id δ) S C`, where `rdKWv vr g δ` is `rdKW g δ`
reading values at `vr`, and `rdKW g δ` is `rdKWv vN g δ`. This is §9.4's clause with the value
reading made explicit.

**Beside, not in place.** Redefining `Goal791N`'s block in place would break, at once, every proof
that opens `cN`'s `F`/`F_Σ` clause (39 files); the branch would not build until all were
re-proved. So the relation at `KW` is a new block, `Core/Chain/CNW835N.lean`:
`vNWE`/`vOWE`/`cNW`/`cBNW`/`retNXW`/`tabNW`/`finNW`/`retNW`, clause for clause `Goal791N`'s, with
`S` an explicit parameter. `Goal791N`'s block and every statement over it are unchanged.

| Clause | At `KW` |
|---|---|
| `F A` | `∀ lo, erwpK KW.PostK (·.Θ.view ·.c) (opTableK ·.lo OpTabK.empty) (vNW S A δ ·.Θ) ⟨Θ, c, lo⟩` |
| `F_Σ R` | `∀ lo, erwpK KW.PostK (·.Θ.view ·.c) (opTableK ·.lo (tabNW S S C δ ·)) (retNW S C δ ·.Θ) ⟨Θ, c, lo⟩` |
| `⊸`, `&`, `⊤`, `∀`, `ν` | `Goal791N`'s, at `cNW S` |
| `cBNW`'s `F`/`F_Σ` | as `cNW`'s, the leaves at `retNXW` |

- **`tabNW S μ C δ x`** is `tabNK`'s recursion inside the block (an entry at `m` owes along
  `x.OwedS μ m`, its cancel row under `finSched μ m`), reading `vNW S`. `tabNW_eq`:
  `tabNW S μ C δ x = tabF (rdKWv (vNW S) id δ) μ C x`, so every lemma over the family applies.
- **The floor is `∀ lo`.** No lemma relates a lend's floor to the lender's (`foldTwin_owed`
  takes `min f x.lo`); the scheduler's `[handle]` holds at every floor
  (`erwpK_handle_schedKW_tab`); a callback is read at the lend's world, whose floor is the lend's
  (`KW.lend`). A post keeps the floor (`KW.PostK`).
- **`F` at the empty table** is `erwp` at the empty table at every floor (no entry, no stop;
  `cNW_ret_iff`): its meaning is unchanged.

**`RowRd` reads values at a field.** `RowRd` gains `vr`, the value relation its entries' payloads
and answers are read at; `RowRd.OK` gains `vrDown` (closed in the index) and `vrPers` (a value of a
persistent type owns nothing), the two facts about `vN` the family's lemmas use; `PayExt` reads
`vr`. `rdKW` and `rdU` set `vr := vN`, so their statements and every statement over them are
unchanged.

### 10.2 The laws

| Law | At `cNW` |
|---|---|
| `vN`'s μ machinery (`vBN`, `vN_roll`/`unfold`/`mu_iff`/`ind`, `vFN`), the environment lemmas | proof text unchanged, at `vNW S` |
| `vN_extR`, `vN_outlives(Le)`, `vN_extend_of_not_free`, `vN_local`, `vN_inStratum_bnd`, `vN_add_eq_bnd`, `vN_above`, `vN_fam_down`, `vN_empty_of_persistent` | unchanged: no clause but `U` reads `cN`, and `U` reads it only through `ExtR`/`δ` |
| `cN_down`, `cN_le`, `cBN_le` | `erwpK_le` at `Inv = (·.Θ.Down)`, the tables by `tabF_downI` |
| `tabN_down`, `finN_down` | `tabF_downI` (at `rdKWv`) |
| `cN_congr`, `tabN_congr`, `finN_congr`, `cBN_congr`, `cBN_poly_ty` | the same recursion at `tabNW`/`finNW` |
| `cBN_mono`, `cN_nu_*`, `cN_head` | `erwpK_mono`, `erwpK_det` |
| `cN_effOf` | `tabNW` at `CTy.effOf` |
| `cN_extA` | the world changes along `ExtA`: a re-indexing of `erwpK` (§10.3, `erwpK_reindex`) |
| new: `rdKWv_ok`, `rdKWv_payExt` at `vNW S` | from `vNW_down`, `vNW_empty_of_persistent`, `vNW_extR` |

### 10.3 The compatibility lemmas

| Class | Lemmas | At `KW` |
|---|---|---|
| no stop owed (values, `ret`, `bind`, the heap and family operations) | `Rules834N` (22), `Fundamental831N` (18), `Fam836N` (21), `FamNew/Slice/Swap836N`, `Count834N`, `Mu836N`, `Nu837N`, `mutSub`/`immSub`/`allI` | the original proof at `erwpK_val`, `erwpK_of_rwp`, `erwpK_bind`, `erwpK_mono` at every floor |
| stops at the row | `perform_compatN`, `raise_compatN`, `sub_compatN`, `await_compatN`, `let_compatN`, `then_compatN`, `thenDiv_compatN`, `iterate_compatN`, `divFuel_compatN` | `erwpK_perform`, `tabF_rowLe_entry`/`finF_mono` for `sub`; `erwpK_frame_then` at `rdKWv`; `erwpK_iterateCI` at `rdKWv` (`erwpK_iterate_tabKW` restated over `vr`) |
| handlers | `handleT_compatN`, `handleL_compatN` | `erwpK_frame_plain_or`, `erwpK_consistentPA`, `KapRelK.extF`, `erwpK_handle_le` |
| lends | `w2`, `w3`, `wF`, `wl`, `sm` (the `*S_compat`), `withbor1/2/3`, `withload`, their `U` forms, `sliceBorrowM/I`, `foldOwnG`, `foldImm`, `withswap` | the frames at the typed tables (§3, §7, §8), restated over `vr`; the callback by `erwpK_reindex` |

**What the lend class needs that is not built.**
- **The table layer over `vr`.** `tabNK`, `tabRK`, `tabGK`, `tabListK` and their lemmas
  (`TabK835N`, `TabKW835N`, `TabKW835N2`, `FrameListKW835N`) read `vN`. They are restated over
  `vr`, reading the facts `vN_extend_of_not_free`, `vN_inStratum_bnd`, `vN_add_eq_bnd`,
  `vN_extR`, `vN_local` of `vr`; the old statements are the instance `vr = vN`.
- **`erwpK_reindex`.** A callback `U F` gives `cNW S F (δ.extend x α) Θ′ c′` at the lend's world
  `x.lend ℓ α F`, its tables indexed by its own worlds. The frame reads it indexed by the lender's
  worlds, at `tabNK S (·.lend ℓ α F)`. The step is `erwpK` along a world map `g` whose image of an
  owed world is owed (`KW.lend` preserves `KW.Owed`), with the values moved by `vN_add_eq_bnd`.

### 10.4 Order

1. `RowRd.vr`; the block `CNW835N.lean`; `tabNW_eq`; the laws of §10.2; `rdKWv_ok`,
   `rdKWv_payExt`.
2. The table layer over `vr`; `erwpK_reindex`; the constants' compat lemmas `w2`, `w3`, `wF`, `wl`,
   `sm`.
3. `let`, `then`, `iterate`, `await`, `perform`, `raise`, `sub`; the handlers T and L.
4. The rest of §10.3.
5. `SemJNW`, `ConstNW`, `FundamentalNW`, `fundamentalNW_all`; `Goal791SchedNW`.

### 10.5 The headlines

No headline's statement or proof changes: each is a statement over `Goal791N`'s `cN`, `erwp` or a
program, and none of those changes.

| Headline | At `KW` |
|---|---|
| `*_compatN`, `constN_*`, `constN_*_inst`, `constsN_of`, `fundamentalN_of`, `fundamentalN_all` | a new statement beside, over `cNW S` (`*_compatNW`, …, `fundamentalNW_all` with `MissingNW`). The old one does not follow from it (another relation) and is not replaced in this unit. |
| `goal791Sched_of*`, `goal791SchedN_of_handlerLaw` | `Goal791SchedNW` beside: the same conclusion (`OrDiverges` of the scheduled program), with `Restrict835 (· = n₀)` and the scheduler's contract at `KW` (`SchedOKNKW`) in place of `SchedOKN`. The old one is replaced once `hs_schedOKN` at `KW` and E10 close `Goal791SchedNW`. |
| `*_of_K`, the `erwp` laws, `erwp_consistent`, the `#820` `*Prog` results | unchanged: they are about `erwp` and concrete programs. |

No headline changes meaning: the old ones keep theirs, and the new ones say the same thing about
the relation at `KW`.

### 10.6 What is built

**Checkpoint 1: the relation and its laws** (`Core/Chain/CNW835N.lean`).
- The block `vNWE`/`vOWE`/`cNW`/`cBNW`/`retNXW`/`tabNW`/`finNW`/`retNW` of §10.1, with `gNW` and
  `SemJNW`. `tabNW_eq`/`finNW_eq`: `tabNW Sch μ F δ x = tabF (rdW Sch δ) μ F x`, with
  `rdW Sch δ = rdKWv (vNW Sch) id δ`; `rdW_ok`, `rdW_payExt`.
- Every law of `Goal791N` §2 at `cNW`, including the μ/ν machinery.
  - Proof text unchanged except for the renaming: `vNW_extR`, `vNW_local`, `vNW_inStratum_bnd`,
    `vNW_add_eq_bnd`, `vNW_above`, `vNW_outlives(Le)`, `vNW_extend_of_not_free`, `vNW_congr`,
    `vNW_ind`, `cNW_nu_*`.
  - Re-proved at the new clauses:
    - `cNW_down` and `cBNW_le` (with `cNW_eff_down`/`cBNW_eff_le`), by `erwpK_le`. The tables are
      closed in the index at the worlds whose location typing is downward closed (`tabNW_downI`,
      `finNW_downI`, by `extTabK_entNK_downI`, `cancelOblK_id_down`).
    - `tabNW_congr`/`finNW_congr` (now with the mode), `cNW_congr`, `cBNW_congr`.
    - `cBNW_mono`, by `erwpK_postMono`.
    - `cNW_effOf` (`F_Σ R` at every floor at `tabNW`) and `cNW_effOf_tabF` (the same at `tabF`).
    - `cNW_extA`, by `erwpK_empty_move` (a run at the empty table reads no world).
    - `cNW_head`/`cBNW_head`, by `erwpK_ret_det`, `cNW_eff_det`, `cBNW_eff_det`.
    - `vNW_empty_of_persistent`.
  - `cNW_ret_iff`: `F A` at `KW` is `erwp` at the empty table, so `F`'s meaning is unchanged.
- **`RowRd` reads values at a field** (`RowFamK835N`). `RowRd.vr`, `RowRd.OK.vrDown`/`vrPers`,
  `RowRd.OK.vr_le`, and `rdKWv`. `rdKW` is `rdKWv` at `vN`; `rdU` sets `vr := vN`.
  - Restated: `RowRd.ent`/`PayExt` read `R.vr`.
  - `errOkF_le` and `errOkF_empty_of_pers` take `hR : R.OK`.
  - `seq_raise_runK`'s pending payload is read at `R.vr`.
  - The `_of_K` statements, `tabF_KW`, `tabF_unit` and every statement at `rdKW`/`rdU` are
    unchanged.

**Toward checkpoint 2** (`Core/Chain/ReindexK835N.lean`).
- `erwpK_comap`: a run from `g x` indexed by `ι` is a run from `x` indexed by `ι′`. It needs the
  location family at `y` to be `g y`'s, the posts carried, and each stop at `g y`'s table to be a
  stop at `y`'s whose continuation is owed only at images. It is read at the worlds an invariant
  holds at.
- `LocTy.extR_add`: adding a lend at `α` is an extension at a resource in `Res_α`, without
  freshness. So `vNW_add_eq` holds at every world: `𝒱⟦A⟧` of an `A` outliving the bound does not
  see a lend below it. The callback's payloads and answers therefore move between the lender's
  world and the lend's world with no `FoldInv`.

### 10.7 What is left

- **The callback's table step**, read by `erwpK_comap` at `g = (·.lend ℓ α F)`: a stop at
  `tabF (rdW Sch δ′) μ F (g y)` is a stop at `tabF (rdKWv (vNW Sch) g δ′) μ F y`.
  - The payload and answer move by `vNW_add_eq` and `vNW_extend_of_not_free`; the answer's view
    by `consistentX_of_outlives`.
  - The order is the same.
  - The cancel obligations move by `erwpK_comap` again, by recursion on the cancel row.
- **The table layer over `vr`.** `tabNK`/`tabRK`/`tabGK`/`tabListK` and the frame lemmas of §3,
  §7 and §8 are read at `vN`. They need to be restated at `rdKWv vr`, or as `tabF` at a reading
  with the lender's twin, so that the frames apply to `vNW`'s tables.
- **The compatibility lemmas** of §10.3, all classes; `SemJNW`-level statements, `FundamentalNW`,
  `fundamentalNW_all`, `Goal791SchedNW`.

### 10.8 The swap: the relation at `KW` under the canonical names

`scope-835-qualifier.md` §5 replaces §10.1's "beside" and its `Sch` parameter.
- `Core/Chain/Goal791N.lean` is the relation at `KW` under the canonical names
  (`vNE`/`vOE`/`cN`/`cBN`/`retNX`/`tabN`/`finN`/`retN`, `vN`/`vO`/`vNX`/`vOX`, `gN`, `SemJN`,
  `rowTabN`, the μ/ν machinery) with §10.2's laws. There is no scheduler-name parameter and no
  mode: every entry, and every entry of a cancel row, owes along `KW.Owed`. `rdN δ` is
  `rdNv vN id δ`, the one-mode reading (`RowRd KW Unit`); `tabN_eq`/`finN_eq`:
  `tabN F δ x = tabF (rdN δ) () F x`.
- `Core/Chain/Goal791N0.lean` is the one-world block and its statements. Every name the `KW` block
  also defines carries `₀` there and at every use (`vN₀`, `cN₀`, `tabN₀`, `vN_down₀`, …, and
  `finN_eq₀`, `vN_empty_of_persistent₀` from `Cancel791N`/`ImmLend833N`). Names only the old block
  defines (`ConstN`, `FundamentalN`, `Goal791SchedN`, `tabN_down`, the `*_compatN`) keep theirs
  until they are restated.
- `CNW835N.lean` is deleted. Done-when for the rework: `Goal791N0.lean` deleted and no `₀` name
  left.
- The table layer at `vr` starts at `rdNv vr g δ` (`RowFamK835N`), `rdKWv` at one mode, with
  `rdNv_ok` and `rdNv_payExt`. `tabNK`/`tabRK`/`tabGK`/`tabListK` still read `vN₀`.

### 10.9 The table layer at one mode, and the callback's table step

**The tables at a value relation, one mode.** `tabNK vr g`, `finNK`, `tabRK R vr g`, `finRK`,
`tabGK R G vr g`, `finGK` (`TabK835N`, `TabKW835N`) read values at `vr` and owe every entry, and
every entry of a cancel row, along `KW.Owed` from `g x` to `g y`. `tabF_N`/`finF_N`:
`tabF (rdNv vr g δ) () F x = tabNK vr g F δ x`; `tabNK_vN`/`finNK_vN`: at `vr = vN`, `g = id` it is
`cN`'s `tabN`/`finN`. What the frames read of `vr` is `ValRelOK` (closed in the index, empty at a
persistent type, blind to an unmentioned variable, in the stratum below a bound the type outlives,
kept along `ExtR`); `valRelOK_vN` discharges it.

- Every frame lemma of §3, §7, §8 is restated with `S` replaced by `vr` and `hv : ValRelOK vr`
  where it reads a value fact. With one mode, every twin's lender entry owes along `KW.Owed` at
  every name, so the premise `F.SchedOnly S` is gone from `erwpK_M_frameCR_tab`,
  `erwpK_M_frameCRG_tab`, `erwpK_M_antiFrameCR_tab`, `erwpK_rebGen_tab`, `erwpK_I_frame_tab`,
  `erwpK_M_frameListKW` and their transfers. `KW.OwedS`, `finSched`, `CTy.SchedOnly`,
  `rdKW`/`rdKWv` and the `*_sched` lookups are removed; nothing outside the layer read them.
- The list frames (`FrameListKW835N`) are at `vN`: `claimL`, `listPostN`, `mutLeafN`,
  `ownLeafN_inStratum` at `vN`, the old ones renamed `₀`.
- `[then]` and the loop are stated at `cN`'s `tabN` (`erwpK_frame_then_tabKW`,
  `erwpK_iterate_tabKW`, `tabN_tick`), `[then]`'s frame carried by `gN_extR` at `KW`
  (`Iface834N`'s is `gN_extR₀`).

**The callback's table step** (`ReindexK835N`). `tabNK_lend_comap`: a stop at
`tabNK vN id F δ′` at `y.lend ℓ α F` is a stop at `tabNK vN (·.lend ℓ α F) F δ′` at `y`. The
payload and the answer move by `vN_lend_eq` (`vN_extend_of_not_free`, then `vN_add_eq`); the
answer's view by `consistentX_of_outlivesN`, which reads the constants' closed bound
(`LifeCtx.empty.Defines bnd`, a conjunct of `Const791.OK`); the order is the same; a cancel
obligation moves by `erwpK_comap`, by induction on how deep cancel rows nest. `erwpK_lend_comap` is
`erwpK_comap` with that step: the callback's run at `tabN F δ′` from the lend's world is its run
indexed by the lender's worlds at the table `erwpK_M_frameCR_tab` reads. `erwpK_M_frameCR_cN` is the
Mut Frame with its callback read that way: a run at `tabN F δ′` from the lend's world, the lender
at its twin `tabRK` at `vN`.

### 10.10 The compatibility lemmas at `cN`: what is restated

Every restated lemma takes the real name; the one-world one keeps its proof under `₀`.

- **`F A` is `erwp` at the empty table** (`cN_ret_iff`), so every rule whose conclusion and premises
  are value judgments keeps its one-world proof, `F A` built by `cN_ret_of` and read by
  `erwp_of_cN_ret` (`RulesKW835N`, `FamKW835N`, `CountKW835N`, `FamOpsKW835N`, `MuKW835N`,
  `FoldGKW835N`, `FoldImmKW835N`). The pure-row lends are such rules: their callbacks stop nowhere,
  so the one-world Mut/Imm Frames and the reborrow apply at the empty table (`BorrowKW835N`,
  `ImmLendKW835N`, `WithloadKW835N` with `withload_rebT` over a table `T`, `FamImmKW835N`).
- **`F_Σ R` is `erwpK` at every floor.** `cN_bind` binds a stop-free run into it
  (`erwpK_bind_frame`); `[sub]` by `tabF_le_of_rowLe`; `[perform]`/`[raise]` stop at once
  (`erwpK_perform_here`, `erwpK_raise_here`, `entN_start`); `[let]`/`[await]` by the plain frame at
  the worlds whose location typing is `OK` (`erwpK_frame_plainI`), the frame `letFrN` carried along
  `KW.Owed`; `[then]` by `erwpK_frame_then` at `rdN`; `iterate` by `erwpK_iterateCI` at the `OK`
  worlds (`tabN_downI_OK`, `tabN_ctxClosed_OK`), its step read at the world the loop is at.

**Not restated.** `divFuel`; the tail and last handlers; `ν` (`nuIn`, `nuOut`, `unfoldN`); the
unwinding-row lends (`withbor1U`/`2U`/`3U`, `withloadU`, `sliceBorrowMU`/`IU`); the suspending
lends (`withbor2S`/`3S`/`FS`, `withloadS`, `sliceBorrowMS`) and their `_inst`; `MissingN`,
`fundamentalN_all` at `SemJN`. What each needs that is not built:
- the finaliser frame (`erwpK_ubindClaimRT`, `erwpK_ubind_cancelRunCR`) is stated with
  `∀ x, (Φ x).Down` and its outer table `Down` at every world, and `erwpK_handle_le` with its tables
  `Down` at every world; at `KW` these are built only at the worlds whose location typing is
  downward closed (`tabNK_downI`), so each is wanted in its form at the worlds an invariant holds
  at, as `erwpK_frame_plainI` is `erwpK_frame_plain`'s;
- the lender's twin carrying the view's consistency to its claim (`erwp_claimX`) and the finaliser
  over its cancel runs, at `tabRK`, by induction on how deep cancel rows nest;
- `ν`'s one unfolding at `F A` and `F_Σ` (`cBN_step`, `node_okN`) at `erwpK`;
- `div_fuel`'s handler by hand (`fuel_totalN`) at `erwpK`, its tick resumed at the stop's own world.

### 10.11 The suspending constants at `cN`

**The finaliser frame and the handler at an invariant** (`MechK835N`, `HandleK835N`).
`erwpK_ubindClaimRTI`, `erwpK_ubind_cancelRunCRI`, `erwpK_handleLe_leI`, `erwpK_handle_leI` and
`erwpK_ccatchLeI` are read at the worlds an invariant `Inv` holds at: the location family closed in
the index there, the tables closed in the index at those worlds (`opTableK`/`cancelTabK` `Down` at
`Inv x`; for the handled run's table, `OpTabK.DownAt`), and every world a stop at a floor no
higher than the run's is resumed at is one `Inv` holds at. The finaliser's claim is read at a world
(`R : ι → Nat → WProp`). Each old statement is the instance at `Inv = True`, its claim constant.

**The claim at a world** (`ClaimKW835N`). At `KW` the finaliser runs `D ()` at the world the `raise`
is at, so the claim it consumes is consistent with that world's view. `tabRWK`/`finRWK` are
`tabRK` at `g = id` with the claim read at a world; `claimXK R z = R ∧ ConsistentX z.c`.
- `erwpK_claimXK`, `erwpK_cancelRun_claimXK`: the lender's run carries the consistency to its claim,
  by induction on how deep cancel rows nest. A continuation is resumed at a world whose view is
  consistent with its share (`KW.Owed`) and with the answer (the entry's answer).
- `tabRWK_ubindCan`: the finaliser over the lender's cancel runs, by `erwpK_ubind_cancelRunCRI` and
  the same induction. `erwpK_ubindClaimRWK`: the finaliser around the body.

**The lender's floor** (`erwpK_flr`, `LendInv`). The claim's content and the lender's post are
values at the lend's world `Θ`; the finaliser and the post read them at the world they are at. The
lender runs from `KW.flr a x`, the floor no higher than `a` (a run there is a run from `x`,
`erwpK_comap` at `KW.flr a`). Every stop then chooses a floor at most `a`, so every world the
lender's run reaches has the location typing above `a` of `Θ` (`LocTy.ExtP.above_eq`); a value in
`Res_a` at `Θ` is one there (`vN_above`). `a` is the lend's lifetime (`withbor2S`, `withbor3S`,
`withborFS`) or the cells' and the result's stratum (`sliceBorrowMS`).

**The constants.**
- `withbor2S_compat`: the Mut Frame with the callback a thunk of `cN` (`erwpK_M_frameCR_cN`), then
  `erwpK_claimXK` and `erwpK_ubindClaimRWK`, `fin_claim`.
- `withbor3S_compat`, `withborFS_compat`: the anti-frame (`erwpK_M_antiFrameCR_tab`, its invariant
  `KW.SealInv`) around the guarded Mut Frame with the callback a thunk of `cN`
  (`erwpK_M_frameCRG_cN`); the resealed source carries `Res_α` (`Rout`); `withborFS` frames the
  opened cell outside (`erwpK_frameGR_tab`) after the `load`.
- `withloadS_compat`: `withload_rebT₀`'s steps at `erwpK` (`withload_reb`), 6.150 at the row's
  table at the typed world (`erwpK_rebGen_tab`), the callback at the image (`callback_at_image`,
  `tabN_extend_suspendC`).
- `sliceBorrowMS_compat`: the `n`-cell frame with its lends read by a predicate
  (`erwpK_M_frameListKWP` at `KW.LendMapB`: lends below the bound and the result's stratum); the
  callback, a thunk of `cN` at the innermost lend's world, read at the lender's worlds
  (`erwpK_lendMapB_comap`, its posts moved along an invariant on the callback's worlds).
- `ConstN`, `ConstsN`, `FundamentalN` at `vN`/`SemJN` (`ConstKW835N`); `constN_*`, `constsN_of` and
  the instances at the hardest case's row, their finalisers read at `SemJN`.

**Not restated.** `divFuel`; the tail and last handlers (`erwpK_handle_leI` is ready for them);
`ν`; the unwinding-row lends; `MissingN` and `fundamentalN_all` at `SemJN`; the instance with a
callback that performs (`withbor2S_perform`).

### 10.12 The handlers, `div_fuel` and the unwinding-row lends at `cN`

**The handlers** (`HandleTKW835N`, `HandleLKW835N`). `erwp_handle_tail` and `erwp_handle_last` at
`erwpK` are `erwpK_handle_leI` at the handled row's table, pre-passed by `erwpK_postPA`.
- **The pre-pass.** A stop at the handler's name records in its payload the view's consistency and
  that its world's location typing is `OK`. It also owes its continuation at the worlds at its own
  location typing and view, at a floor no higher (`postOK`). The stop's share is consistent with
  its own world's view (`rwpG_consistentXV`), so the entry owes it there (`KW.owed_of_post`).
- **A clause** pays its `β` step. It then runs its answering function, or its work, from the floor
  `f` the handled stop chose (`erwpK_flr_tabN`), under the resume frame
  (`erwpK_frame_plain_orI`) or the finaliser frame (`erwpK_frame_then_tabKW`).
- **The frame** is `κ`'s relation, with the world reached owed from the clause's world at `f`, at
  the frame's share. Each of the function's stops is taken at a floor no higher than `f`. Its world
  is owed at `f` from the last (`KW.Owed.floor_le`, `KW.Owed.of_post`, `KW.Owed.trans`). So `κ` is
  resumed or cancelled at the world the function's value is posted at.
- The frames' `hFk`/`hFe` receive the stop's floor bound, which `erwpK_frame_then` and
  `then_cancelK` already had in scope.
- `[handle-last]`'s exit runs at the world the cancel run of `κ` returns at. Its argument is carried
  to each world that run resumes at (`vN_extR`).

**`div_fuel`** (`FuelKW835N`). `fuel_totalN` at `erwpK`, by induction on the index, from a resource
consistent with the view of a world whose location typing is `OK`. A tick is resumed at the stop's
own world, which the tick's entry owes at every floor (`KW.owed_self`). An operation of `Σ` passes
the handler; the run goes on at each world its entry owes.

**The unwinding-row lends** (`UnwindKW835N`). An unwinding row's operations are abortive, so a run
at its table stops only at `raise`s, which owe no continuation and read no world. `F_Σ R` at such a
row is therefore one run at one world (`cN_unwind_iff`, by `erwpK_abort_move` both ways), at the
one-world table `tabUN`, whose payloads are read at `vN`. `withbor1U`, `withbor2U`, `withbor3U`,
`withloadU`, `sliceBorrowMU` and `sliceBorrowIU` are the one-world proofs, with `tabUN`'s facts in
place of `tabN₀`'s.

**`tabRWK` and `tabRK`.**
- At `g = id`, `tabRK R vr id` is `tabRWK (fun _ => R) vr` (`tabRK_id_eq`, `finRK_id_eq`).
- `tabRWK` cannot replace `tabRK` as defined. `tabRK` is read under world maps other than `id`:
  the lend-shifted twin `(g ·).lend ℓ α F` in `FrameListKW835N` (`tabRK_foldTwinR`, `tabRK_canRK`)
  and `ReindexK835N`. `tabRWK` has no world map.
- One definition can cover both: `tabRWK` with a world map, its claim read at a world. That changes
  the claim argument of every statement over `tabRK`.

**Not restated.** `ν` (`nuIn`, `nuOut`, `unfoldN`); `MissingN` and `fundamentalN_all` at `SemJN`;
BOXED-κ's `stop_semN`/`SemCSN`, which is not a compatibility lemma.
### 10.12 `ν` at `cN`

`Core/Chain/NuKW835N.lean` restates `Nu837N` at the relation at `KW`. The one-world statements keep
their proofs under `₀`.

- **The unrolling.** These go through with the proof text unchanged: `vNX_inst_occ`,
  `vNX_inst_poly`, `retNX_inst`, `thunkRN_nuCand`, `cBN_unroll`, `cN_nu_iff`, `nuIn_compatN` and
  `nuOut_compatN`. `tabN_instT` holds at every world.
- **`cBN_step`** (Core's `cB_step`). `F` and `F_Σ` are runs at every floor. A pure step in front is
  handled by `erwpK_ret_det` and `cBN_eff_det`.
- **`node_okN`** (Core's `node_ok`). The leaf runs `c ()`, then maps its answer. At `F_Σ` that run
  stops at the row's table, so the map is bound in by `erwpK_bind_leI`:
  - it is read at the worlds whose location typing is `OK` (`tabN_downI_OK`, `tabN_ctxClosed_OK`);
  - it holds up to the step's index, which replaces `erwp_mono_le`;
  - the answer is mapped at the world it is posted at (`map_okN` at that world's location typing).

  `F A` takes the same route, at the empty table.
- **`unfoldN_compatN`**. Coinduction with `candNN`, as in `Nu837N`. The outer values are built by
  `cN_ret_of`.
- **`reify`'s loop values.** Core's `candR_post` cases on three loop values. Two of them read no
  handler, and these hold at one unfolding at every candidate:
  - `doneLoop_cBN`: `done b`; its *close* runs the residual at `cN (F_Σ R)`;
  - `clLoop_cBN`: `closed r`, at a candidate holding `closed r`.

  Both read the row through `cBN_effOf` (Core's `cB_effOf`, at every row), `vNX_rename` and
  `nuAnsN_inl`/`nuAnsN_inr`.

**Not built.** The loop made at a tick: `candR`'s first disjunct, `reify_next`, `reify_close`. It
is the handler's induction over a segment (`hnd_tick`, `hnd_fwd`, the resumption of the stored
`κ`), so it waits on the handler step at `erwpK` (E10, §12.5 of `scope-831-interface.md`).
