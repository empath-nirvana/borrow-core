# #835: posts across a lend's exit, at the Kripke stop (superseded)

Superseded: this note builds on the restriction (`Restrict835N.lean`), which was retired. The
current design is `chain-interpretation.md` (the interpretation at the typed world `KW`, the
departures from Core, what is proved and what is open), `scope-835-tables.md` §10 and SPEC §62; the
configurations are indexed in `configurations.md`. The body below is the record of that design and
cites files that no longer exist.

This settles the item `scope-835-kripke-stop.md` §5 left open: what a lender's post is after a lend
it took has exited, and whether E10 survives for an ordinary handler around that lender. The Lean
is in `Core/Chain/LendExit835N.lean`. It builds on `Core/Chain/SI/ErwpK.lean` (`erwpK`, `KW`) and
`Core/Chain/Restrict835N.lean` (the restriction, `scope-835-restriction.md`).

## 1. The question

After `vN_local`, a lend's callback result is a value at the lender's location typing `Θ`. The cost
map assumed `vN`'s `U` would read its futures along `ExtP` at the world's floor. Under that
assumption, the result is a value only at the lend's floor `α`, which is below the lender's floor
`lo`. The two routes were:

- **Route 1:** the lender posts at the lower floor `α`. The worry was that a later stop by the
  lender then owes along `ExtP α`, while an ordinary handler around it (a name outside `Sched`, no
  lend live at its operation) reads `κ` at `U` at its own floor `lo`. `main` proves E10 for that
  handler.
- **Route 2:** a lemma raising the floor of values whose borrow cells all lie above `lo`.

## 2. Verdict

**Route 1 does not lose E10, and route 2 is not needed.** Both questions turn on `U` reading a
floor. Under the restriction it does not have to, and it should not.

- **The worry is real if `U` reads a floor.** `flooredExit` / `flooredExit_inst` (Lean, every
  hypothesis discharged):
  - The stuck `κ = ()` at the empty world meets the obligation along `ExtP α`
    (`kapRelP_floor_world`). No public extension at `α` has a key above `α`, so no answer of type
    `Mut 'x 1` at `β > α` exists there (`not_bMut_extP`).
  - The same `κ` fails `U` read along `ExtP lo` for `lo ≥ β` (`Public835N.not_kapRelP_world`).
  - So a floored `U` at the handler's floor cannot read `κ` from a stop at the lowered floor.
- **Under (S1) the entries outside `Sched` owe along `ExtR`, with no floor.**
  - (S1) says no lend's callback performs a resuming operation outside `Sched`. So a stop at a name
    outside `Sched` has no lend frame between its `perform` and its handler.
  - The one producer that cannot owe along `ExtR` is the Mut Frame's fold
    (`Kappa835N.not_extRFoldTransfer`). That producer, and the `imm` and anti-frames with it, only
    forward stops from a lend's callback, so they never build a stop at such a name.
  - So these entries can owe along `KW.OwedR x y ρ`: `ExtR` at the share, a valid location typing,
    and a view consistent with the share. That is exactly the order `vN`'s `U` clause reads today
    (`Goal791N.vN`, `.thunk`; `vN_thunk_iff_kapRelR`).
- **`OwedR` does not read the floor**, so the floor at which the stop was made does not matter:
  - `KW.owedR_floor`: a stop's world at any floor owes the same worlds.
  - `contShareK_owedR_lo`: a stop at an `OwedR` entry is a stop at every floor bound. The floor of a
    lowered post, and the floor the stop chose, are both irrelevant.
  - `contShareK_owedR_U`: the obligation has `U`'s quantifiers (every `Θ′` along `ExtR` at the share,
    every valid `Θ′`, every consistent view, every list) at every floor of the resumption world.
    This is E10's world step: the obligation is `KapRelR`, and `KapRelR` is `vN` at `U`.
  - `not_kapRelR_world`: the stuck `κ` of `flooredExit` fails `OwedR`'s reading at the same world
    and share. So the order outside `Sched` excludes that configuration at every floor.
- **The lend's exit then costs nothing.** With `U` along `ExtR`, `vN` is `main`'s chain `vN`
  unchanged, and the exit is `vN_local` as it is today (§4). The lender posts at its own world, at
  its own floor. Nothing has to be raised, so route 2 does not arise.
- **The restriction stays where it is.** `owedR_not_owed`: the order of a stop under a live lend
  (`KW.Owed` at the lend's floor) owes fewer worlds than `OwedR`, because a key added above the
  lend's floor is an `ExtR` move and not an `ExtP α` one. So a `Sched` stop is still not readable at
  `U`, and only the scheduler (a contract, `SchedOKN`) may catch one.

How this sits in [DNB]'s terms (`scope-835-public.md` §2, §4): §7.2's collapse asks that the stop
and `U` read one order. Outside `Sched` that order is `ExtR` on both sides. Inside `Sched` the stop
reads `ExtP f`, and no value reads it, because the scheduler holds `κ` under `SchedOKN` and not at
`vN`.

## 3. A consequence for `KW.Post`: posts keep the floor

`KW.Post` lets a post lower the floor (`y.lo ≤ x.lo`). That lowering was route 1's encoding, and
with `U` floor-free nothing needs it. It also does harm:

- `not_owed_post_lower`: `KW.Owed`'s bound `y.lo ≤ x.lo` is not carried along a post that lowers the
  floor. The stop's own world is owed at the higher floor and not at the lower one.
- `not_tabLe_post_lower`: so a table whose `Sched` entries owe along `KW.Owed` at the world is not
  `TableK.Le` along such a post. That is `erwpK_bind`/`erwpK_shift`'s premise `hTV`. The
  configuration is a stop at the lower world's table, with a continuation that runs only at floors
  at most `lo′`. It is not a stop at the higher world's table, which owes the stop's own world at
  `lo`.

So the tables unit should make posts keep the floor, i.e. `V` is equality on `KW`. The other option
is to drop `KW.Owed`'s floor bound. The frames unit should check that the Mut Frame reads no floor of
the resumption world other than the lend's `A`. `KW.owed_of_post` and `KW.owedR_of_post` hold at
either reading. `KW.Post` itself is left unchanged here.

## 4. The 12 lend compatibility lemmas

Each one crosses its exit by `ExtR` at a resource in the lend's stratum, or runs its callback at `Θ` itself. Read at a floor-free `vN`,
each step is unchanged, and the post is at the lender's world:

| Lemma | Exit step |
|---|---|
| `withbor3_compatN` (`Borrow834N`) | `vN_local` (l. 290) |
| `withload_compatN` (`Borrow834N`) | `vN_extR` at the callback's world (l. 362) |
| `withbor1_compatN`, `withbor1U_compatN`, `withbor2_compatN`, `withbor2U_compatN` (`ImmLend833N`) | `LocTy.extR_of_addImm` / `vN_extR` (ll. 132, 201, 421) |
| `withbor2S_compat` (`Cancel791N`) | `vN_local` (l. 935); tables by `vN_add_eq_bnd` |
| `withbor3U_compatN`, `withloadU_compatN` (`Unwind833N`) | `vN_local` (l. 329) |
| `withborFS_compat` (`Field791N`) | `vN_local` (l. 483); tables by `vN_add_eq_bnd` |
| `withbor3S_compat` (`Reborrow791N`) | `vN_local` (l. 965); tables by `vN_add_eq_bnd` |
| `withloadS_compat` (`Withload791N`) | none: the callback runs at `Θ` with the reborrow's record on the list (`erwp_rebGen`); the result by `vN_extend_of_not_free` |

The callback's own stops are `Sched` stops by (S1), and they reach the lender through the frame
(the frames unit). They are not posts.

## 5. What is in Lean and what is by reading

In Lean (`LendExit835N.lean`; all registered in `scripts/AxiomCheck.lean`, axioms within
`[propext, Classical.choice, Quot.sound]`):
- `KW.OwedR`, with `KW.owedR_self`, `KW.owedR_of_post`, `KW.OwedR.trans`, `KW.Owed.owedR` and
  `KW.owedR_floor`;
- `contShareK_owedR_lo` and `contShareK_owedR_U`;
- `KapRelR` and `vN_thunk_iff_kapRelR`;
- the configurations `not_bMut_extP`, `kapRelP_floor_world`, `flooredExit`, `flooredExit_inst`,
  `not_kapRelR_world`, `owedR_not_owed`, `not_owed_post_lower` and `not_tabLe_post_lower`.

By reading, not derived:
- **Every producer of a stop outside `Sched` can owe along `OwedR`.** The argument is (S1) plus the
  producer classes of `scope-835-kripke-stop.md` §2: the M class is `erwpK_perform` plus `vN_extR`
  for the context's values, and Fm/Fi/Fa sit inside a lend constant's run and forward only its
  callback's stops. I have not checked each of the 29 Fm/Fi/Fa producers for a stop that does not
  come from a callback. That check belongs to the frames units.
- **E10 itself**, `KapRelR` handed to a clause as `κ : kTy …` at the typed `cN` over `erwpK`. This
  needs `cN` at `KW`, which is not built. What is proved is the world step: the obligation's
  quantifiers are `U`'s.

## 6. Estimate for the rest of the Kripke-stop build

One agent run is about 1 unit.

| Item | Units |
|---|---|
| The 13 `mut` frames at the floor-choosing stop (`kw_owed_fold`, the inner view) | 1–2 |
| The `imm` fold analogue, the anti-frame share transfer and their 16 frames (at `Sched` entries only) | 1–2 |
| The remaining mechanical producers (31 on the path), handlers included, owing `OwedR` outside `Sched` | 1 |
| `tabN`/`entN` at `KW` with the `Sched` split (`KW.Owed` / `KW.OwedR`); posts keeping the floor (§3); `SchedOKN` at `erwpK`. `vN`, `vN_extR`, `vN_local` and `gN` unchanged | 1 |
| Re-pointing the 111 typed and compatibility lemmas at `cN` over `erwpK` | 2–3 |
| E10, `effHandleV`/`VB` at names outside `Sched`, `reify`; `Goal791SchedN` with `Restrict835` | 1 |
| Posts across a lend's exit | 0 |
| **Total** | **7–10** |

The previous estimate was 8–14, or 7–11 without §5. Two things changed. §5 closes at no cost, and
the row "`vN`'s `U` at a floor, `vN_extR` along `ExtP`, `gN` monotone" goes away, because `vN` does
not change.

## 7. Bookkeeping

- Restated declarations: none. `KW.Post` and `KW.Owed` are unchanged; §3 says what the tables unit
  should do with `KW.Post`.
- Unspent hypotheses: none. No result here takes a hypothesis beyond the configuration's own
  objects.
- Uniqueness and functionality results unused: none were needed.
- Untranscribed in the run-up: `cN`/`tabN`/`entN` at `KW`, which E10 itself needs; the `imm` fold
  analogue and the anti-frame share transfer; and the per-producer check in §5.
- Headlines: none lost or weakened.
