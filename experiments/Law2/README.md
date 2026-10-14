# Law2: a lend ended at a stop, re-lent at a fresh lifetime

Build with `lake build Law2`. It imports `Core`, `Restrat` and `GhostEnd`; the library does not
import it, and `Core` is unchanged. There is no `axiom`, `native_decide`, `opaque`, `partial`,
`unsafe` or `implemented_by`. Every result's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]` except those that go through `pj_fundamental`, whose open
steps are the enumerated `sorry`s of `Law2/Fundamental.lean` (the `fl_…` lemmas, one per rule or
part of a rule not derived; listed below). Nothing else in `Law2` uses `sorry`.

## The question

Law 2 (research/effects `synthesis.md` §10, `tier2-status.md`): a lend ended at a stop is re-lent
at a fresh lifetime beneath the resumer's list, and the suspended continuation `κ` is related at
that lifetime — at every borrow-nesting depth, as one result.

GhostEnd built the lender side: 6.65 and 6.64 at a resuming table (`ewpTS_M_frameR`,
`ewpTS_I_frameR`), D16.1's stacked piece `OpenS`, and one commutation step per kind of lend at
every stack (`StackStep.lean`). The κ side is what a borrower owes the piece: at every stop of
every run, the continuation runs again at every re-lend of the stack, handed the views made
afresh.

## Summary

| what | outcome | Lean |
|---|---|---|
| lenders, every mixed stack | **proved**, one induction on the stack | `fold_mixed` |
| the re-lendable reading at every type former | **defined**, one structural recursion | `RSlot`, `RC`, `RTab`, `RIn` |
| U1: pure code answering an unfrozen view, or a closure over one | **proved** (rules `pj_call`, `rslot_lam`, `pj_let`); instances typed, every hypothesis discharged | `view_call_spans`, `closure_call_spans` |
| the fundamental lemma for the piece judgment | **one induction on `CDerives`, every one of its 91 rules a case**: 52 proved, 6 proved at part of their instances, 33 not derived | `pj_fundamental` |
| (S1) for every derivation | **from the fundamental lemma**; its open steps are the rules not derived | `piece_of_typed` |
| Law 2 at every mixed stack | **from (S1)** | `law2` |
| Law 2 for every borrower whose piece judgment holds | **proved**, no open step | `law2_of_pj` |
| (S1) and Law 2 at the fragment of proved rules | **proved**, no open step | `piece_of_bcomp`, `law2_frag` |
| (S1′) at one lend; the program-level `withbor` | **from (S1)**; at the fragment with no open step; the bound's definedness discharged | `relendOfTyped'`, `law2_depth1`, `law2_depth1_withbor`, `law2_depth1_frag` |
| hard cases, every hypothesis discharged | **proved** at depth 2 and a depth-3 reborrow chain | `branch_spans`, `closure_stops_spans`, `loop_spans`, `handler_spans`, `chain3_*` |
| machine-step subject reduction | **not built; not derived; no obstruction verified** | below |

## The re-lendable reading (`Law2/Piece.lean`)

What a value held across a stop must satisfy is GhostEnd's `RelendableS`: its resource splits
into the views it holds and a part in `[top]` that, handed the views made afresh at any re-lend,
is again in the relation. `RSlot σ S₀ A` reads that along `A`'s shape and `RC σ S₀ C` reads the
computation types, one mutual structural recursion, `S₀` the lenders' row:

* `⊗`, `⊕`, `!`, `Ref`: componentwise (a pair's components re-lend each with its own share; a
  reference's owned cell is frozen beside its re-lendable payload);
* `U C`, for **every** `C`: re-lendable, and forced at every re-lend it is `RC C`. A pure closure
  `U(A ⊸ F B)` is read like one that stops: called at a re-lend on a re-lendable argument, it runs
  to a re-lendable answer;
* `[@a] A`: re-lendable, and at every re-lend in `Res_{@a}` and `RSlot A`;
* `Imm`, `Mut`, `μ`, `[L]` and the leaves: re-lendable at the kernel's relation;
* `F_Σ R`, and `F R` as the empty row: the piece (`bodyH`/`OpenH`, `Law2/Inner.lean`) at the
  row's own operations of the lenders' names (`RTab`, the kernel's `effTab` at those names) and the
  operations of other names, caught by a handler inside the borrower (`RIn`), answering in
  `RSlot R`. At `F R` the table is empty and nothing is caught inside: a run to a re-lendable answer
  (`wpTS_of_rc_ret`);
* `A ⊸ C`, `C & D`, `⊤`: as the kernel's `𝒞⟦−⟧`, `RSlot` at the argument; `∀`, `ν`: the kernel's
  relation at the current lifetimes.

`RCtx` is `⊛` of `RSlot` over a context. Proved: `rslot_relendable`/`rctx_relendable` (re-lendable
as such: the frame of a bind), `rctx_split`, `rslot_local`/`rctx_local`, `rslot_vC`/`rctx_gDenC`
(the kernel's relation at the current lifetimes at types free of `U`, `NoThunkT`),
`rslot_of_frozen`, `rslot_outlives` (6.60 at the re-lendable reading), and `rc_step`/`rc_bind` (`RC`
closed under a pure step in front and under a pure bind with a frame, at every computation type).

**`PJ`**, the piece judgment: at every lifetime vector of the stack whose re-lends model `Δ`, from a
re-lendable context, the term is in `RC C`. **`PV`**: from a re-lendable context, a run to a
re-lendable value (`pv_iff_pj`: `PV` is `PJ` at `F A`). `openS_of_pj`: the piece judgment at the
lenders' row, the context rebuilt re-lendably at every re-lend, is D16.1's piece.

## U1: pure code whose answer is not frozen (`Law2/U1.lean`)

**Proved.** The piece judgment of pure code is built by the same rules as that of code that stops:
a pure closure built inside the borrower is re-lendable with its environment (`rslot_lam`); called
at the current lifetimes on a re-lendable argument it answers a re-lendable value (`pj_call` at
`F B`, the answer of whatever type, a view or a closure over one); a bind holds the answer in its
frame across the inner piece's stops (`pj_let`, `rctx_relendable`). The constants a pure helper
calls are read the same way (`Law2/Rules.lean`).

Instances at the depth-2 stack `[s@'x₂ reborrow, s@'x₁]`, each program typed (`d_viewCall`,
`d_closureCall`) and every hypothesis discharged, from the rule lemmas with no open step:

* `view_call_spans`: `id = λz. return z; r = id m; yield 1; use r` — the answer, `Mut 'x₂ _`, reads
  the stack's variable, is held across the stop and used after it;
* `closure_call_spans`: `mk = λz. return (λ_. use z); f = mk m; u = yield 1; f u` — the answer, a
  closure over the view, is held across the stop and called after it.

## The fundamental lemma (`Law2/Rules.lean`, `Law2/Fundamental.lean`)

`pj_fundamental : CDerives Δ Γ e j → PJudg δ σ S₀ Δ Γ e j` — `PV` at `V : A`, `PJ` at `M : C` — by
one induction on the derivation, one case per rule. A rule proved at part of its instances splits
on the rule's own types and rows (never on the stack); the other part is its own `sorry`. No rule
is left without a case.

| rule | outcome | Lean |
|---|---|---|
| `var`, `unitI`, `tensorI`, `sumI₁`, `sumI₂` | proved | `pv_var`, `pv_unit`, `pv_pair`, `pv_inj₁`, `pv_inj₂` |
| `thunkF`, `thunkV`, `bangThunkF`, `bangThunkV` | proved | `pv_thunkF`, `pv_thunkV`, `pv_bangThunkF`, `pv_bangThunkV` |
| `ret`, `ofRet`, `bind` | proved | `pj_ret`, `pv_ofRet`, `pj_bind` |
| `force`, `lam`, `lamDead`, `app`, `lolliE` | proved | `pj_force`, `pj_lam`, `pj_lamDead`, `pj_app`, `pv_lolliE` |
| `withI`, `proj₁`, `proj₂`, `topI` | proved | `pj_withI`, `pj_proj₁`, `pj_proj₂`, `pj_topI` |
| `unitE`, `tensorE`, `sumE`, `zeroE` | proved | `pj_seq`, `pj_letpair`, `pj_case`, `pj_zeroE` |
| `bangE`, `copyBang`, `forgetBang` | proved | `pv_bangE`, `pv_copyBang`, `pv_forgetBang` |
| `boxE`, `immSub`, `mutSub` | proved | `pv_boxE`, `pv_immSub`, `pv_mutSub` |
| `boxI` | proved at a type outliving its lifetime; **not derived** at a type that does not (only the context does) | `pv_boxI_outlives`; `fl_boxI_ctx` |
| `alloc`, `free`, `swap`, `copy`, `forgetImm`, `forgetMut`, `forgetUnk` | proved | `pv_alloc`, `pv_free`, `pv_swap`, `pv_copy`, `pv_forgetImm`, `pv_forgetMut`, `pv_forgetUnk` |
| `lit`, `hostOp` | proved | `pv_lit`, `pv_hostOp` |
| `boundedFix`, `countFold`, `countTry` | proved, by induction on the budget or the count | `pv_boundedFix`, `pv_countFold`, `pv_countTry` |
| `arrSize`, `arrLen`, `arrCopy`, `arrForget`, `sliceLenM`, `sliceEmptyI`, `sliceEmptyM` | proved | `pv_arrSize`, `pv_arrLen`, `pv_arrCopy`, `pv_arrForget`, `pv_sliceLenM`, `pv_sliceEmptyI`, `pv_sliceEmptyM` |
| `arrGet`, `arrReplace`, `sliceGetM`, `sliceSplitI`, `sliceSplitM`, `sliceReplaceM`, `sliceSwapM` | **not derived** | `fl_arrGet`, `fl_arrReplace`, `fl_sliceGetM`, `fl_sliceSplitI`, `fl_sliceSplitM`, `fl_sliceReplaceM`, `fl_sliceSwapM` |
| `arrNew`, `arrFree` | **not derived** | `fl_arrNew`, `fl_arrFree` |
| `allI` | proved at a context free of `U`; **not derived** otherwise | `pj_allI_kernel`; `fl_allI_ctx` |
| `allE`, `allEV` | **not derived** | `fl_allE`, `fl_allEV` |
| `roll` | proved at an unrolling free of `U`; **not derived** otherwise | `pv_roll`; `fl_roll_thunk` |
| `unroll`, `nuIn`, `nuOut`, `unfoldN`, `foldImm`, `foldOwn`, `foldReuse` | **not derived** | `fl_unroll`, `fl_nuIn`, `fl_nuOut`, `fl_unfoldN`, `fl_foldImm`, `fl_foldOwn`, `fl_foldReuse` |
| `withbor1`, `withbor2`, `withbor3`, `withload`, `withswap`, `sliceBorrowM`, `sliceBorrowI` | **not derived** | `fl_withbor1` … `fl_sliceBorrowI` |
| `withbor1U`, `withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU` | **not derived** | `fl_withbor1U` … `fl_sliceBorrowIU` |
| `effSub` | proved | `pj_effSub` |
| `effPerform` | proved at a name caught inside, and at a lenders' name at a resuming operation of data (`ResumeOp`); **not derived** otherwise | `pj_performIn`, `pj_effPerform_resume`; `fl_effPerform_open` |
| `effLet` | proved at a row whose lenders' operations resume linearly (`RowLin`); **not derived** otherwise | `pj_let`; `fl_effLet_open` |
| `effHandleV` | proved at a name outside the lenders', its operations linear; **not derived** otherwise | `pj_handle`; `fl_effHandleV_open` |
| `effRaise`, `effThen` | **not derived** | `fl_effRaise`, `fl_effThen` |
| `letPoly` | proved | `pj_letPoly` |

**Not derived** means: the case is its own `sorry`, and no obstruction is verified — no
configuration a typed program builds is machine-checked to fail any of them. What each lacks:

* `[]I` at a type that does not outlive `@a`: a boxed value held across a stop is re-lent at shorter
  lifetimes; that its views stay in `Res_{@a}` follows from its *type* outliving `@a`
  (`rslot_outlives`), and the rule's premise is that its *context* does. Which views a value holds
  is not recorded against its context's.
* `∀I` at a context holding `U`, `∀E`, `∀E` by value: `∀` is read at the kernel's relation at the
  current lifetimes. Its body's context is then read at the kernel's relation, which a re-lendable
  closure in it is not; and the kernel's relation at an instance does not give the re-lendable one
  (at a row, a run's `ewpTS` at one reading is not the piece, §15's route 1). A `∀` instantiated
  inside the borrower and held across a stop fixes its lifetime while the re-lends move the bound.
* `roll` at an unrolling holding `U`, `unroll`, `ν`, coiteration, the folds: `μ` and `ν` are read at
  the kernel's relation; the unrolling is read componentwise, and a whole value's split into views
  and a frozen part does not split along its components; the folds' algebras and the coiteration's
  step are re-lendable closures the kernel's proofs read at the kernel's relation.
* A leaf or part taken out of a family, or put into one; `array_new`, `array_free`: a family is read
  at the kernel's relation, and its re-lendable split is not split by location; the loops' element
  functions are re-lendable closures building or consuming a family read at the kernel's relation.
* The inner lends (`withbor`, `withload`, `withswap`, the slice borrows, their unwinding forms): the
  kernel's 6.65/6.64/6.66 at the inner lend read the lent value and the callback at the kernel's
  relation and answer at it, which is not re-lendable; a lend opened inside the borrower and held
  across a stop is a stack entry of its own (below).
* `[perform]` at a lenders' name at an operation that is not resuming data, `[let]` at a row whose
  lenders' operations do not all resume linearly, `[handle]` of a lenders' name or at an operation
  that is not linear, `[raise]`, `[then]`: the piece's stops are read by name (`outN`), its
  continuations resumed once, its frames never unwound; a cancel, a copy of `κ`, an unwind and a
  finaliser are outcomes it does not read.

## (S1), and Law 2 (`Law2/Target.lean`)

`piece_of_typed` is `pj_fundamental` followed by `piece_of_pj`: a borrower Core's typing derives at
a row `S`, its context rebuilt re-lendably from the views at every re-lend (`RCtx`), every re-lend
modelling `Δ`, its answer type holding no `U` at a position the reading reads componentwise
(`NoThunkT`) and its answers in `[top]`, is D16.1's piece. `law2` is `fold_mixed` with it, at every
mixed stack. The statement's scope:

* the context is given slot by slot (`RCtx`). The whole-context form — `𝒢⟦Γ⟧` at each re-lend — is
  not derived: a slot's re-lendable reading does not follow from the whole context's kernel
  relation at each re-lend, whose split among the slots is not fixed across re-lends;
* the answer type holds no `U` at a componentwise position: the answer is read back at the kernel's
  relation (`rslot_vC`), and a re-lendable closure is not a kernel-related one.

`law2_depth1` is the program-level statement at one lend; `law2_depth1_withbor` is it at the bound
every `withbor` rule lends below, `⊓Δ`, whose definedness at a reading modelling `Δ` it discharges
(`interp_defined_of_wf`), so `law2_depth1`'s hypothesis `hb` is not an assumption there.

## Side conditions

* **`AboveAll`** (values above the stack's outermost lend) is semantic. The fragment no longer
  takes it: `BVal.frozen` and `BComp.pure` take the syntactic `FrozenTy A` — `A` persistent, or
  outliving every lifetime — and `aboveAll_of_frozenTy` gives `AboveAll` from it at a type free of
  the stack's variables (`aboveAll_of_persistent`, `aboveAll_of_outlives`, 6.60 at a variable of the
  stack).
* **`hb`** (`∃ β, b.interp δ = some β`): discharged at a program's `withbor` (`law2_depth1_withbor`).

## Stops inside the borrower, and the stacked bind (`Law2/Inner.lean`)

A handler installed inside the region the lends span catches some operations: those stops cross
no lend and drop no view. The handler's clause is handed the continuation and may hold it across
later stops of the lenders' row, at which every view is dropped; so the continuation must be
re-lendable as a closure is.

* **`InStop`**: `perform (n, (i, v))` at an operation caught inside (`RI n i = some P`): the
  argument in `P.1`, the continuation's share `RelendableS`, at every re-lend and on every answer
  in `P.2` the piece at depth `0`.
* **`bodyH`, `OpenH`**: D16.1's piece with `InStop` beside the lenders' full-depth stops
  (`StopAt`). Where nothing is caught inside it is D16.1's (`openS_of_openH`).
* **`bodyH_bind`, `openH_bind`**: a pure context `K` around a piece, a frame beside it, its share
  split into views and a frozen part that thaws at every re-lend. At a full-depth stop the frame's
  views are dropped beside the piece's (`dropS_join`) and its frozen part joins every continuation
  (`opTable_frame`); at a stop inside, the whole frame joins the continuation (`relendableS_sep`).
* **`bodyH_tab_mono`, `openH_tab_mono`** (`Law2/Rules.lean`): the piece grows with its table and
  with what it catches inside (`[sub]`).

## A handler installed inside the borrower (`Law2/Handle.lean`)

`handle_n e with H`, `n` a name of neither the lenders' row nor the row outside, its operations
linear, at any cancel rows. `bodyH_handle` is one run: an answer of `e` runs `h_ret`; a stop of the
lenders' row and a stop caught further out pass `hnd H` outward (`opTable_handle`); a stop at `n`
steps to the clause, handed the argument and `κ` at a fresh cell, re-lendable (`rslot_kappaC`).
`openH_handle` is the same at every continuation, `pj_handle` the piece judgment.

## The fragment (`Law2/Fragment.lean`)

`BVal`/`BComp` is a sub-judgment of Core's typing (`toCDerives`) whose piece judgment is proved by
one induction with no open step (`BComp.toPJ`); `piece_of_bcomp` and `law2_frag` are (S1) and Law 2
for it. `law2_of_pj` is Law 2 for every borrower whose piece judgment holds, which the U1 instances
use with piece judgments built from the rule lemmas directly.

## Configuration typing

The plan was subject reduction for the effect machine: typed configurations preserved by every
`Step`, so that at every stop the captured `κ` is a typed segment over `HTV` values. **Machine-step
subject reduction is not built; it is not derived, and no obstruction is verified.** What `OpenS`
needs from a stop is a split of the stop's share by frame and a well-founded measure over re-lent
runs; the piece judgment supplies both by its own induction on the derivation (`openH_bind`'s and
`openH_handle`'s inductions on the inner piece, `rc_bind`, the rules' compatibility lemmas), not by
a typing of the machine's configurations. Whether a configuration typing of the `HTV`/`TypedSeg`
form would supply them is not determined.

## Law 2's remaining sorry list

The `fl_…` lemmas of `Law2/Fundamental.lean`, one per rule (or part of a rule) not derived, each
stated at the rule's premises: `fl_allI_ctx`, `fl_allE`, `fl_allEV`, `fl_boxI_ctx`,
`fl_roll_thunk`, `fl_unroll`, `fl_nuIn`, `fl_nuOut`, `fl_unfoldN`, `fl_foldImm`, `fl_foldOwn`,
`fl_foldReuse`, `fl_arrNew`, `fl_arrFree`, `fl_arrReplace`, `fl_arrGet`, `fl_sliceGetM`,
`fl_sliceSplitI`, `fl_sliceSplitM`, `fl_sliceReplaceM`, `fl_sliceSwapM`, `fl_sliceBorrowM`,
`fl_sliceBorrowI`, `fl_withbor1`, `fl_withbor2`, `fl_withbor3`, `fl_withload`, `fl_withswap`,
`fl_withbor1U`, `fl_withbor2U`, `fl_withbor3U`, `fl_withloadU`, `fl_sliceBorrowMU`,
`fl_sliceBorrowIU`, `fl_effPerform_open`, `fl_effRaise`, `fl_effLet_open`, `fl_effThen`,
`fl_effHandleV_open`. They reach `pj_fundamental`, `piece_of_typed`, `law2`, `relendOfTyped'`,
`law2_depth1` and `law2_depth1_withbor`; nothing else.

## The bridge (`Law2/Bridge.lean`)

`openS_of_stops` is D16.1's piece from a run that, at every re-lend, reaches an answer or a stop of
the table at whatever context the run reached. `openS_of_run_stops` and `openS_yield_stops` derive
`Law2/Straight.lean`'s `openS_of_run` (no stop) and `openS_yield_ds` (a run of no steps stopping at
`.seq .hole rest`) from it. The piece judgment does not go through it: `piece_of_pj` reaches the
piece through `openS_of_pj`, `openS_of_openH` and `openH_bind`. `relend_of_openS₁`: at one `mut`
entry the piece is GhostEnd's `Relend`. `relend_not_emb`: why the bridge reads re-lends directly
rather than through `Restrat.Emb` re-makings.

## The components from the previous rounds

* `fold_mixed` (`Mixed.lean`): D16.1's piece at a mixed stack is its `ewpTS`, one induction on the
  stack. Scope: an entry's payload type may not mention the stack's own variables; a reborrow of an
  `imm` view is not a kind of entry.
* `law2_straight` (`Straight.lean`), `struct_reborrow_spans`, `struct_imm_spans`,
  `closure_reborrow_spans` (`Instances.lean`).
* `kappa_relend`, `htv_relend` (`Kappa.lean`, `Hereditary.lean`): the re-make form; Law 2 as proved
  reads re-lends directly. `tw_remake` (`World.lean`): not used by Law 2. `relend_all`,
  `relend_ret` (`AllF.lean`).

## Verifier minors

* `openS_of_stops` is used: `openS_of_run_stops` and `openS_yield_stops` derive `openS_of_run` and
  `openS_yield_ds` from it. The bridge the fragment and (S1) use is `openS_of_pj`,
  `openS_of_openH`, `openH_bind`.
* The configuration-typing paragraph no longer says the invariant is "realised as" the piece
  judgment: machine-step subject reduction is not built, not derived, no obstruction verified.
* "Any nesting depth": the lender side at every mixed stack; the κ side for every derivation up to
  the rules not derived.

## What is open

* **The rules not derived** (the list above). The ones with most reach: `[]I` at a type that does
  not outlive its lifetime (it needs which views a value holds recorded against its context's), the
  inner lends (a lend opened inside the borrower is a stack entry of its own), `∀` at a row, and
  `μ`/`ν`, whose componentwise reading needs a type-variable environment in `RSlot`.
* **(S1) at a whole context, and at answers holding a closure** (the statement's scope above).
* **An inner lend whose payload reads the stack's own variables**: the lender step for such an
  entry is not built (GhostEnd's views read payloads at `δ`).
* 6.150 at a resuming table (a reborrow of an `imm` view spanning a stop); a typed continuation over
  an `Imm` view; a stop handled between two lenders (`AllCross` beyond constant `true`, #278); the
  borrow constants' frames as machine frames at a stack (#275).

Kill criterion: not met. U1 is proved; no rule failed in a machine-checked configuration, and no
rule took two successive patches.

## Files

| file | content |
|---|---|
| `Law2/Remake.lean` | `RemakeR`; `relend_fov`, `relend_mut` at Core; `relend_derivable` |
| `Law2/Hereditary.lean` | `HTV`, `HTG`; `htv_sound`; `htv_relend`, `htv_relend_vC` |
| `Law2/Kappa.lean` | `TypedSeg`, `KappaRelends`; `kappa_relend`, `kappaRelends_of_typed` |
| `Law2/AllF.lean` | `relend_all`, `relend_ret`, `htv_relend_all`, `htv_relend_ret` |
| `Law2/World.lean` | `RemakeAt`, `tw_cell`, `tw_remakeAt`, `tw_remake`, `ti_remake` |
| `Law2/Mixed.lean` | `MixedStack`, `ownersM`, `withOwnersM`; `fold_mixed` |
| `Law2/Straight.lean` | `RunsAt`; `openS_of_run`, `openS_yield_ds`, `runsAt_of_typed`, `law2_straight` |
| `Law2/Bridge.lean` | `StopAt`, `openS_of_stops` and its two instances; `dropS_join`; `relend_of_openS₁`; `relend_not_emb` |
| `Law2/Inner.lean` | `InStop`, `bodyH`, `OpenH`; `openS_of_openH`; `bodyH_bind`, `openH_bind` |
| `Law2/Piece.lean` | `RSlot`, `RC`, `RTab`, `RIn`, `RCtx`; re-lendability; `rc_step`, `rc_bind`; `PJ`, `PV`; the rules at a row; `openS_of_pj` |
| `Law2/Handle.lean` | `rslot_kappaC`, `opTable_handle`; `bodyH_handle`, `openH_handle`, `pj_handle` |
| `Law2/Fragment.lean` | `BVal`, `BComp`, `FrozenTy`; `toCDerives`, `toPJ`; `piece_of_pj`, `piece_of_bcomp`, `law2_of_pj`, `law2_frag` |
| `Law2/Rules.lean` | the rule lemmas: closures, eliminations, `!`, `[@a]`, sub-lifetimes, the borrow axioms, families, the counted loops, `[sub]`, `[perform]`, `[let-poly]` |
| `Law2/Fundamental.lean` | `PJudg`, the `fl_…` rules not derived, `pj_fundamental` |
| `Law2/Instances.lean` | `struct_reborrow_spans`, `struct_imm_spans`, `closure_reborrow_spans` |
| `Law2/FragInstances.lean` | `branch_spans`, `closure_stops_spans`, `loop_spans`, `handler_spans`, `chain3_*` |
| `Law2/U1.lean` | `law2_A_pj`; `view_call_spans`, `closure_call_spans` and their programs' derivations |
| `Law2/Target.lean` | (S1) `piece_of_typed`, `law2`; `relendOfTyped'`, `law2_depth1`, `law2_depth1_withbor`; `relend_frag`, `law2_depth1_frag` |
