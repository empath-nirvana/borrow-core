# GhostEnd: end a suspended segment's lends at freeze, re-lend fresh at resume (#258, #260, #262)

Issue #258 asks for the ghost-end lemma against BoLo's real carrier. The plan comes from the
sharpened brief: re-derive, don't transport. At a stop, the segment's internal `Mut` lend is
ended as 6.65 ends it at a return. At the resumption the lender re-applies 6.65 at a fresh
lifetime, and the borrower's code is re-derived from its typing at the new assignment. No `wp`
naturality is used, and neither is any naturality from `Restrat`.

Build with `lake build GhostEnd`. It uses only the standard axioms and has no `sorry`. It imports
`Core`, and `Restrat` for `Witness.lean`.

## The results

| step | what | Lean |
|---|---|---|
| 0 | the fundamental lemma for a stack segment with a hole | `segment_fundamental` (`Segment.lean`) |
| 1 | the borrower's ghost end at a stop | `freeze_at` (`Freeze.lean`) |
| 1 | the extent `'h`: a run from `Res_h` ends in `Res_h`, at a stop as at a return | `wpG_box`, `frozen_above_extent` |
| 2 | 6.65 at a **resuming** table, re-applied at each resumption | `ewpTS_M_frameR` (`Relend.lean`) |
| 2 | the borrower's variable after a re-lend | `mutView` (`Chain.lean`) |
| 2 | a straight-line borrower is re-lendable, its last segment re-derived at each lend | `relend_fin`, `relend_yield`, `relend_chainΓ` |
| 2 | stack order respects the nesting | `relend_respects_nesting`, `exists_relend_lifetimes` (`Tree.lean`) |
| 2 | a borrower piece, the lend open across its answer; bind by the piece's own induction | `bodyAt`, `Open`, `open_bind`, `open_yield`, `relend_of_open` (`Body.lean`) |
| 2 | typed borrowers, each stop a typed segment | `RBody`, `rbody_ret`, `rbody_perform`, `rbody_letF`, `rbody_seq`, `rbody_case`, `relend_of_rbody` (`Typed.lean`) |
| 2 | a frame spanning a stop thaws at the fresh lend | `FrameThaws`, `stopSafe_thaws` (`Typed.lean`) |
| 2 | a loop around yields, by induction on its budget | `open_boundedFix` (`Loop.lean`) |
| 3 | `withbor` with a lend spanning yields, at the kernel's relation | `withbor_spans_yields_cC` (`Program.lean`), `withbor_spans_yields_sem`, `handle_spans_yields` (`Handle.lean`) |
| 3 | every hypothesis discharged: a lend spanning two yields | `spans_two_yields`, `spans_two_yields_sem` (`Instance.lean`) |
| 3 | O15.1's resume half for every `RBody` borrower | `withbor_of_rbody` (`Typed.lean`) |
| 3 | every hypothesis discharged: a borrower branching around its yields | `branch_spans_yields` (`Branch.lean`) |
| 3 | every hypothesis discharged: a borrower looping around its yields, at every budget | `loop_spans_yields` (`Loop.lean`) |
| 3 | drop at an affine yield: the unwinding `withbor` at a resuming row | `opTableO`, `ewp_then_owner`, `withborR_compat`, `withborR_spans_yields_cC`, `handleR_spans_yields`, `spans_two_affine_yields` (`Drop.lean`) |
| 3 | 6.64's `hQ`, 6.66, and 6.150's view copy at resuming tables | `opTable_extR`, `ewpTS_M_antiFrameR`, `ptoImm_dup` (`Frames.lean`) |
| 3 | the general case, reduced | `RelendOfTyped`, `withbor_of_relendOfTyped` (`Open.lean`); `RBodyOfTyped`, `relendOfTyped_of_rbodyOfTyped` (`General.lean`) |
| 4 | `mut_not_natural`'s witness under freeze and re-lend | `relent_holds`, `gap_accepted` (`Witness.lean`) |
| 3d | the lend table: the only cell at the lend's lifetime is at `ℓ`, kept by every run (6.50) | `TabAt`, `tabAt_updV`, `wpG_tabAt`, `wpTS_tabAt`, `vC_mut_vary` (`Table.lean`) |
| 3d | stops report the cell they drop; each lend below the last | `stopAtD`, `OpenD`, `bodyAtD_bind`, `openD_bind`, `relend_of_openD` (`Descend.lean`) |
| 3d | values carrying the lend in data, frozen and thawed by type | `LOk`, `fzV_freeze`, `fzV_thaw`, `FrameThawsD`, `lok_thaws`, `stopSafe_lok` (`Values.lean`) |
| 3d | typed borrowers with the table | `RBodyT`, `rbodyT_ret`, `rbodyT_perform`, `rbodyT_letF`, `rbodyT_let`, `rbodyT_case`, `rbodyT_seq`, `withbor_of_rbodyT`, `relendOfTyped_of_rbodyTOfTyped` (`TypedD.lean`) |
| 3d | every hypothesis discharged: `m` moved into a pair across a yield | `tuple_spans_yield` (`Tuple.lean`) |
| 3d | closures carrying the lend, re-derived by `fundamentalC` | `TV`, `TVG`, `tv_sound`, `tv_freeze`, `tv_thaw` (`Closures.lean`) |
| 3d | borrowers over typed contexts | `RBodyC`, `tvg_split`, `rbodyC_ret`, `rbodyC_thunk`, `rbodyC_perform`, `rbodyC_let`, `withbor_of_rbodyC` (`ClosureBody.lean`) |
| 3d | every hypothesis discharged: `m` captured in a closure held across a yield | `closure_spans_yield` (`Capture.lean`) |
| 3d | a closure that stops while holding the lend | `CloL`, `cloL_of_rbodyC`, `cloL_call` (`Callee.lean`) |
| 3d | every hypothesis discharged: the callee yields with the lend inside it | `callee_spans_yields` (`Callee.lean`) |
| 3d | the kernel invariant, where it enters | `capture_hides_lend`, `KernelInvariant`, `rbodyC_retTV` (`Kernel.lean`) |
| 3e | what `TW`'s records carry | `record_shape_thunk`, `tw_heap_any` (`Bridge.lean`) |
| 3e | the re-lendable continuation relation, positive | `KapRelR`, `kapRelR_mono` (`Bridge.lean`) |
| 3e | the frame thaw at a `U` slot, exactly | `URelend`, `frameThawsD_thunk_iff`, `uThaw_free`, `uThaw_tv` (`Bridge.lean`) |
| 3e | the relation re-lendable by construction; `CloL` its `U` clause | `vRL`, `cRL`, `cloL_of_vRL` (`Bridge.lean`) |
| 3f | re-lendability, closed under `⋆`; `URelend` at `vRL` with no hypothesis | `Relendable`, `relendable_sep`, `relendable_thunk`, `uRelendRL` (`RLCompat.lean`) |
| 3f | the key steps of the non-routine compatibility lemmas | `force_RL`, `thunkF_RL`, `thunkF_RL_ctx`, `bind_RL`, `relendable_cont_frame`, `vRL_thunk_closed` |
| 3f | where the single-lend relation stops: a closure under an inner borrow | `relendable_off_cell`, `thunkF_RL_fails_below`, `thunkF_RL_fails_below_at` |
| 3f | the table as a guard; the same closure inside it | `vRLg`, `RelendableG`, `forceG`, `relendableG_thunk`, `uRelendRLg`, `thunkF_RLg`, `thunkF_RLg_below` |
| 3g | `'x` in a borrow's payload: strictness agrees, freshness excludes it, an inner lend, no payload cell at or below the lend | `payload_strict`, `payload_strict_down`, `PayFree`, `payFree_immReborrow`, `payFree_handed`, `lend_in_scope_below`, `tabAt_wit` (`Payload.lean`) |
| 3g | an `Imm` lend spanning a stop: subtraction, union, 6.64 at a resuming table | `imm_ghostEnd_split`, `imm_ghostEnd_empty`, `imm_relend_union`, `imm_erase_sets`, `relent_copies`, `RelendI`, `ewpTS_I_frameR`, `imm_spans_yield` (`ImmLend.lean`) |
| 3g | a nested lend spanning a stop: the commutation lemma | `NestRelend`, `nested_relend`, `nested_spans`, `nest_yield`, `nested_spans_yield` (`Nested.lean`) |
| 3g | two lends spanning a stop, the inner of another place: both views in the piece | `NestRelend₂`, `nested₂_relend`, `nested₂_spans`, `nest₂_yield`, `nested₂_spans_yield` (`Nested.lean`) |
| 3h | D16.1, the stacked relation, by structural recursion on the type, the stack a parameter; GFP (D16.2) stated | `vRLs`, `cRLs`, `effRetS`, `RelendableS`, `OpenS`, `openFS_mono`, `GFPAt`, `GFP` (`Stacked.lean`) |
| 3h | at `σ = []` it is the kernel's relation, and GFP is `fundamentalC` | `vRLs_nil`, `cRLs_nil`, `gRLs_nil`, `bodyS_nil_iff`, `gfpAt_nil_iff`, `gfpAt_nil` |
| 3h | the stacked `U` clause | `force_RLs`, `relendableS_thunk`, `thunkF_RLs`, `thunkE_RLs` |
| 3h | the `withbor` rows at `σ·new`, `|σ| = 1`: D16.1's piece is the nested piece, folded back by the commutation lemmas | `nestRelend_of_openS`, `nestRelend₂_of_openS`, `withbor_reborrow_RLs`, `withbor_other_RLs`, `withbor_reborrow_spans`, `withbor_other_spans` |
| 3h | every hypothesis discharged: a reborrow callback yielding with both lends open, as D16.1's piece | `openS_yield`, `openS_val`, `withbor_reborrow_spans_yield` |
| 3i | the commutation lemma at every stack, `σ·new` to `σ`: a lend of another place, and a reborrow | `stack_step_other`, `stack_step_reborrow` (`StackStep.lean`) |
| 3i | an `imm` entry at `σ·new`, at every stack (6.64 at a resuming table) | `stack_step_imm`, `fold_imm`, `opTable_shift` |
| 3i | `Relendable_σ` closed under `⋆`, at every stack | `relendableS_sep`, `vwS_join`, `vwS_split`, `ptoImmS_join` |
| 3i | a whole stack folds back to `[]` by induction on the stack; the depth-1 and depth-2 rows from the uniform steps | `openS_nil_ewp`, `fold_other`, `stack_spans_mut`, `stack_spans_imm`, `stack2_reborrow_spans` |
| 3i | every hypothesis discharged: three lends of one place spanning a yield; an `imm` lend inside a `mut` lend spanning a yield | `openS_val_any`, `openS_yield_any`, `stack3_reborrow_yield`, `stack2_imm_yield` |
| 3j | GFP as stated does not hold at `σ = [x]`: a callback-shaped function at a lifetime below the stack, every hypothesis discharged | `not_gfpAt_below`, `not_gfp`, `no_flat_mut_of_part`, `tw_innerView` (`Below.lean`) |

### Step 0: the segment fundamental lemma (restated)

`Core` states the fundamental lemma for terms (`fundamentalC`). A frozen segment is a context `K`
whose frames hold values. `SegOf K E γ` says that `K[v] = E[v, γ]` for an open term
`Δ; (□ : B), Γ ⊢ E : C`. `segment_fundamental` is `fundamentalC` at `E`, read at `K`, and it
holds at every `δ ∈ ⟦Δ⟧`. It is a restatement, proved from `fundamentalC` alone.

The straight-line proof below does not go through it. There the re-derivation is `fundamentalC`
applied to the borrower's last segment `N_f`, which has `m` and the frame's values free, at
`δ[x ↦ α′]`. The `;` frames between yields are pure steps (`relend_step`).

### Step 1: the admissibility lemma

BoLo ends a borrow at the borrower's return: 6.65's exit, H26–H35. Ending it at a stop is
admissible for three reasons:

1. **The exit reads no term.** `wpG_M_frameX` is the printed proof of 6.65 over `wpG`, whose
   postcondition is over any final term. Its exit does three things at a stop exactly as at a
   return:
   - it moves the cell `ℓ ↦ mut(α, v″, χ, P̂)` out of `ρ⁺` into `ℓ ↦ own(v″) ● χ` (6.27);
   - it keeps `↭` from the start (6.28);
   - it keeps the memories (6.25 under 6.8).

   This is the M Frame postcondition shape `ℓ ↦ v ⋆ P̂(v)`. Freezing executes nothing: the run's
   last step is the stop itself.
2. **The borrower can let go.** What a stop must supply is what a return supplies: the share in
   `[α] ∀w. ℓ ↦ w ─⋆ P̂(w) ─⋆ Φ`. The borrower's view `ℓ ↦ M_α P̂` is a single `mut` cell, so it
   owns nothing (`noOwn_ptoMutS`) and joins `ρ⁺` (`wpG_garbage`). `freeze_at` does this at a run
   of no steps. The variable `m` still holds `ℓ`, as a value of the stopped term.
3. **The rest of the share is in `[α]`.** In a straight-line borrower the rest is the frame's
   values. Their types do not mention `'x` and outlive it, so 6.60 puts them in `Res_α`
   (`frame_outlives`, from `gSepC_outlives`).

So the condition that makes the ghost end admissible is this: at the stop, the borrower's share
less its view lies in `[α]`. A return meets it by typing (`[@x] B`). A stop has to meet it by the
outlives premise on what the suspended frames hold.

**The extent `'h`.** `wpG_box` is 6.147 at `wpG`: a run from `Res_h` ends with its share in
`Res_h`, at a stop as at a return. `frozen_above_extent` turns that into the invariant: no borrow
cell of a frozen share sits at `h` or below. Internal cells are not in a frozen share at all,
since the freeze ended them. So the split external/owned is exhaustive.

This needs the handler body to start in `Res_h`. That is a typing invariant, and the kernel does
not establish it today, because handlers open no lifetime. It would be established in `[handle]`'s
compatibility lemma (`handle_compatC`) once the handler takes an extent `∀'h`. The extent would be
chosen as 6.65's H4 chooses a lend's lifetime: below every record of the list and, through
`fresh_frame`, below every cell of the body's resource.

### Step 2: resume

`Relend` is the re-lendable callback. It is the least fixed point of `relendF`: lent at a fresh
`α`, the callback runs to a value or to a stop. At either, its share is in `[α]` and hands the
owner back. A stop owes its continuation the owner and `Relend` again.

`ewpTS_M_frameR` proves `owner ⋆ Relend ⊨ ewpTS` at every monotone table, by induction on
`Relend` with `wpG_M_frameX` at each unfolding. So each resumption re-applies 6.65 at a lifetime
chosen at that point (H4), below every record of the resumer's list. This is 6.65's proof as
printed, applied once per resumption. Nothing of the earlier lend survives the stop, and the
stored predicate `P̂ = 𝒱⟦T⟧δ` is rebuilt by 6.65's entry each time. It is never moved, so
`mut_not_natural` is never asked.

On the borrower's side:

- **The view variable.** `𝒱⟦Mut 'x T⟧_{δ[x ↦ α′]}(ℓ)` is the location together with the cell
  `ℓ ↦ M_{α′}`. So the re-lent cell puts the variable that still holds `ℓ` into the relation at
  once (`mutView`).
- **Non-view values.** They need no naturality. `δ[x ↦ α′]` differs from `δ` only at `'x`, and
  `𝒱⟦A⟧` for `'x ∉ A` is unchanged (`vC_extend_of_not_free`). It is carried along `Ext` to the
  resumer's list (`gDenC_local`).
- **The borrower's code.** It is re-derived at `δ[x ↦ α′]` from its typing (`relend_fin`). For a
  straight-line borrower `λm. yield y₁; …; yield yₙ; N_f`, `relend_chainΓ` is the induction on the
  number of yields left. That measure does not depend on any lifetime.

**The nesting.** The nesting is a forest, and stack order is a linear extension of it.
`relend_respects_nesting` shows that lifetimes chosen fresh in stack order put every child below
its parent, and `exists_relend_lifetimes` that such a choice exists. Mechanised for the frames
themselves: one lender frame per segment. Nested lends open together at a resuming stop are not
mechanised (below).

### Step 3: O15.1

**The resume half is closed for straight-line borrowers.** `withbor_spans_yields_cC`:
`withbor ℓ (Λ. λm. yield y₁; …; yield yₙ; N_f)` is in `𝒞⟦F_Σ (Ref T ⊗ B)⟧` from
`ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`. The lend of `ℓ` is open at every yield, `Σ`'s `yield` is linear and resuming,
and `N_f` uses `m` after the last resumption. It is stated on BoLo's carrier at the kernel's
relation.

`withbor_spans_yields_sem` is the same result as a semantic judgment at `r : Ref T`.
`handle_spans_yields` hands it to the kernel's `[handle]` (`handle_compatC`) unchanged, so the
handler's clause receives `κ` in the kernel's continuation type (`KapRel`), as for any other
body. §15's chain (T15.6 → L15.3 → T15.4/T15.5) therefore starts from this body as it does from
a body with no spanning lend.

`spans_two_yields` discharges every hypothesis on a concrete program, so the shape is not vacuous
and it arises.

### Step 3a: general borrowers (#260)

**The measure.** `Relend` is a least fixed point, and the run after a re-lend is a different run
from the one the stop came from. An induction on the stop's own `ewpTS` does not reach it.
`Body.lean` adds the open-ended form of `Relend`: `bodyAt Q X α` is one run with the lend open at
`α`, which answers in `Q α` with the lend still open or stops, and `Open` is its least fixed
point, each unfolding at a fresh `α ⊏ β`. `open_bind` puts a pure context and a frame around a
piece. It is proved by induction on the piece's own `Open`, and the continuations of the piece's
stops are `Open` again. An `Open` quantifies the lifetime of every later lend at its own
unfolding, so the induction hypothesis already covers the re-lent run. The other measures a
borrower needs are its typing derivation (`Typed.lean`) and a loop's budget (`Loop.lean`). None
of them mentions a lifetime.

The brief's candidate was the machine's determinism (`AStep1.deterministic`, `steps_replay`). I
did not take it, for this reason. Determinism fixes the machine's trace: from the same heap and
allocator, the re-lent run reaches the same terms as the run at the old lifetime. An induction
on the old run's `ewpTS` gives its hypothesis at the old run's *ghost* state, and `wpG`'s
post-resources are existential, not determined by the trace. Using that hypothesis for the
re-lent run would need the re-lent configuration presented as a configuration of the old lend.
That is §15's route 1 (re-fold at the old `α`), whose step `RefoldKripke` is refuted at an
arising list (`refoldKripke_false`, `refold_fails_at_consumer_frame`). That the determinism
route needs this step is my reading, not machine-checked. `Open`'s own induction needs neither.

**Each stop is a typed segment.** `RBody Γ ml E A` (`Typed.lean`) is the semantic judgment of a
piece `E` of a borrower, typed in `Γ, m : Mut 'x T` with `m` the last slot (it is the outermost
binder, so every subterm sees it last, holding `ℓ`). At every lend `α ⊏ @bδ`, from
`𝒢⟦Γ, m⟧` at `δ[x ↦ α]`, `E` runs with the lend open at `α`. Its rules mirror the typing rules:

| rule | `RBody` | what happens at a stop |
|---|---|---|
| `[ret]` and every pure rule | `rbody_ret` (`fundamentalC` at `δ[x ↦ α]`) | none: the piece is pure |
| `[perform]` | `rbody_perform` | the stop; the argument is closed data, in `[α]` |
| `[let]` | `rbody_letF`, `rbody_let` | `N`'s context is the frame `(λz. N) [·]`, frozen and thawed |
| `1E` (`V; M`) | `rbody_seq` | as `[let]`'s second half |
| `+E` | `rbody_case` | none in `V`; the branch taken is a piece |

A stop happens only at a `perform`, and the context around it is a stack of `[let]` frames.
Each frame's code `N` is typed, closed by its context's values. That is `segment_fundamental`'s
`SegOf`, and at a resumption the frame is re-derived from `N`'s own judgment at the fresh lend.
What a stop asks of the frame's values is `FrameThaws`: the frame at a lend freezes to a part in
`[α]` and garbage (its view, if it holds `m`), and thaws at the fresh lend with the new view.
`stopSafe_thaws` derives it when every live slot but `m` is free of `'x` and outlives it
(6.60), and `m` is re-instantiated by `mutView`.

`relend_of_rbody` turns `RBody [] true M (['x] B)` into `Relend`, and `withbor_of_rbody` into
O15.1's resume half. `branch_spans_yields` discharges every hypothesis on a borrower that computes
data before a yield, holds it across the yield, and branches on it into a second yield or none.

**Loops.** The kernel's loop is `bounded_fix (s, (k, a))`, whose budget `k` is a number of the
term. `open_boundedFix` is induction on it. `loop_spans_yields` is a borrower holding `m` through
`K` iterations, each yielding once, at every budget `K`. Its leaf `N_f` is derived from its
typing; the iteration is reasoned about directly (`open_yield` and the machine's steps), since
`RBody` has no rule for calls of a function value (below).

**What remains for general borrowers.** `RBodyOfTyped` (`General.lean`) is the fundamental lemma
for `RBody`, and `relendOfTyped_of_rbodyOfTyped` derives `RelendOfTyped` from it (with the bound
`@bδ` defined, added). Two kinds of step are not derived, and I have not verified that any
obstruction is real:

1. **A frame spanning a stop that holds a value whose type mentions `'x`, other than `m`.**
   `m` threaded through a value (`z : Mut 'x T ⊗ D`) or a closure capturing `m` is outside
   `StopSafe`. Thawing a `Mut 'x T` slot uses the view of the slot's location; `FrameThaws` is
   stated at every closing substitution, which does not record that the location is `ℓ`. For a
   closure the thaw is the closure's relation at the fresh lend: O15.2.
2. **Rules whose premises are effectful functions**: `[lam]`, `[app]`, `[force]`, `∀E` at a
   row, `[then]`, `[handle]`, and the borrow constants inside the borrower. Each needs a relation
   for `U`, `→` and `∀` values read with the lend re-lendable.

Step 3d (#262) takes up both. The first is closed for data (`RBodyT`, `lok_thaws`) and for
closures the borrower builds (`RBodyC`, `tv_thaw`). For the second, `[lam]` and `[app]` are
proved with the lend re-lendable (`CloL`). The table of rule cases is in step 3d.

### Step 3b: drop at an affine yield (#260)

At an affine yield the continuation may be cancelled. The lend was ended by the freeze, and the
owner is in the stop's share. `Drop.lean` lifts the unwinding `withborU` to a resuming row, as
6.65 was lifted:

- `opTableO`: the callback's stop, the owner handed back. Resumed, the share (owner included)
  owes the continuation. Cancelled, it splits into the callback's own cancel and the owner.
- `ewp_then_owner`: the frame `ubind (N, D) [·]` around such a callback. At a cancel the
  callback's context unwinds and the finaliser `D` runs on the owner under `cfin`
  (`cancel_then`, as `ewp_frame_then` uses it).
- `withborR_compat`: `withborU d ℓ f` at the row's table, from a callback re-lendable at
  `opTableO` (`ewpTS_M_frameR`) and `d : Ref T ⊸ 1` (`fin_run`).
- `withborR_spans_yields_cC`, `withborR_spans_yields_sem`, `handleR_spans_yields`: a borrower
  spanning affine yields, at the kernel's relation and under `[handle]`, whose clause receives
  `κ` at an affine operation. `spans_two_affine_yields` discharges every hypothesis, with
  `free : Ref 1 ⊸ 1` as the finaliser.

Disposing of the owner needed nothing new: the cancel happens at a list `Ext`-above the stop's,
the owner is Kripke there, and the lend is not re-opened. What a cancel asks of the borrower is
that its frozen share unwinds, which a frame owning nothing does at once. T15.5's drop clause has
its premise for these bodies. `RBody` at an affine row (frames that drop, `cancel_frame` in
`opTable_frame`) is not done; it is the same composition.

### Step 3c: the other printed frames at resuming tables (#260)

`Frames.lean`. Each of 6.64, 6.66 and 6.150 is proved at `wpG` and never reads the term its run
ends at, so each lifts by induction on its callback's own least fixed point, as 6.65 did. The step
each adds:

- **6.64 (Imm Frame)**: its premise `hQ` carries the postcondition along `Ext`, from the list with
  the frame's record to the list without it. At a resuming table the postcondition is the table's
  stop, carried by `Ext.trans` because the continuation's share is quantified over every
  extension: `opTable_extR`, `ewpPostR_ext`. The lift is `ewpTS_I_frameR` (step 3g).
- **6.66 (Anti Frame)**: the frame refolds `ℓ ↦ M_α` at a stop, the continuation is owed the
  view, and the resumption unfolds it again. `ewpTS_M_antiFrameR` is the lift, proved.
- **6.150 (↺)**: the frame consumes `ℓ ↦ Imm α (…)`, and the next resumption needs it again. A
  copy is kept beside the callback and joins the continuation at the stop (`ptoImm_dup`, `I-Dup`
  at the unstratified cell). Mechanical; the lift itself is not written.

**Nested lends** (item 4) compose these: an inner reborrow of `m` is `withbor3`, 6.66 then 6.65.
At a stop the inner lend ends (6.65's exit), 6.66 refolds the outer view into the share, and the
outer freeze drops it; at the resumption the outer re-lend hands a view, 6.66 unfolds it and 6.65
re-lends the inner borrow below it (`relend_respects_nesting`). The step this adds is the stop
condition: the inner borrower's frozen share must be in `[α]` for the *outer* lend, so its frames
must outlive the outermost lend open at the stop. It is not written; it needs an `RBody` rule for
the borrow constants, which is step 3a's second kind.

**§15's statement** (`O151AsStated`) is not attempted (#260, item 5 skipped).

### Step 3d: values carrying a lend across a suspension (#262)

Step 3a left two kinds of step open: a frame holding the lend inside a value other than `m`, and a
rule whose premise is an effectful function. Both come down to one question: what does it mean
for a value to carry a lend across a stop?

**The table** (`Table.lean`). A lend at `α` records one cell, at `ℓ`, at `α`. `TabAt ℓ α ρ` says
that `ρ` agrees: every borrow cell is at a lifetime `⊒ α` (`Res_{↓α}`), and every one away from
`ℓ` is strictly above `α`. It is a fact about runs, read off existing lemmas. `↭` keeps the
lifetime of every flattened borrow cell at its location (6.50). So `tabAt_updV` is
`updV_outlives` at `↓α` together with `updV_outlives_at` away from `ℓ`, and `wpG_tabAt` puts
`TabAt` in the postcondition of every run, at a stop as at a return. A lend a run opens has a
fresh lifetime and is ended before the run returns or stops. A load keeps the lifetimes of the
cells it reads through. For a `Mut` lend, the table entry is the single location `ℓ`.

The `⊒` half is the relation itself: `ptoMutS ℓ α` holds a cell at `b ⊒ α`. A view of a cell
recorded strictly above `α` (an outer view weakened to `'x` by `Mut<`) stays a view at every later
lend `α′ ⊑ α`, by M Vary (`vC_mut_vary`). Only the cell at `ℓ` is ghost-ended and re-lent.

The table is stated over resources, not types. `capture_hides_lend` (`Kernel.lean`) is a closure
of type `U(F 1)`, free of `'x`, whose value holds the lend's cell. So "a value whose type mentions
`'x`" does not pick out the values that hold the lend.

**Two changes to `Open`** (`Descend.lean`). Whether a piece needs the view at the next lend
depends on what its frames froze, and a frame can hold the lend in a value while `m` is dead. So:

* a stop reports what it dropped: `stopAtD` is `dropC d ⋆ [α](…)`, and the continuation is owed
  `X α d`;
* each lend is taken below the last (`OpenD`'s bound is the lend just ended), because a frozen
  frame may keep outer views at lifetimes between `α` and `@bδ`.

`fresh` lets each re-lend choose its own bound, so `relend_of_openD` gives `Relend` unchanged.
Two dropped cells cannot meet, since both are `mut` at `ℓ` and `●` composes only `imm`
(`dropC_disj`).

**Tuples** (`Values.lean`, `TypedD.lean`). `LOk` admits `Mut 'x T`, `⊗` and `⊕` of such, and
types free of `'x` that outlive it. The freeze and the thaw are by induction on the type, with
`Mut` as case 2:

* at `ℓ` the cell is dropped and re-lent (`mutView`);
* elsewhere the table puts the cell above `α`, so it is kept, and it holds at the next lend by
  M Vary;
* data does not see `'x`.

The re-lend produces the cell for the one location the table records at `α`. `lok_thaws` gives
`FrameThawsD` for every `LOk` frame. `RBodyT` carries the table and takes `FrameThawsD` at
`[let]`; it has `RBody`'s rules. `tuple_spans_yield` moves `m` into `z : Mut 'x 1 ⊗ 1`, yields with
`z` in the frame and `m`'s slot dead, and uses the borrow afterwards. Every hypothesis is
discharged.

**Closures, re-derived** (`Closures.lean`, `ClosureBody.lean`). `𝒱⟦U C⟧` reads a closure through
its behaviour only, so it cannot say which part of the closure's resource is the cell to drop.
A closure the borrower builds is a typed term over typed values. `TV` records that: atoms in the
relation, pairs, sums, closures typed by their derivations over a typed environment `TVG`, and
fixed axiomatic constants. The lemmas are inductions over typed values, closures recursing into
their environments:

* `tv_sound` re-derives a closure at `δ[x ↦ α]` by `fundamentalC` at its own derivation;
* `tv_freeze` drops the lend's cell wherever it sits;
* `tv_thaw` puts the fresh view back.

`RBodyC` reads a borrower over typed contexts. `closure_spans_yield` packs `m` into
`f : U(F(['x] 1))`, yields with `f` in the frame, and forces `f` afterwards. `f` is re-derived at
the fresh lend, and nothing is transported.

**A closure that stops while holding the lend** (`Callee.lean`). Called inside the borrower, such
a closure stops inside the callee with the lend's cell in the callee's environment. Through
`fundamentalC` its stops are `ewpTS`'s: the continuation is a wand over the callee's whole share.
The ghost end needs that share split into the view and a part in `[α]`, and the wand does not
expose the split. So re-deriving the closure through the kernel's relation does not reach the
stop, and its body has to be read as a borrower piece.

`CloL` is that reading: applied at every later lend, handed the view if it holds the cell, the
closure is a piece. Its environment is fixed in its resource, so it is uniform in the lend.
`cloL_of_rbodyC` is `[lam]` at an effectful arrow, from the body's `RBodyC`. `cloL_call` is
`[app]`. In `callee_spans_yields` the callee holds `m` across the caller's yield, is called, and
yields again with the lend inside it. Every hypothesis is discharged.

**Rule cases.**

| rule | status |
|---|---|
| `[ret]` and the pure rules | routine: `fundamentalC` from the context's relation (`rbodyT_ret`, `rbodyC_ret`) |
| `[perform]`, `[let]`, `1E`, `+E` | routine: `RBody`'s proofs, with the table and the dropped cell carried (all four for `RBodyT`; `[perform]` and `[let]` for `RBodyC`) |
| `[lam]`, `thunk` (pure body) | routine: the value is a typed closure (`rbodyC_thunk`) |
| `[lam]` (effectful body) | routine given the body's `RBodyC`: `cloL_of_rbodyC` |
| `[app]`, `[force]` of a `CloL` closure | routine: `cloL_call` |
| a pure piece answering a closure | needs the kernel invariant (`KernelInvariant`, `rbodyC_retTV`) |
| a pure piece handed a `CloL` closure | **not routine**; see below and step 3e |
| `∀E` at a row, `[then]`, `[handle]`, borrow constants | not attempted |

The case that is not routine is a pure piece handed a `CloL` closure. A `CloL` closure need not
be in `𝒱⟦U(1 ⊸ F_Σ B)⟧` at any `δ[x ↦ α]`, so `tv_sound` has no case for it, and a pure piece
cannot be handed one through `fundamentalC`. That piece would need the pure rules proved again at
the lend-aware relation, in place of reading them off the kernel's fundamental lemma.
`callee_spans_yields` avoids it: the closure goes from the frame straight to its call. I have not
derived this case and have not verified that any obstruction is real.

**The T15 tripwire.** It is not reached. `TV` is an inductive predicate in which the
environment occurs positively. `CloL` fixes the environment in the closure's resource and is
defined over `bodyAtD`/`OpenD`, which do not mention `TV`. A frozen closure thaws by structural
recursion on its typing derivation, not by a domain equation. The lend's own cell cannot hold a
closure over a view of itself: a cell's witness lies strictly above the cell's lifetime
(`ptoMutS`'s `σ ∈ Res_b`), as §15's L14.9 uses. The tripwire would be reached by
making `TV`'s closure case carry its body's `RBodyC`, which would put `TV` negatively inside its
own constructor: the shape of `no_negative_domain`. `CloL` avoids it by being semantic. I have
not stated that variant in Lean.

### Step 3e: a pure piece handed a lend-aware closure (#264)

**`TW` does not give the kernel invariant.** `TW`'s records are 6.64's frames `⟨le, v, R, T, δ⟩`
typed by `vShape`, which is `True` at every `U C` (`record_shape_thunk`); the heap's own cells are
untyped (`tw_heap_any`); and `TW` constrains worlds, not the answer of a run, which is what
`KernelInvariant` is about. A record at the program's relation at `U` would put `TW` under
`wpTS`'s negative occurrence of `TW`. What would supply `KernelInvariant` is subject reduction for
the machine's configurations over `TV` values. Not derived; no obstruction verified.

**Every route meets one step: the thaw of a frame's values.** At a resumption the continuation is
re-run at a fresh lend. Its code is re-derived from its typing; its frames' values have to be read
at the new lend with the fresh view (`FrameThawsD`).

| route | status |
|---|---|
| (c) re-lend in the continuation relation (`KapRelR`) | positive (`kapRelR_mono`). Closes the case when the frames' values are typed (`uThaw_tv`) or hold no cell at the lend and have types free of `'x` (`uThaw_free`). At a `U` slot of the ordinary relation it needs exactly `URelend` (`frameThawsD_thunk_iff`). Not derived; no obstruction verified |
| (a) a bridge from the pure piece's typing | the same step: the piece passes `f`'s stops through, but its frame values are re-lent at each resumption |
| (b) re-lendable by construction (`vRL`, `cRL`) | supplies `URelend`'s conclusion by definition; `CloL` is its `U` clause (`cloL_of_vRL`). Positive: structural recursion on types. Its fundamental lemma is work, not attempted |

The case left by (a) and (c) is a `U` value of the ordinary relation that holds the lend's cell
(`capture_hides_lend`: the type need not mention `'x`) or whose type mentions `'x`. For it,
`ptoMutS ℓ α` does not hold of the fresh cell at `α′ ⊏ α`, so the reading at `α′` is a fresh-lend
naturality of `wpTS` at `U` (`Restrat`'s `WpNatural`, open). (c) without (b) therefore needs the
frames of pure pieces to hold `TV` values: `KernelInvariant` extended from answers to frames.

**The T15 tripwire is not reached.** `vRL`/`cRL` recur on strictly smaller types, the argument
relation negatively at `A → C`, so there is no domain equation of `no_negative_domain`'s shape.
The shape #262 named is an inductive `TV` carrying its closures' borrower readings, with `TV`
negative in its own constructor. `CloL` and `KapRelR` are not recursive.

### Step 3f: the compatibility lemmas at `vRL`/`cRL` (#266)

`RLCompat.lean`. Route (b)'s cost is the fundamental lemma at `vRL`/`cRL`: one compatibility lemma
per `CDerives` rule. Each is **routine**, the kernel's proof carrying over with a mechanical
change, or **non-routine**, the `U` clause's re-lend entering it.

**Re-lendability.** `Relendable P α` is the shape of `vRL`'s `U` clause with `P` free: the
resource splits into the view it dropped at `α` and a part in `Res_α` that, handed the view at any
`α′ ⊑ α`, is in `P α′`. It is monotone, Kripke and closed under `⋆` (`relendable_sep`), and these
are re-lendable:

- a `U` slot, by construction (`relendable_thunk`). So `URelend` holds at `vRL` at every
  computation type with no hypothesis (`uRelendRL`). At the kernel's relation it is the open step
  (`frameThawsD_thunk_iff`);
- the borrow's own view (`relendable_view`), a slot free of `'x` in `Res_α` (`relendable_free`),
  a pair of re-lendable components (`relendable_tensor`), and a context of re-lendable slots
  (`relendable_gRL`).

Every non-routine lemma below reduces to one of: the context re-lendable (`thunk`), the frame
re-lendable at a stop (`[let]`), or the continuation re-lendable (`[handle]`). All three are
`Relendable` of a separating conjunction of slots.

**The classification.** "Clause" means a clause the merged definition does not have: `vRL` reads
every value type but `U` and `⊗` at the ordinary relation (`A => vC`), and `cRL` is `True` at
`&`, `⊤`, `∀`, `ν` and at a row's layers. The ordinary reading is not a `vRL` reading: a thunk
that stops at `S` is in `vRL (U (F 1))` and not in `vC (U (F 1))`, so an introduction rule whose
premise is at `vRL` cannot conclude at `vC`. "Row" means `cRL` read at each type's own row rather
than at the one row `S`: the merged `cRL` reads every `F B` as a piece that may stop at `S`, so a
pure callback is read as one that may stop.

| rule | class | why |
|---|---|---|
| `var`, `unitI`, `tensorI`, `unitE`, `tensorE`, `sumE`, `zeroE`, `ret`, `ofRet` | routine | `gRL` is `gSepC` at `vRL` and splits as it does; `⊗` is componentwise in both |
| `sumI₁`, `sumI₂`, `bangE`, `copyBang`, `forgetBang`, `boxE`, `roll`, `unroll` | routine, given the clause | with `vRL` recursing at `⊕`, `!`, `[@a]`, `μ` the proofs are the kernel's; `!` holds `∅` |
| `immSub`, `mutSub` | routine | `Imm` and `Mut` are read at the ordinary relation at `δ[x ↦ α]` |
| `boxI` | routine, given the clause | 6.60 at `vRL`: `VOutlives` has no `U` rule, and its `[@b]` and `!` rules carry their own stratum, so the induction is `vC_outlives`'s |
| `withI`, `proj₁`, `proj₂`, `topI` | routine, given the clause | `cRL`'s `&`, `⊤` as `cC`'s |
| `allI`, `allE`, `allEV` | routine, given the clause | `cRL`'s `∀` as `cC`'s, with the reading substitution a parameter apart from the lend's `δ` |
| `nuIn`, `nuOut` | routine, given the clause | `ν`'s greatest fixed point exists because `Relendable` is monotone (`relendable_mono`). The `Aff` rules are derived (`AffRules.lean`), so they are these rows and `unfoldN` |
| `lam`, `app` | routine | `cRL`'s `→` clause is at the same `α`, as `cC`'s; `lam` needs `cRL` closed under head steps, by induction on `C` as `cC_head` |
| `force` | routine | `force_RL`: the clause at `α′ = α` |
| `thunkF`, `thunkV`, `bangThunkF`, `bangThunkV` | **non-routine** | the context re-lendable: `thunkF_RL`, `thunkF_RL_ctx`. A `!` context holds `∅` (`vRL_thunk_closed`) |
| `bind`, `effLet`, `lolliE` | **non-routine** | the frame re-lendable at a stop: `bind_RL`, at a linear resuming table |
| `effThen` | **non-routine** | a frozen frame unwinding at a cancel, at an inner affine row. Not derived; no obstruction verified |
| `effHandle` | **non-routine** | `cRL` needs a second kind of stop, at an operation handled inside the borrower: the lend open, the continuation re-lendable. Through a frame that is `relendable_cont_frame`. The clause and a handler frame passing the lender's stops are not built |
| `effPerform`, `effSub` | routine | `rbodyT_perform`'s proof; table monotonicity, given the row |
| `effRaise` | routine, through `effThen`/`effHandle` | `Row.Resume` has no aborting operation at the lender's row |
| `alloc`, `free`, `swap`, `copy`, `forgetImm`, `forgetMut`, `forgetUnk`, `lit`, `hostOp`, the `arr*` and the `slice{Get,Len,Split,Empty,Replace,Swap}*` constants | routine | closed `U` values (`vRL_thunk_closed`) whose argument and answer types hold no `U`: the kernel's lemma at `δ[x ↦ α′]` (`bodyAtD_of_wpTS`) |
| `countFold`, `countTry`, `foldImm`, `foldOwn`, `foldReuse` | routine, given the row | the callbacks are pure, and their answers thread through the proof unchanged |
| `boundedFix` | routine | the self-reference is a closed `U` value (`vRL_thunk_closed`), by induction on the budget (`open_boundedFix`) |
| `unfoldN` | **non-routine** | the coiteration builds `U X` thunks over its state, so the state must be re-lendable: the frame step again. Not written |
| `withswap` | routine, given the row | its callback is pure; at the merged `cRL` it could stop inside the anti-frame |
| `withbor1`, `withbor2`, `withbor3`, `withload`, `sliceBorrowM`, `sliceBorrowI` | **non-routine** | an inner lend, not spanning a stop. A closure over its view is outside `vRL` (`thunkF_RL_fails_below`) and inside `vRLg` (`thunkF_RLg_below`); the rest is the kernel's proof |
| `withbor1U`, `withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU` | **non-routine** | an inner lend whose callback unwinds to an inner handler: `effHandle`'s step, the lend ended at the unwind |
| a resuming `withbor` inside the borrower (O15.1's rule, not yet in `CDerives`) | **non-routine** | a nested lend spanning a stop: the stacked relation below |

**Where the single-lend relation stops.** `relendable_off_cell`: a re-lendable resource holds no
cell off `ℓ` at or below `α`. `thunkF_RL_fails_below` is the configuration, with every hypothesis
discharged at numerals in `thunkF_RL_fails_below_at`. Inside an inner borrow's callback
(`y ⊏ ⊓Δ`, `'x` in `Δ`) the context holds `n : Mut 'y 1`, a cell at `αy ⊏ α`:

- `thunk (return n)` is typed, and the substitution models the context;
- the context is in `gRL`, and `thunkF_RL`'s body premise holds;
- the context is not re-lendable, and no closure value over that resource is in `vRL`'s `U`
  clause;
- `TabAt` fails, so a fundamental lemma that assumes the table says nothing about the callback.

The resource is an inhabitant of `ptoMutS k αy`, which 6.65's premise
`fresh (λα. ℓ ↦ M_α P̂ ─⋆ …)` quantifies over. So it is in the domain the callback's judgment
is asked at.

**The table as a guard.** `vRLg` asks the stratum and the re-lend of a `U` value only when its
resource is consistent with the table (`RelendableG`). A frame at a stop is consistent with it
(`wpG_tabAt`), so stops lose nothing (`relendableG_thunk`, `uRelendRLg`). A closure over a value
below the lend owes the reading at `α` alone (`forceG`, `thunkF_RLg`), and the configuration above
is inside `vRLg` (`thunkF_RLg_below`). What `vRLg` does not cover is a lend opened inside the
borrower that itself spans a stop: a value then holds a cell of each lend open at the stop and has
to be re-lendable at each, in the nesting order (`relend_respects_nesting`). That is the relation
indexed by the stack of open lends. I have not derived it and have not verified that any
obstruction is real.

**Verdict: go, for the generalised relation; no-go for `vRL`/`cRL` as merged.** As merged they
read one lend at one row with catch-all clauses, and cannot carry a closure under an inner
borrow. The relation the kernel lift can use is route (b) with four changes:

1. a clause at every former (`⊕`, `!`, `[@a]`, `Ref`, `μ`, `[L]`; `&`, `⊤`, `∀`, `ν`), the reading
   substitution apart from the lend's `δ`;
2. each computation type read at its own row: a pure `F B` as `wpTS` into `vRL B`, an operation of
   the lender's row as the ghost-end stop, an operation handled inside the borrower as a stop with
   the lend open and the continuation re-lendable;
3. the table as a guard (`vRLg`);
4. indexed by the stack of open lends, so that at the empty stack the `U` clause is `vC`'s and the
   computation clause is `ewpTS` at the row's table.

Under decision 20 the kernel's `vC`/`cC` become the empty-stack instance in the same change, not a
second relation beside it. That deletes:

- `CloL` (the `U` clause at `U(1 → F_S B)`, `cloL_of_vRL`; `cloL_call` is `force_RL`,
  `cloL_of_rbodyC` is `thunkF_RL`);
- the `URelend` gap (`uRelendRL`) and route (c)'s `KapRelR`, whose role is the inner-stop clause;
- `KernelInvariant`. A pure piece's answer is in `vRL` by the fundamental lemma at `vRL`, which
  carries the `U` clause, so no subject reduction is needed;
- `TV`/`TVG` and the re-derivation by `fundamentalC` (`tv_sound`, `tv_freeze`, `tv_thaw`);
- `RBody`, `RBodyT`, `RBodyC`, their rule lemmas, `RBodyOfTyped`, `RBodyTOfTyped` and
  `FrameThaws`/`FrameThawsD`/`StopSafe`. Their union is the fundamental lemma at `vRL`; a frame's
  thaw is `Relendable` of the frame, and `LOk`'s atom cases survive as `relendable_view` and
  `relendable_free`. `RelendOfTyped` follows through `relend_of_openD`.

It costs:

- every compatibility lemma of `fundamentalC` restated at the generalised relation, most of them
  mechanically, the non-routine ones as above;
- every consumer of `vC`/`cC` in `Core/` (adequacy, every run, totality, the embedding, the
  programs) re-pointed at the empty-stack instance; mechanical if the instance is definitional;
- the stack of lends in the table (`TabAt` for a stack) and the nested freeze;
- 6.150 at a resuming table (its added step is proved; the lift is not written; 6.64's is
  `ewpTS_I_frameR`), and the table of an `Imm` lend (its set bookkeeping is step 3g's).

No index is added to `CDerives` (decision 19): the stack is a parameter of the model.

**Unknown, as against work.**

- Unknown: none. The three listed here at #266 are proved in step 3g: a nested lend spanning a
  stop (`nested_relend`), an `Imm` lend spanning a stop (`ewpTS_I_frameR`), and `'x` inside a
  borrow's payload (`Payload.lean`).
- Work: the clauses, the row index and the inner-stop clause; the guard; `[then]`'s cancel of a
  frozen frame; the per-type re-lendability lemma for the types `LOk` admits plus `U`
  (`relendable_*` are its cases); the restated compatibility lemmas.

### Step 3g: the last unknowns (#268)

Step 3f left three unknowns. Each is now proved.

**1. `'x` inside a borrow's payload** (`Payload.lean`). Closed by the borrow constants and the
table.

- *Strictness.* The model's `Mut` stratum is strict: a cell `mut(α, v, σ, P̂)` holds `σ ∈ Res_α`.
  `withbor` (2)'s side condition is non-strict, `Δ ⊢ T₁ ⊒ @b` at an `@b` defined in `Δ`. They
  agree because the lend is strictly below `@bδ`: 6.60 at `⊒` (`vC_outlivesLe`) puts the payload
  in `Res_α` for every `α ⊏ @bδ` (`payload_strict`), and `withbor2_compatX` applies 6.65 at
  `↓@bδ`, whose H4 chooses the lend below it (`payload_strict_down`). The strict inequality comes
  from the freshness of `'x`, not from the side condition.
- *Freshness.* Every type a borrow constant hands the borrower at `'x` (`Imm 'x T₁`,
  `Mut 'x T₁`, `Imm̲ 'x T₁`) has `'x` in no payload, from the rules' `'x ∉ T₁`
  (`payFree_handed`). `Imm̲ 'x (Imm @a S) = Imm @a S` keeps `@a`, and `'x ∉ Imm @a S` excludes
  `'x` from `@a` as well (`immReborrow_imm_not_free`). In general `Imm̲ 'x T₁` mentions `'x` only as
  the lifetime of a borrow it forms (`payFree_immReborrow`, through `μ` by `immG`).
- *Inner lends.* A borrow whose payload mentions `'x` is opened in `'x`'s scope, and a `withbor`
  there lends at `α ⊏ ⊓(Δ, 'x)δ ⊑ δ('x)` (`lend_in_scope_below`). It is a nested lend, which is
  item 3.
- *The table.* Under `TabAt`, which every run keeps (`wpG_tabAt`), each borrow cell's witness is
  in `Res_α` (`tabAt_wit`). No payload of a frozen share holds the lend's cell or any cell at or
  below it.

**2. An `Imm` lend spanning a stop** (`ImmLend.lean`). The bookkeeping is `[TR]` Definition 6.3's
`⊟` and Lemma 6.43.

- *Ghost end is subtraction.* With `t̄ ⊆ ᾱ` the internal lifetimes: if `ᾱ ∖ t̄ ≠ ∅` the cell
  stays `imm(ᾱ ∖ t̄)`, and `imm(ᾱ) = imm(ᾱ ∖ t̄) ● imm(t̄)` (`imm_ghostEnd_split`). If it is empty,
  `ᾱ = t̄` and `⊟` removes the cell (`imm_ghostEnd_empty`). At the lent place every lifetime is
  internal, so 6.64's exit returns `ℓ ↦ own(v)`.
- *Resume is union.* `imm(ᾱ ∖ t̄) ● imm({α′}) = imm((ᾱ ∖ t̄) ∪ {α′})` (`imm_relend_union`), and
  the one re-lent view is duplicated to every position that held a copy (`relent_copies`, 6.116).
- *The lowered heap.* Value and witness never change, so `⟦−⟧` is the same at every set
  (`imm_erase_sets`).
- *The key step.* `ewpTS_I_frameR` is 6.64 at a resuming table. It is proved by induction on the
  callback's least fixed point (`RelendI`), with `wpG_I_frameX` at each unfolding. At a stop, 6.64's
  exit is the ghost end: the garbage at `ℓ` is exactly the internal view (6.38's H28), and it is
  removed. Each resumption re-applies the entry at a fresh lifetime with a new record.
  `imm_spans_yield` discharges every hypothesis.

**3. A nested lend spanning a stop** (`Nested.lean`). The reborrow `withbor m (Λ. λn. N)`
(`withbor3`) lends `ℓ` again under the borrower's view. `NestRelend` is the inner piece read at
the outer lend `α₁` current at each unfolding. At every `α₂ ⊏ α₁` it runs, hands the inner owner
back, and leaves a share in `[α₁]`.

`nested_relend` is the commutation lemma: a nested piece is re-lendable for the outer lend
(`Relend`). At each outer lend `α₁`:

1. 6.66 unfolds the view the outer lender has just handed out, at `α₁` itself (`wpG_M_antiFrameX`);
2. 6.65 lends the content below `α₁` (`wpG_M_frameX` with the `⋔` bound `α₁`);
3. at a return or a stop, 6.65's exit hands the owner back;
4. 6.66 refolds it into `ℓ ↦ M_{α₁}`, which is left behind;
5. at a stop, the outer owner joins the continuation (`opTable_absorb`).

The refold is always under the outer's *new* witness. The old-lifetime refold
(`ewpTS_M_antiFrameR`'s continuation, `refoldKripke_false`) is not used. The ordering constraint
(inner below outer) is `nestF`'s bound, which `withbor3`'s type gives (`∀'y ⊏ ⊓Δ`, `'x ∈ Δ`).
`nested_spans` composes the lemma with `ewpTS_M_frameR`. `nested_spans_yield` discharges every
hypothesis on a callback that yields with both lends open. No cell is left that the refold cannot
place.

The other two-entry stack is an inner lend of a different place `ℓ′` (`withbor` (1)–(2) inside the
borrower). There the piece may hold the outer view and the inner one at once. `NestRelend₂` hands
it both. `nested₂_relend` is its commutation lemma:

1. the outer lender re-lends first;
2. 6.65 lends `ℓ′` below the outer lend, with the owner of `ℓ′` carried in the continuation;
3. at a stop the piece leaves both views behind.

`nested₂_spans_yield` discharges every hypothesis. The two lemmas are §16's D16.1 at
`σ = [x, y]`, for a `Mut` outer lend, written as the least fixed points of the stops.

**What is work, not unknown.**

- Reading `NestRelend` off the inner borrower's typing. It needs `RBody`'s rule for the borrow
  constants, and the stop condition that the inner frames outlive the outer lend (step 3c).
- The nested piece followed by the outer borrower's own continuation. The answer then keeps the
  refolded view instead of dropping it, so it is `bodyAtD`'s form, and `bind_RL` composes it.
- 6.150 at a resuming table (`withload` spanning a stop). Its exit is 6.52's subtraction, which
  `wpG_reborrow` already runs at a stop. The lift re-instantiates the chooser `rebChooseTW_top` at
  each resumption's list, where the record persists along `Ext`.

### Step 3h: D16.1 in Lean, and GFP (#279)

`docs/effects-tr/16-regress.md` §16.5 read D16.1 as needing no recursive domain, and said that writing
it would make that a fact. `Stacked.lean` writes it.

**The recursion.** `vRLs σ`, `cRLs σ` and `effRetS σ` are one `mutual` block, each with
`termination_by structural` on its type, so Lean checks that every recursive call is at a strict
subterm. The stack `σ` is a fixed parameter. The substitution (extended at `∀`) and the lifetime
vector (re-lent at `U`) are indices. Each clause reads the relation only at a component of its
type:

- `U C`: `RelendableS` of `cRLs σ C`;
- `⊗`, `⊕`, `!`, `[@a]`, `Ref`: `vRLs σ` at the components;
- `F A`: `wpTS` answering in `vRLs σ A`;
- `F_Σ R`: the piece `bodyS`/`OpenS` at Σ's table, answering in `effRetS σ R`;
- `A ⊸ C`: `vRLs σ A` left of `─⋆` and `cRLs σ C`; `&` and `∀` at the components;
- `Imm`, `Mut`, `μ`, `[L]`, the leaves, and `ν`: the kernel's `vC`/`cC` at `δ_σ(αs)`.

The stack-dependent parts take the relation only as a predicate argument. `OpenS` is a least fixed
point over its own continuation variable, which occurs only positively (`openFS_mono`), as in
`OpenD`. No predicate is defined in terms of itself at the same type, and nothing is stored in the
world.

**The components §16.4 left open.** They are fixed as the stacked forms of the proved single-lend
objects.

- *Entries* carry `(ℓ, x, T, k)` and the lender's row (`cross`: the names whose stops cross the
  lend). `withbor`'s type carries that row.
- *Views*: a reborrow shadows its parent's view, which 6.66 has unfolded.
- *Stops*: an operation stops at the depth its name reaches in the stack. It ghost-ends that many
  innermost entries and keeps the rest open, owing a continuation re-lendable over them
  (`RelendableN`). Depth `|σ|` is D16.1's "stop at the lenders' row" and depth `0` its "row handled
  inside". A depth in between is a handler between two lenders. D16.1 reaches it from the inner
  lend's side ("a stop inside an inner lend is at an extension `σ·τ`").
- *`ghostS`*: what a stop owes the lenders it crosses, in `nestF`'s shape.

At one `mut` entry `RelendableS` has `Relendable`'s shape. At `[]` every component is the kernel's: `Relendable_[]`
is the `U` clause's `Ext`-closure (`relendableS_nil`), a stop is a stop of the table (`stopS_nil`),
and the piece is `ewpTS` (`bodyS_nil_iff`, by induction on each least fixed point).

**GFP at `[]`.** `vRLs [] = vC`, `cRLs [] = cC` and `gRLs [] = gDenC`, by induction on the type.
`gfpAt_nil_iff` makes `GFPAt []` equivalent to the conclusion of `fundamentalC`, and `gfpAt_nil`
proves it from `fundamentalC`.

**The `withbor` rows at `σ·new`, `|σ| = 1`.** Take D16.1's piece at `[new, outer]`, answering as a
callback (`ghostS`: the new lend ends), with every stop of the row crossing both lends. It is
#268's `NestRelend` when `new` reborrows `outer`'s place (`nestRelend_of_openS`), and `NestRelend₂`
when `new` lends another place (`nestRelend₂_of_openS`). Each is proved by induction on `OpenS`:
one unfolding at `α₁` and at `α₂ ⊏ α₁` is one `openFS` at the re-lend `[α₂, α₁]`. A run's
postcondition is read as `nestF`'s by `post_nest`. The commutation lemmas then fold the stack back
to `[outer]`:

- `withbor_reborrow_RLs` (`nested_relend`) and `withbor_other_RLs` (`nested₂_relend`);
- at the outer lender, `withbor_reborrow_spans` and `withbor_other_spans`.

`withbor_reborrow_spans_yield` discharges every hypothesis. The callback yields once with both lends
open and then returns `()`. It is written as D16.1's piece: `openS_yield` builds a stop at the
lenders' row, which drops both views and hands the inner owner back.

**Not shown here.**

- GFP's induction itself.
- The step from the inner callback's piece (GFP's hypothesis at `σ·new`, answering in `vRL_{σ·new}`)
  to the callback form these rows take (answers in `ghostS`). That is `relend_of_openD` at a stack,
  and it is the content of reading `NestRelend` off typing (#275).
- The reborrow followed by the outer borrower's continuation (#276).
- The rows at a depth between `0` and `|σ|` (`effHandle`'s inner-stop clause, #278).

I have not derived these and have not verified that any obstruction is real.

### Step 3i: the stacked lemmas at every stack (#279)

Step 3h left three lemmas. Each is proved once, for every stack (`StackStep.lean`). Each is one
statement with the stack a parameter. Its proof is one induction on D16.1's piece `OpenS` at
`σ·new`, its least fixed point of stops. Lemmas by recursion on the stack list carry the entries of
`σ` along. No step depends on `|σ|`.

**The hypothesis on stops.** `AllCross σ Tab` says that every operation of the row crosses every
entry. It generalises step 3h's `hcross`. A stop is then at depth `|σ|`: `stopS_full` takes a stop
apart and `stopS_of_full` builds one. The rows at an intermediate depth are #278's.

**1. The commutation lemma, `σ·new` to `σ`.** Each shape maps D16.1's piece at `σ·new` to D16.1's
piece at `σ`, both answering as a callback.

- `stack_step_other`: `new` lends a place `ℓ′` not in `σ`. The owner of `ℓ′` is beside the piece.
  1. At each re-lend `αs′` of `σ`, 6.65 lends `ℓ′` below the innermost of `αs′` and below the new
     entry's last lifetime.
  2. The piece at `σ·new` runs at `α :: αs′`.
  3. At a return, the owner of `ℓ′` joins the answer.
  4. At a stop, it joins the continuation (`opTable_frame`).
- `stack_step_reborrow`: `new` lends again the place `ℓ` of `σ`'s innermost `mut` entry.
  1. 6.66 unfolds the view of `ℓ` that `σ` is handed.
  2. 6.65 lends its content.
  3. At a stop, 6.66's refold is the cell the stop drops for that entry.
  4. The owner passes through `ghostS`, so this shape needs no `LinResume`.

This is `nested_relend`'s argument run at D16.1's piece, with `σ`'s other entries carried along.
`nested_relend` concludes `Relend`, the single-lend form, so it is not the step.

At a stop, `σ`'s dropped views pass 6.65's exit. The table at the new lend (`wpG_tabAt`) puts every
cell away from the new place strictly above the new lifetime. So the views are kept for the next
re-lend, not discarded.

The index moves from `b :: bs` to `bs`. The new entry's next lifetime is chosen below
`b ⊓ head αs′`, so the continuation's index is the re-lend of `σ` itself.

**2. An `imm` entry at `σ·new`.**

- `stack_step_imm` is 6.64 at every stack.
- 6.64 runs the callback at a list it extends with a fresh record. The piece is therefore given at
  every `Ext`-extension of the list. This is the quantifier `RelendI` builds into its unfolding.
- Inside the induction the table owes every continuation at every extension (`opTable_shift`), and
  `fold_imm` folds that family back to the piece at `σ`.
- 6.64's postcondition (`Q64`) is stated before the owner is handed back, in the form `hQ` carries
  along `Ext` (`q64_ext`).

**3. `RelendableS` closed under `⋆`.** `relendableS_sep` is proved by one induction on the stack,
entry by entry.

- A `mut` view is in at most one part (`vwE_disj`, `dropC_disj`).
- Two `imm` views at one entry compose only at one value and payload, into the cell at the union of
  their sets (`ptoImmS_join`, 6.43). At the re-lend the view is duplicated (`ptoImmS_dup`, 6.116).

**The fold.**

- At `σ = []` the piece is `ewpTS` (`openS_nil_ewp`). The steps at `σ = []` are 6.65 and 6.64 at a
  resuming table (`stack_spans_mut`, `stack_spans_imm`).
- `fold_other` folds a stack of `mut` lends of distinct places to `ewpTS`, by induction on the
  stack.
- `stack2_reborrow_spans` is step 3h's `withbor_reborrow_spans`. It no longer needs `a₂ < a₁`.
- `stack3_reborrow_yield` takes three lends of one place across a yield. It is folded by
  `stack_step_reborrow` at `σ₀ = [outer]` and at `σ₀ = []`, then `stack_step_other` at `[]`.
- `stack2_imm_yield` is an `imm` lend inside a `mut` lend.
- Each instance discharges every hypothesis.

**Not shown here.**

- GFP's induction itself.
- `relend_of_openD` at a stack (#275).
- The reborrow followed by the outer borrower's continuation (#276).
- The rows at an intermediate depth (#278).

I have not derived these and have not verified that any obstruction is real.

### Step 3j: GFP at a non-empty stack (#279)

The final run on #279 was to prove GFP (D16.2) by induction on `CDerives`, at D16.1, case by case,
unknowns first. GFP as stated does not hold at the stack `[x]` (`Below.lean`).

**The configuration** (`not_gfpAt_below`). `Δ = x ⊏ ⊤`, `σ = [x]`, the lend at `1`, the empty
context and resource. The derivation is `allI` over `lam`: `Λ. λn. return (thunk (return n))` at
`∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`, the shape of a borrow callback's type. Every
hypothesis of `GFPAt [x]` is discharged.

1. D16.1's `∀` clause takes `'y` at every lifetime below `⊓Δ`, which is `x`'s: here `3`.
2. Its `⊸` clause hands every argument in `vRL_σ (Mut 'y 1)`: here the inner view `k ↦ M_3`.
3. The answer's `U` clause (`RelendableS`) puts the closure's resource, apart from the stack's
   views, in `Res_2`.
4. Forcing the closure needs a `mut` cell at `k`. That resource is a part, in `Res_2`, of a
   `↭`-update of the inner view, so neither it nor a `↭`-update of it flattens to a `mut` cell
   at `k` (`no_flat_mut_of_part`).

The refutation runs both: the first from the inner view's typed world (`tw_innerView`), the second,
the force, from the first run's final world.

**Which case.** The rule whose compatibility lemma fails is `lam`, with `allI`: #266 classed both
routine. Their induction hypothesis is GFP at the body, guarded by `TabAt_σ`. D16.1's `⊸` and `∀`
clauses are not guarded, and hand arguments whose cells lie below the stack.

**What it measures.** At `σ = [x]` such a cell arises only from a lend opened inside `x`'s borrower:
a borrow constant applied to a callback of this shape. §16.4's sketch applies the induction
hypothesis to that callback's premise at `σ·y`. In `CDerives` the borrow operations are constants,
and their callbacks reach them as values. D16.1 reads a value at `σ`, with `'y` a plain variable;
no clause of D16.1 extends the stack. So #275 (the inner callback's piece at `σ·new`) has no
induction hypothesis to start from, and the `lam` row has no proof at a non-empty stack.

**The verdict: blocked.** Repairing GFP needs a construct the list does not contain: a reading of
values at an extended stack in D16.1's `U`, `∀` or `⊸` clause, or borrow rules whose callback is a
premise (a `CDerives` change). A table guard on the `⊸` clause would remove this configuration;
whether a borrow constant's row survives it, its callback handed a view below the stack, is not
checked. I have not derived any repair and have not verified that any obstruction to one is real.

### Step 4: the witness

`mut_not_natural`'s cell `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)` is below the cut,
so the freeze ends it. The move reaches only the frozen payload:
`e·(ℓ′ ↦ imm({1}, (), ∅)) = ℓ′ ↦ imm({2}, (), ∅)` (`moved_payload`). The re-lend builds a new cell
over that payload whose predicate is `𝒱⟦Imm 'b 1⟧_{e∘δ}` itself. That cell is in
`𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}` (`relent_holds`), where `fails` shows the moved one is not. The gap
resource that defeats the moved cell satisfies the new cell's predicate (`gap_accepted`).

Whether `ρ₀` with these numerals arises in a run is not checked. The shape arises: it is what
6.65's entry builds when a place holding an `Imm 'b 1` view is lent. The route never asks
naturality at such a cell.

## Report lists

**Printed hypotheses not spent.** None. 6.65's `P̂ ⊨ [β]P̂` (`hP`) is spent in `wpG_M_frameX` at
each re-application, and 6.60's outlives premise in `frame_outlives` and `stopSafe_outlives`.
6.66's premises are spent in `wpG_M_antiFrameX` at each unfolding of `ewpTS_M_antiFrameR`.

**Uniqueness and functionality results not used.**

- `CompS.functional` is used.
- The machine's determinism (`AStep1.deterministic`, `steps_replay`) is not. The measure is
  `Open`'s own least fixed point, the typing derivation and the loop's budget (step 3a).

**Printed lemmas in the run-up that are untranscribed at a resuming table.**

- 6.150 (↺): its added step (`ptoImm_dup`) is proved; the lift is not written.

Lifted: 6.64 (`ewpTS_I_frameR`), 6.65 (`ewpTS_M_frameR`), 6.66 (`ewpTS_M_antiFrameR`), and the
unwinding form of 6.65 (`withborR_compat`, from `ewp_then_owner`).

**Step 3f (#266).** No printed hypothesis is left unspent: `relendable_free` takes `ρ ∈ Res_α` as
a hypothesis, which 6.60 (`vC_outlives`) supplies for a type outliving `'x`, as `fzAtom_freeze`
uses it. `ResU.CompS.functional` and `dropC_disj` are used; the machine's determinism is not. The
printed lemmas in the run-up of the borrow-constant rows that are untranscribed at a resuming
table are 6.64 and 6.150, as above.

**Printed lemmas in the run-up, #262.** 6.50 is used at `↓α` and at one location
(`updV_outlives`, `updV_outlives_at`); 6.60 at frames (`vC_outlives`); 6.65 and 6.66 as lifted
above. The table for an `Imm` lend (many locations, through nested references) is not built:
nested lends spanning a stop are not in scope.

**Step 3g (#268).**

- *Printed hypotheses not spent.* None. `nested_relend` spends 6.65's `hP` at each inner lend, and
  `ewpTS_I_frameR` spends 6.64's `AdmWf` and its `hQ`. 6.64's `hQ` is discharged by `hQ` on the
  answer and by `hTL` on the table (`opTable_extR`).
- *Uniqueness and functionality results not used.* `ResU.CompS.functional` and
  `LSet.Diff.functional` (through `CellU.subLS_of_diff`) are used. The machine's determinism is not.
- *Untranscribed printed lemmas in the run-up.* 6.150 at a resuming table. Its exit (6.52 at a stop)
  is proved, inside `wpG_reborrow`; the lift is not written. 6.64 is lifted (`ewpTS_I_frameR`).
- *Hypotheses added.* `ewpTS_I_frameR` takes `hTL`, the table carried along `Ext`, which is 6.64's
  `hQ` at a resuming table. `opTable_extR` discharges it for `opTable` at a `Local` table, and
  `imm_spans_yield` uses that discharge. `nested_relend` takes `LinResume`: a stop keeps the outer
  owner in its continuation (`opTable_absorb`), which a cancelled continuation could not dispose
  of. `relend_yield` needs the same.

**Hypotheses added.** `relendOfTyped_of_rbodyOfTyped` takes `@bδ` defined, which `RelendOfTyped`
does not carry: `Relend`'s `И` needs a bound. `rbody_letF` takes `FrameThaws` of the frame, the
condition a stop puts on the values the frame holds; `stopSafe_thaws` discharges it for frames
whose slots other than `m` are free of `'x` and outlive it.

**Step 3h (#279).**

- *Printed hypotheses not spent.* None. The rows take `nested_relend`'s and `nested₂_relend`'s
  hypotheses (`LinResume`, 6.65's `hP`) and pass them on.
- *Uniqueness and functionality results not used.* `ResU.CompS.functional` is used (at `[]`).
  `dropC_disj` is not: `RelendableS`'s `⋆`-closure is not proved here.
- *Untranscribed printed lemmas in the run-up.* As for step 3g: 6.150 at a resuming table.
- *Hypotheses added.* The `withbor` rows take `hcross`: every operation of the callback's row
  crosses both lends. That is the single table `NestRelend` and `NestRelend₂` stop at. They also
  take the old lifetimes in nesting order (`a₂ < a₁`), which every stop's re-lend supplies
  (`openFS`'s chain).

**Step 3i (#279).**

- *Printed hypotheses not spent.* None.
  - 6.65's `hP` is spent in `wpG_M_frameX` at each re-lend, in both commutation steps.
  - 6.66's premises are spent in `wpG_M_antiFrameX`, in the reborrow step.
  - 6.64's `AdmWf` is spent in `wpG_I_frameX`. Its `hQ` is discharged by `q64_ext`, from
    `Tab.Local` (`opTable_extR`) and `hQa`.
- *Uniqueness and functionality results.*
  - Used: `ResU.CompS.functional` and `CellU.immOf_inj` (in `ptoImmS_join` and `vwE_join`), and
    `dropC_disj` (in `vwE_disj`).
  - Not used: the machine's determinism, and `LSet.Diff.functional`.
- *Untranscribed printed lemmas in the run-up.* As for step 3g: 6.150 at a resuming table.
- *Hypotheses added.*
  - `AllCross`, which generalises `hcross`. The instances discharge it by constant `true`.
  - `stack_step_other` and `stack_step_imm` take `hβ`: the outermost index of `σ` is at or below
    the payload stratum of `ℓ′`.
    - It places the owner of `ℓ′`, carried across a stop, in `[top]`.
    - `nested₂_relend` got it by choosing the outer lend below `β′` inside `Relend`'s `⋔`.
      `OpenS` fixes that bound by its index.
    - It is vacuous at `σ = []`. `stack2_imm_yield` discharges it.
  - `stack_step_imm` takes the piece at every `Ext`-extension of the list, `Tab.Local`, and `hQa`.
    These are what `RelendI`, `ewpTS_I_frameR`'s `hTL` and its `hQ` carry at depth 1.
    `stack2_imm_yield` discharges them.
  - `stack_step_reborrow` takes the reborrowed entry to be `mut` at the payload type `T`. That is
    the shape of `withbor` (3).
- *Hypotheses removed.* `stack2_reborrow_spans` does not take `a₂ < a₁`.

**Step 3j (#279, the final run).**

- *Hypotheses not spent.* `not_gfpAt_below` instantiates every hypothesis of `GFPAt`. It does not
  use `e₀.cross` or the stack's place: the failure is in the `U` clause's stratum.
- *Uniqueness and functionality results.* Used: `ResU.CompS.functional`, `ResU.Flat.functional`,
  and the machine's determinism through `ARun.rest`. Not used: `ResU.Lower.functional`.
- *Printed lemmas in the run-up that are untranscribed at a resuming table.* 6.150 (↺), as above.
  GFP's other cases (#276, #277, #278, #280, `effThen`, `unfoldN`, the `*U` constants) were not
  attempted after the refutation, under the hard stop.
