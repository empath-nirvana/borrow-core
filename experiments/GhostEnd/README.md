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
  extension: `opTable_extR`, `ewpPostR_ext`. Mechanical; the lift itself is not written.
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
| a pure piece handed a `CloL` closure | **not routine**; see below |
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

- 6.64 (Imm Frame): its added step (`opTable_extR`) is proved; the lift is not written;
- 6.150 (↺): its added step (`ptoImm_dup`) is proved; the lift is not written.

Lifted: 6.65 (`ewpTS_M_frameR`), 6.66 (`ewpTS_M_antiFrameR`), and the unwinding form of 6.65
(`withborR_compat`, from `ewp_then_owner`).

**Printed lemmas in the run-up, #262.** 6.50 is used at `↓α` and at one location
(`updV_outlives`, `updV_outlives_at`); 6.60 at frames (`vC_outlives`); 6.65 and 6.66 as lifted
above. The table for an `Imm` lend (many locations, through nested references) is not built:
nested lends spanning a stop are not in scope.

**Hypotheses added.** `relendOfTyped_of_rbodyOfTyped` takes `@bδ` defined, which `RelendOfTyped`
does not carry: `Relend`'s `И` needs a bound. `rbody_letF` takes `FrameThaws` of the frame, the
condition a stop puts on the values the frame holds; `stopSafe_thaws` discharges it for frames
whose slots other than `m` are free of `'x` and outlive it.
