# GhostEnd: end a suspended segment's lends at freeze, re-lend fresh at resume (#258, #260)

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

**Hypotheses added.** `relendOfTyped_of_rbodyOfTyped` takes `@bδ` defined, which `RelendOfTyped`
does not carry: `Relend`'s `И` needs a bound. `rbody_letF` takes `FrameThaws` of the frame, the
condition a stop puts on the values the frame holds; `stopSafe_thaws` discharges it for frames
whose slots other than `m` are free of `'x` and outlive it.
