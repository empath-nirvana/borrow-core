# GhostEnd: end a suspended segment's lends at freeze, re-lend fresh at resume (#258)

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
| 3 | `withbor` with a lend spanning yields, at the kernel's relation | `withbor_spans_yields_cC` (`Program.lean`), `withbor_spans_yields_sem`, `handle_spans_yields` (`Handle.lean`) |
| 3 | every hypothesis discharged: a lend spanning two yields | `spans_two_yields`, `spans_two_yields_sem` (`Instance.lean`) |
| 3 | the general case, reduced | `RelendOfTyped`, `withbor_of_relendOfTyped` (`Open.lean`) |
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

**O15.1 is not closed.** Three parts remain, and for none of them have I verified that an
obstruction is real:

- **General borrowers.** `RelendOfTyped`, stated in `Open.lean`, asks that every borrower typed
  at a resuming row is `Relend`. `withbor_of_relendOfTyped` derives O15.1's resume half from it.
  Two steps are not derived:
  1. presenting each stop of a typed borrower as a typed segment (`SegOf`), which is what
     `segment_fundamental` needs;
  2. a well-founded measure on the interaction that does not depend on the internal lifetimes.
     `Relend` is a least fixed point, and the run after a re-lend is a different `ewpTS` from the
     one the stop came from.
- **Drop.** The yield here is linear. At an affine yield, a cancel must dispose of the
  ghost-ended owner, and the bare `withbor` frame has no finaliser. That would take the unwinding
  form (`withborU`) at a resuming row, which is not derived. So T15.5's drop clause, which needs
  `aff` (H1), is not reached.
- **§15's statement.** `O151AsStated` is §15's form, whose premise quantifies the callback from
  its start. It is not derived from `ewpTS_M_frameR`, whose premise is `Relend`.

Also not covered:

- nested lends open together at a stop;
- reborrow frames (6.150, 6.66) and Imm frames (6.64) at resuming tables;
- a frame holding a value with no outlives rule, such as a closure (O15.2).

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
each re-application, and 6.60's outlives premise in `frame_outlives`.

**Uniqueness and functionality results not used.**

- `CompS.functional` is used.
- The machine's determinism (`AStep1.deterministic`, `steps_replay`) is not. It is the evident
  candidate for the lifetime-independent measure `RelendOfTyped` needs: a stop's term does not
  depend on lifetimes. That route is not attempted.

**Printed lemmas in the run-up that are untranscribed at a resuming table.**

- 6.64 (Imm Frame);
- 6.66 (Anti Frame);
- 6.150 (reborrow);
- the unwinding form of 6.65 (`withborU`).

Only 6.65 is lifted (`ewpTS_M_frameR`). At the abortive tables all four are mechanised
(`ewpTS_I_frameU`, `ewpTS_M_antiFrameU`, `withbor*U_compatX`).
