# WorldW checkpoint: open lends handed across a stop

Branch `probe-open-frames`, experiment `experiments/WorldW`. Every result below holds at a
**draft** world `(ρ, ls, σ)` defined only in this experiment (`WorldW/Defs.lean`). These are probe
results. They are not kernel results, and they are not results at Unit 3's `W`. `Core/` and every
other experiment are untouched.

> [!WARNING]
> **Two of three verifiers failed this checkpoint with major findings.** All of them were about
> prose that claimed more than the Lean proves. They are resolved: README.md, DESIGN.md, and the
> docstrings of `Checks.lean` and `Diag.lean` now state only what is proved. The list below records
> what was corrected. The Lean builds, and
> every theorem's axioms are within `[propext, Classical.choice, Quot.sound]`. One verifier checked
> all 148 theorems. The problem is the README and DESIGN: their prose claims more than the Lean
> proves. The major findings:
>
> 1. **6.66 obstruction is not proved.** README/DESIGN say `OpenFrame66` "asks for more than its
>    premise gives" and "(a) gains nothing over (b) for 6.66". `anti_handOn_needs_invariant` is
>    narrower than that. It *assumes* the stop's ghost resource holds `own(w)` with `P̂(w)`
>    unsatisfiable. No body, `ewpW` run or `TW` history forces a run into that shape, and
>    `¬ OpenFrame66` is not proved. I have not derived `OpenFrame66` and have not verified that any
>    obstruction is real.
> 2. **"Must carry H16 and the pin" is a necessity claim with no proof.** `close_upd_coherent`
>    proves *sufficiency*: with H16 and the pin in `CloseE`, the closure is coherent. The pin's
>    counterexample (`UnpinnedIncoherent`) is unfinished. The H16 case is prose only, and no Lean
>    statement of it exists.
> 3. **"Conservative extension" is not shown.** `ewpTS_ewpW` goes one way: Core's `ewpTS` implies
>    `ewpW []`. `ewpW [] []` is strictly more permissive, because `StopW` lets a stop hand on
>    entries. So the `σ = []` instance of the draft is not Core's relation, and the converse (T1) is
>    open. `Nil.lean`'s own docstring says so; the README contradicts it.
> 4. **Exclusivity at a stop is open, not settled.** "Exclusive keys alternate and repeat across
>    nested `withbor3`s" rests on `HoldsChain` (unfinished) and on `not_holdsInjective`, a witness
>    built by surgery on one bare `mut` cell with no `TW` history and no `withbor3` derivation.
> 5. **The frozen-list diagnostic does not settle checkpoint 3.** `not_mutViewSurvives_reads` is
>    refuted at an input that is not built from a `TW` history. It does not predict where the
>    list-reading probes stop. It also does not show the failure belongs to Core's `ptoMutS` rather
>    than to (a). Under LIFO an older frame cannot close while a younger `Mut` view lives; only
>    (a)'s out-of-order closing creates that situation.
>
> Minor findings, listed under "Verification" below, also need prose fixes.

## 1. The question

Under OQ-9 (a), a stop (an effect operation suspending the computation) does **not** end the
borrows opened inside the run. A 6.64 shared-borrow frame, a 6.65 mutable lend, a 6.66 anti-frame
or a 6.150 reborrow record stays open. It is handed to the handler's table together with the
continuation. The question: does every path the continuation can take still close it? The paths
are resume, cancel and drop. A further case: a handler sits *between* two lenders and resumes a
continuation holding the inner lend. That is asked with a handler extent (OQ-3 (a)) and without
one (OQ-3 (b)).

OQ-9 (b), the ghost end (end the lend at the stop and re-lend fresh on resume), is already proved at
today's stop in `experiments/GhostEnd`. It is the comparison point and was not redone.

## 2. Outcomes, by Lean name

PROVED = a Lean theorem. UNFINISHED = stated as a named `def … : Prop`, not proved. *Refuted* = the
negation is proved. Both refutations are at inputs **not** built from a `TW` history. They are
facts about our draft definitions, not obstructions to (a).

**The draft's closure and stop (Stage A)**
- `close_upd_coherent`: PROVED at every *valid* resource (`ResU.Valid π` is a premise). With
  H16 and the pin in `CloseE`, the relativised `↭` of conjunct (37) does not depend on which
  closure a run picks. `upd_choice_free`, `pin_harmless`, `closeE_anti_flat` and
  `close_flat_agree` (corrected statement) are also PROVED.
- `UnpinnedIncoherent`: UNFINISHED. `FrameCopyBlocksExit` (F0): UNFINISHED.
  `ClosedCompatW`: UNFINISHED.
- `compatW_iff_hash` (F1): PROVED. At `mut` and `anti` entries the new frame condition `CompatW`
  is just `#`; at `imm` and `reb` entries it is stricter.
- `entryRecorded_mut` (F2, OQ-44's `MutLendRecorded`): PROVED. A `mut` cell at the stop that the
  start's closure lacks forces a `mut` entry at its place and lifetime among the entries the stop
  hands on, from (37) alone.
- `not_holdsInjective`: the injectivity form of exclusivity is refuted, at a non-arising
  resource. `HoldsChain`: UNFINISHED.
- `close_relend_anti`, `not_closeE_anti_at_mut`, `close_frame`, `compat_at_stop`,
  `compat_resume`, `younger_preserved`: PROVED.
- `wpGW_nil`, `ewpTS_ewpW`: PROVED. Core embeds into the draft; this is one direction only (see
  warning 3).
- `ewpW_fold`, `ewpW_unfold`, `ewpW_σmono_opTabW`: PROVED, and their axioms are printed. The
  README also names `ewpW_ind`, `opTabW_mono` and `ewpW_σmono` as proved, but `Axioms.lean` does not
  print axioms for those names.
- `dropKappa_by_surgery`: not stated.

**6.64 and 6.65: resource core of the hand-on (Stages B, C1)**
- `handOn64`, `exit64`, `handOn65`: PROVED, using printed lemmas only (6.24, 6.27, 6.28, 6.29,
  6.38, 6.39, 6.50), with the lend table (6.50) standing for the box. They hold **at the closure of
  the whole stop resource** (DESIGN §4.3 (ii)–(iv)). They do not yet hold at the share the
  continuation starts from: the transfer, DESIGN §4.3 (i) and (vi), is not built.
- `OpenFrame64`, `OpenFrame65`, `OpenFrame65Out`, `OpenFrame65OutStable`: UNFINISHED. The
  probes themselves are not proved.

**6.150 (Stage E)**
- `handOn150` (with `reb_restrict`), `rebChooseTW_pin_W`: PROVED at the resource level. This is
  not yet connected to `CloseE`'s 6.150 step or to the lender's `ClosePre`, so "closed on both
  sides" is not shown in terms of `Close`.
- `OpenRecord150`, `RebChooseTWTopW`, `RebChooseTWDeepW`: UNFINISHED.

**6.66 (Stage C2)**
- `anti_unclosable`, `anti_handOn_needs_invariant`: PROVED. Under the draft's (37), suppose a stop's
  resource holds `own(w)` at an open anti place and `P̂(w)` is unsatisfiable. Then the stop fails
  the lender's (37).
- `OpenFrame66`: UNFINISHED.

**Between lenders (Stage D)**
- `reentryInheritA`, `reentryFreshA`, `resumeOutOfOrder`, `extentObligation_bypassed`,
  `argBelowExtent`, `argAboveExtent`: PROVED as conditional statements. Their premises are shown
  satisfiable at one hand-picked resource (`*_premises`), not derived from a `TW` history of the
  between-lenders program.
- `mutViewSurvives_stable`: PROVED. `not_mutViewSurvives_reads`: refuted at a non-arising input.
- `HandlerBetweenLendersB` (and its cancel and drop forms), `EwpHandleW`, `EwpHandleWExt`,
  `ClauseBetween*Stmt`: UNFINISHED.

## 3. What this settles and leaves open

**OQ-9 (a) vs (b).** Nothing is decided.
- Shown at the draft: a closure-relative (37) can be made coherent (sufficiency only). The
  resource-level step of carrying a 6.64 frame, a 6.65 lend and a 6.150 record across a resuming
  stop goes through on printed lemmas. So does closing the first two at a later return, abortive
  stop or cancel's end. This is evidence that (a) is not blocked at the resource level for these
  three. It is not a proof of any probe.
- For 6.66, the draft's (37) needs `P̂` at the content of a stop that hands on an anti entry. That
  is the condition `anti_handOn_needs_invariant` names. Whether every run is forced into that shape
  is not shown. So whether (a) has any advantage over (b) for 6.66 is open.

**OQ-3.** Open. The conditional statements say three things. (a)'s own rule rejects resuming `κ`
inside a lend younger than `κ`'s inner lend, with an inherited extent and with a fresh one. Read
under D-ORD, the resumed stack is out of order under both options. The draft does not enforce
(a)'s nesting, because `ewpW` is σ-monotone. At the two argument shapes tested, the extent check
rejects nothing `CompatW` admits. This supports DESIGN's FINDING-2: telling OQ-3 (a) from (b) needs
D-ORD (OQ-8) or a relation that reads `σ`'s lifetimes, not this draft. That support is conditional:
nothing was derived from an arising history, and the (b)-arm probes are unfinished.

**OQ-44.** `entryRecorded_mut` shows OQ-44 (a)'s entries record an open 6.65 lend. The `imm` and
anti forms are not stated.

**OQ-57.** Not addressed. DESIGN's FINDING-3 stands: OQ-57's settling statement needs a second
fixed point (`ewpC`) beside the one draft relation, so a one-relation probe cannot settle it.

**Unit 3, and findings about the structure.**
- Conjunct (40) cannot simply be removed. The draft replaces it with `StopW`, which adds list
  bookkeeping, a freshness conjunct for `imm` entries only, and two `CompatW` conjuncts. That is a
  change at the level of the plan.
- **First-rule point: lifetimes.** The draft constrains the lifetime of a handed-on entry only for
  `imm` entries. `mut`, `anti` and `reb` entries are unconstrained relative to `σ` and `ls`, `σ` is
  unordered, and `ewpW` is σ-monotone. So the draft as defined does not establish the lifetimes
  guarantee at stops. That depends on D-ORD or on a `TW` change.
- **First-rule point: exclusivity.** Exclusivity at a stop is OPEN. Form (i) is refuted at a
  non-arising resource, and form (ii) (`HoldsChain`) is unfinished.
- **First-rule point: leak freedom.** The draft relation does not enforce `κ`'s linearity when
  `κ` holds entries. DESIGN §1.6 shows that a clause holding `τ′ = [e₂]` can reach a value without
  running `κ`: it closes the lender's entry by surgery and keeps `ℓ₂ ↦ own` in its answer. Only
  typing (`U C` is not `Drop`) and tight postconditions prevent it. `dropKappa_by_surgery` would
  check this and is not stated.
- **`CompatW` narrows the frame quantifier** beyond Core's `#` for `τ ≠ []`. Whether this is the
  printed H14 carried across stops or an extra guard beside `TW` is open: its necessity (F0) and
  its dischargeability (`ClosedCompatW`) are both unproved.
- Core embeds into the draft, one way only. The converse, T1 for tier-1 programs, is open.

## 4. Verification

Three verifiers ran.
- **Verifier 1: pass.** Two minor findings. (a) Comments in `Checks.lean` (module docstring, and
  `close_flat_agree`) tell history ("corrected", "after correction 2", "now asks"). They should say
  what each statement is and point to DESIGN §2. (b) `Axioms.lean` covers the 39 delivered results.
  The verifier checked all 148 theorems separately, and all are within the allowed axioms.
- **Verifier 2: fail.** Majors 1 and 2 in the warning above. Minors: `handOn64`/`handOn65` hold
  at the stop's closure, not at the share; `handOn150` is not bridged to `Close`; "FINDING-2 holds
  in Lean" overstates (conditional statements, non-arising premises, two argument shapes); the
  diagnostic's "would stop there" is a prose prediction.
- **Verifier 3: fail.** Majors 3, 4, 5 and 2 in the warning above. Minors: `CompatW`'s grounding is
  unproved; `StopW` is an unreported change at the level of the plan, and the draft has no lifetime
  nesting for non-`imm` entries; the drop-κ property is not surfaced; small mismatches
  (`ResU.Valid` premise, axiom coverage of the named `ewpW` lemmas, "contradicts" should be "fails
  at a list satisfying the alternation").

None of the findings says a proved theorem is wrong. All of them say the README and DESIGN prose
draws conclusions the Lean does not carry. This checkpoint states the narrower readings. The README
and DESIGN themselves are **not yet corrected**.

## 5. What this means for the next batch

1. **First, a correction pass on README, DESIGN and `Checks.lean`.** Restate every necessity claim
   as sufficiency, or prove it. Mark exclusivity, conservativity and checkpoint 3 as open. Remove
   history from comments. Surface the drop-κ and lifetimes points. Nothing should build on the
   current README's conclusions until this is done.
2. **Then, deep on one probe rather than broad.** The best candidate is `OpenFrame65`: `handOn65`
   already serves every path. The remaining work is the transfer from the stop's closure to
   `OpenInv` at the share (DESIGN §4.3 (i), (vi)) and the wp-level steps. `OpenFrame64` is next,
   with its list (DESIGN §4.3).
3. **Claims that steer decisions need Lean configurations built from an arising history.** This
   covers the 6.66 counter-body (`write w ∉ P̂; perform`, with its `ewpW` and `TW` history),
   `UnpinnedIncoherent` and an H16 analogue at concrete resources, a doubly nested `withbor3` list
   for `HoldsChain`, and a `TW` history of the between-lenders program for checkpoint 3 and the
   OQ-3 premises. If none is built, these stay open, and OQ-9 (a)/(b) and OQ-3 are not decided on
   them.
4. **Lifetimes at stops depend on D-ORD (OQ-8).** The draft's σ-monotone `ewpW` cannot carry them,
   so that decision gates both the lifetimes guarantee and OQ-3.
