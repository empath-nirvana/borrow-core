# WorldW — open lends handed across a stop (OQ-9 (a), OQ-3)

**World of every result here: the W-draft `(ρ, ls, σ)`, with the closing obligation `τ` an index
beside it.** The draft definitions live in this experiment only. `Core/` and every other experiment
are untouched. A result here is not a result at Core's relation (`σ = []`), except where it says so
(`Nil.lean`). It is not a result at Unit 3's `W` either: this experiment defines no relation at `W`.

Build: `lake build WorldW`. The build has no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial` or `unsafe`. `WorldW/Axioms.lean` prints the axioms of every delivered result; each
reports `[propext, Classical.choice, Quot.sound]`.

The design, with the four corrections made while building it, is [`DESIGN.md`](DESIGN.md).

## The question

Under OQ-9 (a) a stop does not end the lends opened inside the run. A `[TR]` 6.64 frame, a 6.65
lend, a 6.66 anti-frame or a 6.150 record stays open and is handed to the table with the
continuation. Does every path the continuation can take close it: resume, cancel, drop? And when a
handler sits between two lenders and resumes a continuation that holds the inner lend, with a
handler extent (OQ-3 (a)) and without one (OQ-3 (b))? OQ-9 (b), the ghost end, is proved at
today's stop in `experiments/GhostEnd` and is the comparison point; it is not redone here.

## The draft definitions (`WorldW/Defs.lean`, DESIGN §1)

| name | what it is |
|---|---|
| `OEnt` | an open entry: `imm` (6.64 frame), `mut` (6.65 lend), `anti` (6.66), `reb` (6.150), `hnd` (marker) |
| `CloseE`, `ClosePre`, `Close`, `Holds` | each entry's lender exit as resource surgery, innermost first; the anti step chooses a split and is pinned (`AntiPin`) |
| `CompatW` | the σ-component of `#`: the frame is compatible with every closure and inert under it (6.64's H14 carried by the world) |
| `StopW`, `wpGW` | `wpG` with conjunct (37) read at the closures, (40) (T1) replaced by `StopW`, and the frame quantifier extended by `CompatW` and the 6.64 selection of `σ` |
| `ewpW`, `opTabW`, `cancelTabW`, `shareW`, `owedW`, `extTabW`, `KapRelW` | `ewpTS` and its tables at the W-draft |
| `OpenInv`, `OpenInvReb` | the open-entry invariant a continuation holding an entry starts from |
| `ClosedOps`, `NoUnr`, `OblWf`, `YoungerThan`, `ListStable`, `QExt` | the table and payload conditions of §1.8 |

**Corrections made while building** (each recorded in DESIGN §2 with its reason; all four are
about our draft, none about OQ-9 (a) or a printed lemma):

1. `close_flat_agree`'s second conjunct was mis-stated: a later 6.65 entry at an anti entry's place
   unfolds the refolded cell again. Built at the anti entries no later 6.65 entry at their place
   follows; the first conjunct is strengthened. The design's first conjunct is proved as stated.
2. `CloseE`'s 6.150 step now asks `ResU.Reb β σR χ` (the printed H16). Without it the image may
   hold `imm` cells at lifetimes the pin does not cover, and two closures of one resource differ.
3. `holds_injective` (i) contradicts (ii) once a location's exclusive chain has two anti entries,
   which a doubly nested `withbor3` closes. Refuted as stated (`not_holdsInjective`); to be read at
   the `imm` keys only.
4. `compat_at_stop` takes the composite of the frame with the stop resource as a premise.

## Outcomes

PROVED means a Lean theorem of the design's statement (or of the corrected statement, where
marked). UNFINISHED means the statement elaborates as a named `def … : Prop` and has no proof here.
No OBSTRUCTION is reported: I have not derived any of the UNFINISHED probes, and I have not verified
that any obstruction to them is real.

### Stage A — definitions and checks (`Refold.lean`, `Coherence.lean`, `Checks.lean`, `Nil.lean`, `Wp.lean`)

| statement | outcome |
|---|---|
| `closeE_anti_flat` | PROVED |
| `close_flat_agree` | PROVED (corrected, correction 1); `close_flat_agree_off_anti` (the design's first conjunct) PROVED |
| `close_upd_coherent` (the stage gate) | PROVED (after correction 2), at every resource, no other premise |
| `upd_choice_free` | PROVED |
| `pin_harmless` | PROVED |
| `UnpinnedIncoherent` | UNFINISHED: stated; no concrete resource built |
| `FrameCopyBlocksExit` (F0) | UNFINISHED: stated; the `TW` history of §5 is not built |
| `compatW_iff_hash` (F1) | PROVED |
| `EntryRecordedMut` (F2) | UNFINISHED: stated; `entryRecorded_imm`/`_anti` not stated |
| `HoldsInjective` (i) | refuted as stated: `not_holdsInjective` (correction 3); the corrected (`imm` keys) form is not stated |
| `HoldsChain` (ii) | UNFINISHED: stated |
| `close_relend_anti` | PROVED (both halves: `close_relend_anti`, `not_closeE_anti_at_mut`) |
| `close_frame` | PROVED |
| `ClosedCompatW` | UNFINISHED: stated |
| `compat_at_stop` | PROVED (with correction 4's premise) |
| `compat_resume` | PROVED |
| `younger_preserved` | PROVED, in the form `StopW` gives it (a record at `α` present at both ends) |
| `dropKappa_by_surgery` | UNFINISHED: not stated (it needs a `wpGW` run of one β-step) |
| `wpGW_nil`, `ewpTS_ewpW` (§1.9, conservativity) | PROVED |
| `ewpW_ind`/`_fold`/`_unfold`, `opTabW_mono`, `ewpW_σmono` (§4.2) | PROVED |

### Stage B — 6.64 at a mixed row (`Frame64.lean`, `HandOn.lean`)

| statement | outcome |
|---|---|
| `OpenFrame64` | UNFINISHED |
| `handOn64` (resume: reading 2 for 6.64 at the resource level) | PROVED |
| `exit64` (return, abortive stop, cancel's end: the printed exit at the resource level) | PROVED |

`handOn64` and `exit64` are the steps of `OpenFrame64` that touch resources (DESIGN §4.3 (ii)–(iv)
and the value case), each a chain of printed lemmas: 6.50 keeps the table; 6.29 puts the view at
the top of the stop's closure; 6.38, with the split view ↦ `ρ⁺` and the table off `ℓ` standing for
H4, makes the exit defined there; 6.39 gives the lender's relativised `↭`. So the frame's
open-entry invariant (its resource half) holds again at every resuming stop, and the printed exit
applies at every return, abortive stop and cancel's end whose resource splits into a part in
`Res_α` and an own-free rest.

What `OpenFrame64` still needs, by the step of DESIGN §4.3 it belongs to:
* the frame quantifier: `CompatW τi` from `CompatW (τi ++ [e₀])` (6.34 across closures), and the
  closures of the borrower and the lender reconciled through the pins (reading 7);
* the value case: `TW.immEnd`, `Tagged` by `frameLife_back`, `StopW`'s value clause, `QExt` along
  the record list without `e₀`'s lineage, and the owner handed through `exitI`'s wand;
* the resuming stop: `StopW`'s stop clause (frame list, record list, freshness), the two
  `CompatW (τ′ ++ [e₀])` conjuncts (6.38's G1 at the stop), and the table: `shareW (τ′ ++ [e₀])`
  from the borrower's `shareW τ′` by the induction hypothesis, which needs `OpenInv` at the share
  and answer at every `Ext` (the resource half is `handOn64`; the payload's `vC` along `Ext` and
  along the stop's own list change is where `YoungerThan` is spent), `Holds`, and the argument's
  `CompatW`;
* the abortive stop and the cancel's end: the owner beside the stop (`withOwnerW`), and
  `openFrameCancel64` at the cancel table.

### Stage C1 — 6.65 (`Frame65.lean`, `HandOn.lean`)

| statement | outcome |
|---|---|
| `OpenFrame65` | UNFINISHED |
| `OpenFrame65OutStable` | UNFINISHED |
| `OpenFrame65Out` | UNFINISHED |
| `handOn65` (every path: reading 2 for 6.65 at the resource level) | PROVED |

`handOn65`: 6.27 puts the lend's cell at the top of the stop's closure with the same lifetime and
predicate, 6.24 makes the exit defined, 6.28 (an iff) gives the lender's relativised `↭`, 6.50 keeps
the rest above `α`. The 6.65 exit needs no box at the resource level, so the same lemma serves the
resume, the return, the abortive stop and the cancel's end. 6.40 (untranscribed) is not needed.

### Stage D — between lenders (`Between.lean`, `Instances.lean`, `Diag.lean`)

| statement | outcome |
|---|---|
| `HandlerBetweenLendersB`, `…Cancel`, `…Drop` (at `T3Stable`, `T3Reads`) | UNFINISHED: they rest on `OpenFrame64`, `OpenFrame65Out(Stable)` and `EwpHandleW` |
| `EwpHandleW`, `EwpHandleWExt`, `ClauseBetweenStmt`, `ClauseBetweenCancelStmt`, `ClauseBetweenAStmt` | UNFINISHED: stated |
| `ReentryInheritA` | PROVED (`reentryInheritA`); premises satisfied at a concrete share (`reentryInheritA_premises`) |
| `ReentryFreshA` | PROVED (`reentryFreshA`); premises satisfied (`reentryFreshA_premises`) |
| `ResumeOutOfOrder` | PROVED (`resumeOutOfOrder`); premises as `reentryInheritA_premises` |
| `extentObligation_bypassed` | PROVED |
| `ArgBelowExtent` | PROVED (`argBelowExtent`); premises satisfied (`argBelowExtent_premises`) |
| `ArgAboveExtent` | PROVED (`argAboveExtent`) |
| `MutViewSurvivesOlderClose T3Stable` (diagnostic) | PROVED (`mutViewSurvives_stable`) |
| `MutViewSurvivesOlderClose T3Reads` (diagnostic) | refuted (`not_mutViewSurvives_reads`) at a non-arising input |

The instances are at the resource level (the first stop's share, `e₂`'s view, with
`α₃ ⊏ α₂ ⊏ h`). They are not built from a `TW` history of the between-lenders program.

The diagnostic settles checkpoint 3 of DESIGN §3.4. `ptoMutS` stores the payload predicate frozen
at the list of records longer-lived than the cell, and asks it to *equal* the payload relation at
that list. When an older 6.64 frame closes while the younger `Mut` view exists, its records leave
the list. At `1 ⊕ 1` nothing changes. At `1 ⊕ Imm 'x₁ 1` the relation reads the list through
`CohE`, and at a view of the older frame's place the two lists give different predicates, so the
view is no longer `ptoMutS` at the shorter list. The distinguishing input is not built from a `TW`
history, so this measures our `ptoMutS` (`[about ours]`), not (a): the list-reading between-lenders
probes would stop there, and the list-stable ones need not (reading 4). Under OQ-9 (b) the re-lend
at a fresh lifetime keeps the list LIFO and the case does not occur.

### Stage E — 6.150 (`Record150.lean`)

| statement | outcome |
|---|---|
| `OpenRecord150` | UNFINISHED |
| `handOn150` (resume: reading 2 for 6.150 at the resource level), with `reb_restrict` | PROVED |
| `RebExitW`, `RebChooseTWW` | stated |
| `rebChooseTW_pin_W` | PROVED |
| `RebChooseTWTopW`, `RebChooseTWDeepW` | UNFINISHED: stated |

`handOn150`: 6.52 with the split `ρ′ := ∅`, `ρ⁺ :=` the stop's resource puts the image at the top
of the stop's closure with its subtraction in `Res_β` (the open-entry invariant's strata again);
6.59 gives the lender's relativised `↭` with the reborrow closed on both sides and the view kept.
The image restricted to the source's exclusive locations is a reborrow image (`reb_restrict`), so
6.52 and 6.59 apply to it as printed. The step DESIGN §3.3 says to watch, the exit's typing by
`TW.rebEnd` at a world holding a younger lend, is at the wp level and is not reached here.

### Stage C2 — 6.66 (`Frame66.lean`, `HandOn.lean`)

| statement | outcome |
|---|---|
| `OpenFrame66` | UNFINISHED; see below |
| `anti_unclosable`, `anti_handOn_needs_invariant` | PROVED |

A stop that hands the anti entry on must close it in (37), and closing it refolds the place, which
needs `P̂` of the content at the stop. `anti_handOn_needs_invariant`: if the place holds `own(w)` at
the top of the stop's resource and `P̂(w)` holds of no resource, no closure of the stop, by any list,
is `↭`-related to the start's closure. `OpenFrame66`'s premise (the body's `ewpW`) does not exclude
such a stop: a body may store a value outside `P̂` and then perform. So the statement asks for more
than its premise gives at such a body. I have not built that body, its `ewpW` or its `TW` history,
so `¬ OpenFrame66` is not proved. OQ-9 (b)'s `AntiRelend` (GhostEnd) asks the body to restore
`ℓ ↦ w ⋆ 𝒱⟦T⟧(w)` at every stop: under this draft's (37), (a) for 6.66 needs the same.

## What the outcomes mean

**OQ-9 (a).** Two things are settled in Lean, one is not.
* The draft's relativised `↭` is coherent: conjunct (37) does not depend on which closures a run
  picks (`close_upd_coherent`, `upd_choice_free`), at every resource. That needed two corrections
  to our closure (corrections 1 and 2), both about `Close`, neither about (a). A definition of
  Unit 3's stop that reads `↭` relative to the closure of the open entries must carry the printed
  H16 at the 6.150 exit and the pin at the anti step.
* The resource core of carrying a 6.64 frame, a 6.65 lend and a 6.150 record across a resuming
  stop, and of closing the first two at a later return, abortive stop or cancel's end, goes through
  with printed lemmas only (6.24, 6.27, 6.28, 6.29, 6.38, 6.39, 6.50, 6.52, 6.59), with the lend
  table (6.50) standing for the box (`handOn64`, `exit64`, `handOn65`, `handOn150`). That is
  DESIGN §7's reading 2, checked for 6.64, 6.65 and 6.150.
* For 6.66 the draft's (37) needs the anti entry's invariant `P̂` at every stop that hands it on
  (`anti_handOn_needs_invariant`): closing the entry at the stop refolds the place. That is the
  invariant OQ-9 (b)'s `AntiRelend` asks for at each stop. So under this (37), (a) gains nothing
  over (b) for 6.66, unless (37) reads an open anti place by the entry's own `(β, P̂)` instead of
  refolding it.
* The probes themselves (`OpenFrame64`, `OpenFrame65`, `OpenFrame66`, `OpenRecord150`) are
  unfinished. The steps 6.64's and 6.65's still need are listed above; none of them is a step
  these results found blocked.

**OQ-3.** FINDING-2 holds in Lean, at an unordered `σ`. (a)'s own rule rejects resuming `κ` inside
a lend younger than `κ`'s inner lend: at once with an inherited extent (`reentryInheritA`), and at
the second stop with a fresh extent (`reentryFreshA`). Read under D-ORD, the resumed term's stack is
out of nesting order under both options (`resumeOutOfOrder`). The draft relation does not enforce
(a)'s nesting (`extentObligation_bypassed`), and at the configuration's stop the extent's check
rejects nothing `CompatW` admits (`argBelowExtent`, `argAboveExtent`). So whether a handler between
two lenders may resume, cancel or drop `κ` inside a younger lend is decided by OQ-8's D-ORD
together with OQ-3, not by this draft. The (b) arm's probes, which would show (b) accepting the
configuration at an unordered `σ`, are unfinished.

**OQ-57.** Not addressed here, as DESIGN scopes it out; FINDING-3 stands as written there.

**Unit 3.** For the definitions:
* the stop relativisation is a conservative extension: Core is the `τ = σ = []` instance
  (`wpGW_nil`, `ewpTS_ewpW`);
* the σ-component of `#` restricts frames only at `imm` and `reb` entries; at `mut` and `anti`
  entries it is `#` (`compatW_iff_hash`, F1);
* exclusivity at a stop is not injectivity of entries to keys: the exclusive keys at one location
  alternate, and repeat across nested `withbor3`s (correction 3);
* a resumer's frame inherits compatibility from the stop's pieces and its own
  (`compat_at_stop`, `compat_resume`); a resumer read only through a relation is FINDING-1, unchanged.

## Report lists (CLAUDE.md §5)

**Printed hypotheses spent by the proved results.** `handOn64`/`exit64` spend 6.29's H1 and H3,
6.38's H1–H4 (H3 and H4 through the lend table) and 6.39's H1–H3. `handOn65` spends 6.27's `@ρ ⊐ α`,
6.24 and 6.28's validity premises. `handOn150` spends 6.52's `@ρₑ ⊐ α` (the open-entry invariant's
strata) and `@ρ′ ⊐ α` (at `ρ′ := ∅`), and 6.59's H(`@ρ_b ⊐ β`), `ρ_b # ρᵢ` and `ρ′ ● ρ⁺ # ρᵢ`. The 6.150 exit's H16 is spent in `CloseE` (correction 2).
**Unspent**, because the entry lemmas and the wp-level probes are not built: 6.64/6.65's И
freshness (H4, 6.112), 6.65's `P̂ ⊨ [β]P̂`, 6.150's `RebEscrow` and its local strata, and Core's
added `hQ` (`QExt`).

**Uniqueness and functionality results.** Used: `ResU.CompS.functional`, `ResU.SubKeep.functional`,
`ResU.Flat.functional`, `CellU.mutOf_at`, `CellU.mutOf_inj`, `CellU.immOf_inj`, `LSet.ext`. Unused:
`head_det_eff`, `AStep1.deterministic`, `ResU.Lower.functional`, `TI`'s uniqueness of open frames.

**Printed lemmas in the run-up that are untranscribed.** 6.40 (`Paper/INDEX.md`). No proved result
here needs it: the 6.65 exits in `handOn65` use 6.24.

## Layout

```
WorldW.lean            root
WorldW/Defs.lean       §1: the draft definitions
WorldW/Refold.lean     refold sequences: the machinery behind F-CLOSE
WorldW/Coherence.lean  two closures of one resource: close_pair
WorldW/Checks.lean     §2: F-CLOSE, F1, exclusivity, the other checks
WorldW/Wp.lean         §4.2: ewpW's fixed point, σ-monotonicity
WorldW/Nil.lean        §1.9: Core is the τ = σ = [] instance
WorldW/HandOn.lean     reading 2: the resource core of the hand-on (6.64, 6.65, 6.150); 6.66's refold
WorldW/Frame64.lean    OpenFrame64
WorldW/Frame65.lean    OpenFrame65, OpenFrame65OutStable, OpenFrame65Out
WorldW/Frame66.lean    OpenFrame66
WorldW/Record150.lean  RebExitW, RebChooseTWW, OpenRecord150
WorldW/Between.lean    between lenders; the OQ-3 (a) arm; the argument variant
WorldW/Diag.lean       MutViewSurvivesOlderClose
WorldW/Instances.lean  non-vacuity of the negative statements
WorldW/Axioms.lean     #print axioms of every delivered result
```
