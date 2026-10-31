# Tombstone: lends held across suspensions

**Closed by decision 71 (`docs/decisions.md`), 2026-10-31.** This page records a research line
that is closed. Do not propose reopening it, or any of the approaches below, unless the user
brings a breakthrough (*Reopen condition*).

## The rule

**Owned across suspensions, borrowed within.** No borrow is held across a suspension: a
resuming effect operation, `await`, `yield`, or a loop's tick (`Div` is a handled effect, so every
iteration of a loop that is not counted is a resuming operation, decision 67). Data that crosses a
suspension is owned: it is moved into the suspended code and moved back out. Inside one stretch
between suspensions, borrow freely. This is T1 (`Row.Unwind` on the borrow constants, SPEC §19),
made the permanent design rule. The kernel already enforces it, and no rule is added.

The fixes a refusal names:

- **end the borrow before suspending**: put the borrow block inside the loop's body or around one
  stretch, so that the `await` or `yield` comes after it;
- **move ownership in and out**: give the task or generator the owned value, and have it hand the
  value back;
- **iterate by index, or with a counted `for`**: a counted `for` over data is a total fold with no
  tick (decision 47);
- **copy the value out**: read what the suspended code needs into owned values first.

Kept, all of it on `main` and unchanged:

- lexical lends, and borrows across abortive operations (an error unwinds through the lend,
  SPEC §19);
- counted `for` over data (`count_try`, SPEC §16);
- LoopLend, the per-observation lend (decision 40, SPEC §14, `Frontend/Elab/LoopLend.lean`,
  `lib/lend.bc`): its output is core that the kernel checks;
- BOXED-κ (SPEC §28);
- scoped tasks, `spawn_in`/`run_in` (SPEC §32): a task holds a borrow lent from outside the
  scheduler, which runs inside that borrow's scope;
- capabilities as borrows (SPEC §11, §34).

Frozen: R1 (SPEC §29: a task's own cell lent `mut` across resuming operations, under `PinLaw`'s
`LendFrame`), with #750's cancel-path widening (SPEC §29a), exactly as on `main` at `d418de4c`.
`PinLaw` (`Core/PinLaw.lean`) gets no new field, case or premise. R2 (`lendLoopR`, `LoopFrame`)
stays in the judgment and is not emitted; that is frozen too, not future work.

## Why it was closed

In the user's words (2026-10-31): "Freeze r1 for now. Keep looplend. Rewrite the corpus and spec
and plan. Tombstone the abandoned path so we don't bring it up again unless we have some
brilliant breakthrough." It followed: "What if we just gate this path off permanently. What do we
lose if we just narrow it to what we can prove _easily_ or already have proved."

The calculus's proof (BoLo) is about scoped callbacks: its invariant, `↭`, brackets every borrow
cell inside one run. A suspension splits a run, and a lend open at the stop is outside what the
model can say. Two months of attempts, listed below, each found that wall again from a different
side. Every widening was paid for in assertions, not proofs (`PinLaw` was restated or widened at
nearly every step, history §7 item 6), and every
attempt to retire LoopLend lost programs it carried. No literature pass found a complete proof to
import or a working language to port for the general problem. Narrowing to what is proved costs a
known, small set of program shapes, each with a written idiom (*The rule*).

## Abandoned approaches

One line each; dates are 2026. The full record is the history (*Sources*).

| approach | why it was stopped |
|---|---|
| l_lang's transient borrow (07–08) | refused across suspension; the construct admitted no program |
| `iterImm`, boxed-lifetime codata over cells (09-27, PR #61) | `↭` excludes returning a view |
| O1 spanning lend, `withbor` through `ν` (09-29, PR #111, `experiments/LoopBorrow`) | refolding proved, the Kripke step refuted (`refoldKripke_false`); needs a register of open lends, never stated |
| handlers as borrows, "T2 unblocks T1" (09-30, #170, #173) | claim withdrawn: T2 is not T1 |
| narrow run, stratified places (10-02, PR #255) | `nu_op_fails_linear` open |
| the `mut`-cell lemma (10-02, PR #254) | O15.1 (a lend spanning a suspension) not derived |
| re-stratification as naturality (10-02, PR #257) | `mut_not_natural`; `WpNatural` not derived |
| GhostEnd: end at the stop, re-lend at resume (10-02→03) | lender half proved; the borrower's GFP reading failed |
| GFP over a lend stack, tier 2 (10-02→05, PRs #284, #285) | `not_gfp`; closed unmerged |
| Kripke-extension reading (10-03, #286, PR #287) | closed unmerged; never carried into a relation |
| WorldW, one Kripke world (10-03→05, `probe-open-frames`) | open frames unfinished |
| ProbeD1, a lend stack in the callback's ∀ (10-06→08) | `U`-intros not derived; abandoned |
| bridge and segment-shift probes (10-12) | `not_coreThawTop`, `segShiftFailsAtEveryCut`; tier 2 shelved |
| A1 colourless surface over rank-1 rows (10-13, PR #472) | fails at order 3 |
| dense carrier, lifetimes in ℚ (10-13) | `carrier_rigid`, `core_not_relend_kU` |
| Law 2, a re-lendable reading of every type (10-13/14) | 59 of 91 proved; infinite regress |
| nominal lifetimes (10-14) | a fragment proved; the FP never built |
| PinLaw v1 at `opTableO` (10-14) | probable cancel-path hole; restated |
| R2, the `imm` loop lend (10-14) | in the judgment, never emitted (U6); now frozen |
| per-site unsafe assertions, option D (10-15/16) | never merged |
| #644 B2 per-turn lend in the elaborator (10-21) | reverted: the elaborator doing kernel work |
| #644 B2, loops elaborated to `Div` (10-21, PR #646) | moved 12 lend programs to pending; closed |
| #645 SuspSpike, operation classes (10-21, PR #648) | class 1 proved; classes 2 and 3 had no technique for a stored `κ` |
| class 1 as a `Bool` grade (10-21, PR #654) | "needs a proper algebra"; closed |
| #564 R-1, direct `for`, handle-last (10-22, PR #665) | superseded by the hybrid |
| M1 grades stage 1 (10-22/23, PR #678) | merged, then reverted |
| the hybrid Core→Core rewriter (10-22→27, #669) | judged a failure; reverted (#697) |
| E2, a third PinLaw field `[lend-ν]` (10-23) | more trust for little coverage |
| L3 packing (10-23) | design only; does not prove PinLaw |
| a general former, a borrow-only re-lend (10-23) | argued, not built |
| class1-revive (10-29) | P1 only; one step copied a linear value; rejected |
| #743 falsification rounds 1–5 and P/P2/P3 (10-30/31) | no counterexample (coverage, not proof); `not_lifeNatural` |
| PinLaw as two schemas (10-31, PR #754) | merged; adds no content (`pinLaw_iff`). Stays, frozen |
| stackK spikes (10-31) | neither typeable nor a `LendFrame` instance; asserted |
| #743-B5, loops as `Div` with class 1 and a two-point world (10-31) | kernel green, the surface hit four stops; parked |
| unit R, Koka rows with a Granule world solve (10-31, #766) | design only: "the same swamp" |
| "loops asserted", round 6: port the relaxed rules, open callbacks (10-31) | approved, nothing built: "an endless pile of assertions" |

Also closed with them, as designs on the way to lifting T1: L0, segmenting a borrow block at an
`await` by elaboration (U3 of `docs/async-capabilities.md`); emitting R2 (U6); shrinking `PinLaw`
(U8); OQ-1 beyond the cancel path, OQ-2 (`imm` relaxed lends), OQ-3 (a `mut` loop lend), OQ-5
beyond cancellable waits; spike S-T, "T1 at tail-resumptive operations" (#601); the lending
cursor elaborated from a generator over a borrow; steps B2–B7 of the #743 plan.

## Where the artefacts are

All read-only. Most branches are local and unpushed.

| artefact | where |
|---|---|
| #743-B5 kernel (two-point world, class 1) | branch `743-b5-loops`, head `58ca551b`; `~/repos/borrow-core-743b5` |
| #743 plan, log, charter, world history and literature, B5 evidence | `~/repos/scratch-archive/743/` |
| spike rounds 1–6 | branches `spike-743-pinlaw`, `spike-743-natural`, `spike-743-natural2`, `spike-743-r5`, `spike-743-r6` (`c7ef41c8`); reports in `~/repos/scratch-archive/spike743/` |
| #750 spikes | `spike-cancel-resume`, `spike-trio-cancel`; reports in `~/repos/scratch-archive/linear-types/` |
| stackK spikes | `spike-stackk-ref` (`5bcb5c97`), `spike-stackk-lend` (`70cb3123`) |
| #644 B2, class 1, R-1 | branches `b2-div`, `call-grade`, `b2-main`; PRs #646, #654, #665 |
| class1-revive | `~/repos/borrow-core-class1`; reports in `~/repos/scratch-archive/across-743/` |
| SuspSpike | branch `susp-spike`; PR #648 |
| WorldW | `origin/probe-open-frames` (`experiments/WorldW`), `244bf2d9` |
| ProbeD1 and the tier-2 shelf | `origin/targets` (`experiments/ProbeD1`, `research/effects/src/tier2-status.md`, `Restricted/RunEnd.lean`) |
| carriers | branches `law2-typed-world`, `nominal-lifetimes`, `origin/dense-carrier` |
| unsafe design | branch `unsafe-spec`, `docs/unsafe.md` |
| E2 | branch `e2-spike`; `~/repos/682-work/` |
| unit R design | `~/repos/scratch-archive/row-inference/design.md` |
| hard-problem corpus, P1–P12 probes | `~/repos/borrow-core-across/scratch-743/` |
| on `main` | `experiments/LoopBorrow`, `experiments/GhostEnd`, `docs/effects-tr/15-mut-cell.md`, `16-regress.md`, `17-borrow-callbacks.md`, `docs/prior-art-suspension-borrows.md` |

## Reopen condition

Only a breakthrough the user brings. In the user's words (2026-10-31): "Either a paper with a
complete proof we can import or a direct example in a working language we can port over." An
agent does not reopen this line, propose one of the approaches above again, or file work toward
lifting T1 or widening `PinLaw`. A program that needs a borrow across a suspension is rewritten
in the idiom above, or is a reject that names the fix.

## Sources

- The full history: `~/repos/scratch-archive/history-lends-across-suspension.md` (coverage
  2026-09-02 to 2026-10-31; §6 the attempts, §7 the recurring patterns, §10 the parked
  artefacts).
- `docs/decisions.md` decision 71; SPEC §19 (T1), §29 (R1, frozen), §14 (LoopLend).
- `docs/theory-index.md` T1; `docs/async-capabilities.md`; `docs/loops.md`;
  `docs/expressiveness.md` B5; `docs/roadmap.md`.
