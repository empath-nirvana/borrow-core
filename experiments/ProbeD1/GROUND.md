# ProbeD1: grounding the draft in Core — the design

This is the design for the unit after the guard-gap unit (`NEXT.md`, latest commit `3e84262`). It
plans four parts:
- **(0)** the doc fixes the guard-gap unit's content review asked for;
- **(1)** a grounding ledger (`LEDGER.md`, `GroundLedger.lean`): every ProbeD1 definition that has a
  Core counterpart, set against it, with a theorem wherever they are claimed to agree;
- **(2)** a regression suite (`GroundRegress.lean`, a section of `LEDGER.md`): Core's own typed
  borrow-only programs, and four seeds, each with the draft's acceptance obligation at the empty
  stack and a status;
- **(3)** the block entry (`NEXT.md` §1.6, item 1b): the designed fix for the two-cell gap, built in
  place in the one draft relation.

It contains no proofs. Every Lean block below elaborates against the built ProbeD1 at `3e84262` with
Core's program modules imported (`Core.Examples`, `Core.Folds`, `Core.RecordPrograms`,
`Core.FamilyPrograms`, `Core.BlockPrograms`, `Core.AffPrograms`, `Core.ArrayPrograms`,
`Core.Demonic`) [checked outside the build: a scratch file, not committed]. The exception is the
`vRLM` clause in §4.2, which is a fragment. *[unchecked]* marks a claim argued in prose and not in
Lean; *[read]* marks a claim read off the source; *[expected]* marks a status the build has to
confirm.

The rules are unchanged. Nothing breaks the borrow calculus: no printed BoLo definition is edited,
and nothing in `Core/`, `Paper/`, `Support/`, `GhostEnd/` or `Targets/` changes. Only ProbeD1's draft
may change, and only in part (3). The paper is not wrong. An obstruction is reported only as an
elaborating `def … : Prop` or as a configuration that arises with every hypothesis discharged
(DESIGN §11), `ArisesVI` included for views. There is no new relation family and no step index, and
multi-shot is ignored. Builds are targeted (`lake build ProbeD1`). There is no `sorry`, `axiom`,
`native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`, and every axiom set is within
`[propext, Classical.choice, Quot.sound]`. The regression entries use the named sub-derivations
Core already has; nothing inverts `CDerives` (CLAUDE.md, *Growth discipline*).

---

## 0. On one page

**What grounding means here.** Borrow-only programs (ordinary closures, higher-order functions,
borrows without suspension) are proved in Core: `fundamentalC` (`Core/Fundamental.lean:434`) at
`σ = []`. The draft W must reproduce that. A gap on such a program is a defect of the draft, to be
fixed, never a restriction (the user's corrections of 2026-10-08, `NEXT.md` §10). The last unit found
one such gap by luck: `withload` of a pair of references. This unit makes the comparison systematic:
the ledger says where the draft's definitions differ from Core's, and the suite runs Core's programs
through exactly those differences.

**Four facts, read off the source, shape the design.**

1. **A program's root says nothing.** At a flat answer type, the draft's computation relation at
   the empty stack *is* Core's: `nilSoundRetM` (`R1Stmt0.lean:133`) proves one way, and the converse
   follows by the same `bodyS_nil_iff` and `vRLMData` (`CRLMRetNil`, planned). So for a closed
   program at `F 1`, "the draft accepts it at `σ = []`" holds by Core's own proof, and no draft clause
   is read. The suite therefore states the obligation at the judgements of a program's derivation
   where the draft reads its own clauses: the callbacks and closures it builds, and the borrow
   constants it applies (§3.1).

2. **At first-order judgements the draft is Core** [read; to be proved as G5, §2.9]. Take a
   judgement whose context types are first-order arguments (flat data, `Mut` and `Imm` leaves, and
   their products, sums, boxes, `Ref`s and families) and whose type is a first-order computation
   type with no lifetime `∀` and no row. There the draft's semantic judgement `SemSM .binder0`
   follows from `fundamentalC`, at every index (`CoreToSemSM`). The reasons:
   - W's leaves contain Core's (their first conjunct is Core's leaf);
   - W's flat types are Core's;
   - at `⊸`, `&` and `F`, `binder0` reads no future and no instantiation.

   Composed with the draft's proved `U`, `∀I` and `!U` rows (`statement0UFullM`,
   `allIRowMUFree0`), G5 is expected to put every closed first-order callback in the draft's
   relation (§3.2). If it does, the places where the draft can diverge from Core on a borrow-only
   program are these [read]:
   - **producer side**, where a value is shown to be in the draft's relation:
     - (i) a callback whose context holds a `U` value at the own push: the `∀I` row at a live `U`
       slot, not derived;
     - (ii) a persistent polymorphic value carried across the binder-named push:
       `VRLMStackRename`, stated, not derived;
   - **consumer side**, where a value in the draft's relation is used:
     - (iii) `∀E`, which reads the `∀` clause's first conjunct, and (E1) restricts that conjunct to
       instances in scope;
     - (iv) every borrow constant's row, which must hand its callback the lend's argument at an own
       push, where the guard is read. That is where the two-cell gap lives.

   The suite targets exactly these places.

3. **Core's own family and block borrows are nested single-place lends.** `withborF2`
   (`Core/Family.lean:69`) and `withborS` (`Core/BlockBorrow.lean:347`) borrow each leaf with its
   own `withbor` and shorten to the innermost lifetime. So they never meet the two-cell gap: at the
   inner push both places are lent, each by its own entry [read]. But their inner callback captures
   the user's callback, a linear `U` value (`Family.lean:62`, `:65`), so they need the `∀I` row at a
   live `U` slot. That row is therefore a floor obligation, not only tier 2. `swapBoth`,
   `readFamily`, `splitFour`, `blockSwap` and the other block programs are affected.

4. **The user's case already exists in Core.** The fold programs (`countFoldProg`, `anyTreeProg`,
   `Folds.lean:375`, `:469`) bind the persistent, lifetime-polymorphic fold
   `g : !U(∀'a. Imm 'a M ⊸ F R)` (`fTy`, `Folds.lean:216`) at the top level. They capture it in the
   borrow's callback and call `g [] b` at the callback's own lifetime (`d_borrowerG`,
   `Folds.lean:253`). `corpus/array-get.bc`'s top-level `read` is used the same way [read]. No new
   program is needed for this seed (§3.5).

**The plan.**
- (0) Correct README, DESIGN §15.10, and `NEXT.md` §9–§10 to match CHECKPOINT's warning box (§1).
- (1) The ledger, rows and theorems (§2).
- (2) The suite, at the current relation (§3).
- (3) The block, built in place, gate first, then rebuilt and the suite re-run (§4).

(0)–(2) must be done even if (3) does not close (§5).

---

## 1. Part (0): the doc edits

Each edit replaces the passage at the lines given (at `3e84262`) with the text shown. Each one
carries one finding of CHECKPOINT's second warning box (`CHECKPOINT.md:72–119`):
- (a) the `!` clause is not fixed;
- (b) `withloadUPairGapNilE1`'s view is not shown to arise;
- (c) the box's pushes are a new reach of the `!` clause;
- (d1) "real" holds for [TR] 6.175's route;
- (d2) what `reconB′` owes is unchecked until it is typed.

### 1.1 `README.md`

**R1. `:333–336`** (R1 section, finding d1). Replace "Since then, … which is not built;" with:

    Since then, the unchecked step is proved at an arising configuration at `withloadU`'s type, on
    [TR] 6.175's route (`withloadUPairGapReal`); no `withloadU` row is refuted. Under the
    corrections of 2026-10-08 it is treated as a defect of the draft, not a restriction; that its
    cause is the single-place stack entry is [read]. The designed fix is a block (`NEXT.md` §1.6),
    which is not built;

**R2. `:391–403`** (findings b, d1). Replace the bullet "The two-cell gap is real at `withloadU`" with:

    - **The two-cell gap is real at `withloadU`, on [TR] 6.175's route** (`withloadUPairGapReal`).
      - The configuration arises: three allocations and a 6.64 lend. Its view arises, and the
        judgement's index holds there.
      - The program is typed at `withloadU`'s type. [TR] 6.150's `TW.reb` reborrows the payload at
        an own push's lifetime into a tagged typed world.
      - At every reading the callback's clause offers, the pair reborrowed at the reading's own
        lifetime fails the guard. No `withloadU` row is refuted: another argument might meet the
        table at a non-identity instantiation (`PairArgCellsLe`, not built). The non-vacuity push
        `pEn` lends place 3 at type `1`, unrelated to the payload.
      - At `withload`'s own thunked type, the statement is refuted at the same configuration
        (`not_withloadPairGapInst`). The answer's `U` clause moves the lend below the cells, where
        they meet the table.
      - After (E1) the route fails at the empty stack too (`withloadUPairGapNilE1`), but at a view
        not shown to arise (no `ArisesVI` witness). That is not evidence of a defect, and not a
        trigger to revisit (E1). `pairNilOldGuardHolds` says only that the table at `[]` holds of
        every resource.
      - Under the corrections this is treated as a defect of the draft on a borrow-only program,
        not a restriction. That its cause is the single-place stack entry is [read], not a theorem.
        The designed fix is item 1b's block, which is not built. The slice gate is not built either.

**R3. `:419–434`** (finding a). Replace the bullet "The floor." up to its "Open:" list with:

    - **The floor.**
      - Before the box, `vRLM`'s `!` clause did not carry persistent values across a push by
        construction, with or without (E1). At `vRLJ`, a persistent closure at a type with no
        lifetime `∀` is related at a stack and not after the own lend's push (`gdBangJ`). That is
        at `gd`, which is not shown to arise, and `gdF` is no Core value, so it is not evidence of a
        defect on a borrow-only program.
      - (E1) was kept, and the `!` clause gained the persistence box. The clause is not fixed. The
        box carries a persistent thunk across instantiations and own pushes at the empty resource
        under reserved names (`NsVar`) only (`persistentPushN`, `monoOwnGMAtBoxN`). The two `!U`
        rows are re-proved at it (`statement0UFullM`).
      - Two pushes are outside the box: the push `gdBangJ` fails at (`gdY`, named `2`, no reserved
        name), and the `∀` clause's own push, named by the type's binder (`OwnPushI`, `e.x = x`).
        The second is correction (i)'s case, a lifetime-polymorphic `!U` combinator carried into a
        lend's callback. Both wait on `VRLMStackRename` (stated, not derived) and a reduction that
        is not built. No `binder0` clause makes a reserved-name push, so the carrying proved may
        have no consumer yet. The user's example was not built, so it is unchecked that `withload`
        of a pair is the only borrow-only program (E1) affects.
      - Open:
        - the `∀I` row's binder-named push at a persistent context (`VRLMStackRename` and the
          reduction);
        - the reading transports at a `!U` slot;
        - a persistent slot reaching `U` below its top;
        - linear closures across a push;
        - the floor's own statement at `σ = []` (OQ-58's statements, not attempted).

**R4. `:435–440`** (finding d2). Replace the bullet "`reconB′`, as the language writes it" with:

    - **`reconB′`, as the language writes it** (`reconB'`).
      - `retry` is a handler installed around the lend, and the callback performs `wait`. It runs to
        `(tt, ff)` with no cell left (`reconB'_eval`).
      - Its callback is closed [read]. `reconCb_allI` is `allIRowMUFree0 []` under a
        program-specific name. The typing is not built.
      - What it owes beyond that row is [unchecked]. Its lend is `lendCell`, whose term is
        `withborUE dFlag`, which only the unwinding rules type, and those do not admit `wait`. Which
        typing rule and which callback row apply (`CallbackExtImmM` at the `.arr` shape, or the
        thunked `CallbackExtImmMF`, stated and not proved, a borrow-level obligation and not tier 2)
        is open. The suspension inside the lend (tier 2) is among what it owes.

**R5. `:441–448`** (findings c, d1). Replace the bullet "What it decides." with:

    - **What it decides.**
      - OQ-8 is not decided. The gate's gap is on [TR] 6.175's route; that it lies in the stack
        entry and the guard, which the placements share, is [read]. No refutation of a placement's
        statement passed DESIGN §11, and `cbpv` and `binder` were not redone at `vRLM`.
      - No failure of type (a) or (b) occurred.
      - (d) has not occurred, since statement 0 does not yet hold. The box is a new reach of the `!`
        clause, beyond `FutQ` and beyond the type it reads: its pushes are under reserved names at
        any thunk type, while the `∀` clause's own push is at the type it reads, named by its
        binder. If statement 0 comes to hold only with the box, DESIGN §12.2's reading of (d)
        applies; (d) is reported against both of §12.2's readings.
      - The fallback is not triggered.

**R6. Files table (`:450–500`).** Add rows for `GROUND.md`, `LEDGER.md`, `ProbeD1/GroundLedger.lean`,
`ProbeD1/GroundRegress.lean`, `ProbeD1/Block.lean` and `ProbeD1/GroundBlock.lean`, once they exist.

### 1.2 `DESIGN.md` §15.10

**D1. `:2288–2290`** (finding c). Replace the box bullet with:

    - The persistence box (`NEXT.md` §10.2). `vRLM`'s `!` clause reads a persistent thunk at every
      instantiation, every list kept outside, and every finite sequence of own pushes at the empty
      resource under reserved names (`NsVar`). The pushes are a new reach of the `!` clause: no
      `binder0` clause pushes under a reserved name.

**D2. `:2299–2310`** (findings b, d1). Replace the bullet "The two-cell gap is real at `withloadU`" with:

    - **The two-cell gap is real at `withloadU`, on [TR] 6.175's route** (`withloadUPairGapReal`).
      - At an arising configuration, the program is typed at `withloadU`, and one own push has a
        closed payload type. [TR] 6.150's `TW.reb` reborrows at the push's lifetime into a tagged
        typed world, and the pair reborrowed at each reading's own lifetime fails the guard at every
        reading the callback's clause offers. No `withloadU` row is refuted: another argument might
        meet the table at a non-identity instantiation (`PairArgCellsLe`, not built). The
        non-vacuity push `pEn` lends place 3 at type `1`, unrelated to the payload.
      - At `withload`'s own thunked type, the statement is refuted at the same configuration
        (`not_withloadPairGapInst`). The answer's `U` clause instantiates the lend below the cells,
        where they meet the table.
      - After (E1), the route fails at the empty stack too (`withloadUPairGapNilE1`), at a view not
        shown to arise (no `ArisesVI` witness). That is not evidence of a defect, and not a trigger
        to revisit (E1). `pairNilOldGuardHolds` says only that the table at `[]` holds of every
        resource.
      - The slice gate (`SliceUGapReal`) is not built.
      - Under the corrections this is treated as a defect of the draft on a borrow-only program, not
        a restriction. That its cause is the single-place stack entry is [read], not a theorem. The
        designed fix is item 1b's block (`NEXT.md` §1.6), which is not built.

**D3. `:2328–2341`** (finding a). Replace the bullet "The floor (correction (i))." with:

    - **The floor (correction (i)).**
      - Before the box, nothing in the `!` clause carried a persistent value across a push. At
        `vRLJ`, before (E1), a persistent closure at a type with no lifetime `∀` is related at a
        stack and not after the own lend's push (`gdBangJ`). That is at `gd`, not shown to arise,
        and its closure is no Core value, so it is not evidence of a defect on a borrow-only
        program.
      - (E1) was kept, and the `!` clause gained the persistence box. The clause is not fixed. The
        box carries a persistent thunk by construction across instantiations and own pushes at the
        empty resource under reserved names (`NsVar`) only (`persistentPushN`, `monoOwnGMAtBoxN`);
        the two `!U` rows are re-proved at it (`statement0UFullM`).
      - Two pushes are outside it: the push `gdBangJ` fails at (`gdY`, named `2`), and the `∀`
        clause's own push, named by the type's binder (`OwnPushI`, `e.x = x`). The second is
        correction (i)'s case, a lifetime-polymorphic `!U` combinator carried into a lend's
        callback. Both wait on `VRLMStackRename` (stated, not derived) and a reduction not built.
        No `binder0` clause makes a reserved-name push, so the carrying proved may have no consumer
        yet. The user's example was not built.
      - Open:
        - the `∀I` row's binder-named push at a persistent context (`VRLMStackRename` and the
          reduction);
        - the reading transports at a `!U` slot;
        - `PBox` at a `!B` reaching `U` below its top;
        - linear closures across a push;
        - the floor's own statement at `σ = []` (OQ-58's statements, not attempted).

**D4. `:2342–2346`** (finding d2). Replace the `reconB′` bullet with R4's text, its heading reading
"**`reconB′`, as the language writes it (correction (ii))** (`reconB'`, `reconB'_eval`)".

**D5. `:2349–2365`** (findings a, c, d1). Replace the bullet "What it decides." with:

    - **What it decides.**
      - OQ-8 is not decided.
        - The gate's gap is at an arising configuration, on [TR] 6.175's route. That it lies in the
          stack entry and the guard, which the placements share, is [read]; 1b is designed to fix it.
        - No refutation of a placement's statement passed §11.
        - `cbpv` and `binder` were not redone at `vRLM`.
      - No failure of type (a) or (b) occurred: there is no guard beside `TW`, and no relation
        family beside W.
      - (d) did not occur, because statement 0 does not yet hold, with the box or without it.
        - The box is a new reach of the `!` clause, beyond `FutQ` and beyond the type it reads: its
          pushes are under reserved names at any thunk type. `binder0`'s `U` clause makes the
          instantiations, but its `∀` clause's push is at the type it reads, named by its binder, so
          `binder0` does not already make the box's pushes.
        - If statement 0 comes to hold only with the box, §12.2's reading of (d) applies to it. (d)
          is reported against both of §12.2's readings.
      - The fallback is not triggered.
      - Under the corrections, gaps found on borrow-only programs are the draft's to fix: the
        two-cell gap (item 1b) and the `!` clause at the binder-named push (`VRLMStackRename`).

### 1.3 `NEXT.md` §9–§10

**N1. `:2401–2403`** (finding a). Replace "It answers correction (i)." with "It answers correction
(i) in part: it carries a persistent thunk across instantiations and own pushes under reserved names;
the binder-named push that correction (i)'s case meets is open (§10.4)."

**N2. `:2428–2444`** (finding d1). Replace the "The gate" bullet and the "What it means." bullet:

    - **The gate: `WithloadUPairGapReal` is proved** (`withloadUPairGapReal`), for [TR] 6.175's
      route. The configuration arises, and the program is typed at `withloadU`'s type. One own push
      has a closed payload type, and [TR] 6.150's `TW.reb` reborrows at its lifetime into a tagged
      typed world. At every reading the callback's clause offers, the pair reborrowed at the
      reading's own lifetime fails the guard. No `withloadU` row is refuted: another argument might
      meet the table at a non-identity instantiation (`PairArgCellsLe`, not built). The non-vacuity
      push `pEn` lends place 3 at type `1`, unrelated to the payload.

and

    - **What it means.** `withload` of a pair of references is a borrow-only program. Under
      correction (i) (§10), a borrow-only program that the draft does not cover is a defect of the
      draft, never a restriction or a cost.
      - On [TR] 6.175's route, the pushed entry lends one place, and the table puts a borrow cell
        at a place no entry lends strictly above the outermost lend, so one of the two reborrowed
        cells always fails (`loadGuardFails2`). That the defect is the single-place entry is [read],
        not a theorem.
      - Item 1b's block is the designed fix (§1.6). It is not built (§9.6).

**N3. `:2465–2474`** (finding b). Replace the "Item 1a′." bullet with:

    - **Item 1a′.**
      - `WithloadUPairGapNilE1` is proved (`withloadUPairGapNilE1`). At the gate's world at the
        empty stack, after (E1), no instance in scope is below `⊓Δ`, and every own push fails the
        guard at the reborrowed pair. The view is not shown to arise (no `ArisesVI` witness): no
        transition of the arising set makes an `Imm` value arise at the empty stack other than a
        run's answer. So it is not evidence of a defect on a borrow-only program, and not a trigger
        to revisit (E1), until an `ArisesVI` witness exists.
      - `WithloadPairGapNilInstE1` is refuted (`not_withloadPairGapNilInstE1`). At the thunked
        type, the answer's `U` clause moves the push below the reborrowed cells.
      - `pairNilOldGuardHolds` says only that the table at `[]` holds of every resource. It does
        not show that the row went through before (E1).
      - `SliceUGapNilE1` and `SliceGapNilInstE1` were not stated.

**N4. `:2532–2535`** (finding d1). Replace "1a is real, so 1b's trigger is met." with "1a is real on
[TR] 6.175's route at `withloadU`'s type (§9.1), so 1b's trigger is met.", and "1b is the designed fix
for the defect of §9.1 and §9.3 (§10.2)." with "1b is the designed fix for the defect of §9.1."

**N5. `:2615–2616`** (finding a). After "it gave no persistent value a way across a push." add "It
is not evidence of a defect on a borrow-only program."

**N6. `:2623`, `:2651–2663`** (findings a, b). Rename the heading to "### 10.2 The persistence box,
with (E1) kept", and replace the paragraph "(E1) is kept, and the `!` clause is fixed." and its list
with:

    **(E1) is kept, and the `!` clause gained the box. The clause is not fixed.** The reasons, and
    what stays open:
    - What `gdBangJ` shows is about the clause before (E1): it gave no persistent value a way across
      a push. It is at `gd`, not shown to arise, with a closure that is no Core value, so it is not
      evidence of a defect on a borrow-only program.
    - The box carries a persistent thunk across instantiations and own pushes at the empty resource
      under reserved names (`NsVar`) only (`persistentPushN`, `monoOwnGMAtBoxN`). Two pushes are
      outside it: the push `gdBangJ` fails at (`gdY`, named `2`), and the `∀` clause's own push,
      named by the type's binder (`OwnPushI`, `e.x = x`). The second is correction (i)'s case. Both
      wait on `VRLMStackRename` (stated, not derived) and a reduction not built (§10.4).
    - No `binder0` clause makes a reserved-name push, so the carrying proved may have no consumer
      yet.
    - §3.3's route to the reading transports reads (E1) (§3.1). Without (E1), they were not derived
      (`R1MONO.md` §8).
    - Which borrow-only programs (E1) affects is unchecked: the user's example was not built.
      `withloadUPairGapNilE1` is at a view not shown to arise, so it is not evidence that (E1)
      affects `withload` of a pair at the empty stack.
    - Item 1b's block is designed to serve the pair at every stack [unchecked: 1b is not built].
      (E1) is revisited at the empty stack only if 1b's gate fails and an `ArisesVI` witness for the
      empty-stack view exists.

**N7. `:2665–2671`** (finding c). Replace "The box against DESIGN §12.2 (d)." and its list with:

    **The box against DESIGN §12.2 (d).** The box makes the `!` clause reach stacks other than its
    own by something other than `FutQ`: instantiations, and own pushes at the empty resource under
    reserved names. `binder0`'s `U` clause makes the instantiations. Its `∀` clause's push is at the
    type it reads, named by its binder, while the box's pushes are under reserved names at any thunk
    type. So the pushes are a new reach of the `!` clause, beyond `FutQ` and beyond the type it
    reads.
    - The box was made to answer correction (i). Statement 0 does not yet hold, with the box or
      without it, so (d) has not occurred.
    - If statement 0 comes to hold only with the box, DESIGN §12.2's reading of (d) applies to it.
      (d) is reported against both of §12.2's readings.

**N8. `:2689–2700`** (finding d2). Replace "Push-stability, judged against it." and "What it owes" with:

    - **Push-stability, judged against it.**
      - The callback `Λ. λb. …` is closed [read]. So its `∀I` row can be read at the empty context,
        where it holds at every index. `reconCb_allI` is `allIRowMUFree0 []` under a
        program-specific name.
      - The typing at the probe's rule set is not built. So it is [unchecked] that the derivation
        applies the row at a context with no live `U` slot.
      - `reconB′`'s handlers are installed around the lends, at the empty stack, where every hiding
        is invisible [read].
    - **What it owes** beyond that row is [unchecked]. Its lend is `lendCell`, whose term is
      `withborUE dFlag`; only the unwinding rules type that term (`Row.Unwind`,
      `Core/EffBorrow.lean`), and `wait` is resumed, so they do not admit it. Which typing rule and
      which callback row apply is open: `CallbackExtImmM` at the `.arr` shape, or the thunked
      `CallbackExtImmMF`, stated and not proved, a borrow-level obligation and not tier 2. The
      suspension inside the lend (statements 1–3, tier 2) is among what it owes: the callback
      performs `wait` while its lend is open, the scheduler resumes it, and `timeout`'s cancel ends
      the lend's frame by the finaliser.

### 1.4 The notes that point at these edits

- `CHECKPOINT.md:73–76`: replace "This file is corrected below. README, DESIGN §15.10 and `NEXT.md`
  §9–§10 still carry the wording each finding names, and are not yet corrected. Until they are, read
  this file over them." with "This file is corrected below, and README, DESIGN §15.10 and `NEXT.md`
  §9–§10 carry the same corrections (`GROUND.md` §1)."
- `CHECKPOINT.md:595–596`: replace "corrected here and not yet in README, DESIGN §15.10 or `NEXT.md`
  §9–§10." with "corrected here and in README, DESIGN §15.10 and `NEXT.md` §9–§10."
- `research/effects/src/synthesis.md:1705`: replace "recorded and corrected in CHECKPOINT's warning,
  not yet corrected in README, DESIGN §15.10 or `NEXT.md`" with "recorded and corrected in
  CHECKPOINT's warning, and since in README, DESIGN §15.10 and `NEXT.md` §9–§10".

---

## 2. Part (1): the grounding ledger

### 2.1 Conventions

- **The two sides.** The draft is the one draft relation `vRLM`/`cRLM`/`effRetM`/`gRLM`/`SemSM`
  at `.binder0` (`R1.lean:150–262`). Core is `vCE`/`cC`/`effRet`/`gDenC`/`SemC`
  (`Core/Relation.lean:119–231`).
- **The comparison point.** Clauses are compared at the empty stack (`σ = []`, `αs = []`, where
  `extS δ [] [] = δ` by definition) and, separately, at a non-empty stack. A clause is compared
  *given its components*: "same clause" means the two clauses have one shape once their
  sub-relations are identified.
- **Direction.** For predicates on one domain, "draft ⊆ Core" means the draft's implies Core's: the
  draft relates fewer. "Core ⊆ draft" is the converse. "Equal" means both. "Incomparable" means the
  clauses add obligations on both sides. "Not stated" means no statement relates them.
- **No overclaim.** `LEDGER.md` writes "agrees" or a direction only where a named theorem proves it.
  Every planned theorem below is marked *planned*, and stays so until it is proved. A relationship
  argued without a theorem is marked [read] or [unchecked].

### 2.2 Rows: the relation's clauses

All draft lines are `R1.lean`; all Core lines are `Core/Relation.lean` unless named.

| # | draft | Core | at `σ = []` | at `σ ≠ []` | theorem | what a disagreement means for programs |
|---|---|---|---|---|---|---|
| C1 | `vRLM` `U` (`:152`) | `vCE` `U` (`:127`) | Core ⊆ draft, given bodies: the draft reads the body only at extensions that keep the tags (`KeepsT`, `BinderJ.lean:49`); the only instantiation of `[]` is the identity (`instAt_nil_eq`, `GapPos.lean:87`); the guard is trivial | incomparable: instantiations at the stack's cut, views handed back, `guardPV` | `VRLMThunkNil`, `CoreSubWNil` (planned) | at `[]` every Core thunk with a first-order body is a draft thunk; at a stack only thunks with a Core derivation are shown (§3.2) |
| C2 | `vRLM` `⊗`, `⊕`, `[@a]`, `Ref`, `[L]` (`:159`, `:161`, `:166`, `:168`, `:183`) | `:121`, `:124`, `:131`, `:132`, `:149` | same clause | same clause, leaves at `extS δ σ αs` | inside `VRLMFlat` (planned) | none |
| C3 | `vRLM` `!` (`:164`) | `:130` | draft ⊆ Core given the payload (`PBox` added at a thunk payload); equal at a non-thunk payload | the same | `VRLMBangNil` (planned) | a persistent thunk must hold at every box world (divergence D4) |
| C4 | `vRLM` `Mut`, `Imm` (`:170`, `:174`) | `:137`, `:134` | equal: `CohS` and `RetainedPay` hold at `[]` | draft ⊆ Core: Core's leaf, plus `CohS` and `RetainedPay` | `VRLMNilTy`, `VRLMFOArg` (planned) | a consumer at a pushed stack must establish `CohS` and `RetainedPay` for the arguments it hands over (D7) |
| C5 | `vRLM` type variable (`:178`), environment `WEnt` (`:72`) | `:143`, `TEnt` (`:72`) | candidates; W's drop the mode and the list | the same | `EnvCore` (`R1.lean:1363`), used by `vRLMDataE` | none at data |
| C6 | `vRLM` `μ` (`:179`) | `:144` | equal at data (`vRLMDataE`, `R1Stmt0.lean:48`); at flat types, planned; with a thunk inside, not stated | the same | `VRLMFlat` (planned) | W reads a thunk inside `μ` with its own `U`; after (E1) the adjacency closure is a draft value (`muAdjVRLME1`) |
| C7 | `vRLM` default: `1`, `0`, `Unk`, `int`, `opq` (`:186`) | `:120`, `:123`, `:140–142` | equal | equal at `extS` | by definition | none |
| C8 | `cRLM` `F` (`:192`) | `cC` `F` (`:155`) | same clause (`wpTS`); equal at a flat answer | same clause | `CRLMRetNil` (planned; `nilSoundRetM` is one direction at data) | none |
| C9 | `cRLM` `F_Σ` (`:193`) | `cC` `F_Σ` (`:165`) | equal at a flat answer (`bodyS_nil_iff`, `GhostEnd/Stacked.lean:476`) | GhostEnd's piece (a stop ghost-ends entries): no Core counterpart | `CRLMRetNil` (planned) | effectful callbacks at a pushed stack read the piece (out of this suite, §3.6) |
| C10 | `cRLM` `⊸` (`:201`) | `cC` `⊸` (`:156`) | same clause; `guardPV` trivial | same clause plus `guardPV` at the stack | `CRLMArrNil`, `GuardPVNil` (planned) | a call at a stack needs the table and views of the composite (D9) |
| C11 | `cRLM` `&`, `⊤`, `ν` (`:206`, `:209`, `:220`) | `:158`, `:160`, `:163` | same clause; `ν` is Core's at `extS` | the same | by definition | none |
| C12 | `cRLM` `∀` (`:210`) | `cC` `∀` (`:161`) | incomparable: the first conjunct reads only instances in scope ((E1), `InScope`, `:95`), and the own-lend conjunct (`OwnPushM`, `:101`) has no Core counterpart; at the top level the first conjunct reads nothing (`inScope_top_none`, `NxFloor.lean:40`) | the same | `CRLMAllNil`, `CRLMAllTop` (planned) | every borrow callback is checked at its own push: producer side shown for first-order callbacks (G5 with the rows); consumer side is the gate (§3.3) (D1, D2) |
| C13 | `effRetM` (`:223`) | `effRet` (`:176`) | same clause | same clause | by definition | none |
| C14 | `gSepRLM`, `gRLM` (`:231`, `:240`) | `gSepC`, `gDenC` (`:218`, `:224`) | same clause | same clause | by definition | none |
| C15 | `SemSM` (`:246`) | `SemC` (`:228`), `SemJ` (`Fundamental.lean:429`) | incomparable as definitions: `SemSM` adds `BindersLow`, `Scoped`, `SubDom` and the index; at `[]` the index holds | the same | `SemSMNilOfSemSM`, `CoreToSemSM` (planned) | Core's judgements at first-order types are the draft's at every index |

### 2.3 Rows: world, index, guard

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| W1 | `Stk`, `LEnt`, `LStack` (`World.lean:53`; `GhostEnd/Stacked.lean:99`, `:107`) | none: Core is `σ = []` | draft-only (§2.7) | — | — |
| W2 | `guardPV` (`Binder.lean:164`), `TabAtS` (`Stacked.lean:290`), `PlaceViewsL` (`Binder.lean:144`) | none in Core's relation; meant as `TW`'s run invariant (statement 1, `tabAt_of_TW`, not in Lean) | trivial at `[]` | `GuardPVNil` (planned; from `pvlNil`, `BinderPV.lean:358`) | at a stack the guard restricts every call (D9) |
| W3 | `CohS` (`Binder.lean:178`) | `CohE` (`Relation.lean:57`) | different objects: a view tied to its lending entry, an `imm` cell tied to a record; `CohS` vacuous at `[]` | inside `VRLMNilTy` (planned) | D7 |
| W4 | `OwnPushM`, `OwnOKI` (`R1.lean:101`, `Binder.lean:194`, `:200`) | Core's `∀` instance (`Relation.lean:161`); 6.64/6.65's lend start (`TW.immFrame`, `TW.mutFold`, `World.lean:115`, `:135`) | not stated: the own push reads an instance as a lend | — | the single-place entry (D2) and `placeFree` (D3) |
| W5 | `Inst`, `InstAt`, `RelendJ` (`Binder.lean:314`, `:346`; `BinderJ.lean:53`) | Core's `U` quantifier over `Ext` (`Relation.lean:127`) | at `[]` `RelendJ` is Core's `U` with `KeepsT` added | `RelendJNil` (planned) | D8 |
| W6 | `KeepsT` (`BinderJ.lean:49`) | `Keeps` (`FrameRecords.lean:156`, `Ext`'s first conjunct, `:172`) | draft ⊆ Core: a record kept with its tag is kept | `KeepsTKeeps` (planned, one line) | D8 |
| W7 | `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `OuterBelowTop`, `cutOf` (`Binder.lean:250`, `:280`, `:285`, `:265`, `:242`, `:227`) | [TR] 6.64/6.65 H4's fresh lifetime; nearest Core object `TW.reb`'s `StratumLe` (`World.lean:92`, `:122`) | draft-only bookkeeping (§2.7) | — | — |
| W8 | `PBox`, `BoxStep` (`R1.lean:121`, `:133`) | none: Core's `!` is `ρ = ∅ ∧ vC true A` | draft-only (§2.7) | — | D4, D5 |
| W9 | `StackJM`, `BindersLow`, `Scoped`, `SubDom` (`R1.lean:108`; `Sem.lean:66`, `:74`, `:78`) | `Scoped` ↔ `VScoped`; `Δ.Models` | `Scoped` is `VScoped` at the judgement [read]; the others draft-only | — | a judgement binding a reserved name (`NsVar`) is outside `SemSM` (vacuous there) |
| W10 | `vwEW`, `vwSW`, `vwSL` (`Binder.lean:121`, `:125`, `:159`) over GhostEnd's `vwE` (`Stacked.lean:122`) | `ptoImmS`, `ptoMutS` (`Relation.lean:51`, `:43`) | the views read an `imm` payload at `vC true`; Core's `Imm` leaf at `vC false` | — | at a payload holding a thunk the views ask more (D11) |

### 2.4 Rows: arising against the typed world

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| A1 | `ArisesI` (`Binder.lean:582`) | `TW` (`World.lean:110`), `Tagged` (`:171`) | the arising set's worlds are tagged `TW` worlds (draft ⊆ Core, worlds); at `[]` every tagged `TW` world arises (Core ⊆ draft); so at `[]` the two coincide as world sets | `ArisesITW`, `ArisesINilOfTW` (planned) | a refutation at `[]` needs nothing beyond Core's arising |
| A2 | `ArisesI.lendImm`, `LendImmI` (`Arising.lean:106`; `Binder.lean:576`) | `TW.immFrame` (`World.lean:115`) | `LendImm` carries `TW.immFrame`'s premises, the push, and H4's freshness (`LendFresh`, `α < ⊤`) | inside `ArisesITW` | — |
| A3 | `ArisesI.lendMut`, `LendMutI` (`Arising.lean:88`; `Binder.lean:571`) | `TW.mutFold` (`World.lean:135`) | the same | inside `ArisesITW` | — |
| A4 | `RunEnd` (`Arising.lean:73`) | `wpTS`'s run conjuncts (`World.lean:186`) | `RunEnd` transcribes them at a fixed configuration [read] | `RunEndOfWpTS` (planned, optional) | — |
| A5 | (none) | `TW.immEnd`, `TW.mutUnfold` (`World.lean:151`, `:140`) | not stated: `ArisesI` has no lend-end transition; lends end only inside runs | — | configurations after a lend ends are reached only through `run` |
| A6 | (none) | `TW.reb`, `rebDeep`, `rebEnd` (`World.lean:122`, `:128`, `:157`); `wpG_reborrow` (`Reborrow.lean:232`) | not stated: `ArisesI` has no reborrow transition; the gate's witness uses `TW.reb` inside a world; `LendRebI` is designed (`NEXT.md` §1.6), not built; `RebFrameR` (`Statement2.lean`) is 6.150 at a resuming table, stated | — | a configuration inside `withload`'s callback with its push on the stack is not in `ArisesI`; refutations there cannot pass DESIGN §11 |
| A7 | `ArisesVI` (`Binder.lean:598`) | none: Core quantifies over all values in `TW` worlds | draft-only (refutation check) | — | at `[]` no `Imm` value arises except a run's answer, so a refutation at `[]` of an open judgement with a borrow-typed context cannot pass DESIGN §11 |

### 2.5 Rows: judgement, typing, statement 0, adequacy

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| J1 | `ProbeRules` (`Rules.lean:31`) | `CDerives` (`Fundamental.lean:60`); Targets' `CDerivesNU` (`Targets/Base/Typing.lean:82`) | `CDerivesNU` ⊆ `ProbeRules` (through `ExtendsNU`'s `Tier1SubNU`); `ProbeRules` ⊄ `CDerives` (the spanning rules); judgements with resuming `unr` operations are not in `ProbeRules` (multi-shot ignored) | `ProbeRulesOfNU` (planned) | every borrow-only Core program is a `ProbeRules` program |
| J2 | statement 0 (`Statement0M`, `R1.lean:1444`; `statement0MBesideMono0`, `R1Stmt0.lean:447`) and the other draft rows | `fundamentalC` (`Fundamental.lean:434`) | the draft has rows at `force`, `thunkF`, `thunkV`, `!` (with `PersistentBoxed`), `∀I` (contexts reaching no `U`), `roll`, `unroll`; Core proves all 89 constructors; no theorem relates the two | `DraftFL` and `DraftFLNil` (stated, the floor); `CoreToSemSM` (planned: the floor at first-order judgements) | §2.6 lists the rows |
| J3 | `semTyping`, `GenSelfAccepted`, `ReconAccepted` (`Programs.lean:38`, `:42`, `:46`) | Targets' `AcceptedAt` (`Targets/I/Programs.lean:259`); `adequacyD` | `semTyping` reads `SemS` (`Sem.lean:102`), statement 0's relation `vRL`, not the current draft `SemSM`: stale [read] | — | statement 5's acceptance is not stated at `vRLM` |
| J4 | (no adequacy theorem) | `adequacyD` (`Demonic.lean:312`), `adequacyD_obs` (`EffPrograms.lean:41`), `theorem32D` (`Demonic.lean:292`) | draft acceptance at `[]` at `F 1` gives Core's adequacy | `AdequacyNilM` (planned) | the draft's floor inherits safety and termination at `[]` |
| J5 | `NilSoundRet`, `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` (`Statement0.lean:95`, `:154`, `:161`, `:167`, `:173`, at `vRL`); `NilSoundRetM` (`R1.lean:1383`) | OQ-58 (a) | at `vRLM` only `NilSoundRetM` is stated and proved; the others are at statement 0's relation, not attempted | `CRLMRetNil`, `CoreSubWNil` restate the usable part at `vRLM` (planned) | OQ-58 at `vRLM` is answered only at first-order types |

### 2.6 The rows against `fundamentalC`

`LEDGER.md` gives one line per `CDerives` constructor (89, `Fundamental.lean:60–372`), with the
compatibility lemma `fundamentalC` applies (`:437–560`) and the draft row. The builder takes the
constructor list and lemma names from those lines. Their file and line come from a grep of
`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/EffBorrow.lean`, `Core/Slices.lean`,
`Core/FoldImm.lean`, `Core/EffRules.lean` and `Core/Nu.lean`. Known draft rows at `.binder0`:

| Core rule (lemma) | draft row | status at `3e84262` |
|---|---|---|
| `force` (`force_compatC`) | `ForceRowM` | proved (`forceRowM`, `R1Stmt0.lean:367`) |
| `thunkF`, `thunkV` (`thunkF_compatC`, `thunkV_compatC`) | `ThunkFRowM`, `ThunkVRowM` | proved (`statement0UFullM`, `R1Box.lean:579`) |
| `bangThunkF`, `bangThunkV` | `BangThunkFRowM`, `BangThunkVRowM` | proved with `PersistentBoxed` (`statement0UFullM`) |
| `allI` (`allI_compatC`) | `AllIRowMAt` | proved at contexts reaching no `U` (`allIRowMUFree0`, `NxAllI.lean:209`); open at a live `U` slot |
| `roll`, `unroll` | `RollRowM`, `UnrollRowM` | proved (`rollRowM`, `unrollRowM`, `NxUnroll.lean`) |
| `ret`, `ofRet` | the identity (`jdgCty`) | trivial, not stated |
| `withbor1`/`2`/`3` (`withbor*_compatX`) | consumer facts `CallbackExt*M` (`.arr` shape), `CallbackExt*MF` (thunked) | `.arr`: proved (`callbackExt*M_own`); thunked: stated (`Nx.lean:466`, `:483`); the rows themselves not stated |
| `withbor*U`, `withloadU`, `sliceBorrow*U` | `SpanW1Row`, `SpanW2Row`, `SpanLoadRow` (at `SemS`) | not attempted, at statement 0's relation |
| `effThen` | `ThenRow` (at `SemS`) | not attempted |
| every other rule | none | not stated; at first-order judgements `CoreToSemSM` covers every rule at once |

### 2.7 Draft-only definitions

Each exists for suspension. Some are read at every borrow callback, because `binder0` reads each
`∀` instance as a lend (the own push). Those reach borrow-only programs, and the divergence
register (§2.8) tracks them.

| definition | why it exists |
|---|---|
| `Stk`, `LEnt`, `LStack`, `StackOK`, `hideS` | the lends open across a stop, innermost first, with the rows whose stops cross each; read at every own push |
| `TabAtS`, `guardPV` | the only borrow cell at an internal lifetime is at a lent place, so a resume can re-lend exactly those; read at every own push |
| `PlaceViewsL`, `DeepAt`, `ExAt`, `innerAt`, `vwEW`, `vwSW`, `vwSL` | a borrow cell at a lent place is the lend's view, handed back at the thaw (the freeze binder's location half) |
| `CohS` | the 6.65 analog of `CohE`: a view at a lent place is the binder's; read at every own push |
| `OwnOKI`, `OwnPushI`, `OwnPushM`, `ViewAt` | the callback's own lend: an instance read as the lend it names, so a stop can see it; read at every borrow callback |
| `InScope` ((E1)) | so the `∀` clause's reading transports pass the effect clause's re-lend (`NEXT.md` §3.1); read at every `∀E` |
| `Inst`, `InstAt`, `RelendJ`, `KeepsS`, `RecUpTo`, `KeepsT` | a resume re-lends every internal lifetime as one order-preserving instantiation (the freeze binder's lifetime half) |
| `cutOf`, `Internal`, `InternalVar`, `OuterBelowTop`, `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `BoundInside` | the instantiation's bookkeeping: what it moves and what it must fix |
| `PayExt`, `RetainedPay` | a retained cell's payload reads only lifetimes the instantiation fixes (`mut_not_natural`'s mechanism kept out); read at every stack |
| `PBox`, `BoxStep` | a persistent value carried to every world a resume or a push can carry it to |
| `StackJ`, `StackJM`, `BindersLow`, `SubDom`, `CtxFresh`, `OwnHyg` | the hygiene between the stack's names and the judgement's binders |
| `bodyS`, `OpenS`, `openFS`, `stopS`, `ghostS`, `dropS` (GhostEnd) | the piece: a stop ghost-ends the lends it crosses and owes their re-lend |
| `Fut`, `FutStep`, `FutQ`, `FutI`, `FutAvoids`, `OrdW`, `RelendU`, `RelendUI` | the other placements' futures (`cbpv`, `binder`); `binder0` reads none |
| `ArisesVI`, `ArisesCtxI`, `Cfg` | the arising check of a refutation (DESIGN §11) |
| `Placement` | the candidates for where the future-world quantifier sits (OQ-8) |

### 2.8 The divergence register

Each draft condition that is stricter or weaker than Core where it can reach a borrow-only program
is listed with the programs that probe it (§3).

| # | draft condition | what it can reject or leave unproved | probes |
|---|---|---|---|
| D1 | (E1): `∀`'s first conjunct reads instances in scope only | `∀E` at an instance not in scope; a top-level polymorphic value is checked by its own pushes alone | `cInst` (`∀E` at `'a`, in scope); the folds (`g [] b` at the callback's own lifetime, in scope at the push); every callback |
| D2 | the own push lends one place (`OwnPushM`) | a consumer handing its callback several cells at one lifetime | `pairLoad`, `pairLoadU`, `sliceLoad` (seeds); `readFields` (one cell, the positive control) |
| D3 | `OwnOKI.placeFree`: the callback holds no cell at the lent place, at any depth | a callback holding a copy of the view whose witness owns the reborrowed places | `loadKeepsView` (optional seed) |
| D4 | `PBox`: a persistent thunk holds at every box world | a persistent value Core accepts that misbehaves at a phantom push | `cBang`, the folds' algebras, `arrProg`'s `tab10V` |
| D5 | the box carries only reserved-name pushes | a persistent context value across the `∀I` row's binder-named push | the folds' borrower (the user's case) |
| D6 | the `∀I` row at a live `U` slot is not derived | a callback capturing a closure | `withborF2` (`swapBothB`, `readFamily`), `withborS` (`blockSwap`) |
| D7 | `CohS`, `RetainedPay` at a pushed stack | arguments a consumer must hand over with these; `EntryPayLeaves` at a bound `Mut` read-out | `mutFields` (`withswap`), `counterProg` (`callMut`, a closure payload) |
| D8 | `KeepsT` in the `U` clause | a thunk forced at a list that keeps a relevant record without its tag [unchecked: runs keep tags] | `cRecBorrow` (forces a thunk after the lend) |
| D9 | `guardPV` at `⊸` and `∀` | a call inside a callback whose composite fails the table | `readFamily` (`readBoth` on a copied family at the inner push) |
| D10 | W's own `μ`, `[L]`, type variables | a thunk inside `μ` read by W's `U` | `bagProg`, the folds (lists, trees) |
| D11 | the views read an `imm` payload at `vC true` | a lend whose payload holds a thunk | `cRecBorrow` (`withbor` at `methodsTy`) |

### 2.9 `GroundLedger.lean`: the theorems

`GroundLedger.lean` imports `ProbeD1.NxRecon` and `Core.Demonic`. Each item is a `def … : Prop` with
a theorem of the lowercase name. G1–G5, with their empty-stack forms G3, G4′ and G5′, are the
grounding core. G6 states the empty-stack judgement and the floor. G7–G11 are unfoldings, arising,
typing and adequacy.

**The type classes.** `FlatB` mirrors Core's `VTy.DataB` (`Targets/Base/Machine.lean:28`), with
`Unk`, `opq`, `[@a]`, `Ref`, non-thunk `!` and `[L]` added.

```lean
/-- Types at which the draft relation is Core's at every stack, `k` variables bound. -/
inductive FlatB : Nat → VTy → Prop
  | unit (k : Nat) : FlatB k .unit
  | zero (k : Nat) : FlatB k .zero
  | unk (k : Nat) : FlatB k .unk
  | int (k w) : FlatB k (.int w)
  | opq (k o) : FlatB k (.opq o)
  | tvar {k n : Nat} : n < k → FlatB k (.tvar n)
  | tensor {k : Nat} {A B : VTy} : FlatB k A → FlatB k B → FlatB k (.tensor A B)
  | sum {k : Nat} {A B : VTy} : FlatB k A → FlatB k B → FlatB k (.sum A B)
  | box {k : Nat} {a : Lifetime.Life} {A : VTy} : FlatB k A → FlatB k (.box a A)
  | ref {k : Nat} {A : VTy} : FlatB k A → FlatB k (.ref A)
  | bang {k : Nat} {A : VTy} : (∀ C, A ≠ .thunk C) → FlatB k A → FlatB k (.bang A)
  | fam {k : Nat} {L : VTy} : FlatB k L → FlatB k (.fam L)
  | mu {k : Nat} {A : VTy} : FlatB (k + 1) A → FlatB k (.mu A)

def FlatTy (A : VTy) : Prop := FlatB 0 A

/-- First-order arguments: the draft relation is contained in Core's at every stack. -/
inductive FOArg : VTy → Prop
  | flat {A : VTy} : FlatTy A → FOArg A
  | mut (a : Lifetime.Life) (T : VTy) : FOArg (.mut a T)
  | imm (a : Lifetime.Life) (T : VTy) : FOArg (.imm a T)
  | tensor {A B : VTy} : FOArg A → FOArg B → FOArg (.tensor A B)
  | sum {A B : VTy} : FOArg A → FOArg B → FOArg (.sum A B)
  | box {a : Lifetime.Life} {A : VTy} : FOArg A → FOArg (.box a A)
  | ref {A : VTy} : FOArg A → FOArg (.ref A)
  | fam {L : VTy} : FOArg L → FOArg (.fam L)

/-- First-order computation types with no lifetime `∀` and no row. -/
inductive FOComp : CTy → Prop
  | ret {B : VTy} : FlatTy B → FOComp (.ret B)
  | arr {A : VTy} {C : CTy} : FOArg A → FOComp C → FOComp (.arr A C)
  | amp {C D : CTy} : FOComp C → FOComp D → FOComp (.amp C D)
  | top : FOComp .top
  | nu (C : CTy) : FOComp (.nu C)

def CtxFO (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → FOArg s.ty
```

**G1–G5: the draft is Core at first-order judgements, at every stack.**

```lean
/-- G1. At a flat type the draft relation is Core's, at every stack (`VRLMData` widened). -/
def VRLMFlat : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), FlatTy A →
    ∀ (ls : List SRec) (v : Val),
      vRLM (ℍ := ℍ) p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v

/-- G2. At a first-order argument type the draft relation is contained in Core's. -/
def VRLMFOArg : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), FOArg A →
    ∀ (ls : List SRec) (v : Val) (ρ : WRes),
      vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ

/-- G4. At a first-order computation type, Core's relation is contained in the draft's. -/
def CoreSubWComp : Prop :=
  ∀ (C : CTy), FOComp C → ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (e : Expr) (ρ : WRes),
    cC C ls (extS δ σ αs) e ρ → cRLM (ℍ := ℍ) .binder0 σ δ C αs ls e ρ

/-- G5. **The floor at first-order judgements**: Core's derivation gives the draft's semantic
judgement at every index. -/
def CoreToSemSM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CtxFO Γ → FOComp (jdgCty j) →
    CDerives Δ Γ e j → SemSM (ℍ := ℍ) .binder0 Δ Γ e j
```

Routes:
- **G1** is `vRLM_dataE`'s induction (`R1Stmt0.lean:48`) with the `EnvCore` environment, widened
  by the cases `Unk`, `opq`, `[@a]`, `Ref`, non-thunk `!` (where `PBox` is `True`) and `[L]`. Each
  added case is one clause shape on each side.
- **G2** reads off the first conjunct at `Mut` and `Imm`, G1 at flat types, and `sepRange_mono'`
  (`Core/SepRange.lean:46`) at `[L]`.
- **G4** is an induction on `FOComp`. At `binder0`, `⊸` has `ExtQ false` and `FutQI false`, which
  force the list and the stack, and `guardPV` only adds hypotheses. `F` is G1 under `wpTS_mono`,
  and `ν` is Core's clause by definition.
- **G5**: from the index, `gRLM` gives `gDenC` at `extS δ σ αs` slot by slot (G2), and `Δ.Models`
  holds there. `fundamentalC` gives `cC (jdgCty j)` there, and G4 gives `cRLM`. Cheap: no
  instantiation is read.

**G3, G4′, G5′: the same at the empty stack, where the leaves are equal and Core's thunks are the
draft's.**

```lean
/-- Types at which the draft relation at the empty stack is Core's. -/
inductive NilTy : VTy → Prop
  | flat {A : VTy} : FlatTy A → NilTy A
  | mut (a : Lifetime.Life) (T : VTy) : NilTy (.mut a T)
  | imm (a : Lifetime.Life) (T : VTy) : NilTy (.imm a T)
  | tensor {A B : VTy} : NilTy A → NilTy B → NilTy (.tensor A B)
  | sum {A B : VTy} : NilTy A → NilTy B → NilTy (.sum A B)
  | box {a : Lifetime.Life} {A : VTy} : NilTy A → NilTy (.box a A)
  | ref {A : VTy} : NilTy A → NilTy (.ref A)
  | fam {L : VTy} : NilTy L → NilTy (.fam L)

mutual
/-- Value types at which Core's relation at the empty stack is contained in the draft's. -/
inductive NilVal : VTy → Prop
  | ty {A : VTy} : NilTy A → NilVal A
  | thunk {C : CTy} : NilComp C → NilVal (.thunk C)
  | tensor {A B : VTy} : NilVal A → NilVal B → NilVal (.tensor A B)
/-- Computation types at which Core's relation at the empty stack is contained in the draft's. -/
inductive NilComp : CTy → Prop
  | ret {B : VTy} : NilVal B → NilComp (.ret B)
  | arr {A : VTy} {C : CTy} : NilTy A → NilComp C → NilComp (.arr A C)
  | amp {C D : CTy} : NilComp C → NilComp D → NilComp (.amp C D)
  | top : NilComp .top
  | nu (C : CTy) : NilComp (.nu C)
end

def CtxNil (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → NilTy s.ty

/-- G3. -/
def VRLMNilTy : Prop :=
  ∀ (p : Placement) (δ : LSub) (A : VTy), NilTy A → ∀ (ls : List SRec) (v : Val),
    vRLM (ℍ := ℍ) p none [] δ A [] ls v = vC true A ls δ v

/-- G4′. Core inside the draft at the empty stack, thunks included. -/
def CoreSubWNil : Prop :=
  (∀ (B : VTy), NilVal B → ∀ (δ : LSub) (ls : List SRec) (v : Val) (ρ : WRes),
      vC true B ls δ v ρ → vRLM (ℍ := ℍ) .binder0 none [] δ B [] ls v ρ) ∧
  ∀ (C : CTy), NilComp C → ∀ (δ : LSub) (ls : List SRec) (e : Expr) (ρ : WRes),
      cC C ls δ e ρ → cRLM (ℍ := ℍ) .binder0 [] δ C [] ls e ρ

/-- G5′. The floor at the empty stack at first-order judgements, constants included. -/
def CoreToSemSMNil : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CtxNil Γ → NilComp (jdgCty j) →
    CDerives Δ Γ e j → SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j
```

G4′ at a thunk is G7's `VRLMThunkNil`, with Core's `U` clause at every `Ext` and the body by
induction. Because the empty stack has only the identity instantiation, this holds for semantic
values, not only derived ones. That is what puts `alloc`, `free`, `copy` and `forget` at first-order
payloads in the draft's relation at `[]` (§3.4).

**G6: the empty-stack judgement and the floor's statement.**

```lean
/-- The draft's semantic judgement at the empty stack. At `[]` the index hypotheses `StackOK`,
`OuterBelowTop`, `StackJM`, `RecsOutside`, `SubOutside`, `TabAtS` and `PlaceViewsL` hold of every
index, and `extS δ [] [] = δ`. -/
def SemSMNil (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (ls : List SRec) (γ : List Val) (ρ : WRes),
    SubDom δ Δ → Δ.Models δ → gRLM (ℍ := ℍ) p [] δ [] ls Γ γ ρ →
      cRLM (ℍ := ℍ) p [] δ (jdgCty j) [] ls (substAll γ e) ρ

def SemSMNilOfSemSM : Prop :=
  ∀ (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    SemSM (ℍ := ℍ) p Δ Γ e j → SemSMNil (ℍ := ℍ) p Δ Γ e j

/-- **The floor**: the draft's fundamental lemma for Core's rules. Stated, not claimed. -/
def DraftFL : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    CDerives Δ Γ e j → SemSM (ℍ := ℍ) .binder0 Δ Γ e j

/-- **The floor's own statement at the empty stack.** Stated, not claimed. -/
def DraftFLNil : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    CDerives Δ Γ e j → SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j
```

`DraftFLNil` has no induction of its own: at `[]` a callback's own push reads its body at `[en]`,
so an induction proving it needs `DraftFL`'s hypothesis at every index. G5 is `DraftFL`'s
first-order part.

**G7: the empty-stack unfoldings.**

```lean
def GuardPVNil : Prop :=
  ∀ (s : LSub) (ls : List SRec) (P : WProp) (ρ : WRes), guardPV s [] [] ls P ρ ↔ P ρ

def RelendJNil : Prop :=
  ∀ (δ : LSub) (P : LSub → List Life → List SRec → WProp) (ls : List SRec) (ρ : WRes),
    RelendJ δ [] P [] ls ρ ↔ ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ → P δ [] ls' ρ

def VRLMThunkNil : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (f : Val) (ρ : WRes),
    vRLM (ℍ := ℍ) .binder0 none [] δ (.thunk C) [] ls f ρ ↔
      ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ →
        cRLM (ℍ := ℍ) .binder0 [] δ C [] ls' (forceE C (.val f)) ρ

def CRLMArrNil : Prop :=
  ∀ (δ : LSub) (A : VTy) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] δ (.arr A C) [] ls e ρ ↔
      ∀ v, (vRLM (ℍ := ℍ) .binder0 none [] δ A [] ls v ─⋆
        cRLM (ℍ := ℍ) .binder0 [] δ C [] ls (.app e (.val v))) ρ

def CRLMAllNil : Prop :=
  ∀ (δ : LSub) (x : LifeVar) (c : Lifetime.Life) (C : CTy) (ls : List SRec) (e : Expr)
    (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] δ (.all x c C) [] ls e ρ ↔
      (∀ α, (⌜LtLife δ c α ∧ InScope δ α⌝ ─⋆
          cRLM (ℍ := ℍ) .binder0 [] (δ.extend x α) C [] ls (.app e (.val .unit))) ρ) ∧
      ∀ (en : LEnt) (α : Life), OwnPushM δ (.all x c C) ρ ([], []) en α →
        RecsOutside [α] ls → SubFresh δ α →
        guardPV (extS (δ.extend x α) [en] [α]) [en] [α] ls
          (cRLM (ℍ := ℍ) .binder0 [en] (δ.extend x α) C [α] ls (.app e (.val .unit))) ρ

/-- At the top level a polymorphic value is checked by its own pushes alone. -/
def CRLMAllTop : Prop :=
  ∀ (x : LifeVar) (c : Lifetime.Life) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] (⟨[]⟩ : LSub) (.all x c C) [] ls e ρ ↔
      ∀ (en : LEnt) (α : Life), OwnPushM (⟨[]⟩ : LSub) (.all x c C) ρ ([], []) en α →
        RecsOutside [α] ls → SubFresh (⟨[]⟩ : LSub) α →
        guardPV (extS ((⟨[]⟩ : LSub).extend x α) [en] [α]) [en] [α] ls
          (cRLM (ℍ := ℍ) .binder0 [en] ((⟨[]⟩ : LSub).extend x α) C [α] ls
            (.app e (.val .unit))) ρ

def CRLMRetNil : Prop :=
  ∀ (δ : LSub) (S : Row) (A : VTy) (ls : List SRec) (e : Expr) (ρ : WRes), FlatTy A →
    (cRLM (ℍ := ℍ) .binder0 [] δ (CTy.effOf S A) [] ls e ρ ↔ cC (CTy.effOf S A) ls δ e ρ)
```

Plus `VRLMBangNil` (the `!` clause at `[]` with `PBox` unfolded to every `BoxStep` sequence from
`([], [])`) and `KeepsTKeeps` (`KeepsT ls ls' ρ → Keeps (rsOf ls) (rsOf ls') ρ`). Lemmas to reuse:
- `pvlNil` and `instAt_nil_eq`;
- `relendJ_emp` and `relendJ_empty_at` (`BinderRows.lean:471`, `R1Mono.lean:1080`);
- `vwSW_false`, `placeViewsL_empty`, `tab_empty` and `inScope_top_none`;
- `GhostEnd.bodyS_nil_iff`, and `vRLMData` under G1.

**G8–G11: arising, typing, adequacy.**

```lean
def ArisesITW : Prop :=
  ∀ c : Cfg, ArisesI (ℍ := ℍ) c → TW c.fρ c.ps (rsOf c.ls) ∧ Tagged c.fρ c.ps c.ls

def ArisesINilOfTW : Prop :=
  ∀ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec), TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    ArisesI (ℍ := ℍ) ⟨fρ, ρf, ρ, ps, ls, [], []⟩

def ProbeRulesOfNU : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    Targets.CDerivesNU Δ Γ e j → ProbeRules Δ Γ e j

def AdequacyNilM : Prop :=
  ∀ (e : Expr), BindersLow [] (CTy.ret .unit) → Scoped LifeCtx.empty [] (CTy.ret .unit) →
    SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] e (.comp (.ret .unit)) →
    ∀ {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}, BoCa.BoLo.Steps Adequacy.emptyMem e μ₁ e₁ →
      BoCa.BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val .unit)
```

The routes:
- **`ArisesITW`** is an induction on `ArisesI`. `run` uses `RunEnd`'s `TW`. `lendImm` is `TW.immFrame`
  from `LendImm`'s fields, and `lendMut` is `TW.mutFold`. `part` and `hide` keep the world.
- **`ArisesINilOfTW`** is `ArisesI.nil` itself, stated so that the ledger row can name it.
- **`ProbeRulesOfNU`** unfolds `ProbeRules` and applies `ExtendsNU`'s first conjunct at the empty row
  context.
- **`AdequacyNilM`** follows `adequacyD`'s proof (`Demonic.lean:312`), with `nilSoundRetM` in place
  of `fundamentalC`.

**Cost.** G1, G2, G4, G5, G3, G4′ and G5′ are each an induction or a slot-by-slot conversion, a few
hundred lines in all. G6–G11 are short. No theorem here reads an instantiation, a push or a view.

---

## 3. Part (2): the regression suite

### 3.1 The acceptance statement

A program's **acceptance obligation at the empty stack** is `SemSMNil .binder0` at the judgements of
its derivation where the draft reads its own clauses. There are three kinds:
- **R, the root**: the program's own judgement. At a flat answer it is Core's (G5′), so it is listed
  as a sanity check that reads no draft clause.
- **V, the values it builds at a type with `U`, `∀` or `!`**: its callbacks, closures and
  persistent combinators. These read the draft's `U` thaw, the `∀` clause's own push, and the box.
- **K, the borrow constants it applies, at its payloads**: `withbor`, `withload`, `withswap`,
  `alloc`, …, each Core's typing rule instance (a `CDerives` constructor at a dead context). These
  read the draft's consumer side: the callback's clause at an own push, with the lend's argument.

**Why this is fundamentalC's analog.** `fundamentalC` proves `SemJ` at every node of a derivation.
The draft's nodes at first-order types are Core's (G5). So a program-specific divergence can sit
only at R, V and K nodes. The generic glue at higher-order types (`app`, `bind`, `letpair` at
non-first-order types) is program-independent. It is tracked once, in §2.6's rows table, and is not
part of any entry.

**The obligation is read where the program's derivation has the judgement.**
- A K constant used inside a callback is at the callback's lifetime context (`Δ₁`, open in `'a`).
- `SemSMNil` there is the draft's Core-style reading, with no lend on the stack. Proving it is sound
  and meaningful: the draft must reproduce Core when nothing is lent. A refutation there cannot be a
  FAILS: no `Imm` view arises at the empty stack except as a run's answer (ledger A7).
- The draft's actual reading of a callback-internal judgement is at the own push. Each enclosing V
  entry exercises that reading, and the every-index rows (`WithloadRowM`, §4.6) do too.

**Statuses.**
- **PROVED**: a theorem proves the entry's `def … : Prop`.
- **FAILS**: only with a configuration that arises (`ArisesI`, with `ArisesVI` for every value the
  refutation reads), every hypothesis discharged, and the program's own judgement refuted. A route
  refuted is not a FAILS: it is recorded as "route blocked" under NOT BUILT.
- **NOT BUILT**: the exact missing lemma, named as an existing or new `def … : Prop`.

**The floor rule.** Every borrow-only program Core accepts must be accepted by the draft. A FAILS is
a draft defect, never a restriction. NOT BUILT entries are the floor's remaining work.

### 3.2 The producer lemmas (V)

Each V entry is one application of these to the program's named body derivation. They compose:
- the draft's proved rows: `ThunkVRowM` and `BangThunkVRowM` from `statement0UFullM`, and
  `AllIRowMAt _ []` from `allIRowMUFree0 []`;
- the `ret` node, which is the identity on `SemSM` by `jdgCty`;
- G5, applied at the λ's judgement.

Every Core callback has the shape `thunkV (allI (ret (thunkV (lam body))))` (`callbackW`,
`Core/Splits.lean:94`; `d_borrower`, `Examples.lean:121`; `d_algI`, `Folds.lean:60`).

```lean
/-- A closed first-order callback at the non-unwinding shape `∀'x ⊏ ⊓Δ. F (U (A ⊸ F B))`. -/
def SemSMCallbackOfCore : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → FOArg A → FlatTy B →
    CDerives (Δ.extend x Δ.meetOfDom) [⟨A, true⟩, ⟨.unit, false⟩] body (.val B) →
    SemSM (ℍ := ℍ) .binder0 Δ [] (.val (.lam (.val (.lam body))))
      (.val (.all x Δ.meetOfDom (.lolli A B)))

/-- The same at the `.arr` shape `∀'x ⊏ b. A ⊸ F B` (`cInst`'s `polyC`, `cbUTy` at the empty row). -/
def SemSMCallbackArrOfCore : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → b.mentions x = false → FOArg A → FlatTy B →
    CDerives (Δ.extend x b) [⟨A, true⟩, ⟨.unit, false⟩] body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ [] (.val (.lam (.val (.lam body))))
      (.val (.thunk (.all x b (.arr A (.ret B)))))

/-- A persistent first-order callback (`d_algI`'s algebras). -/
def SemSMBangCallbackOfCore : Prop :=
  ∀ (x : LifeVar) (A B : VTy) (body : Expr), FOArg A → FlatTy B →
    CDerives (LifeCtx.empty.extend x LifeCtx.empty.meetOfDom) [⟨A, true⟩, ⟨.unit, false⟩] body
      (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 LifeCtx.empty [] (.val (.lam (.val (.lam body))))
      (.val (.bang (VTy.all x LifeCtx.empty.meetOfDom (VTy.lolli A B))))

/-- A persistent first-order function (`cBang`'s closure, `arrProg`'s `tab10V`, `d_algO`). -/
def SemSMBangFnOfCore : Prop :=
  ∀ (Δ : LifeCtx) (A B : VTy) (body : Expr), FOArg A → FlatTy B →
    CDerives Δ [⟨A, true⟩] body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ [] (.val (.lam body)) (.val (.bang (VTy.lolli A B)))

/-- A thunk of a first-order computation type (`cRecBorrow`'s `cMethods`). -/
def SemSMThunkOfCore : Prop :=
  ∀ (Δ : LifeCtx) (N : Expr) (C : CTy), C.isRet = false → FOComp C →
    CDerives Δ [] (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ [] (.val (.lam N)) (.val (.thunk C))
```

The side conditions of `allI` come from `Δ.Ok`, as `allI_fresh` takes them. `OwnHyg` holds at
`Γ = []` with `Δ.find? x = none`. `PersistentBoxed []` and `Persistent []` are vacuous.

### 3.3 The consumer gates (K)

Every K entry for a higher-order constant has the full row as its obligation (NOT BUILT, §3.4).
Beside it, one statement isolates the draft-specific step of the row's route. That step is where
the two-cell gap lives:
- **`withbor` (1), (2)**: the callback at an own push lending the view's place. These are the
  existing consumer facts: `CallbackExtImmM`/`CallbackExtMutM` at the `.arr` shape (proved), and
  `CallbackExtImmMF`/`CallbackExtMutMF` at the thunked shape Core's programs use (stated,
  `Nx.lean:466`, `:483`).
- **`withload`**: [TR] 6.175's argument, Core's reborrowed payload at a fresh `β`, as
  `withload_compatX` hands it to the callback (`Compatibility.lean:252`). Some own push must admit it:
  related at the pushed index, and the composite meeting the guard. The statement below reads the
  guard at the push itself, which is the identity instantiation of the thunked answer's `U` clause.
  The non-identity route (`not_withloadPairGapNilInstE1`) is not the row's route.

```lean
abbrev loadCbF (A B : VTy) (x : LifeVar) : CTy :=
  .ret (.lolli (A.immReborrow (.var x)) (.box (.var x) B))
abbrev loadCbU (A B : VTy) (x : LifeVar) : CTy :=
  .arr (A.immReborrow (.var x)) (.ret (.box (.var x) B))

/-- **The `withload` gate at the empty stack** (single-entry form). -/
def LoadGateNil (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (r : FrameRec) (x : LifeVar) (c : Lifetime.Life) (β : Life)
    (cb ρc ρ : WRes),
    r.T = A → r ∈ rsOf ls → ¬ VFree x A → δ.find? x = none →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β r.R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) r.v cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ en : LEnt, OwnPushM δ (.all x c (C' x)) ρc ([], []) en β ∧
      vRLM (ℍ := ℍ) .binder0 none [en] (δ.extend x β) (A.immReborrow (.var x)) [β] ls r.v cb ∧
      TabAtS [en] [β] ρ ∧ PlaceViewsL (extS (δ.extend x β) [en] [β]) [en] [β] ls ρ
```

What it decides at each payload `A`:
- **No reborrowed cell** (`A = 1`, `B`, `methodsTy`, whose `Imm̲` is `Unk`): one entry at a fresh
  place with a closed payload type. Expected PROVED.
- **One cell** (`A = Ref 1`; `Pt.valTy = B ⊗ Ref B`, `readFields`'s record): the entry lends that
  cell's place. Its view is at exactly `β`, and `CohS` and `RetainedPay` hold. Expected PROVED.
- **Two or more** (`pairTy`, `Array i32` at length 2): the table's second conjunct rejects the cell
  at the unlent place at every push (`loadGuardFails2`, `pairCallbackGuardFails`). Expected refuted
  ("route blocked"). The refuting data is `withloadUPairGapNilE1`'s, whose view is not shown to arise.
- **The views' payload reading.** At a leaf payload with a thunk, `PlaceViewsL`'s `vwEW` asks the
  payload at `vC true` while Core's leaf gives `vC false` (D11). Every leaf payload in the suite is
  data, where the two agree.

The block form, `LoadGateNilB` (§4.6), has `∃ τ` (a block) in place of `∃ en`.

### 3.4 The programs reused

Line numbers are at `3e84262`. "Exact missing lemma" names what the entry waits on. Statuses are
*[expected]* until the build records them. Abbreviations: `PROVED[G5′]` is by `CoreToSemSMNil`;
`PROVED[cb]` is by the producer lemma named. In a table's Lean column, `_` in a type stands for the
derivation's bound, `Δ.meetOfDom` at the entry's `Δ`, or for the answer type the derivation uses.
The program's statement is the conjunction of its entries. P1's is written out below as the
template, with the gate and two entries from P10 and S1; all of them elaborate.

**P1 `cImmBorrow`** (`Core/Examples.lean:88`; `cImmBorrow_derives` `:127`). `withbor` (1) at `1`,
`withload` at `1` (no cell).

| entry | Lean (`SemSMNil .binder0 …`) | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] cImmBorrow (.comp (.ret .unit))` | PROVED[G5′] | — |
| V1 | `LifeCtx.empty [] (borrower cLoader) (.val (borrowerTy .unit))` | PROVED[cb] (`SemSMCallbackOfCore` at `d_borrowBody`, `:104`) | — |
| V2 | `Δ₁ [] cLoader (.val (loaderTy .unit))` | PROVED[cb] at `Δ = Δ₁` (`d_loader`, `:94`) | — |
| K1 | `LifeCtx.empty [] withbor (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom .unit .unit))` | NOT BUILT | `Withbor1NilRowM` (the port of `withbor1_compatX`, `Compatibility.lean:937`); its draft step `CallbackExtImmMF .binder0` |
| K2 | `Δ₁ [] withload (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit)))` | NOT BUILT; gate `LoadGateNil .unit (loadCbF .unit _)` PROVED | `WithloadNilRowM` (§4.6) |
| K3, K4 | `alloc` at `.lolli .unit (.ref .unit)`, `free` at `.lolli (.ref .unit) .unit` | PROVED[G5′] | — |

```lean
def AccImmBorrowRoot : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] cImmBorrow (.comp (.ret .unit))
def AccImmBorrowCb : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] (borrower cLoader) (.val (borrowerTy .unit))
def AccImmBorrowLoader : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 Δ₁ [] cLoader (.val (loaderTy .unit))
def AccImmBorrowWithbor : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom .unit .unit))
def AccImmBorrowWithload : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 Δ₁ [] withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit)))
def AccImmBorrowAlloc : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] (.val (.prim .alloc))
    (.val (.lolli .unit (.ref .unit)))
def AccImmBorrowFree : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] (.val (.prim .free))
    (.val (.lolli (.ref .unit) .unit))

/-- `cImmBorrow`'s acceptance obligation at the empty stack. -/
def AccImmBorrow : Prop :=
  AccImmBorrowRoot (ℍ := ℍ) ∧ AccImmBorrowCb (ℍ := ℍ) ∧ AccImmBorrowLoader (ℍ := ℍ) ∧
    AccImmBorrowWithbor (ℍ := ℍ) ∧ AccImmBorrowWithload (ℍ := ℍ) ∧ AccImmBorrowAlloc (ℍ := ℍ) ∧
    AccImmBorrowFree (ℍ := ℍ)

/-- K2's draft step. -/
def GateImmBorrowLoad : Prop := ∀ B : VTy, LoadGateNil (ℍ := ℍ) .unit (loadCbF .unit B)

/-- P10's V2: the user's case. -/
def AccCountFoldBorrower : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [⟨fTy listL natN, true⟩] borrowerE
    (.val (VTy.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) listL) (.box (.var 0) natN))))

/-- S1's K2: `withload` of a pair. -/
def AccPairLoadWithload : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 Δ₁ [] withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit)))
```

**P2 `cRecBorrow`** (`:217`; `:247`). A payload holding a thunk; `withload` gives `Unk`.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] cRecBorrow (.comp (.ret .unit))` | PROVED[G5′] | — |
| V1 | `LifeCtx.empty [] (borrower cRecLoader) (.val (borrowerTy methodsTy))` | PROVED[cb] (`d_borrowBody` with `d_recLoader`; arg `Imm '0 methodsTy` is `FOArg`) | — |
| V2 | `Δ₁ [] cRecLoader (.val (loaderTy methodsTy))` | PROVED[cb] (arg `Unk`) | — |
| V3 | `LifeCtx.empty [] cMethods (.val methodsTy)` | PROVED (`SemSMThunkOfCore` at `d_methods`, `:227`) | — |
| K1 | `withbor` at `axWithbor1Ty 0 _ methodsTy .unit` | NOT BUILT | `Withbor1NilRowM`; D11 at the view of a thunk payload |
| K2 | `withload` at `axWithloadTy (.var 0) 1 _ methodsTy _` | NOT BUILT; gate PROVED (no cell) | `WithloadNilRowM` |
| K3, K4 | `alloc`, `free` at `methodsTy` | NOT BUILT | `methodsTy` is not `NilTy`: `AllocNilRowM`, a port of `alloc_compatX` (`:579`) whose stored value is the argument [cheap] |

**P3 `cBang`** (`:175`; `:179`). A persistent closure used twice and dropped.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] cBang (.comp (.ret .unit))` | PROVED[G5′] | — |
| V1 | `LifeCtx.empty [] (.val (.lam (.var 0))) (.val (.bang (.thunk (.arr .unit (.ret .unit)))))` | PROVED (`SemSMBangFnOfCore`) | — (exercises the box, D4) |

**P4 `cInst`** (`:307`; `:311`, open at `Δ₁`). `∀E` at a non-`F` type, at an instance in scope.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | `Δ₁ [] cInst (.comp (.ret .unit))` | PROVED[G5′] | — |
| V1 | `Δ₁ [] (.val (.lam (.val (.lam (.var 0))))) (.val (.thunk polyC))` | PROVED (`SemSMCallbackArrOfCore`) | — |
| K1 | `∀E` at `'a` (the `allE` node) | NOT BUILT | `AllERowM` (not stated); its draft step `InScopeOfInterp` (`Nx.lean:396`, stated) (D1) |

**P5 `readFields`** (`Core/RecordPrograms.lean:82`; `d_readFields` `:137`). Field access through an
`Imm` borrow: `withload` of a record with one `Ref` field (one reborrowed cell), and `withload` of
the field's view.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] readFields (.val .unit)` | PROVED[G5′] | — |
| V1 | `LifeCtx.empty [] readBorrower (.val (.all 0 _ (.lolli (.imm (.var 0) Pt.valTy) (.box (.var 0) (.tensor BB BB)))))` | PROVED[cb] (`d_readBody`, `:116`) | — |
| K1 | `withbor` at `Pt.valTy` | NOT BUILT | `Withbor1NilRowM` |
| K2 | `withload` at `Pt.valTy` | NOT BUILT; gate PROVED (one cell: **the positive control**) | `WithloadNilRowM` |
| K3 | `withload` at `BB` (`readCell`, `:69`; `d_readCell` `:103`) | NOT BUILT; gate PROVED (no cell) | `WithloadNilRowM` |
| K4 | `copy` at `Imm '0 Pt.valTy` | PROVED[G5′] | — |

**P6 `mutFields`** (`:216`; `:238`). `Mut` borrow and `swapField` (D7).

| entry | Lean | expected | missing |
|---|---|---|---|
| R, V1 | root; `mutBorrower` (`:214`) | PROVED[G5′], PROVED[cb] | — |
| K1 | `withbor` (2) at `Pt.valTy` | NOT BUILT | `Withbor2NilRowM`; draft step `CallbackExtMutMF` |
| K2 | `withswap` | NOT BUILT | `WithswapNilRowM`; `EntryPayLeaves` at a bound `Mut` read-out (`R1MONO.md` §8) |

**P7 `readFamily`** (`Core/FamilyPrograms.lean:282`; `:322`) and **P8 `swapBothB`** (`:152`;
`:154`). Core's family borrow `withborF2`, nested single-place lends (D6, D9).

| entry | Lean | expected | missing |
|---|---|---|---|
| R | root | PROVED[G5′] | — |
| V1 | `readCb` (`:273`, `d_readCb` `:300`), `swapCb` (`:49`, `d_swapCb` `:77`) at `cbTy2 …` | PROVED[cb] (arg `famTy2`, a tensor of leaves) | — |
| K1 | `LifeCtx.empty [] withborF2 (.val (withborF2Ty immM 0 LifeCtx.empty.meetOfDom BB BB B3))` (and `mutM`) | NOT BUILT | `AllIRowMAt .binder0 Γ` at `Γ` holding `g : cbTy2 …`, a live linear `U` slot (`outer2`, `inner2`, `Family.lean:62–65`). Its route stopped at `not_readEquivRelend`; also `MonoOwnGMAtPS` and 3b-ii's steps (`Nx.lean:617–687`); and `Withbor1NilRowM`/`Withbor2NilRowM` |

**P9 `blockSwap`** (`Core/BlockPrograms.lean:113`; `:121`). Core's block borrow `withborS`.
Entries as P8, with V1 `swapCb` at `cbT mutM 0 _ σ2 .unit` (`d_swapCbB`, `:104`) and K1 `withborS`.
The same missing lemmas apply (D6).

**P10 `countFoldProg`** (`Core/Folds.lean:375`; `:377`) and **P11 `anyTreeProg`** (`:469`; `:471`).
The user's case (D5): the persistent polymorphic fold `g : fTy M R` is captured by the borrow's
callback and called at the callback's own lifetime.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | root at `F N` / `F B` | PROVED[G5′] | — |
| V1 | `LifeCtx.empty [] (.val countAlgV) (.val (algTy listF 0 natN))` (and `anyTAlgV` at `btreeF`) | PROVED (`SemSMBangCallbackOfCore` at `d_countAlgB`, `:78`) | — (exercises the box) |
| V2 | `LifeCtx.empty [⟨fTy M R, true⟩] borrowerE (.val (VTy.all 0 _ (.lolli (.imm (.var 0) M) (.box (.var 0) R))))` at `M = listL`, `R = natN` | NOT BUILT | `AllIRowMAt .binder0 [⟨fTy M R, true⟩]`: `VRLMStackRename` (`NxFloor.lean`, stated), the reduction from it with `persistentPushN`, and the reading transports at a `!U` slot (`CtxExtendMSAt`, `CtxShadowMSAt`) |
| K1 | `foldImm` at `listF`, `btreeF` | NOT BUILT | `FoldImmNilRowM` (a higher-order constant: it consumes the algebra) |
| K2 | `withbor` at `listL` | NOT BUILT | `Withbor1NilRowM` |

**P12 `counterProg`** (`Core/AffPrograms.lean:235`; `:237`). An affine closure stored in a cell,
lent `Mut`, called through the borrow (D7).

| entry | Lean | expected | missing |
|---|---|---|---|
| R, V1 | root at `F i32`; `Aff.cntCb` at `Δ₁` (`:134`, `d_cntCb` `:136`; arg `Mut 'w PC`) | PROVED[G5′], PROVED[cb] | — |
| K1 | `withbor` (2) at `PC` | NOT BUILT | `Withbor2NilRowM` |
| K2 | `callMut` (`withswap` at `PC`) | NOT BUILT | `WithswapNilRowM`; `EntryPayLeaves` at a closure payload |

**P13 `arrProg`** (`Core/ArrayPrograms.lean:47`; `:54`). No borrow: the box at persistent prims
(D4).

| entry | Lean | expected | missing |
|---|---|---|---|
| R | root | PROVED[G5′] | — |
| V1, V2 | `tab10V : !(I32 ⇒ I32)`, `dropI32V` | PROVED (`SemSMBangFnOfCore`, `d_tab10`, `d_dropI32`) | — |
| K1 | `arrNew` | NOT BUILT | higher-order (`!(I32 ⇒ A)` argument): `ArrNewNilRowM` |
| K2 | `arrReplace`, `arrSize` (closed types, flat results) | NOT BUILT | the box reads them at box worlds, where Core's relation of a semantic value at an instantiated reading is not available from Core's lemma statements. Missing: `CoreClosedToW` — at a type with no free lifetime variable, Core's relation is reading-independent, so Core's `U` is the draft's at every stack [planned, cheap] |

*Should*, after the must list: `matchSome`, `bagProg`, `swapBothL`, `splitFour`, `nestSwap`,
`blockRead`, `anyListProg`, `natCopyProg`, with the same entry kinds.

### 3.5 The seeds

**S1 `pairLoad` and `pairLoadU`: `withload` of a pair of references.** These are new terms. They
are `cImmBorrow`'s skeleton at the payload `pairTy = Ref 1 ⊗ Ref 1` (`Nx.lean:39`), reusing
`borrower`, `borrowBody` and `d_borrower` (generic in the payload and the loader):

    alloc (alloc (), alloc ()) to r.
    withbor r (borrower pairLoader) to p. let (r′, t) = p in t;
    free r′ to c. let (c₁, c₂) = c in free c₁; free c₂

`pairLoader = Λ'1. return (λq. let (u, w) = q in forget u; forget w; return (box (box ())))`, at
`loaderTy pairTy`, so its argument is `Imm '1 1 ⊗ Imm '1 1`. `pairLoadU` is the same term with
`withload` typed by `withloadU` at the empty row (`Row.Unwind x []` holds vacuously). It needs the
loader at `cbUTy` (`.arr` shape), which the same term types. To build: `d_pairLoader`,
`pairLoad_derives`, `pairLoadU_derives`, modelled on `d_loader` and `cImmBorrow_derives`.

| entry | Lean | expected now | after the block |
|---|---|---|---|
| R | `LifeCtx.empty [] pairLoad (.comp (.ret .unit))` | PROVED[G5′] | PROVED |
| V1, V2 | the borrower at `borrowerTy pairTy`; `pairLoader` at `Δ₁` | PROVED[cb] | PROVED |
| K1 | `withbor` at `axWithbor1Ty 0 _ pairTy .unit` | NOT BUILT (`Withbor1NilRowM`) | the same |
| K2 | `Δ₁ [] withload (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit)))` | NOT BUILT; gate `LoadGateNil pairTy (loadCbF pairTy _)` route blocked | gate `LoadGateNilB` PROVED; row PROVED if §4.6's stretch closes |
| K2′ (`pairLoadU`) | the same at `withloadUTy … pairTy … []` | NOT BUILT; gate (`loadCbU`) route blocked | as K2 |

**S2 `sliceLoad`: `withload` of a slice.** A reduced transcription of `corpus/array-get.bc`:
`withbor` (1) lends `Imm 'x (Array i32)`, and `withload` turns it into the family
`ArrayImm 'y i32` of two leaf views at one lifetime:

    array_new (2, tab10) to a. alloc a to r.
    withbor r (Λ'0. return (λb. withload b sliceLoader to t. return (box t))) to p.
    let (r′, t) = p in free r′ to a′. array_free (dropI32, a′); t

`sliceLoader = Λ'1. return (λf. array_len f to n. return (box n))`. Its argument is
`fam (Imm '1 i32)` (`FOArg`), and its result is flat. To build: `d_sliceLoader` and
`sliceLoad_derives`, reusing `d_tab10`, `d_dropI32`, `CDerives.arrNew`, `.arrLen` and `.arrFree`.

| entry | expected now | after the block |
|---|---|---|
| R; V (the borrower, `sliceLoader`) | PROVED[G5′]; PROVED[cb] | PROVED |
| K `withload` at `Array i32` | NOT BUILT; gate `LoadGateNil (.array .i32) _` route blocked (two cells) | gate PROVED; row as S1 |
| K `arrLen` at `'1` | NOT BUILT (`!` at box worlds: `CoreClosedToW` does not apply, the type reads `'1`) | the same |

The slice *lend* (`slice_borrow_imm`, `corpus/slice-imm.bc`; `sliceBorrowI`) is optional: its gate
mirrors `LoadGateNil` with the lend's frames (`SliceFrames`, `Nx.lean:278`), as `SliceGateNil`.

**S3 the user's case.** Served by P10 and P11, which already exist (§0, fact 4). No new seed is
built. The expected V2 status is NOT BUILT, and its missing lemma is the binder-named push at a
persistent context.

**S4 `reconB′`** (`NxRecon.lean`, `reconB'`, `reconCb`). Tier 2, not floor: no Core derivation
exists, since `wait` resumes inside the lend and the unwinding rules do not admit it.

| entry | Lean | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] reconB' (.comp (.ret (.tensor Flag Flag)))` | NOT BUILT | a flat-answer root is Core's semantic acceptance (G7's `CRLMRetNil`); with no Core derivation, only a semantic proof of the run would give it, and that reads no draft clause |
| V | `reconCb` at its callback type | NOT BUILT | the typing (which rule types `withborUE dFlag` under `wait`); the callback row `CallbackExtImmMF`; the body at the `F_Σ` type at the push (statements 1–3); `reconCb_allI` covers only the `∀I` step |

**S5 `loadKeepsView`, optional (D3).** `cImmBorrow` with the borrower copying its view and the loader
capturing the copy: `let (b₁, b₂) = copy b in withload b₁ (Λ'1. return (λq. forget b₂; …))`. The
loader's context is `b₂ : Imm '0 1`, which is `FOArg` and reaches no `U`, so its V entry is PROVED
by `AllIRowMAt` at that context with G5 [expected]. The K gate at `A = Ref 1` fails `OwnOKI.placeFree`
at the needed entry: the callback deep-holds the reborrowed place's `own` cell under the copy's
`imm` ancestor. `OwnOKB`'s relaxed `placeFree` (§4.2) admits it. So the gate is route-blocked now,
and PROVED after the block [expected].

### 3.6 Not in this suite

Core's effect programs are tier-1 floor, with abortive operations inside a lend and no suspension:
`logInBorrow`, `reborrowRaise`, `storeCancel` (`Core/EffPrograms.lean:615`, `:386`, `:939`). They
read the draft's `F_Σ` clause at the pushed stack (GhostEnd's piece) and the unwinding callback rows
(`CallbackExt*M` at the `.arr` shape). They belong to the next suite, whose seeds they are.
Codata-only programs (`StreamPrograms`, `DelayPrograms`) read `ν` through Core's `cC`, equal by
definition (C11), and are omitted. Corpus programs have no Lean derivation, so the seeds transcribe
them.

### 3.7 `GroundRegress.lean`

`GroundRegress.lean` imports `ProbeD1.GroundLedger` and the Core program modules. It holds:
- the producer lemmas (§3.2) with their proofs;
- the gate (§3.3);
- the seeds' terms and derivations (§3.5);
- per program, one `def Acc<Prog><Entry> : Prop` per entry, as in the tables. Each has a theorem
  where PROVED, and otherwise a docstring naming the missing lemma.

Also `def Acc<Prog> : Prop`, the entries' conjunction, and the results table in `LEDGER.md`: program,
entry, status, theorem or missing lemma.

---

## 4. Part (3): the block entry

### 4.1 Why a block, and what Core does

[TR] 6.150's reborrow puts every reborrowed cell at one lifetime `β` (`reb_β`). A cell at an internal
lifetime and at an unlent place can be neither a view nor above the cut. The freeze binder's thaw
can therefore neither retain it nor transport it, as `NEXT.md` §1.6 argues. So the stack must lend
every reborrowed place at `β`: a block of entries sharing variable, lifetime and lender's row.
GhostEnd's `LEnt` lends one place and stays unedited.

Core does this differently, by design, in its derived family and block borrows (§0, fact 3). That is
why the gap shows only at a constant whose own semantics makes several cells at one lifetime:
`withload` on a payload with several `Ref` or `Mut` leaves, and the slice constants.

### 4.2 The definition changes, in place

The block is built **in place in the one draft relation**, as (E1)–(E4) were (`NEXT.md` §3.1). So no
second relation exists at any time. The new definitions go in a new file `ProbeD1/Block.lean`, which
imports `ProbeD1.Binder` and which `R1.lean` imports: they read only `World.lean`'s, `Sem.lean`'s and
`Binder.lean`'s definitions. They are `NEXT.md` §1.6's, with two corrections (§4.3).

```lean
/-- `τ`'s entries all at `a`. -/
abbrev blockL (τ : LStack) (a : Life) : List Life := τ.map fun _ => a

/-- **A stack in shape, blocks admitted**: one lifetime per entry, non-decreasing outward; two
entries share a variable exactly when they share a lifetime; a block's entries share their lender's
row. `StackOK` is the case with no block (`StackOKBOfOK`). -/
def StackOKB (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· ≤ ·) αs ∧
    (∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.1.x = q.1.x ↔ p.2 = q.2) ∧
    ∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.2 = q.2 → p.1.cross = q.1.cross

/-- **A borrow leaf of a type at `'x`**, through the formers `vRLM` reads at one index. -/
inductive LeafTyAt (x : LifeVar) : VTy → Bool → VTy → Prop
  | mut (S : VTy) : LeafTyAt x (.mut (.var x) S) true S
  | imm (S : VTy) : LeafTyAt x (.imm (.var x) S) false S
  | tensorL {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.tensor A B) k S
  | tensorR {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x B k S → LeafTyAt x (.tensor A B) k S
  | sumL {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.sum A B) k S
  | sumR {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x B k S → LeafTyAt x (.sum A B) k S
  | bang {A : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.bang A) k S
  | box {a : Lifetime.Life} {A : VTy} {k : Bool} {S : VTy} :
      LeafTyAt x A k S → LeafTyAt x (.box a A) k S
  | fam {L : VTy} {k : Bool} {S : VTy} : LeafTyAt x L k S → LeafTyAt x (.fam L) k S
  | mu {A : VTy} {k : Bool} {S : VTy} : (VTy.mu A).Cl 0 →
      LeafTyAt x (VTy.inst (.mu A) A) k S → LeafTyAt x (.mu A) k S

/-- **The block a callback's own lend pushes**, tied to the argument at the `.arr` shape. -/
def ViewAtB (x : LifeVar) (τ : LStack) (A : VTy) : Prop :=
  (∀ e ∈ τ, ∃ S, ((e.k = .mut ∧ LeafTyAt x A true S) ∨
      ((∃ u, e.k = .imm u) ∧ LeafTyAt x A false S)) ∧ e.T = S) ∨
  ((¬ ∃ k S, LeafTyAt x A k S) ∧ ∃ e, τ = [e] ∧ ∀ y, ¬ VFree y e.T)

/-- **A block's own lend.** `placeFree` admits `own` cells at a block place frozen under an `imm`
ancestor (a copy of the lend's view held by the callback, `NEXT.md` §1.6). -/
structure OwnOKB (δ : LSub) (σ : LStack) (αs : List Life) (x : LifeVar) (τ : LStack) (a : Life)
    (ρ : WRes) : Prop where
  ne : τ ≠ []
  named : ∀ e ∈ τ, e.x = x
  sameRow : ∀ e ∈ τ, ∀ e' ∈ τ, e.cross = e'.cross
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : x ∉ σ.map LEnt.x
  placesNodup : (τ.map LEnt.l).Nodup
  places : ∀ e ∈ τ, e.l ∉ σ.map LEnt.l
  placeFree : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ
  pay : ∀ e ∈ τ, ∀ y, VFree y e.T → (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y ≠ none
  selfFree : ∀ e ∈ τ, ¬ VFree x e.T

/-- **The own lend at the type `C`, a block** (`OwnPushM`'s `payLocal` kept). -/
def OwnPushB (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (τ : LStack) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ x ∉ CTy.binders C' ∧
    OwnOKB δ s.1 s.2 x τ a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    (∀ e ∈ τ, ∀ y, VFree y e.T → CFree y C) ∧
    ∀ A D, C' = .arr A D → ViewAtB x τ A

/-- **`StackJM` with blocks**: `StackJ`'s distinct variables dropped (`StackOKB`'s variable condition
replaces them), its third kind and `StackJM`'s extra conjunct read at the innermost block. -/
def StackJB (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (∀ e ∈ σ, ∀ y, VFree y e.T → (∃ u, Δ.find? y = some u) ∨ y ∈ σ.map LEnt.x) ∧
  (∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head?.map LEnt.x = some e.x ∧ CtxFresh e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧
        ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)) ∧
  ∀ e ∈ σ, Δ.find? e.x = none → σ.head?.map LEnt.x = some e.x → (∃ c C', C = .all e.x c C') →
    (∀ a ∈ αs.head?, SubFresh δ a) ∧ ∀ e' ∈ σ, ¬ VFree e.x e'.T
```

**The edits to existing definitions** (`R1.lean`, after its import of `ProbeD1.Block`), and nothing
else:
- `cRLM`'s `∀` clause (`:210`): the own-lend conjunct pushes a block (the fragment below).
- `SemSM` (`:246`) and `SemIdxM` (`:946`): `StackOK` becomes `StackOKB`, and `StackJM` becomes
  `StackJB` (`SemIdxM`'s `StackJ` becomes `StackJB`).
- `SemSMC` (`:803`), the restricted route's judgement: the same two changes, kept in step.

The fragment for the own-lend conjunct:

```lean
        (p.allOwn = true → ∀ (τ : LStack) (α : Life), OwnPushB δ (.all x c C) ρ (σ', αs') τ α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (τ ++ σ') (blockL τ α ++ αs')) (τ ++ σ')
            (blockL τ α ++ αs') ls'
            (cRLM p (τ ++ σ') (δ.extend x α) C (blockL τ α ++ αs') ls' (.app e (.val .unit))) ρ)
```

**Unchanged:**
- `BoxStep` and `PBox`: a box step pushes one reserved-name entry strictly below the head, which
  keeps `StackOKB`.
- `OwnPushM`, `OwnPushI`, `MonoOwnGM` and the other single-push statements stay as they are, as
  facts about single pushes.
- `ArisesI` stays: the reborrow's and the slice's block lends (`LendRebI`, `LendSliceI`, `NEXT.md`
  §1.6) are needed only before a refutation at a block configuration is claimed, and none is
  planned.
- `cbpv` and `binder`'s `RelendU` push.

### 4.3 Corrections to `NEXT.md` §1.6

1. **`OwnPushBOfM` is false as stated.** At an `.arr` type whose argument has its borrow leaves below
   the top (`(Imm 'x 1 ⊗ Imm 'x 1) ⊸ D`), `OwnPushI`'s `ViewAt` is `True`, so `OwnPushM` admits an
   entry whose payload type matches no leaf (`int`). `ViewAtB` rejects that entry. The design's
   statement is replaced by the form its consumers need, the callback rows at `e.T = T` under a
   top-level `Mut 'y T` or `Imm 'y T`, and the counterexample is recorded as a fact about our
   statement:

   ```lean
   def OwnPushBOfMView : Prop :=
     ∀ (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life),
       OwnPushM δ C ρ s e a →
       (∀ x c A D, C = .all x c (.arr A D) → ViewAtB x [e] A) →
       OwnPushB δ C ρ s [e] a

   def NotOwnPushBOfM : Prop :=
     ¬ ∀ (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life),
         OwnPushM δ C ρ s e a → OwnPushB δ C ρ s [e] a
   ```

   So at the `.arr` shape the block clause drops the single pushes that match no leaf. That means
   fewer obligations for the `∀I` row and none lost for a consumer.
2. **`StackJB`'s third kind** reads "the innermost block", `σ.head?.map LEnt.x = some e.x`, where
   §1.6 said "every entry of the innermost block" without a formula.

### 4.4 The gate, first

`Block.lean` adds definitions only, so it changes no existing result. Before the edits to `cRLM`,
`SemSM`, `SemIdxM` and `SemSMC`, prove in a new file `GroundBlock.lean`, after `GroundRegress.lean`:

```lean
def StackOKBOfOK : Prop := ∀ (σ : LStack) (αs : List Life), StackOK σ αs → StackOKB σ αs

def InstStackOKB : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ι : Inst), InstAt αs ι → StackOKB σ αs → StackOKB σ (ι.life αs)

def PairGuardHoldsB : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (x : LifeVar) (β : Life)
    (τ : LStack) (cb ρc ρ : WRes),
    StackOKB σ αs → OwnOKB δ σ αs x τ β ρc → TabAtS σ αs ρc →
    PlaceViewsL (extS δ σ αs) σ αs ls ρc →
    (∀ e ∈ τ, ∃ ψ : CellU BoCa.Loc Val, cb.get e.l = some ψ ∧
      vwEW (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) e true β ls (ResU.single e.l ψ)) →
    (∀ l ψ, cb.get l = some ψ → l ∈ τ.map LEnt.l) → ResU.CompS ρc cb ρ →
    TabAtS (τ ++ σ) (blockL τ β ++ αs) ρ ∧
      PlaceViewsL (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) (τ ++ σ)
        (blockL τ β ++ αs) ls ρ

def PVLStartB : Prop :=
  ∀ (s s' : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (τ : LStack) (α : Life)
    (ρ a R : WRes), StackOKB σ αs → List.IsChain (· < ·) (α :: αs) →
    (τ.map LEnt.l).Nodup → (∀ e ∈ τ, e.l ∉ σ.map LEnt.l) →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s σ αs ls ρ →
    (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) →
    vwSW s' [] τ (τ.map fun _ => true) (blockL τ α) ls a →
    PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls a →
    ResU.CompS ρ a R → PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls R
```

Then `OwnPushBOfMView`, `NotOwnPushBOfM`, and the block gate at the suite's payloads: `LoadGateNilB`
(below) at `pairTy` and `Array i32`, at both shapes, and at `Ref 1` under S5's frozen copy.

```lean
def LoadGateNilB (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (r : FrameRec) (x : LifeVar) (c : Lifetime.Life) (β : Life)
    (cb ρc ρ : WRes),
    r.T = A → r ∈ rsOf ls → ¬ VFree x A → δ.find? x = none →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β r.R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) r.v cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ τ : LStack, OwnPushB δ (.all x c (C' x)) ρc ([], []) τ β ∧
      vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (A.immReborrow (.var x)) (blockL τ β) ls r.v cb ∧
      TabAtS τ (blockL τ β) ρ ∧ PlaceViewsL (extS (δ.extend x β) τ (blockL τ β)) τ (blockL τ β) ls ρ
```

`LoadGateNilB` reads `vRLM`. Before the edit it is checked at the current `vRLM`, whose `Mut`, `Imm`,
`⊗` and `[L]` clauses the edit does not touch. Its route: choose `τ` as one entry per reborrowed cell
(kind `imm`, payload the leaf's type, place the cell's).
- The argument's leaves get `CohS` from `innerAt` at their own entry.
- The table holds: the cells are at block places, and `ρc` is strictly above `β`.
- The views hold: each cell is its entry's view at exactly `β`, and the payload is data.
- At the thunked shape `ViewAtB` is vacuous, since `C'` is a `.ret`.

### 4.5 The rows to re-prove, in build order

The policy:
- A relation-independent lemma that a row uses with `StackOK σ αs` is generalized to
  `StackOKB σ αs`, and its old statement is re-derived through `StackOKBOfOK`. So historical
  statements keep their text.
- A statement whose text changes is listed (§4.7).
- The order follows the import chain. Each file is rebuilt (`lake build ProbeD1`) before the next.

1. **`R1.lean`**: the edits of §4.2. Statements reading `SemSM` keep their text.
2. **`R1Thaw.lean`**: the thaw at a block stack: `relendMValueE`, `ctxRelendsAllM`, `thawInstM`, and
   the `U` rows. The reading at a zip member uses "same variable ⇒ same lifetime" (from `StackOKB`),
   and `InstStackOKB` gives the shape after an instantiation. Relation-independent lemmas from
   `Binder*`/`Gap*` that take `StackOK` are generalized as needed (`guardInst`, `viewSlotInstOB`,
   `cohEInstOB`, the `extS` lookups).
3. **`R1Mono.lean`**: `monoExtM0` at the block index, and a new `monoOwnGUFreeMB`, the `U`-free push
   of a block. A context value's exposed cells are not at block places (`OwnOKB.placeFree`'s
   `¬ ExAt`), so its `CohS` and `RetainedPay` read the entries they read before. Frozen `own` cells
   at block places are outside `PlaceViewsL` (`PVLStartB`).
4. **`R1Owed.lean`**: `OuterBelowTopPushB` and `RetainedPayViewRowB`, at every entry of a block.
5. **`R1Box.lean`**: the box at a block index (`boxIdx`, `pBox_world`, the two `!U` rows,
   `statement0UFullM`).
6. **`R1Stmt0.lean`**:
   - `all_ownM` at a block push;
   - `callbackExtMutM_own` and `callbackExtImmM_own`, through `OwnPushBOfMView` (`LeafTyAt.mut`,
     `.imm` at `e.T = T`);
   - `forceRowM`, `statement0SharedM`, `statement0MBesideMono0`.
7. **`R1AllI.lean`, `NxAllI.lean`**: the `∀I` row serving every block push (`allIRowMNKAt0_of`,
   `allIRowMAt0_of`, `ctxExtendNamedMAt_uFree`, `allIRowMUFree0`). The premise is read at
   `(τ ++ σ, blockL τ α ++ αs)`, where the block's variable is the binder, of `StackJB`'s first kind.
   Use `subOutsideExtendNamed` at the block, and `monoOwnGUFreeMB`.
8. **`NxUnroll.lean`**: `rollRowM` and `unrollRowM` at the block index.
9. **`NxE1.lean`**:
   - `muAdjVRLME1`: the adjacency closure at every block push.
   - `pairGate_afterEdits`.
   - `withloadUPairGapNilE1`: its text reads `OwnPushM`, so it stays a fact about single pushes, and
     its docstring says the relation now reads blocks.
   - `not_withloadPairGapNilInstE1`: re-checked.
10. **`NxHide.lean`, `NxFloor.lean`, `NxRecon.lean`**: re-checked (`monoOwnGMAtBoxN` is at
    `BoxStep`).
11. **`GroundLedger.lean`, `GroundRegress.lean`**: re-checked. G1–G5 do not read the push. The
    producer lemmas compose the re-proved rows.

### 4.6 The suite after the block, and the stretch

The target: the gates of S1 and S2 (`LoadGateNilB` at `pairTy` and `Array i32`, both shapes) and of
S5 go PROVED. Every other entry keeps its status.

**The stretch: the `withload` rows**, which turn K2 PROVED for every payload:

```lean
def WithloadNilRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSMNil (ℍ := ℍ) .binder0 Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))

def WithloadUNilRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSMNil (ℍ := ℍ) .binder0 Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B []))
```

The route is `withload_compatX`'s (`Compatibility.lean:252`) and `withloadU_compatX`'s
(`EffBorrow.lean:548`), step for step, with one step changed. Where Core instantiates the
callback's `∀` at the fresh `β` (6.150's `wpTS_reborrow` premise), the draft takes:
- the callback's own-lend conjunct at the block of the reborrowed places, at `β`, where `β` is
  chosen below the records' readings as well (`И` admits every lifetime below a bound);
- at the thunked shape, the answer's `U` clause at the identity (`relendJ_id`, `R1Mono.lean:1345`);
- the `⊸` at the reborrowed argument, with `LoadGateNilB`'s facts.

The callback's answer is flat (`['x] B` with `B` flat in the suite), so it is Core's (G1). The rest
is Core's proof. At a payload with no reborrowed cell, the block is one entry at a fresh place with a
closed payload type (`ViewAtB`'s second disjunct). The every-index form (`WithloadRowM`, at
`SemSM`), the reading inside a lend, uses `PairGuardHoldsB` at a non-empty stack. It is preferred if
the proof is uniform in the stack.

### 4.7 The statement-change register

The outcome lists:
- (a) every theorem whose text changed, with the reason;
- (b) every theorem whose proof changed and whose text did not;
- (c) every claim, in the docs, about a theorem whose text did not change but whose meaning did,
  because it reads `vRLM`, `cRLM` or `SemSM`: `statement0UFullM`, `allIRowMUFree0`,
  `callbackExt*M_own`, `forceRowM`, `rollRowM`, `unrollRowM`, `muAdjVRLME1`, the box's facts, and
  the `Ground*` theorems.

Historical relations (`vRL`, `vRLI`, `vRLJ`) and their results do not change.

### 4.8 Success, the stop rule, the fallback

**Success.** All of the following:
- The gate lemmas of §4.4 are proved.
- With the edit, `lake build ProbeD1` is clean. Every theorem proved before is proved after, with
  its text unchanged unless it is listed in §4.7 (a) with its reason. There is no forbidden keyword,
  and every axiom set is within the three.
- S1's and S2's gates are PROVED at the block relation, and S5's if built.

The stretch (§4.6) turns S1's and S2's K2 PROVED. Otherwise the outcome names the step of
`withload_compatX`'s route that did not port.

**The stop rule.**
- Gate first. If `StackOKBOfOK`, `InstStackOKB`, `PairGuardHoldsB`, `PVLStartB` or `LoadGateNilB` at
  `pairTy` fails, make no edit. Record the failing statement as an elaborating `def … : Prop` with
  its counterexample, if one exists.
- Re-prove in §4.5's order. Stop at the first row whose proof needs a definition change beyond §4.2's
  list. Record that row and the change it needs.

**The fallback.** If the stop rule fires after the edit:
- Revert the edits to `cRLM`, `SemSM`, `SemIdxM` and `SemSMC`, so the branch builds clean with every
  earlier result.
- Keep `Block.lean` and `GroundBlock.lean`, beside the relation and not in it, as `NEXT.md` §1.6's
  convention keeps a candidate.
- Record the frontier.

The suite then reports the pair and slice entries as NOT BUILT, with the frontier as the missing
lemma. If `OwnOKB`'s relaxed `placeFree` is what fails, use `OwnOKI`'s strict form for blocks, as
`NEXT.md` §1.6's fallback says. Then record that a callback holding a copy of the view has no block
push, and S5 stays route-blocked.

---

## 5. Order of work and the stop rule

1. (0): the doc edits, one commit.
2. (1): `GroundLedger.lean` (G1–G11), then `LEDGER.md`'s rows (§2.2–§2.8) and the rows table
   (§2.6), one commit.
3. (2): `GroundRegress.lean`: the producer lemmas, the gate, the seeds' derivations, the entries;
   then `LEDGER.md`'s suite section and results table, one commit.
4. (3): `GroundBlock.lean`'s gate, then the in-place edit and §4.5's re-proofs, then the suite re-run,
   one or more commits. Stretch: §4.6.
5. The outcome: `LEDGER.md` §results, CHECKPOINT, README.

**The stop rule.** (0)–(2) are done whatever (3) does. In (2), an entry whose proof does not close is
recorded NOT BUILT with its exact missing lemma; it does not stop the suite. No FAILS is recorded
without an arising configuration (§3.1).

---

## 6. Files

| file | contents |
|---|---|
| `GROUND.md` | this design |
| `LEDGER.md` | the ledger (§2) and the suite's results (§3), with the outcome |
| `ProbeD1/GroundLedger.lean` | G1–G11 and the floor's statements (`DraftFL`, `DraftFLNil`) |
| `ProbeD1/GroundRegress.lean` | the producer lemmas, the gate, the seeds, the entries |
| `ProbeD1/Block.lean` | the block's definitions (§4.2), imported by `R1.lean` |
| `ProbeD1/GroundBlock.lean` | the block's gate lemmas and the block gates (§4.4) |
| `ProbeD1/R1.lean` and the files of §4.5 | the in-place edit and its re-proofs |
| `ProbeD1.lean` | imports of the new files |

---

## 7. Report lists (to fill in the outcome)

- **Printed objects read.**
  - [TR] 6.150 (`TW.reb`, `wpTS_reborrow`) in the gates and the stretch.
  - [TR] 6.172–6.175's compatibility lemmas as the rows' routes (`withbor1_compatX`,
    `withload_compatX`, `withloadU_compatX`).
  - `fundamentalC` and `adequacyD` as the grounding theorems' sources.
- **Printed hypotheses unspent.** None expected. The unit proves no printed lemma; every statement is
  ProbeD1's, about the draft, and the printed objects are applied with every premise discharged.
- **Uniqueness and functionality results.** Expected used: `ResU.CompS.functional` in the gates. To
  report: whether the stretch reads 6.150's chooser determinacy.
- **Printed lemmas in the run-up that are untranscribed.** None for (0)–(2). For (3)'s stretch, the
  draft analog of 6.150 consumed through an own push is ProbeD1's own, not printed.
- **Hypotheses added.**
  - `FOArg`/`FlatTy`/`FOComp` and `NilTy`/`NilVal`/`NilComp` on the grounding theorems. Each is
    non-vacuous at the suite's types.
  - The gate's freshness hypotheses (`ρc.InStratum β`, `RecsOutside [β] ls`, `SubFresh δ β`,
    `β < ⊤`). The row's choice of `β` meets them.
  - On the block: §4.3's `OwnPushBOfMView` hypothesis.
- **Technique built.** The grounding theorems follow `vRLM_dataE`'s environment induction (G1) and
  `adequacyD`'s proof (G11). The stretch follows `withload_compatX` step for step.
