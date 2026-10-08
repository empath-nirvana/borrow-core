# ProbeD1: grounding the draft in Core — the design

This is the design for the unit after the guard-gap unit (`NEXT.md`, latest commit `3e84262`). It
plans four parts:
- **(0)** the doc fixes the guard-gap unit's content review asked for;
- **(1)** a grounding ledger (`LEDGER.md`, `GroundLedger.lean`): every ProbeD1 definition that has a
  Core counterpart, set against it, with a theorem wherever they are claimed to agree;
- **(2)** a regression suite (`GroundRegress.lean`, a section of `LEDGER.md`): every program
  theorem of `Core/`, classified, and each borrow-only program's obligation, `DraftFL` at every
  node of its derivation and at every index, with a status per node;
- **(3)** the block entry (`NEXT.md` §1.6, item 1b): the designed fix for the two-cell gap, built in
  place in the one draft relation, then the `withbor` (1) and `withload` rows attempted at the
  empty stack.

It contains no proofs. Every Lean block below elaborates against the built ProbeD1 (unchanged since
`3e84262`) with Core's program modules imported (`Core.Examples`, `Core.Folds`,
`Core.RecordPrograms`, `Core.FamilyPrograms`, `Core.BlockPrograms`, `Core.AffPrograms`,
`Core.ArrayPrograms`, `Core.Demonic`, `Core.IntPrograms`, `Core.CommonList`, `Core.Count`,
`Core.CountFree`, `Core.MapMut`, `Core.ReuseList`, `Core.Lists`, `Core.EmbeddingExamples`)
[checked outside the build: a scratch file, not committed]. The exception is the `vRLM` clause in
§4.2, which is a fragment. *[unchecked]* marks a claim argued in prose and not in Lean; *[read]*
marks a claim read off the source; *[expected]* marks a status the build has to confirm.

The rules are unchanged. Nothing breaks the borrow calculus: no printed BoLo definition is edited,
and nothing in `Core/`, `Paper/`, `Support/`, `GhostEnd/` or `Targets/` changes. Only ProbeD1's draft
may change, and only in part (3). The paper is not wrong. An obstruction is reported only as an
elaborating `def … : Prop` or as a configuration that arises with every hypothesis discharged
(DESIGN §11), `ArisesVI` included for views. There is no new relation family and no step index, and
multi-shot is ignored. Builds are targeted (`lake build ProbeD1`). There is no `sorry`, `axiom`,
`native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`, and every axiom set is within
`[propext, Classical.choice, Quot.sound]`. The regression entries use the named sub-derivations
Core already has, or rebuild one from the same constructors where Core builds it inside a proof;
nothing inverts `CDerives` (CLAUDE.md, *Growth discipline*).

---

## 0. On one page

**What grounding means here.** Borrow-only programs (ordinary closures, higher-order functions,
borrows without suspension) are proved in Core: `fundamentalC` (`Core/Fundamental.lean:434`) at
`σ = []`. The draft W must reproduce that. A gap on such a program is a defect of the draft, to be
fixed, never a restriction (the user's corrections of 2026-10-08, `NEXT.md` §10). The last unit found
one such gap by luck: `withload` of a pair of references. This unit makes the comparison systematic:
the ledger says where the draft's definitions differ from Core's, and the suite runs every Core
program through exactly those differences.

**The obligation is Core's fundamental lemma, node by node.** `fundamentalC` proves Core's semantic
judgement at every node of a derivation. Its analog for one program is `DraftFL` restricted to that
program's derivation: `SemSM .binder0` at every node, at every index (§3.1). The reading at the
empty stack (`SemSMNil`) is its corollary, not the obligation: no `Imm` view arises at the empty
stack except as a run's answer, so a refutation there could not pass DESIGN §11 [read: ledger A7].

**Four facts, read off the source, shape the design.**

1. **A program's root says nothing.** At a flat answer type, the draft's computation relation at
   the empty stack *is* Core's: `nilSoundRetM` (`R1Stmt0.lean:133`) proves one way, and the converse
   follows by the same `bodyS_nil_iff` and `vRLMData` (`CRLMRetNil`, planned). At every index a
   closed program's root is a first-order judgement, which G5 (fact 2) gives from Core's own
   proof, and no draft clause is read. So the content is at the other nodes of a derivation, where
   the draft reads its own clauses: the callbacks and closures a program builds, the constants it
   applies, and the glue between them (§3.1).

2. **At first-order judgements the draft is Core** [read; to be proved as G5, §2.9]. Take a
   judgement whose context types are first-order arguments (flat data, `Mut` and `Imm` leaves, and
   their products, sums, boxes, `Ref`s and families) and whose type is a first-order computation
   type with no lifetime `∀` and no row, its answers flat. There the draft's semantic judgement
   `SemSM .binder0` follows from `fundamentalC`, at every index (`CoreToSemSM`), whatever the
   derivation below it. The reasons:
   - W's leaves contain Core's (their first conjunct is Core's leaf);
   - W's flat types are Core's;
   - at `⊸`, `&` and `F`, `binder0` reads no future and no instantiation.

   The same holds of a term derived at a dead context at a thunk or persistent thunk of such a type
   (G5c): the `U` clause reads it at instantiated readings and the box at reserved-name pushes, and
   Core's derivation gives it at every reading that models `Δ`. Composed with the draft's proved
   `U`, `∀I` and `!U` rows (`statement0UFullM`, `allIRowMUFree0`), G5 is expected to put every
   first-order callback in the draft's relation (§3.2). If it does, the places where the draft can
   diverge from Core on a borrow-only program are these [read]:
   - **producer side**, where a value is shown to be in the draft's relation:
     - (i) a callback whose context holds a `U` value at the own push: the `∀I` row at a live `U`
       slot, not derived;
     - (ii) a persistent polymorphic value carried across the binder-named push:
       `VRLMStackRename`, stated, not derived;
   - **consumer side**, where a value in the draft's relation is used:
     - (iii) `∀E`, which reads the `∀` clause's first conjunct, and (E1) restricts that conjunct to
       instances in scope;
     - (iv) every higher-order constant's row, which must hand its callback the lend's argument at
       an own push, where the guard is read. That is where the two-cell gap lives;
   - **the glue** at judgements that are not first-order (`app`, `bind`, `letpair`, `lolliE`,
     `bangE`, … at a context holding a `U` or `!` slot, or at an answer holding a borrow leaf):
     (v) their rows, none stated (§2.6).

   The suite targets exactly these places.

3. **Core's own family and block borrows are nested single-place lends.** `withborF2`
   (`Core/Family.lean:69`) and `withborS` (`Core/BlockBorrow.lean:347`) borrow each leaf with its
   own `withbor` and shorten to the innermost lifetime. So they never meet the two-cell gap: at the
   inner push both places are lent, each by its own entry [read]. But their inner callback captures
   the user's callback, a linear `U` value (`Family.lean:62`, `:65`), so they need the `∀I` row at a
   live `U` slot. That row is therefore a floor obligation, not only tier 2. `swapBoth`,
   `readFamily`, `splitFour`, `blockSwap` and the other block programs are affected.

4. **The user's case already exists in Core, in user-written code, on both sides.** `countProg`
   (`Core/Count.lean:377`; `countProg_derives`, `:335`) builds `count : !U(∀'a. Imm 'a L ⊸ F N)`
   stage by stage.
   - The producer: `stepV` (`d_step`, `:178`) is a persistent lifetime-polymorphic function, made
     at a persistent context that holds the previous stage `g : countTy`.
   - The carry side: each stage's own callback `cbE` (`d_cb`, `:124`) and the program's borrower
     (`d_borrowerE`, `:288`) capture `g` and call `g [] t` at the callback's own lifetime.

   The fold programs (`countFoldProg`, `anyTreeProg`, `Folds.lean:375`, `:469`) exercise the
   carry side only: their `g` is `foldImm countAlg`, a constant, whose producer row is
   `FoldImmRowM`. `corpus/array-get.bc`'s `read` is declared `all 'z < top. imm 'z i32 => i32`, with
   no `!`, so it is not a persistent value carried into a callback [read]. No new program is
   needed for this seed (§3.6).

**The plan.**
- (0) Correct README, DESIGN §15.10, `NEXT.md` §9–§10 and the box's Lean docstrings to match
  CHECKPOINT's warning box, with OQ-8 (d) reported against both of DESIGN §12.2's readings (§1).
- (1) The ledger, rows and theorems (§2), with the existing agreement statements, the older arising
  set and the superseded relations among the rows.
- (2) The suite (§3): every program theorem of `Core/` classified; every borrow-only program's
  nodes, at every index, at the current relation.
- (3) The block, built in place, gate first, then rebuilt; the rows `Withbor1NilRowM`,
  `WithloadNilRowM` and `WithloadUNilRowM` attempted; the suite re-run (§4). The block's forward
  obligations at the `F_Σ` clause are carried (§4.2).

(0)–(2) must be done even if (3) does not close (§5).

---

## 1. Part (0): the doc edits

Each edit replaces the passage at the lines given (at `3e84262`; README, DESIGN, NEXT and the Lean
files are unchanged since) with the text shown. Each one carries one finding of CHECKPOINT's second
warning box (`CHECKPOINT.md:72–119`):
- (a) the `!` clause is not fixed;
- (b) `withloadUPairGapNilE1`'s view is not shown to arise;
- (c) the box's pushes are a new reach of the `!` clause;
- (d1) "real" holds for [TR] 6.175's route;
- (d2) what `reconB′` owes is unchecked until it is typed.

OQ-8's (d) is reported against both of DESIGN §12.2's readings, in README (R5), DESIGN (D5) and
NEXT (N7), each report written out.

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
      - (d), reported against both of DESIGN §12.2's readings:
        - **The design's reading** (was a clause changed to reach a stack other than its own by
          something other than `FutQ`?). Yes: `vRLM`'s `!` clause gained the persistence box. It
          reads a persistent thunk at every instantiation of the stack and at own pushes at the
          empty resource under reserved names (`NsVar`), not through `FutQ`. The reserved-name
          pushes are a new reach of the clause, beyond `FutQ` and beyond the type it reads.
          Statement 0 does not hold at `binder0`, with the box or without it: its monotonicity
          facts are refuted as stated at `gd`, a configuration not shown to arise
          (`monoUnrestrictedRefuted0`), and their consumer form waits on the `∀I` row
          (`Statement0MAtConsumers0`). So (d) has not occurred. If statement 0 comes to hold only
          with the box, (d) under this reading applies.
        - **The synthesis's wording** (was `OwnPush` at `U` needed, and how did `MonoOwnG` come
          out?). `binder0` has no own push at `U` (`uOwn .binder0 = false`); its own push is the
          `∀` clause's. `MonoOwnG` at that push is not derived. Unrestricted
          (`MonoOwnGM .binder0`) it is refuted at `gd`, not shown to arise
          (`monoUnrestrictedRefuted0`). Its restrictions are proved at contexts whose live slots
          reach no `U` (`monoOwnGUFreeMA`, which `allIRowMUFree0` reads) and, at persistent
          contexts, across pushes under reserved names (`monoOwnGMAtBoxN`). It is not derived at a
          live `U` slot, nor at the binder-named push at a persistent context (`VRLMStackRename`,
          stated). No push was made a future: `binder0` reads none.
      - The fallback is not triggered.

**R6. Files table (`:450–500`).** Add rows for `GROUND.md`, `LEDGER.md`, `ProbeD1/GroundLedger.lean`,
`ProbeD1/GroundRegress.lean`, `ProbeD1/Block.lean` and `ProbeD1/GroundBlock.lean`, once they exist.

**R7. `:385–387`** (finding c). Replace the box bullet "The persistence box. `vRLM`'s `!` clause
reads a persistent thunk at every world `binder0`'s order reaches from the stack: …" with:

    - The persistence box. `vRLM`'s `!` clause reads a persistent thunk at every instantiation of
      the stack, every list kept outside, and every finite sequence of own pushes at the empty
      resource under reserved names (`NsVar`). The pushes are a new reach of the `!` clause: no
      `binder0` clause pushes under a reserved name.

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
      - (d), reported against both of §12.2's readings:
        - **The design's reading.** A clause was changed to reach stacks other than its own by
          something other than `FutQ`: the `!` clause's box, at instantiations and at own pushes at
          the empty resource under reserved names. `binder0`'s `U` clause makes the
          instantiations; its `∀` clause's push is at the type it reads, named by its binder, so
          the reserved-name pushes are a new reach of the `!` clause. Statement 0 does not hold,
          with the box or without it (`monoUnrestrictedRefuted0` at `gd`, not shown to arise; the
          consumer form waits on `AllIRowM .binder0`), so (d) did not occur. If statement 0
          comes to hold only with the box, (d) under this reading applies to it.
        - **The synthesis's wording.** `OwnPush` at `U` was not needed: `binder0` has no own push
          at `U`. `MonoOwnG` at the `∀` clause's push is not derived: refuted unrestricted at `gd`,
          not shown to arise (`monoUnrestrictedRefuted0`); its restrictions proved at contexts
          reaching no `U` (`monoOwnGUFreeMA`, read by `allIRowMUFree0`) and at persistent contexts
          across reserved-name pushes (`monoOwnGMAtBoxN`); not derived at a live `U` slot or at the
          binder-named push (`VRLMStackRename`, stated). No push was made a future.
      - The fallback is not triggered.
      - Under the corrections, these are open on borrow-only programs, and the draft's to close if
        they fail: the two-cell gap on [TR] 6.175's route (item 1b), and the `!` clause at the
        binder-named push (`VRLMStackRename`, stated, not derived).

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
    reads. The two reports:
    - **Under DESIGN §12.2's reading**: a clause was changed, the `!` clause, by the box. The box was
      made to answer correction (i). Statement 0 does not yet hold, with the box or without it, so
      (d) has not occurred. If statement 0 comes to hold only with the box, (d) under this reading
      applies to it.
    - **Under the synthesis's wording**: `binder0` has no own push at `U`. `MonoOwnG` at the `∀`
      clause's push is not derived. Unrestricted it is refuted at `gd`, not shown to arise
      (`monoUnrestrictedRefuted0`). Its restrictions are proved at contexts reaching no `U`
      (`monoOwnGUFreeMA`, read by `allIRowMUFree0`) and at persistent contexts across
      reserved-name pushes (`monoOwnGMAtBoxN`). It is not derived at a live `U` slot or at the
      binder-named push (`VRLMStackRename`, stated). No push was made a future.

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

**N9. `:2630–2632`** (finding c). Replace the `PBox` bullet with:

    - `PBox A δ σ αs P` holds at a thunk type when `P` holds at every instantiation of the stack
      (`InstAt`), every list kept outside the instantiated lifetimes, and every finite sequence of
      `BoxStep`s from there. At every other type it is `True`. The `BoxStep`s are a new reach of
      the `!` clause: no `binder0` clause pushes under a reserved name.

### 1.4 The box's Lean docstrings

The same wording as D1 (finding c), in the files that carry it. These are comment-only edits, made
in part (0)'s commit; `lake build ProbeD1` confirms that no statement changed.
- **L1. `R1Box.lean:4`.** The module title: "a persistent thunk at every world of `binder0`'s
  order" becomes "a persistent thunk at every instantiation and every reserved-name push".
- **L2. `R1Box.lean:6–8`.** "`vRLM`'s `!` clause reads a persistent thunk at every world
  `binder0`'s order reaches from the stack (`PBox`, `R1.lean`): every instantiation of the stack,
  …" becomes "`vRLM`'s `!` clause reads a persistent thunk at every instantiation of the stack,
  every list the instantiated lifetimes keep outside, and every finite sequence of own pushes at
  the empty resource under reserved names (`PBox`, `BoxStep`, `R1.lean`). No `binder0` clause
  pushes under a reserved name: the pushes are a new reach of the `!` clause."
- **L3. `R1.lean:116`** (`BoxStep`). "One step of `binder0`'s world order at a persistent value"
  becomes "One step of the persistence box".
- **L4. `R1.lean:149`** (`vRLM`). "a persistent thunk is read at every world of `binder0`'s order"
  becomes "a persistent thunk is read at every instantiation and every reserved-name push".
- **L5. `R1.lean:427`** (`PersistentBoxed`) **and `R1Thaw.lean:765`.** "at every world of
  `binder0`'s order" becomes "at every instantiation and every reserved-name push".

### 1.5 The notes that point at these edits

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
- **Statuses** of a statement the ledger cites: *stated*, *proved*, *planned*, or *refuted at a
  configuration not shown to arise*. The last is a fact about the statement (DESIGN §11), not a
  disagreement on a program.
- **No overclaim.** `LEDGER.md` writes "agrees" or a direction only where a named theorem proves it.
  Every planned theorem below is marked *planned*, and stays so until it is proved. A relationship
  argued without a theorem is marked [read] or [unchecked].
- **Paths.** Draft lines are `experiments/ProbeD1/ProbeD1/`, Core's `Core/`, GhostEnd's
  `experiments/GhostEnd/GhostEnd/`, and Targets' `experiments/Targets/Targets/`, unless a row names
  the file in full.

### 2.2 Rows: the relation's clauses

All draft lines are `R1.lean`; all Core lines are `Core/Relation.lean` unless named.

| # | draft | Core | at `σ = []` | at `σ ≠ []` | theorem | what a disagreement means for programs |
|---|---|---|---|---|---|---|
| C0 | `WInsideCoreM`, `CoreInsideWM` (`:849`, `:856`): the two agreement facts at every stack and every type, with the index hypotheses (`StackOK`, `TabAtS`, `PlaceViewsL`; and `OuterBelowTop`, `RecsOutside` for the second) | `vC` at `extS δ σ αs` | at `NilTy` both are G3 (planned) | stated, not attempted (`R1MONO.md` §2.6 and `:1914`; `NEXT.md:1404`). G2 is `WInsideCoreM` restricted to first-order arguments, and G1 is both restricted to flat types, the index hypotheses unused (`GRestrict`). G4 is `CoreInsideWM`'s analog at first-order computation types; G4 does not give `CoreInsideWM` at `U C` at a non-empty stack [read: the `U` clause reads instantiated readings, where Core's relation of a value known at one reading is not given, C1] | `GRestrict` (planned, definitional); G1, G2 (planned) | a `⊸` hands a draft argument to Core's clause (W inside Core) and reads its answer back (Core inside W). Outside first-order types neither is known, so a consumer that moves a value between the two relations is covered only there |
| C1 | `vRLM` `U` (`:152`) | `vCE` `U` (`:127`) | Core ⊆ draft, given bodies: the draft reads the body only at extensions that keep the tags (`KeepsT`, `BinderJ.lean:49`); the only instantiation of `[]` is the identity (`instAt_nil_eq`, `GapPos.lean:87`); the guard is trivial | incomparable: instantiations at the stack's cut, views handed back, `guardPV` | `VRLMThunkNil`, `CoreSubWNil` (planned) | at `[]` every Core thunk with a first-order body is a draft thunk; at a stack only thunks with a Core derivation are shown (§3.2) |
| C2 | `vRLM` `⊗`, `⊕`, `[@a]`, `Ref`, `[L]` (`:159`, `:161`, `:166`, `:168`, `:183`) | `:121`, `:124`, `:131`, `:132`, `:149` | same clause | same clause, leaves at `extS δ σ αs` | inside `VRLMFlat` (planned) | none |
| C3 | `vRLM` `!` (`:164`) | `:130` | draft ⊆ Core given the payload (`PBox` added at a thunk payload); equal at a non-thunk payload | the same | `VRLMBangNil` (planned) | a persistent thunk must hold at every box world (divergence D4) |
| C4 | `vRLM` `Mut`, `Imm` (`:170`, `:174`) | `:137`, `:134` | equal: `CohS` and `RetainedPay` hold at `[]` | draft ⊆ Core: Core's leaf, plus `CohS` and `RetainedPay` | `VRLMNilTy`, `VRLMFOArg` (planned) | a consumer at a pushed stack must establish `CohS` and `RetainedPay` for the arguments it hands over (D7) |
| C5 | `vRLM` type variable (`:178`), environment `WEnt` (`:72`) | `:143`, `TEnt` (`:72`) | candidates; W's drop the mode and the list | the same | `EnvCore` (`R1.lean:1363`), used by `vRLMDataE` | none at data |
| C6 | `vRLM` `μ` (`:179`) | `:144` | equal at data (`vRLMDataE`, `R1Stmt0.lean:48`); at flat types, planned; with a thunk inside, not stated | the same | `VRLMFlat` (planned) | W reads a thunk inside `μ` with its own `U`; after (E1) the adjacency closure is a draft value (`muAdjVRLME1`) |
| C7 | `vRLM` default: `1`, `0`, `Unk`, `int`, `opq` (`:186`) | `:120`, `:123`, `:140–142` | equal | equal at `extS` | by definition | none |
| C8 | `cRLM` `F` (`:192`) | `cC` `F` (`:155`) | same clause (`wpTS`); equal at a flat answer | same clause | `CRLMRetNil` (planned; `nilSoundRetM` is one direction at data) | none |
| C9 | `cRLM` `F_Σ` (`:193`) | `cC` `F_Σ` (`:165`) | equal at a flat answer (`bodyS_nil_iff`, `GhostEnd/Stacked.lean:476`) | GhostEnd's piece (a stop ghost-ends entries): no Core counterpart | `CRLMRetNil` (planned) | effectful callbacks at a pushed stack read the piece (out of this suite, §3.7); after the block it splits a block (D12, §4.2) |
| C10 | `cRLM` `⊸` (`:201`) | `cC` `⊸` (`:156`) | same clause; `guardPV` trivial | same clause plus `guardPV` at the stack | `CRLMArrNil`, `GuardPVNil` (planned) | a call at a stack needs the table and views of the composite (D9) |
| C11 | `cRLM` `&`, `⊤`, `ν` (`:206`, `:209`, `:220`) | `:158`, `:160`, `:163` | same clause; `ν` is Core's at `extS` | the same | by definition | none |
| C12 | `cRLM` `∀` (`:210`) | `cC` `∀` (`:161`) | incomparable: the first conjunct reads only instances in scope ((E1), `InScope`, `:95`), and the own-lend conjunct (`OwnPushM`, `:101`) has no Core counterpart; at the top level the first conjunct reads nothing (`inScope_top_none`, `NxFloor.lean:40`) | the same | `CRLMAllNil`, `CRLMAllTop` (planned). Core's `∀` alone: it reads the room between lifetimes, holding at a `mut` cell adjacent to `⊤` and failing at one at `2` (`coreAllAdjacent`, `GapWitness.lean:127`), and it is not invariant under an embedding that opens the room (`coreAllNotNatural`, `:150`); it does not imply reading (A) (`CutAllC`) at `σ = []` (`not_coreAllImpCutAll`, `:156`). All three proved (statements `Gap.lean:289`, `:296`, `:303`) | every borrow callback is checked at its own push: producer side shown for first-order callbacks (G5 with the rows); consumer side is the gate (§3.3) (D1, D2). `GAP.md:470` records the Core ⇒ W half of agreement failing at the witness's type once W's `∀` at `σ = []` is read as `CutAllC` [unchecked identification]; at `vRLM`'s (E1) clause the witness is not stated |
| C13 | `effRetM` (`:223`) | `effRet` (`:176`) | same clause | same clause | by definition | none |
| C14 | `gSepRLM`, `gRLM` (`:231`, `:240`) | `gSepC`, `gDenC` (`:218`, `:224`) | same clause | same clause | by definition | none |
| C15 | `SemSM` (`:246`) | `SemC` (`:228`), `SemJ` (`Fundamental.lean:429`) | incomparable as definitions: `SemSM` adds `BindersLow`, `Scoped`, `SubDom` and the index; at `[]` the index holds | the same | `SemSMNilOfSemSM`, `CoreToSemSM` (planned) | Core's judgements at first-order types are the draft's at every index |

### 2.3 Rows: world, index, guard

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| W1 | `Stk`, `LEnt`, `LStack` (`World.lean:53`; `GhostEnd/Stacked.lean:99`, `:107`) | none: Core is `σ = []` | draft-only (§2.7) | — | — |
| W2 | `guardPV` (`Binder.lean:164`), `TabAtS` (`GhostEnd/Stacked.lean:290`), `PlaceViewsL` (`Binder.lean:144`) | `TW` read pointwise: `TabOfTWPointwise`, `HeldUnderTW` (`Statement1.lean:125`, `:119`); `TW`'s run invariant: statement 1's per-transition facts (`TabNil` … `TabResume`, `Statement1.lean:43–100`) | pointwise, the table is not read off one `TW` world: `TabOfTWPointwise` fails at `innerView` (DESIGN §5.2, §11), whose world is a `TW` world (`tw_innerView`, `GhostEnd/Below.lean:120`) and fails the table at `[x]` (`not_tabAtS_innerView`, `GhostEnd/Arising.lean:130`), at a configuration not in `Arises` (`wpG_below_not_arises`, `:139`): a fact about the pointwise statement. As a run invariant, `TabRelend` is proved (`tabRelend`, `Thunk.lean:185`) and the other eight facts are stated. Trivial at `[]` | `NotTabOfTWPointwise` (planned, cheap: the three GhostEnd facts); `GuardPVNil` (planned; from `pvlNil`, `BinderPV.lean:358`) | at a stack the guard restricts every call (D9); a guard proved only pointwise from `TW` is not available, and the transitions' facts are the route |
| W3 | `CohS` (`Binder.lean:178`) | `CohE` (`Relation.lean:57`) | different objects: a view tied to its lending entry, an `imm` cell tied to a record; `CohS` vacuous at `[]` | inside `VRLMNilTy` (planned) | D7 |
| W4 | `OwnPushM`, `OwnOKI` (`R1.lean:101`, `Binder.lean:194`, `:200`) | Core's `∀` instance (`Relation.lean:161`); 6.64/6.65's lend start (`TW.immFrame`, `TW.mutFold`, `World.lean:115`, `:135`) | not stated: the own push reads an instance as a lend | — | the single-place entry (D2) and `placeFree` (D3) |
| W5 | `Inst`, `InstAt`, `RelendJ` (`Binder.lean:314`, `:346`; `BinderJ.lean:53`) | Core's `U` quantifier over `Ext` (`Relation.lean:127`) | at `[]` `RelendJ` is Core's `U` with `KeepsT` added | `RelendJNil` (planned) | D8 |
| W6 | `KeepsT` (`BinderJ.lean:49`) | `Keeps` (`FrameRecords.lean:156`, `Ext`'s first conjunct, `:172`) | draft ⊆ Core: a record kept with its tag is kept | `KeepsTKeeps` (planned, one line) | D8 |
| W7 | `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `OuterBelowTop`, `cutOf` (`Binder.lean:250`, `:280`, `:285`, `:265`, `:242`, `:227`) | [TR] 6.64/6.65 H4's fresh lifetime; nearest Core object `TW.reb`'s `StratumLe` (`World.lean:92`, `:122`) | draft-only bookkeeping (§2.7) | — | — |
| W8 | `PBox`, `BoxStep` (`R1.lean:121`, `:133`) | none: Core's `!` is `ρ = ∅ ∧ vC true A` | draft-only (§2.7) | — | D4, D5 |
| W9 | `StackJM`, `BindersLow`, `Scoped`, `SubDom` (`R1.lean:108`; `Sem.lean:66`, `:74`, `:78`) | `Scoped` ↔ `VScoped`; `Δ.Models` | `Scoped` is `VScoped` at the judgement [read]; the others draft-only | — | a judgement binding a reserved name (`NsVar`) is outside `SemSM` (vacuous there) |
| W10 | `vwEW`, `vwSW`, `vwSL` (`Binder.lean:121`, `:125`, `:159`) over GhostEnd's `vwE` (`Stacked.lean:122`) | `ptoImmS`, `ptoMutS` (`Relation.lean:51`, `:43`) | the views read an `imm` payload at `vC true`; Core's `Imm` leaf at `vC false` | — | at a payload holding a thunk the views ask more (D11) |
| W11 | `WP p` (`Sem.lean:119`): W as a `Targets.SemWorld`; `Fam := TW ∧ Tagged ∧ StackOK`; `val`/`comp` read `vRL`/`cRL` | `Targets.coreW` (`experiments/Targets/Targets/I/World.lean:165`): `Fam := TW ∧ Tagged`, `val`/`comp` Core's | stale: it reads statement 0's relation `vRL`, not `vRLM`; at the index `([], [])` its `Fam` is Core's [read] | — | Targets' interface statements (`SemW`, `FL`) are not stated at the current draft; nothing in this unit reads `WP` |

### 2.4 Rows: arising against the typed world

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| A1 | `ArisesI` (`Binder.lean:582`) | `TW` (`World.lean:110`), `Tagged` (`:171`) | the arising set's worlds are tagged `TW` worlds (draft ⊆ Core, worlds); at `[]` every tagged `TW` world arises (Core ⊆ draft); so at `[]` the two coincide as world sets | `ArisesITW`, `ArisesINilOfTW` (planned) | a refutation at `[]` needs nothing beyond Core's arising |
| A2 | `ArisesI.lendImm`, `LendImmI` (`Arising.lean:106`; `Binder.lean:576`) | `TW.immFrame` (`World.lean:115`) | `LendImm` carries `TW.immFrame`'s premises, the push, and H4's freshness (`LendFresh`, `α < ⊤`) | inside `ArisesITW` | — |
| A3 | `ArisesI.lendMut`, `LendMutI` (`Arising.lean:88`; `Binder.lean:571`) | `TW.mutFold` (`World.lean:135`) | the same | inside `ArisesITW` | — |
| A4 | `RunEnd` (`Arising.lean:73`) | `wpTS`'s run conjuncts (`World.lean:186`) | `RunEnd` transcribes them at a fixed configuration [read] | `RunEndOfWpTS` (planned, optional) | — |
| A5 | (none) | `TW.immEnd`, `TW.mutUnfold` (`World.lean:151`, `:140`) | not stated: `ArisesI` has no lend-end transition; lends end only inside runs | — | configurations after a lend ends are reached only through `run` |
| A6 | (no transition) | `TW.reb`, `rebDeep`, `rebEnd`, `rebEndDeep` (`Core/World.lean:122`, `:128`, `:157`, `:162`); `wpG_reborrow` (`Core/Reborrow.lean:232`) | not stated: `ArisesI` has no reborrow transition, and lends end only inside runs. The gate's witness uses `TW.reb` inside a world (`withloadUPairGapReal`). `LendRebI` is designed (`NEXT.md` §1.6), not built. Statement 2 transcribes 6.150 at a resuming table, at Core's relation: the view `rebView`, one unfolding `rebF`, its least fixed point `RebRelend`, the payload input carried along `Ext` `RCarried`, the record kept on the table's resumption lists `TabKeepsRec`, the lift `RebFrameR`, and `RebChooserNonVacuous` (`Statement2.lean:67`, `:75`, `:84`, `:94`, `:103`, `:116`, `:130`): all stated, none proved | — | a configuration inside `withload`'s callback with its push on the stack is not in `ArisesI`; a refutation there cannot pass DESIGN §11. `RebFrameR` is the lift a spanning `withload` row reads (statement 2), not this suite |
| A7 | `ArisesVI` (`Binder.lean:598`) | none: Core quantifies over all values in `TW` worlds | draft-only (refutation check) | — | at `[]` no `Imm` value arises except a run's answer, so a refutation at `[]` of an open judgement with a borrow-typed context cannot pass DESIGN §11 |
| A8 | `Arises`, `ArisesV`, `ArisesCtx` (`Arising.lean:134`, `:158`, `:175`); `ArisesAt` (`:53`); `ArisesNonVacuous` (`:186`) | `TW`, `Tagged` (through `nil` and `ArisesAt`) | the first arising set, superseded by `ArisesI`, whose lends carry `LendFresh` and `α < ⊤`: each `ArisesI` constructor is an `Arises` one with a stronger premise, so `ArisesI ⊆ Arises` and `ArisesVI ⊆ ArisesV` [read]. `ArisesAt` is the pointwise consequence: a tagged `TW` world, `StackOK`, the 6.64 entries among the records, the 6.65 places `mut` cells, the table | `ArisesIArises` (planned, cheap) | none: refutations read `ArisesI` (DESIGN §11) |
| A9 | `ArisesSound` (`Statement1.lean:112`): every `Arises` configuration has `ArisesAt` | `TW` (through `ArisesAt`) | stated, not proved; used only to exclude a witness, never to admit one | — | none |

### 2.5 Rows: judgement, typing, statement 0, adequacy

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| J1 | `ProbeRules` (`Rules.lean:31`) | `CDerives` (`Core/Fundamental.lean:60`); Targets' `CDerivesNU` (`experiments/Targets/Targets/Base/Typing.lean:82`) | `CDerivesNU` ⊆ `ProbeRules` (through `ExtendsNU`'s `Tier1SubNU`); `CDerivesNU` ⊆ `CDerives` (`CDerivesNU.toCDerives`, `Typing.lean:395`); `ProbeRules` ⊄ `CDerives` (the spanning rules); judgements with resuming `unr` operations are not in `ProbeRules` (multi-shot ignored) | `ProbeRulesOfNU` (planned) | every `CDerivesNU` program is a `ProbeRules` program. A Core program whose `CDerives` derivation uses none of the five effect rules is built by the same constructors as a `CDerivesNU` one [read], but no theorem converts it, since nothing inverts `CDerives`. So the arising check of a Core program (DESIGN §11, item 2) rebuilds its derivation in `CDerivesNU` or `ProbeRules`, as `PairWithloadUTyped` does |
| J2 | statement 0 (`Statement0M`, `R1.lean:1444`; `statement0MBesideMono0`, `R1Stmt0.lean:447`) and the other draft rows | `fundamentalC` (`Fundamental.lean:434`) | the draft has rows at `force`, `thunkF`, `thunkV`, `!` (with `PersistentBoxed`), `∀I` (contexts reaching no `U`), `roll`, `unroll`; Core proves all 89 constructors; no theorem relates the two | `DraftFL` and `DraftFLNil` (stated, the floor); `CoreToSemSM` (planned: the floor at first-order judgements) | §2.6 lists the rows |
| J3 | `semTyping`, `GenSelfAccepted`, `ReconAccepted` (`Programs.lean:38`, `:42`, `:46`) | Targets' `AcceptedAt` (`experiments/Targets/Targets/I/Programs.lean:259`); `adequacyD` | `semTyping` reads `SemS` (`Sem.lean:102`), statement 0's relation `vRL`, not the current draft `SemSM`: stale [read] | — | statement 5's acceptance is not stated at `vRLM` |
| J4 | (no adequacy theorem) | `adequacyD` (`Demonic.lean:312`), `adequacyD_obs` (`EffPrograms.lean:41`), `theorem32D` (`Demonic.lean:292`) | draft acceptance at `[]` at `F 1` gives Core's adequacy | `AdequacyNilM` (planned) | the draft's floor inherits safety and termination at `[]` |
| J5 | `NilSoundRet`, `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` (`Statement0.lean:95`, `:154`, `:161`, `:167`, `:173`, at `vRL`); `NilSoundRetM` (`R1.lean:1383`) | OQ-58 (a) | at `vRLM` only `NilSoundRetM` is stated and proved; the others are at statement 0's relation, not attempted | `CRLMRetNil`, `CoreSubWNil` restate the usable part at `vRLM` (planned) | OQ-58 at `vRLM` is answered only at first-order types; the `vRL` statements are among the superseded relations' claims (§2.10) |
| J6 | `DraftFLEmbed` (planned, stated in `GroundLedger.lean`) | `embed` (`Core/Embedding.lean:235`), `adequacy_of_derivesWf` (`:326`) | the floor at BoLo's image: a `DerivesWf` derivation, embedded, is the draft's at every index; not attempted | — | the paper's own programs (`Core/EmbeddingExamples.lean`) are its instances (§3.4) |

### 2.6 The rows against `fundamentalC`

`LEDGER.md` gives one line per `CDerives` constructor (89, `Fundamental.lean:60–372`), with the
compatibility lemma `fundamentalC` applies (`:437–560`) and the draft row. The builder takes the
constructor list and lemma names from those lines. Their file and line come from a grep of
`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/EffBorrow.lean`, `Core/Slices.lean`,
`Core/FoldImm.lean`, `Core/EffRules.lean` and `Core/Nu.lean`.

A draft row is its constructor's statement at `SemSM .binder0`. It is read at a judgement that is
not first-order; at a first-order judgement G5 gives the node from Core, and at a first-order
constant G5c does. A row adds, as named hypotheses, the `BindersLow` and `Scoped` facts of its
premises' types that its conclusion's do not give, as `AllIRowMAt` adds the binder's freshness
[unchecked: which rows need them]. The rows the suite names:

| Core rule (lemma) | draft row | status at `3e84262` |
|---|---|---|
| `force` (`force_compatC`) | `ForceRowM` | proved (`forceRowM`, `R1Stmt0.lean:367`) |
| `thunkF`, `thunkV` (`thunkF_compatC`, `thunkV_compatC`) | `ThunkFRowM`, `ThunkVRowM` | proved (`statement0UFullM`, `R1Box.lean:579`) |
| `bangThunkF`, `bangThunkV` | `BangThunkFRowM`, `BangThunkVRowM` | proved with `PersistentBoxed` (`statement0UFullM`) |
| `allI` (`allI_compatC`) | `AllIRowMAt` | proved at contexts reaching no `U` (`allIRowMUFree0`, `NxAllI.lean:209`); open at a live `U` slot (D6) and at a persistent `!U` slot, whose push is binder-named (`VRLMStackRename`, D5) |
| `roll`, `unroll` | `RollRowM`, `UnrollRowM` | proved (`rollRowM`, `unrollRowM`, `NxUnroll.lean`) |
| `ret`, `ofRet` | the identity (`jdgCty`) | trivial, not stated |
| `var` (`var_compatC`) | `VarRowM` | not stated; [read: the slot's relation is the answer's, through `wpTS` at a value] |
| `lam` (`lam_compatC`) | `LamRowM` | not stated; `LamRow` (`Statement1.lean:134`) is at the superseded `SemS` (§2.10) |
| `app` (`app_compatC`) | `AppRowM` | not stated; reads the `⊸` clause's `guardPV` at the index (D9) |
| `bind` (`bind_compatC`) | `BindRowM` | not stated |
| `tensorE` (`tensorE_compatC`), `letpair` | `LetPairRowM` | not stated |
| `allE` (`allE_compatC`) | `AllERowM` | not stated; reads the `∀` clause's first conjunct at an instance in scope, whose step is `InScopeOfInterp` (`Nx.lean:396`, stated) (D1) |
| `allEV` (`allE_compatX`) | `AllEVRowM` | the same |
| `bangE` (`bangE_compatC`) | `BangERowM` | not stated; [read: the `!` clause's second conjunct is the answer] |
| `lolliE` (`lolliE_compatX`) | `LolliERowM` | not stated; reads the `⊸` clause with its `guardPV` (D9) |
| `boxI` (`boxI_compatC`) | `BoxIRowM` | not stated |
| a constant whose answer holds a `Mut` or `Imm` leaf (`copy` at `Imm`, `arrGet`, `arrCopy`, the slice operations), and `immSub`, `mutSub` | `<rule>RowM` by name | not stated; the answer's leaves owe `CohS` and `RetainedPay` at the index (D7) |
| the other structural rules (`unitI`, `tensorI`, `sumI₁`, `sumI₂`, `withI`, `proj₁`, `proj₂`, `topI`, `unitE`, `sumE`, `zeroE`, `boxE`, `copyBang`, `forgetBang`, `nuIn`, `nuOut`) | `<rule>RowM` by name | not stated |
| first-order constants (`alloc`, `free`, `swap`, `forgetImm`, `forgetMut`, `forgetUnk`, `lit`, `hostOp`, `arrSize`, `arrReplace`, `arrLen`, `arrForget`) at first-order payloads, and any term Core derives at a dead context at a first-order thunk type | — | G5c (planned) |
| `withbor1`/`2`/`3` (`withbor*_compatX`) | `Withbor1RowM`, `Withbor2RowM`, `Withbor3RowM`; consumer facts `CallbackExt*M` (`.arr` shape), `CallbackExt*MF` (thunked) | rows not attempted; `.arr`: proved (`callbackExt*M_own`); thunked: stated (`Nx.lean:466`, `:483`); `Withbor1NilRowM` attempted in (3) (§4.6) |
| `withload` (`withload_compatX`) | `WithloadRowM`; its draft step the gate (§3.3) | not attempted; `WithloadNilRowM` attempted in (3) |
| `withswap` (`withswap_compatX`) | `WithswapRowM` | not stated |
| `foldImm`, `foldOwn`, `foldReuse` | `FoldImmRowM`, `FoldOwnRowM`, `FoldReuseRowM` | not stated |
| `unfoldN` (`unfold_compatX`) | `UnfoldNRowM` | not stated |
| `arrNew`, `arrFree`, `countFold`, `countTry`, `boundedFix` (higher-order: a `!U` argument) | `<rule>RowM` by name | not stated |
| `withbor*U`, `withloadU`, `sliceBorrow*U` | `SpanW1Row`, `SpanW2Row`, `SpanLoadRow` (at `SemS`, §2.10); at the empty row `WithloadURowM` | not attempted; `WithloadUNilRowM` attempted in (3) |
| `sliceBorrowM`, `sliceBorrowI` | `SliceBorrowMRowM`, `SliceBorrowIRowM` | not stated; the gate `SliceGateNil` (§3.6) |
| `effSub`, `effPerform`, `effRaise`, `effLet`, `effThen`, `effHandle` | `ThenRow` (at `SemS`); the rest not stated | the effect rules: the next suite (§3.7) |

```lean
/-- `[var]` at `SemSM`. -/
def VarRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (i : Nat) (A : VTy),
    Ctx.SoloP Γ i A → SemSM (ℍ := ℍ) .binder0 Δ Γ (.var i) (.val A)

/-- `[lam]` at `SemSM`. -/
def LamRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy) (C : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ (⟨A, true⟩ :: Γ) M (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam M)) (.comp (.arr A C))

/-- `[app]` at `SemSM`. -/
def AppRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M : Expr) (i : Nat) (A : VTy) (C : CTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ M (.comp (.arr A C)) →
    Ctx.SoloP Γ₂ i A → SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.var i)) (.comp C)

/-- `[bind]` at `SemSM`. -/
def BindRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N : Expr) (A : VTy) (C : CTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ M (.comp (.ret A)) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨A, true⟩ :: Γ₂) N (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app (.val (.lam N)) M) (.comp C)

/-- `[⊗E]` (`letpair`) at `SemSM`. -/
def LetPairRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γp Γb : Ctx VTy) (V M : Expr) (A B : VTy) (C : CTy),
    Ctx.SplitP Γ Γp Γb → SemSM (ℍ := ℍ) .binder0 Δ Γp V (.val (.tensor A B)) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.letpair V M) (.comp C)

/-- `[∀E]` at `SemSM`. -/
def AllERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (x : LifeVar) (b a : Lifetime.Life) (C : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ M (.comp (.all x b C)) → Δ.EntailsLt a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))

/-- `[∀E]` call-by-value (`allEV`) at `SemSM`. -/
def AllEVRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (x : LifeVar) (b a : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (VTy.all x b A)) → Δ.EntailsLt a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))

/-- `[!E]` (dereliction) at `SemSM`. -/
def BangERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.bang A)) → SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A)

/-- `[⊸E]` call-by-value (`lolliE`) at `SemSM`. -/
def LolliERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (f a : Expr) (A B : VTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ a (.val A) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ₂ f (.val (.lolli A B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app f a) (.val B)

/-- `[]I` at `SemSM`. -/
def BoxIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A) → CtxOutlives Δ Γ a →
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.box a A))

/-- `withbor` (1) at `SemSM`, at every index (`withbor1_compatX`'s statement). -/
def Withbor1RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    VScoped Δ A → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))

/-- `withbor` (2) at `SemSM`. -/
def Withbor2RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))

/-- `withbor` (3), the reborrow of a `Mut`, at `SemSM`. -/
def Withbor3RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ →
    Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))

/-- `withload` at `SemSM`, at every index (`withload_compatX`'s statement). -/
def WithloadRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))

/-- `withload` at its unwinding type at the empty row, at `SemSM`. -/
def WithloadURowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B []))

/-- `withswap` at `SemSM`. -/
def WithswapRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withswap (.val (axWithswapTy a A B))

/-- `foldImm` at `SemSM`. -/
def FoldImmRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy),
    Ctx.DeadP Γ → F.WF → F.Guarded → ¬ VFree y (.mu F.ty) → ¬ VFree y R →
    (∀ Δ' a, VOutlives Δ' a R) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))

/-- `foldOwn` at `SemSM`. -/
def FoldOwnRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (F : FShape) (R : VTy), Ctx.DeadP Γ → F.WF → F.Guarded →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))

/-- `unfold` (coiteration) at `SemSM`. -/
def UnfoldNRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (S : VTy), C.NuOk → Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
```

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
is listed with the entries that probe it (§3.4–§3.6), read off the programs' terms [read]. A probe
whose entry is NOT BUILT reads the condition only once its rows are built.

| # | draft condition | what it can reject or leave unproved | probes |
|---|---|---|---|
| D1 | (E1): `∀`'s first conjunct reads instances in scope only | `∀E` at an instance not in scope; a top-level polymorphic value is checked by its own pushes alone | P4 (`∀E` at `'a`, in scope); P7, P21, P22 (`readOne ()`, `readBoth ()` at `'0`); P20 (`swapFn ()` at `'0`); the borrowers' `g [] b` at the callback's own variable (P10, P11, P25–P27, P29, P33, P34); P29's `natCopy []` inside a persistent algebra; P33's `cbE` |
| D2 | the own push lends one place (`OwnPushM`) | a consumer handing its callback several cells at one lifetime | S1, S2 (two cells); one cell, the positive controls: P5's `withload` of a record, P16's of a variant, P33's of a list cell; no cell: P1, P2, P27's leaf load |
| D3 | `OwnOKI.placeFree`: the callback holds no cell at the lent place, at any depth | a callback holding a copy of the view whose witness owns the reborrowed places | S5 |
| D4 | `PBox`: a persistent thunk holds at every box world | a persistent value Core accepts that misbehaves at a phantom push | P3; the steps of P12 and P35–P41; P13's `tab10V`, `dropI32V`; the algebras of P10, P11, P25–P27, P29; P33's stages; P39's `passF` |
| D5 | the box carries only reserved-name pushes | a persistent context value across the `∀I` row's binder-named push | P33 (`stepV` at `g : countTy`; `cbE` and the borrower capturing `g`), P34, and the borrowers at `g : fTy` (P10, P11, P25–P27, P29) |
| D6 | the `∀I` row at a live `U` slot is not derived | a callback capturing a closure | `withborF2` (P7, P8, P18, P19), `withborS` (P9, P20–P24), `borrowerM` capturing `mapInc` (P30–P32) |
| D7 | `CohS`, `RetainedPay` at a pushed stack, and at answers holding a borrow leaf | arguments a consumer must hand over with these; answers that return a view; `EntryPayLeaves` at a bound `Mut` read-out | P6 and every `withswap` (P8, P12, P17, P23, P30–P32, P39, P41); P39's `passF` (answer `Mut 'w PC ⊗ I32`); P41's `logStep` (its state, a `Mut` leaf, in the answer); `copy` at `Imm` (P5, P7, P21); P20's `swapFn ()` (answer a `Mut` family); S2's `arrGet`, `arrCopy` |
| D8 | `KeepsT` in the `U` clause | a thunk forced at a list that keeps a relevant record without its tag [unchecked: runs keep tags] | P2 (forces a thunk after the lend) |
| D9 | `guardPV` at `⊸` and `∀` | a call inside a callback whose composite fails the table | only entries that call a higher-order value inside a callback at a pushed stack: the glue at `readOne ()`, `readBoth ()` and `swapFn ()` (P7, P20–P22: `AllEVRowM`, `LolliERowM`), the borrowers' `g [] b` (P10, P11, P25–P27, P29, P33, P34), P33's `cbE`. All are NOT BUILT. G5 closes a first-order callback such as `readCb` without reading the guard, so no PROVED entry reads D9 |
| D10 | W's own `μ`, `[L]`, type variables | a thunk inside `μ` read by W's `U` | the list and tree programs (P10, P11, P25–P27, P29–P34), P17's bag, P13's arrays |
| D11 | the views read an `imm` payload at `vC true` | a lend whose payload holds a thunk | P2 (`withbor` at `methodsTy`) |
| D12 | after the block (§4.2): GhostEnd's piece re-lends a block's entries at distinct lifetimes after a stop (`openFS`'s strict chain), and `StackOKB` fails at that vector | an effectful callback under a block lend: its continuation read at a vector `StackOKB` does not admit | none in this suite (borrow-only programs read no `F_Σ` row); the tier-1 seeds of §3.7 with an abortive effect inside a `withload`-of-pair callback |

### 2.9 `GroundLedger.lean`: the theorems

`GroundLedger.lean` imports `ProbeD1.NxRecon` and `Core.Demonic`. Each item is a `def … : Prop` with
a theorem of the lowercase name. G1–G5, with their empty-stack forms G3, G4′ and G5′ and the
constants' forms G5c and G5v, are the grounding core; `GRestrict` places G1 and G2 under the two
agreement statements the draft already has (C0). G6 states the empty-stack judgement and the floor.
G7–G11 are unfoldings, arising, typing and adequacy, with the pointwise table's refutation and the
arising sets' inclusion. G12 states the floor at BoLo's image.

**The type classes.** `FlatB` mirrors Core's `VTy.DataB`
(`experiments/Targets/Targets/Base/Machine.lean:28`), with `Unk`, `opq`, `[@a]`, `Ref`, non-thunk `!`
and `[L]` added.

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

**`GRestrict`: G1 and G2 as restrictions of C0's statements.**

```lean
/-- `WInsideCoreM` at the types `P` admits. -/
def WInsideCoreMOn (p : Placement) (P : VTy → Prop) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    P A → StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ

/-- `CoreInsideWM` at the types `P` admits. -/
def CoreInsideWMOn (p : Placement) (P : VTy → Prop) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    P A → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vC true A ls (extS δ σ αs) v ρ → vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ

/-- **G1 and G2 restrict the two stated agreement facts**: at every type the restricted forms are
`WInsideCoreM` and `CoreInsideWM`; G2 gives the first at first-order arguments and G1 the second
at flat types, the index hypotheses unused. -/
def GRestrict : Prop :=
  (∀ p, WInsideCoreMOn (ℍ := ℍ) p (fun _ => True) ↔ WInsideCoreM (ℍ := ℍ) p) ∧
  (∀ p, CoreInsideWMOn (ℍ := ℍ) p (fun _ => True) ↔ CoreInsideWM (ℍ := ℍ) p) ∧
  (VRLMFOArg (ℍ := ℍ) → ∀ p, WInsideCoreMOn (ℍ := ℍ) p FOArg) ∧
  (VRLMFlat (ℍ := ℍ) → ∀ p, WInsideCoreMOn (ℍ := ℍ) p FlatTy ∧ CoreInsideWMOn (ℍ := ℍ) p FlatTy)
```

At `fun _ => True` the restricted forms are the stated ones, by definition. G2 is
`WInsideCoreM` restricted to first-order arguments, its index hypotheses unused, and G1 is both
statements restricted to flat types. G4 is `CoreInsideWM`'s analog at first-order computation
types, not its restriction: `CoreInsideWM` at `U C` reads the `U` clause at instantiated readings,
where Core's relation of a value known at one reading is not given (C1) [read].

**G5c, G5v: first-order constants and hand-proved first-order values, at every index.**

```lean
/-- Types of first-order constants: a thunk, or a persistent thunk, of a first-order computation
type. -/
inductive FOConstTy : VTy → Prop
  | thunk {C : CTy} : FOComp C → FOConstTy (.thunk C)
  | bang {C : CTy} : FOComp C → FOConstTy (.bang (.thunk C))

/-- G5c. **First-order constants at every index**: a term Core derives at a dead context of
first-order slots, at a first-order constant type, is the draft's there at every index. -/
def CoreToSemSMConst : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy), Ctx.DeadP Γ → CtxFO Γ → FOConstTy A →
    CDerives Δ Γ e (.val A) → SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A)

/-- G5v. **A closed value Core relates at every reading, at a first-order constant type, is the
draft's at every index**: the same route for a value Core proves by hand (`freeAll_vC`). -/
def CoreValToW : Prop :=
  ∀ (A : VTy) (v : Val), FOConstTy A →
    (∀ (δ : LSub) (ls : List SRec), vC true A ls δ v PMap.empty) →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec), StackOK σ αs →
      vRLM (ℍ := ℍ) .binder0 none σ δ A αs ls v PMap.empty
```

The route [read]:
- At a dead context the resource is empty. The `U` clause (`RelendJ`) then holds at the empty
  resource with no view dropped, and at each instantiation it asks `cRLM` at the instantiated
  reading.
- Core gives `vC` at every reading that models `Δ`: `fundamentalC` for a derived term (G5c), the
  hand proof's own quantifier for a value (G5v, `freeAll_vC`, `Lists.lean:136`). The instantiated
  reading models `Δ` (`instModels`, `BinderInst.lean:249`), and G4 turns `cC` into `cRLM`.
- At `!U C` the box asks the same at each box world, whose reading models `Δ` (`boxIdx_steps`,
  `R1Box.lean:231`).

G5c covers the primitive constants and every first-order function Core derives at a dead context
(`allocS`, `freeS`, the host operations). No reading-independence lemma is needed: Core relates
the term or the value at every reading the clauses reach.

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
payloads in the draft's relation at `[]` (their `SemSMNil` forms, §3.5). At every index, `copy`'s
answer holds `Imm` leaves, so it needs `CopyRowM` (§2.6).

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

**G8–G12, continued: the pointwise table, the arising sets, the floor at BoLo's image.**

```lean
/-- **The pointwise reading of the table fails at `innerView`**: a `TW` world (`tw_innerView`)
whose part fails the table at `[x]` (`not_tabAtS_innerView`), at a configuration not in `Arises`
(`wpG_below_not_arises`). A fact about the pointwise statement (DESIGN §5.2, §11). -/
def NotTabOfTWPointwise : Prop := ¬ TabOfTWPointwise

/-- **The revised arising set is inside the first**: `ArisesI`'s transitions are `Arises`'s with
stronger lends (`LendMutI`, `LendImmI`), and its values are `ArisesV`'s. -/
def ArisesIArises : Prop :=
  (∀ c : Cfg, ArisesI (ℍ := ℍ) c → Arises (ℍ := ℍ) c) ∧
  ∀ (c : Cfg) (v : Val) (A : VTy), ArisesVI (ℍ := ℍ) c v A → ArisesV (ℍ := ℍ) c v A

/-- **The floor at BoLo's image**: a BoLo derivation, embedded (`embed`, `Core/Embedding.lean`),
is the draft's at every index. -/
def DraftFLEmbed : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), DerivesWf Δ Γ e T → Δ.Ok →
    Ctx.ScopedB Δ Γ → SemSM (ℍ := ℍ) .binder0 Δ (cbvCtx Γ) e (.val (cbv T))
```

The routes:
- **`ArisesITW`** is an induction on `ArisesI`. `run` uses `RunEnd`'s `TW`. `lendImm` is `TW.immFrame`
  from `LendImm`'s fields, and `lendMut` is `TW.mutFold`. `part` and `hide` keep the world.
- **`ArisesINilOfTW`** is `ArisesI.nil` itself, stated so that the ledger row can name it.
- **`ProbeRulesOfNU`** unfolds `ProbeRules` and applies `ExtendsNU`'s first conjunct at the empty row
  context.
- **`AdequacyNilM`** follows `adequacyD`'s proof (`Demonic.lean:312`), with `nilSoundRetM` in place
  of `fundamentalC`.
- **`NotTabOfTWPointwise`** applies `TabOfTWPointwise` at `innerView k αy` as the whole world and
  the local part, the frame empty, no records, and the stack of one `mut` entry at `α` lending a
  place other than `k`, with `αy < α`. `tw_innerView` gives the world; `Tagged` and the 6.64
  condition are vacuous; `HeldUnderTW` holds, since the cell at `k` is a `mut` cell at a place no
  entry lends. The conclusion contradicts `not_tabAtS_innerView`.
- **`ArisesIArises`** is a mutual induction: each `ArisesI` constructor is the `Arises` one, its
  lend's first conjunct (`LendMutI`'s, `LendImmI`'s) the `Arises` premise.
- **`DraftFLEmbed`** (G12) is stated, not attempted. Its route is `embed`'s induction, with the
  draft's row at each `DerivesWf` rule's image (`ofRet`, `unitE`, `tensorE`, `sumE`, `lolliE`,
  `allEV`, `thunkV`, `allI`, `bangThunkV`, `bangE`, the axioms).

**Cost.** G1, G2, G4, G5, G3, G4′ and G5′ are each an induction or a slot-by-slot conversion, a few
hundred lines in all. G5c and G5v read the `U` clause at the empty resource and the box's worlds,
through `instModels` and `boxIdx_steps`. `GRestrict`, G6–G11, `NotTabOfTWPointwise` and
`ArisesIArises` are short. G12 is not attempted. No theorem here reads a push's view.

### 2.10 Superseded relations

Each earlier draft relation stays as the statement it was (convention of `vRLI → vRLJ → vRLM`,
`NEXT.md` §1.6). The ledger lists them so that no result is read at the wrong relation. Each family's
Core counterpart is Core's (`vCE`/`cC`/`gDenC`/`SemC`); the column says how it relates to the
current draft and which doc claims still rest on it.

| family | definitions | to `vRLM` | results and doc claims that rest on it |
|---|---|---|---|
| W₀ | `vRL`, `cRL`, `effRet`, `gRL` (`Relation.lean:108`, `:131`, `:176`); `SemS` (`Sem.lean:102`); `SemSR` (`Thunk.lean:227`); `WP` (`Sem.lean:119`, W11) | no `CohS`, no `RetainedPay`, no instantiations: the `U` clause is GhostEnd's `RelendableS` under `guardW` | statement 0's bundle and shared lemmas (`Statement0.lean`; `statement0Shared`, `Shared.lean:19`; `nilSoundRet`, `Bridge.lean:133`); the rows `ForceRow`, `ThunkFRow`, `ThunkVRow`, `BangThunk*Row` (`Statement0.lean:215–248`; proved at `binder0`, `Rows0.lean`, `Thunk.lean`); statements 1–4 and 6 (`Statement1/2/34.lean`, `Programs.lean`: `LamRow`, `AllIRow`, `BelowRow`, `SpanW1Row`, `SpanW2Row`, `SpanLoadRow`, `HandleRow`, `ThenRow`, `semTyping`, `GenSelfAccepted`, `ReconAccepted`); OQ-58's `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` (J5). DESIGN §12's success criteria are stated at these |
| W revised | `vRLI`, `cRLI`, `gRLI`, `SemSI` (`BinderW.lean:42`, `:66`, `:115`, `:122`) | an earlier revision: `CohS` without `RetainedPay`, `RelendI` in place of `RelendJ`, no `μ`, `[L]` or type variable of its own, no (E1)–(E4), no box [read] | the binder unit's results (`BINDER.md`); the rows `*RowI`, `*RowTF` (`BinderW.lean`) |
| R1-before | `vRLJ`, `cRLJ`, `gRLJ`, `SemSJ` (`BinderJ.lean:72`, `:98`, `:147`, `:152`); `Statement0UFullJ` (`:202`) | `vRLM = vRLJ` at types with no `μ`, `[L]`, type variable, lifetime `∀` or persistent thunk (`RelMAgreesJ`, `R1.lean:334`; proved, `relMAgreesJ`, `R1Thaw.lean:195`) | `gdBangJ` (`NxFloor.lean:55`), which part (0) cites (R3, D3, N5, N6) as the relation before the box: `gdTy` has no lifetime `∀`, so (E1) plays no part, and at `!gdTy` the two `!` clauses differ by the box; `GAP.md`'s adjacency at `vRLJ` (`adj_not_cRLJ`, `adj_not_wU`); the rows `*RowJ`, `*RowTFJ`, `*RowKJ` (`BinderJ.lean`, `BinderRows.lean`, `Gap.lean`) |
| GhostEnd | `vRLs`, `cRLs` (D16.1), `vRLa` (`GhostEnd/Stacked.lean`, `GhostEnd/Arising.lean`) | the ancestors: the stack and the piece without W's guard and leaves | GhostEnd's own results; the piece (`bodyS`, `OpenS`, `openFS`) is read by `vRLM`'s `F_Σ` clause unchanged (D12) |

No claim of this unit rests on a superseded family, except where it says so: `gdBangJ` (at
`vRLJ`) and the `SpanLoadRow`/`ThenRow` mentions (at `SemS`).

---

## 3. Part (2): the regression suite

### 3.1 The obligation

**A program's obligation is `DraftFL` restricted to its derivation**: at every node
`Δ; Γ ⊢ e : j` of the program's `CDerives` derivation, `SemSM .binder0 Δ Γ e j`, at every index.
That is `fundamentalC`'s instance at the program, read at the draft. At a node, `SemSMNil` is the
corollary (`SemSMNilOfSemSM`, G6). It is recorded as a second status only where it alone is
proved.

**First-order nodes are Core's.** At a node whose context's live slots are first-order arguments and
whose type is a first-order computation type (§2.9), G5 gives the node from `fundamentalC`,
whatever the derivation below it. At a term derived at a dead context at a first-order thunk type,
G5c does. So the entries are the other nodes, of four kinds:
- **R, the root**: a closed program's root is first-order (G5), a sanity check that reads no draft
  clause; the root of a program open in recursive values is not (P33, P34, P32).
- **V, the values built at a type with `U`, `∀` or `!`** (`thunkF`, `thunkV`, `bangThunkF`,
  `bangThunkV`, `allI`): callbacks, closures, persistent combinators. These read the draft's `U`
  thaw, the `∀` clause's own push, and the box.
- **K, the constants** (a constructor at a dead context): first-order ones by G5c; the
  higher-order ones (the borrow constants, the folds, `unfoldN`, `arrNew`, `arrFree`) by their rows
  (§2.6). These read the draft's consumer side: a callback's clause at an own push, with the lend's
  argument.
- **G, the glue**: every other node that is not first-order (`var`, `lam`, `app`, `bind`,
  `letpair`, `lolliE`, `allE`, `allEV`, `bangE`, `boxI`, …, at a context holding a `U` or `!` slot,
  or at an answer holding a borrow leaf). The glue rows are program-independent and are tracked
  once in §2.6. Each program names the glue rows its derivation reads at such nodes, and a NOT BUILT
  V or K entry names the glue rows inside its own sub-derivation (or states its missing lemma as
  `DraftFL` restricted to that named sub-derivation).

**Entries name Core's sub-derivations.** Where Core names one (`d_borrower`, `d_passF`), the entry
cites it. Where Core builds it inside a proof (`d_scopeProg`'s callback, `d_loader`'s body), the
builder rebuilds it from the same constructors, never by inverting `CDerives`. An entry is stated
at every dead context when Core's lemma is parametric in one (`∀ Γ, Ctx.Dead Γ → …`): neither the
index nor the conclusion reads a dead slot.

**Why every index.** At every index, an entry is read at pushed stacks, where views arise
(`ArisesVI.view`). The one arising configuration known, `withloadUPairGapReal`, sits at the stack
of an enclosing 6.64 lend, which S1's `withload` entries read (§3.6). At the empty stack alone, no
`Imm` view arises except as a run's answer, so an entry posed only there could not fail [read:
A7].

**Statuses.**
- **PROVED**: a theorem proves the entry at every index. "PROVED at `[]`" records a proof of the
  `SemSMNil` form only.
- **FAILS**: only with a configuration that arises (`ArisesI`, with `ArisesVI` for every value the
  refutation reads), every hypothesis discharged, and the entry's own judgement refuted. A route
  refuted is not a FAILS: it is recorded as "route blocked" under NOT BUILT, with the refuted step
  and whether its configuration arises.
- **NOT BUILT**: the exact missing lemma, a row of §2.6 or another named `def … : Prop`.

**Not vacuous.** Every PROVED entry has a short lemma `EntryRead Δ Γ j`, discharging `BindersLow` and
`Scoped` at its types (a `simp` over the type's binders and free variables), so that the entry's
proof does not hold because its premises fail. At a dead context `EntryRead` reads no slot, so the
lemma at `[]` serves every dead `Γ`.

**A program's status** is written "entries: n PROVED, m NOT BUILT; glue rows (§2.6): …, not
stated". It is never written "accepted". The floor is met at a program when every entry is PROVED
and every glue row it reads is.

**The floor rule.** Every borrow-only program Core accepts must be accepted by the draft. A FAILS is
a draft defect, never a restriction. NOT BUILT entries are the floor's remaining work.

```lean
/-- **An entry**: the draft's semantic judgement at one node of a Core derivation, at every index
(`DraftFL` at that node). -/
abbrev AccNode (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  SemSM (ℍ := ℍ) .binder0 Δ Γ e j

/-- The entry at the empty stack: `SemSMNilOfSemSM`'s corollary of `AccNode`. -/
abbrev AccNodeNil (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j

/-- **The entry is read**: its judgement's binders are no reserved names and its free lifetime
variables are `Δ`'s, so the two premises `SemSM` and `SemSMNil` open with hold, and a proof of the
entry is not vacuous. -/
def EntryRead (Δ : LifeCtx) (Γ : Ctx VTy) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) ∧ Scoped Δ Γ (jdgCty j)
```

### 3.2 The producer lemmas (V)

Each V entry at a first-order callback or closure is one application of these to the program's
named body derivation. They compose:
- the draft's proved rows: `ThunkVRowM` and `BangThunkVRowM` from `statement0UFullM`, and
  `AllIRowMAt _ Γ` from `allIRowMUFree0 Γ` at a context of first-order slots, which reach no `U`
  (`UFreeM` holds of every `FOArg` type [read]);
- the `ret` node, which is the identity on `SemSM` by `jdgCty`;
- G5, applied at the body's or the λ's judgement.

Every Core callback has the shape `thunkV (allI (ret (thunkV (lam body))))` (`callbackW`,
`Core/Splits.lean:94`; `d_borrower`, `Examples.lean:121`; `d_algI`, `Folds.lean:60`). The body
premise is at `.comp (.ret B)`, as `d_borrowBody` and `d_readBody` derive it; a `callbackW` body,
derived at `.val B`, is read through `ret`.

```lean
/-- A first-order callback at the non-unwinding shape `∀'x ⊏ ⊓Δ. F (U (A ⊸ F B))`, at a context
of first-order slots the binder avoids. -/
def SemSMCallbackOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → CtxFO Γ → CtxFresh x Γ → FOArg A → FlatTy B →
    CDerives (Δ.extend x Δ.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (.all x Δ.meetOfDom (.lolli A B)))

/-- The same at the `.arr` shape `∀'x ⊏ b. A ⊸ F B` (`cInst`'s `polyC`, `cbUTy` at the empty
row). -/
def SemSMCallbackArrOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → b.mentions x = false → CtxFO Γ → CtxFresh x Γ → FOArg A →
    FlatTy B →
    CDerives (Δ.extend x b) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (.thunk (.all x b (.arr A (.ret B)))))

/-- A persistent first-order callback at a dead context (`d_algI`'s algebras, `c₀V`). -/
def SemSMBangCallbackOfCore : Prop :=
  ∀ (Γ : Ctx VTy) (x : LifeVar) (A B : VTy) (body : Expr), Ctx.Dead Γ → FOArg A → FlatTy B →
    CDerives (LifeCtx.empty.extend x LifeCtx.empty.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ)
      body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 LifeCtx.empty Γ (.val (.lam (.val (.lam body))))
      (.val (.bang (VTy.all x LifeCtx.empty.meetOfDom (VTy.lolli A B))))

/-- A persistent thunk of a first-order computation type at a dead context (`cBang`'s closure,
`counterStep`, `tab10V`, `d_algO`'s algebras). -/
def SemSMBangThunkOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Ctx.Dead Γ → C.isRet = false →
    FOComp C → CDerives Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- A thunk of a first-order computation type at a context of first-order slots (`cMethods`,
`pushG`, `withswap`'s callbacks). -/
def SemSMThunkOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxFO Γ → C.isRet = false → FOComp C →
    CDerives Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.thunk C))
```

The side conditions of `allI` come from `Δ.Ok` and `CtxFresh x Γ`, as `allI_fresh` takes them.
`OwnHyg` holds at `Γ` with `Δ.find? x = none` and `CtxFresh x Γ`. `PersistentBoxed` and `Persistent`
are vacuous at a dead context. A persistent first-order function `!(A ⊸ F B)` is
`SemSMBangThunkOfCore`'s case `C = A ⊸ F B`.

### 3.3 The consumer gates (K)

Every K entry for a higher-order constant has the full row as its obligation, at every index
(NOT BUILT, §3.5). Beside it, one statement isolates the draft-specific step of the row's route at
the empty stack. That step is where the two-cell gap lives:
- **`withbor` (1), (2)**: the callback at an own push lending the view's place. These are the
  existing consumer facts: `CallbackExtImmM`/`CallbackExtMutM` at the `.arr` shape (proved), and
  `CallbackExtImmMF`/`CallbackExtMutMF` at the thunked shape Core's programs use (stated,
  `Nx.lean:466`, `:483`).
- **`withload`**: [TR] 6.175's argument, Core's reborrowed payload at a fresh `β`, as
  `withload_compatX` hands it to the callback (`Compatibility.lean:252`). Some own push must admit
  it: related at the pushed index, and the composite meeting the guard. The statement below reads
  the guard at the push itself, which is the identity instantiation of the thunked answer's `U`
  clause. The non-identity route (`not_withloadPairGapNilInstE1`) is not the row's route.

`withload_compatX` splits on `CohE` (`:316`): at the top, the view is a record's own cell and 6.150
reborrows the record's payload (`rebChooseTW_top`, `TW.reb`); deep, the view is a cell a chain of
`Ref` steps reaches inside a record's payload, and 6.150 reborrows that cell's witness
(`rebChooseTW_deep`, `TW.rebDeep`). The gate takes both, through `LoadPay`.

```lean
abbrev loadCbF (A B : VTy) (x : LifeVar) : CTy :=
  .ret (.lolli (A.immReborrow (.var x)) (.box (.var x) B))
abbrev loadCbU (A B : VTy) (x : LifeVar) : CTy :=
  .arr (A.immReborrow (.var x)) (.ret (.box (.var x) B))

/-- **The payload a load reborrows at `ℓ`**, by `withload_compatX`'s two cases of `CohE`: the
value and payload of the record whose cell `ℓ` is (`TW.reb`), or the value a chain of `Ref` steps
from a record's value reaches, with the witness of the `imm` cell there (`TW.rebDeep`). In both,
the world's cell at `ℓ` is `imm(s, u, R)`. -/
def LoadPay (W : WRes) (rs : List FrameRec) (ℓ : BoCa.Loc) (u : Val) (R : WRes) : Prop :=
  (∃ (s : LSet) (h : R.InStratum s.join), W.get ℓ = some (CellU.immOf s u R h)) ∧
    ((∃ r ∈ rs, ℓ = r.le ∧ u = r.v ∧ R = r.R) ∨
      ∃ r ∈ rs, ∃ (p : Option BoCa.Loc) (S₀ : VTy), Chain r.R r.T r.v p ℓ S₀ u)

/-- **The `withload` gate at the empty stack** (single-entry form): at a view `Coh` admits,
whichever of its two cases, [TR] 6.175's argument, the payload reborrowed at a fresh `β`, is
admitted by some own push of the callback, related at the pushed index, with the composite
meeting the guard there. -/
def LoadGateNil (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (W : WRes) (ℓ : BoCa.Loc) (u : Val) (R : WRes) (x : LifeVar)
    (c : Lifetime.Life) (β : Life) (cb ρc ρ : WRes),
    CohE (rsOf ls) ℓ A δ → LoadPay W (rsOf ls) ℓ u R → ¬ VFree x A → δ.find? x = none →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) u cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ en : LEnt, OwnPushM δ (.all x c (C' x)) ρc ([], []) en β ∧
      vRLM (ℍ := ℍ) .binder0 none [en] (δ.extend x β) (A.immReborrow (.var x)) [β] ls u cb ∧
      TabAtS [en] [β] ρ ∧ PlaceViewsL (extS (δ.extend x β) [en] [β]) [en] [β] ls ρ
```

What it decides at each payload `A`, in both of `CohE`'s cases:
- **No reborrowed cell** (`A = 1`, `B`, `I32`, `methodsTy`, whose `Imm̲` is `Unk`): one entry at a
  fresh place with a closed payload type. Expected PROVED.
- **One cell** (`A = Ref 1`; `Pt.valTy = B ⊗ Ref B`, `readFields`'s record; the variant `Opt`; the
  list `L`, whose `Imm̲` unrolls to one `Imm` leaf): the entry lends that cell's place. Its view is
  at exactly `β`, and `CohS` and `RetainedPay` hold. Expected PROVED.
- **Two or more** (`pairTy`, `Array i32` at length 2): the table's second conjunct rejects the cell
  at the unlent place at every push (`loadGuardFails2`, `pairCallbackGuardFails`). Expected refuted
  ("route blocked"). The refuting data at the empty stack is `withloadUPairGapNilE1`'s, whose view
  is not shown to arise; at the stack of an enclosing lend the data is `withloadUPairGapReal`'s,
  whose configuration and view arise (§3.6).
- **The deep case** asks the same of the chain's cell: the reborrow's cells are the own cells of
  that cell's witness [unchecked: the route at the top case carries over].
- **The views' payload reading.** At a leaf payload with a thunk, `PlaceViewsL`'s `vwEW` asks the
  payload at `vC true` while Core's leaf gives `vC false` (D11). Every payload the suite's gates
  reborrow is data, where the two agree. P2's `withbor` lends a view whose payload holds a thunk
  (`methodsTy`), which its K entry, not a gate, reads.

The block form, `LoadGateNilB` (§4.4), has `∃ τ` (a block) in place of `∃ en`.

### 3.4 The enumeration

Every `*_derives` theorem and every closed `CDerives` program theorem of `Core/`, from a grep of
`Core/*.lean` for theorems whose statement is a `CDerives` at `LifeCtx.empty` or `Δ₁` and an empty
context, or is named `*_derives` (line numbers at `3e84262`). The classes:
- **B, borrow-only**: no effect rule (`effPerform`, `effRaise`, `effLet`, `effThen`, `effHandle`,
  `effSub` at a non-empty row, or a `*U` constant at a non-empty row). A `ν` inside a closure type
  (the affine closure `Aff`, spec §22) does not change the class: Core's `ν` is the draft's by
  definition (C11), and an affine closure is an ordinary closure of the floor.
- **E, effect**: an effect rule, so the `F_Σ` clause at a pushed stack (GhostEnd's piece). The next
  suite (§3.7).
- **C, codata**: a `ν` stream, delay or loop whose subject is the codata itself, with no borrow
  constant and no lend.
- **X, not a program**: a generic rule or an adequacy theorem.

Every B program is in the suite. An E, C or X theorem carries its reason.

| theorem (file:line) | program | class | in the suite |
|---|---|---|---|
| `cImmBorrow_derives` (`Examples.lean:127`) | `cImmBorrow` | B | P1 |
| `cRecBorrow_derives` (`:247`) | `cRecBorrow` | B | P2 |
| `cBang_derives` (`:179`) | `cBang` | B | P3 |
| `cInst_derives` (`:311`, at `Δ₁`) | `cInst` | B | P4 |
| `d_readFields` (`RecordPrograms.lean:137`) | `readFields` | B | P5 |
| `d_mutFields` (`:238`) | `mutFields` | B | P6 |
| `d_readFamily` (`FamilyPrograms.lean:322`) | `readFamily` | B | P7 |
| `d_swapBothB` (`:154`) | `swapBothB` | B | P8 |
| `d_blockSwap` (`BlockPrograms.lean:121`) | `blockSwap` | B | P9 |
| `countFoldProg_derives` (`Folds.lean:377`) | `countFoldProg` | B | P10 |
| `anyTreeProg_derives` (`:471`) | `anyTreeProg` | B | P11 |
| `counterProg_derives` (`AffPrograms.lean:237`) | `counterProg` | B | P12 |
| `arrProg_derives` (`ArrayPrograms.lean:54`) | `arrProg` | B | P13 |
| `exProg_derives` (`Fundamental.lean:601`) | `exProg` | B | P14 |
| `build3_derives` (`Lists.lean:65`, at `.val listL`) | `build3` | B | P15 |
| `d_matchSome` (`RecordPrograms.lean:309`) | `matchSome` | B | P16 |
| `d_bagProg` (`:385`) | `bagProg` | B | P17 |
| `d_swapBothL` (`FamilyPrograms.lean:173`) | `swapBothL` | B | P18 |
| `d_splitFour` (`:522`) | `splitFour` | B | P19 |
| `d_nestSwap` (`BlockPrograms.lean:184`) | `nestSwap` | B | P20 |
| `d_blockRead` (`:225`) | `blockRead` | B | P21 |
| `d_nestRead` (`:291`) | `nestRead` | B | P22 |
| `d_bagBlock` (`:360`) | `bagBlock` | B | P23 |
| `d_crossPack` (`:407`) | `crossPack` | B | P24 |
| `anyListProg_derives` (`Folds.lean:425`) | `anyListProg` | B | P25 |
| `natCopyProg_derives` (`:513`) | `natCopyProg` | B | P26 |
| `sumListProg_derives` (`IntPrograms.lean:280`) | `sumListProg` | B | P27 |
| `signProg_derives` (`:341`) | `signProg` | B | P28 |
| `sumProg_derives` (`CommonList.lean:316`) | `sumProg` | B | P29 |
| `mapProgC_derives` (`:415`), `mapProgOpenC_derives` (`:390`, open at `ΓMC`) | `mapProgC` | B | P30 |
| `mapProgR_derives` (`ReuseList.lean:211`) | `mapProgR` | B | P31 |
| `mapProg_derives` (`MapMut.lean:471`, open at `ΓM`) | `mapProg` | B | P32 |
| `countProg_derives` (`Count.lean:335`, open at `ΓF`) | `countProg` | B | P33 (S3) |
| `countFreeProg_derives` (`CountFree.lean:258`, open at `ΓC`) | `countFreeProg` | B | P34 |
| `ofFnProg_derives` (`AffPrograms.lean:380`) | `ofFnProg` | B | P35 |
| `onceProg_derives` (`:407`) | `onceProg` | B | P36 |
| `dropProg_derives` (`:427`) | `dropProg` | B | P37 |
| `nestProg_derives` (`:510`) | `nestProg` | B | P38 |
| `passProg_derives` (`:656`, every `n`) | `passProg n` | B | P39 |
| `retProg_derives` (`:717`) | `retProg` | B | P40 |
| `logProg_derives` (`:842`) | `logProg` | B | P41 |
| `*_runsC` (`EmbeddingExamples.lean:22–54`): `embed d_X` (`Embedding.lean:235`) of BoLo's `allocFree`, `fig2c`, `immBorrow`, `mutBorrow`, `loadClosure`, `aliasLoad`, `swapTwo`, `greetProg`, `ownedFn`, `mutClosure` | the paper's programs | B | P42 (×10) |
| `sumToProg_derives` (`IntPrograms.lean:157`) | `sumToProg` | C | no: `fixD`, DelayPrograms' `progD`. Its draft nodes are the persistent step (the box, as P3 and the steps of P35–P41), `unfoldN` (`UnfoldNRowM`, read by every affine program's `mkBox`) and the driver at `ν`, which is Core's (C11). It reads no row the suite does not |
| `loopProg_derives`, `countDownProg_derives`, `counterProg_derives` (`DelayPrograms.lean:184`, `:247`, `:308`) | delay loops | C | no: as `sumToProg` |
| `d_takeCloseR`, `d_natsSum` (`StreamPrograms.lean:110`, `:199`) | streams | C | no: as `sumToProg`, with `foldOwn` (P10's row) in `natsSum`'s step |
| `prog_derives`, `progC_derives` (`EffExamples.lean:45`, `:77`) | handled programs | E | no: `effHandle`, `effPerform` |
| `d_logOutside`, `d_failOutside`, `d_reborrowRaise`, `d_nLogOutside`, `d_nFailOutside`, `d_logInBorrow`, `d_tickProg`, `d_takeProg`, `d_storeCancel`, `d_tickAnsProg` (`EffPrograms.lean:233`, `:298`, `:385`, `:489`, `:496`, `:614`, `:720`, `:846`, `:939`, `:1002`) | effect programs | E | no: abortive or resumed operations, several inside a lend (§3.7) |
| `d_readByte`, `d_writeByte`, `d_mkInput`, `d_mkOutput`, `d_takeInput`, `d_takeOutput`, `d_writeAll`, `d_readInto` (`Stdio.lean:176`–`:556`) | the I/O capabilities | E | no: values at extern computation types with I/O rows |
| `d_foldProg` (`Folds.lean:334`), `d_scopeProg` (`AffPrograms.lean:213`), `d_swapBoth` (`FamilyPrograms.lean:118`), `drive_derives`, `d_progD` (`DelayPrograms.lean:75`, `:148`), `d_progS`, `d_takeE` (`StreamPrograms.lean:57`, `:76`), `drop_derives` (`Dtor.lean:330`) | generic rules | X | no: each is read through the programs above that instantiate it |
| `adequacyC` (`Fundamental.lean:590`), `adequacyD`, `adequacyD_safe`, `adequacyD_val` (`Demonic.lean:312`–`:334`), `adequacyD_obs` (`EffPrograms.lean:41`), `runs_i32` (`AffPrograms.lean:345`), `wp_of_derives` (`Folds.lean:366`), `take_runs`, `drive_runs_*`, `total_*` (`Totality.lean`), `meets_of_derives` (`Stdio.lean:219`), `adequacy_of_derivesWf` (`Embedding.lean:326`) | adequacy | X | no: J4's counterparts |

### 3.5 The entries

Line numbers are at `3e84262`. Statuses are *[expected]* until the build records them; the node
lists are [read] off the programs' terms and derivations, and the builder confirms them against the
derivations. Abbreviations:
- `[G5]`, `[G5c]`, `[G5v]`: PROVED by `CoreToSemSM`, `CoreToSemSMConst`, `CoreValToW`;
- `[cb]`, `[cb→]`, `[bcb]`, `[bt]`, `[t]`: PROVED by `SemSMCallbackOfCore`,
  `SemSMCallbackArrOfCore`, `SemSMBangCallbackOfCore`, `SemSMBangThunkOfCore`, `SemSMThunkOfCore`
  at the named body derivation;
- **NB**: NOT BUILT, with the missing lemma.

At the empty stack G5′ (`CoreToSemSMNil`) gives every node at a `NilComp` judgement whose context is
`CtxNil`, so an NB entry there is "PROVED at `[]`" [expected]: `copy` at `Imm`, `alloc` and `free`
at a thunk payload (P2), and the other nodes of such types whose answer holds a borrow leaf.

Every K entry and every V entry is at every index; its `SemSMNil` form is its corollary. P1 is
written out as the template, and P39, P27 and P33 after it: the first two probe the box at a nested
push and a `withload` inside a persistent algebra, and the third is the user's case (S3). The
others are in the tables that follow; their Lean entries are `AccNode` at the node named, in P1's
form.

**P1 `cImmBorrow`** (`Core/Examples.lean:88`; `cImmBorrow_derives` `:127`). `withbor` (1) at `1`,
`withload` at `1` (no cell).

| entry | node | every index | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] cImmBorrow (.comp (.ret .unit))` | [G5] | — |
| V1 | `d_borrower` at a dead `Γ`: `borrower cLoader` at `borrowerTy .unit` | [cb] at `d_borrowBody` (`:104`) | — |
| V2 | `d_loader` (`:94`) at a dead `Γ`: `cLoader` at `loaderTy .unit`, `Δ = Δ₁` | [cb], its body rebuilt as `d_loader`'s | — |
| K1 | `withbor` at `axWithbor1Ty 0 _ .unit .unit` | NB | `Withbor1RowM` (the port of `withbor1_compatX`, `Compatibility.lean:937`); its draft step `CallbackExtImmMF .binder0`. Its empty-stack form is attempted in (3) (§4.6) |
| K2 | `withload` at `axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit)` | NB; gate `LoadGateNil .unit (loadCbF .unit _)` expected PROVED (no cell) | `WithloadRowM`; its empty-stack form attempted in (3) |
| K3, K4 | `alloc` at `.lolli .unit (.ref .unit)`, `free` at `.lolli (.ref .unit) .unit` | [G5c] | — |
| glue | `bind` at a slot of `withbor`'s type, of the borrower's, of the partial application; `app` of a forced `U` slot | NB | `BindRowM`, `AppRowM`; `ForceRowM` is proved |

```lean
def AccImmBorrowRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] cImmBorrow (.comp (.ret .unit))
def AccImmBorrowCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (borrower cLoader) (.val (borrowerTy .unit))
def AccImmBorrowLoader : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ cLoader (.val (loaderTy .unit))
def AccImmBorrowWithbor : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom .unit .unit))
def AccImmBorrowWithload : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit)))
def AccImmBorrowAlloc : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (.prim .alloc)) (.val (.lolli .unit (.ref .unit)))
def AccImmBorrowFree : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (.prim .free)) (.val (.lolli (.ref .unit) .unit))

/-- `cImmBorrow`'s entries. -/
def AccImmBorrow : Prop :=
  AccImmBorrowRoot (ℍ := ℍ) ∧ AccImmBorrowCb (ℍ := ℍ) ∧ AccImmBorrowLoader (ℍ := ℍ) ∧
    AccImmBorrowWithbor (ℍ := ℍ) ∧ AccImmBorrowWithload (ℍ := ℍ) ∧ AccImmBorrowAlloc (ℍ := ℍ) ∧
    AccImmBorrowFree (ℍ := ℍ)

/-- Every entry of `cImmBorrow` is read (its dead slots are not). -/
def ReadImmBorrow : Prop :=
  EntryRead LifeCtx.empty [] (.comp (.ret .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (borrowerTy .unit)) ∧
    EntryRead Δ₁ [] (.val (loaderTy .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom .unit .unit)) ∧
    EntryRead Δ₁ [] (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit))) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli .unit (.ref .unit))) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli (.ref .unit) .unit))

/-- K2's draft step. -/
def GateImmBorrowLoad : Prop := ∀ B : VTy, LoadGateNil (ℍ := ℍ) .unit (loadCbF .unit B)
```

**P10's V2 list**, the carry side: P10's borrower entry, which P11, P25–P27, P29, P33 and P34
share. `borrowerE` at a context holding `g : fTy M R` (or `countTy`) needs
- `AllIRowMAt .binder0 [⟨fTy M R, true⟩]`: the `∀I` row's binder-named push at a persistent
  context (`VRLMStackRename`, `NxFloor.lean:176`, stated; the reduction from it with
  `persistentPushN`, not built; the reading transports at a `!U` slot, `CtxExtendMSAt` and
  `CtxShadowMSAt`) (D5);
- `AllEVRowM` at `g []`, instantiated at the callback's own variable `'0`, in scope at the push:
  its step `InScopeOfInterp` (`Nx.lean:396`, stated) (D1);
- `LolliERowM` at `g [] b`: the `⊸` clause's `guardPV` at the pushed stack (D9);
- `BangERowM`, `BindRowM`, and `VarRowM` at the `!U` slot. The answer `n : R` is boxed at a
  first-order judgement (G5).

**P39 `passProg n`** (`Core/AffPrograms.lean:654`; `passProg_derives` `:656`). The counter lent
`Mut`, handed through `n` persistent functions to `passF 0`, which reborrows it with `withbor` (3)
and calls through it. It probes D4 (`passF`'s box) and D7 (answers holding the `Mut` view, at the
push of `passCb`'s binder and at `withbor` (3)'s nested push). It does not probe D5: `passF n` is
built inline at a dead context, never a slot carried across a binder-named push [read].

| entry | node | every index | missing |
|---|---|---|---|
| R | `AccPassRoot` | [G5] | — |
| V scope | `AccPassScope`: `scopeCbOf (scopeBodyWith (passCb n))`, the lend of `d₀ : Ref 1` | [cb], its body rebuilt as `d_scopeProg`'s callback (`seqV` of `forget d` and `ofRet (d_scopeBodyWith …)`) | — |
| V `passCb` | `AccPassCb` (`d_passCb`, `:642`): `∀'1 ⊏ ⊓Δ₁. Mut '1 PC ⊸ ['1] I32` | [cb], its body rebuilt as `d_passCb`'s | — |
| V `counterStep` | `AccPassStep` (`d_counterStep`, `:53`) | [bt]: `Ref I32 ⊸ (I32 ⊸ F(I32 ⊗ [@⊤] Ref I32)) & F 1` is first-order | — |
| V `passF n` | `AccPassF` (`d_passF`, `:631`) at `passTy = !U(Mut '1 PC ⊸ F(Mut '1 PC ⊗ I32))` | NB | `BangThunkVRowM` (proved: the box at `passTy`, D4); `LamRowM`, since the answer holds a `Mut` leaf and the λ's judgement is not first-order; in the body `LetPairRowM`, `LolliERowM` at `reV`, `twiceV` and `passF n`, `BangERowM`, `TensorIRowM`, `VarRowM` at `Mut`; the answer's leaf owes `CohS` and `RetainedPay` at the index (D7) |
| V `twiceV`, `reV` | `AccPassTwice`, `AccPassRe` (`d_twice`, `:580`; `d_re`, `:608`) | NB | as `passF`; `twiceV` calls through `withswap` (`callMut`), `reV` through `withbor` (3) |
| V `reCb` | `AccPassReCb` (`d_reCb`, `:597`): `∀'2 ⊏ ⊓Δ₂. Mut '2 PC ⊸ ['2] I32` | [cb], its body rebuilt as `d_reCb`'s | — |
| K `withbor` (1) at `1` | the scope's lend | NB | `Withbor1RowM` |
| K `withbor` (2) at `PC` | `AccPassWithbor2` | NB | `Withbor2RowM`; its draft step `CallbackExtMutMF` |
| K `withbor` (3) at `PC` | `AccPassWithbor3` | NB | `Withbor3RowM`: the reborrow of a `Mut` at a nested push, `'2 ⊏ '1` |
| K `withswap` at `PC` | `callMut` (`d_callMut`, `AffRules.lean:205`) | NB | `WithswapRowM` (D7: its answer is `Mut 'w PC ⊗ I32`) |
| K `unfoldN` at `affBody` | `mkBox` (`d_mkBox`, `AffRules.lean:140`) | NB | `UnfoldNRowM` |
| K `alloc`, `free`, `forgetMut`, `swap`, `hostOp` | at first-order payloads | [G5c] | — |
| glue | `d_mkBox`'s nodes; `d_closeBox`'s; `letpair` and `bind` at a `PC` slot | NB | `BindRowM` at a `!U` code slot, `BoxIRowM` at `PC`, `WithIRowM`, `NuInRowM`, `BoxERowM`, `Proj₂RowM`, `LetPairRowM` |

**P27 `sumListProg`** (`Core/IntPrograms.lean:278`; `sumListProg_derives` `:280`). A list of
`I32`, summed inside an immutable borrow by `foldImm`, whose algebra reads each payload leaf by
`withload` (`readI`). A `withload` inside a persistent algebra: the load runs at the algebra's own
push, inside the fold's run, inside the borrow's lend, a nested push the every-index entry reads.

| entry | node | every index | missing |
|---|---|---|---|
| R | `AccSumListRoot` | [G5] | — |
| V `sumIAlg` | `AccSumListAlg` (`d_sumIAlg`, `:230`): `!U(∀'0. 1 ⊕ (Imm '0 I32 ⊗ I32) ⊸ F I32)` | [bcb], its body rebuilt as `d_sumIAlg`'s | — |
| V the loader | `AccSumListLoader`: `Λ. λv. v` at `ΔA` (`callbackW` in `d_sumIAlg`) | [cb] | — |
| K `withload` at `I32` | `AccSumListLoad`, in the algebra | NB; gate expected PROVED (no cell; `CohE` deep: the leaf is a cell inside the list's payload) | `WithloadRowM` |
| K `foldImm` at `ilistF` | `AccSumListFoldImm` | NB | `FoldImmRowM`: it hands the algebra each node's leaves at the algebra's own push |
| V `freeIAlg` | `AccSumListFreeAlg` (`d_freeIAlg`, `:263`) | [bt] | — |
| K `foldOwn` at `ilistF` | `AccSumListFoldOwn` | NB | `FoldOwnRowM` |
| V the borrower | `AccSumListBorrower` (`d_borrowerG`, `Folds.lean:253`) at `g : fTy ilistL I32` | NB | P10's V2 list |
| K `withbor` (1) at `ilistL` | in `progOpen` | NB | `Withbor1RowM` |
| K `alloc`, `free`, `hostOp` add, `buildI`'s allocations | at first-order payloads | [G5c] | — |
| glue | `progOpen`'s nodes at the context `g : fTy ilistL I32, f : ilistL ⊸ 1`; `freeIE`'s and `sumIE`'s application | NB | `BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`, `BangERowM` |

**P33 `countProg`** (`Core/Count.lean:377`; `countProg_derives` `:335`, open at `ΓF`). The user's
case on both sides (§0, fact 4; S3).

| entry | node | every index | missing |
|---|---|---|---|
| R | `AccCountRoot`: `LifeCtx.empty ΓF countProgOpen (.comp (.ret natN))` | NB | the root's context holds `U` slots (`countN : U(N ⊸ F countTy)`, `freeAll : U(L ⊸ F 1)`): glue at `U` slots (`BindRowM`, `LolliERowM` at `countN 3`, `AppRowM`, `LetPairRowM`, `UnitERowM`) |
| values | `CountNW`; `freeAll` | NB; `freeAll` [G5v] from `freeAll_vC` | `CountNW`, the draft's `countN_vC`: induction on the fuel, each stage `c₀V` or `stepV`'s instance (it reads `AccCountZero`, `AccCountStep`) |
| V `c₀V` | `AccCountZero` (`d_c₀`, `:106`) | [bcb] | — |
| V `stepV` | `AccCountStep` (`d_step`, `:178`) at `g : countTy`: the producer | NB | `AllIRowMAt .binder0 (⟨countTy, true⟩ :: Γ)`: the binder-named push at a persistent context (`VRLMStackRename`, the reduction from it with `persistentPushN`, `CtxExtendMSAt`/`CtxShadowMSAt` at a `!U` slot; D5); `BangThunkVRowM` (proved; `PersistentBoxed` holds); in the body `LolliERowM` twice at `withload l cbE` |
| V `cbE` | `AccCountCb` (`d_cb`, `:124`) at `g : countTy`: the carry side | NB | `AllIRowMAt` at the persistent slot (as `stepV`); in the body `SumERowM`, `UnrollRowM` (proved), `BindRowM`, `LolliERowM` at `g [] t` (D9), `AllEVRowM` at `g []` with `'x` in scope (`InScopeOfInterp`, D1), `BangERowM`, `BoxIRowM` |
| V the borrower | `AccCountBorrower` (`d_borrowerE`, `:288`) at `g : countTy` | NB | P10's V2 list |
| K `withload` at `L` | `AccCountLoad`, in `stepV` | NB; gate expected PROVED (one cell: `Imm̲ 'x L` unrolls to `1 ⊕ Imm 'x L`; `CohE` top at the first stage, deep at a tail) | `WithloadRowM` |
| K `withbor` (1) at `L` | in `countProgOpen` | NB | `Withbor1RowM` |
| K `alloc`, `free`, `build3`'s allocations | at first-order payloads | [G5c] | — |

```lean
/-! passProg -/
def AccPassRoot : Prop := ∀ n : ℕ,
  AccNode (ℍ := ℍ) LifeCtx.empty [] (Aff.passProg n) (.comp (.ret .i32))
def AccPassScope : Prop := ∀ n : ℕ,
  AccNode (ℍ := ℍ) LifeCtx.empty [⟨.ref .unit, false⟩]
    (Aff.scopeCbOf (Aff.scopeBodyWith (Aff.passCb n)))
    (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .i32))))
def AccPassCb : Prop := ∀ (n : ℕ) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ (Aff.passCb n) (.val Aff.cntCbTy)
def AccPassStep : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ (.val Aff.counterStep)
    (.val (.bang (.thunk (.arr (.ref .i32) (affStepC .top .i32 .i32 (.ref .i32))))))
def AccPassF : Prop := ∀ (n : ℕ) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₂ Γ (.val (Aff.passF n)) (.val Aff.passTy)
def AccPassTwice : Prop := AccNode (ℍ := ℍ) Δ₂ [] (.val Aff.twiceV) (.val Aff.passTy)
def AccPassRe : Prop := AccNode (ℍ := ℍ) Δ₂ [] (.val Aff.reV) (.val Aff.passTy)
def AccPassReCb : Prop :=
  AccNode (ℍ := ℍ) Δ₂ [] Aff.reCb
    (.val (.all 2 Δ₂.meetOfDom (.lolli (.mut (.var 2) Aff.PC) (.box (.var 2) .i32))))
def AccPassWithbor2 : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withbor (.val (axWithbor2Ty 1 Δ₁.meetOfDom Aff.PC .i32))
def AccPassWithbor3 : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₂ Γ withbor (.val (axWithbor3Ty (.var 1) 2 Δ₂.meetOfDom Aff.PC .i32))

/-! sumListProg -/
def AccSumListRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] sumListProg (.comp (.ret .i32))
def AccSumListAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val sumIAlgV) (.val (algTy ilistF 0 .i32))
def AccSumListLoader : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) ΔA Γ (lam2 (.var 0))
    (.val (.all 1 ΔA.meetOfDom (.lolli .i32 (.box (.var 1) .i32))))
def AccSumListLoad : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) ΔA Γ withload (.val (axWithloadTy (.var 0) 1 ΔA.meetOfDom .i32 .i32))
def AccSumListFoldImm : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (foldImmV ilistF))
    (.val (.lolli (algTy ilistF 0 .i32) (foldTy ilistF 0 LifeCtx.empty.meetOfDom .i32)))
def AccSumListFreeAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val freeIAlgV) (.val (algOTy ilistF .unit))
def AccSumListFoldOwn : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (foldOwnV ilistF))
    (.val (.lolli (algOTy ilistF .unit) (foldOTy ilistF .unit)))
def AccSumListBorrower : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty (⟨fTy ilistL .i32, true⟩ :: Γ) borrowerE
    (.val (VTy.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) ilistL) (.box (.var 0) .i32))))

/-! countProg -/
def AccCountRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty ΓF countProgOpen (.comp (.ret natN))
/-- **`countN` in the draft relation** (the draft's `countN_vC`). -/
def CountNW : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec), StackOK σ αs → OuterBelowTop αs →
    RecsOutside αs ls → SubOutside σ αs δ →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.lolli natN countTy) αs ls countNV PMap.empty
def AccCountZero : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val c₀V) (.val countTy)
def AccCountStep : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty (⟨countTy, true⟩ :: Γ) (.val stepV) (.val countTy)
def AccCountCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ (⟨.imm (.var 0) listL, false⟩ :: ⟨.unit, false⟩ :: ⟨countTy, true⟩ :: Γ)
    cbE (.val cbTy)
def AccCountBorrower : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty (⟨countTy, true⟩ :: Γ) borrowerE
    (.val (VTy.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) listL) (.box (.var 0) natN))))
def AccCountLoad : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom listL natN))
```

**The other programs.** One row each; the V and K columns give each entry's node and expected
status, the glue column the glue rows its derivation reads at nodes that are not first-order, and
the last column the divergences it probes.

| program | V | K | glue (§2.6), NB | probes |
|---|---|---|---|---|
| **P2 `cRecBorrow`** (`Examples.lean:217`; `:247`) | `cMethods` at `methodsTy` (`d_methods`, `:227`) [t]; `borrower cRecLoader` at `borrowerTy methodsTy` [cb]; `cRecLoader` (`d_recLoader`, `:232`; argument `Unk`) [cb] | `withbor` (1) at `methodsTy`: NB `Withbor1RowM`; `withload` at `methodsTy`: NB `WithloadRowM` (gate: no cell); `alloc`, `free` at `methodsTy`: NB `AllocRowM`, `FreeRowM` (a thunk payload, outside G5c); `forgetUnk` [G5c] | `BindRowM`, `AppRowM` at `U` slots; `Proj₁RowM` at `methodsTy` | D8, D11 |
| **P3 `cBang`** (`:175`; `:179`) | `λx. x` at `!U(1 ⊸ F 1)` [bt] (the derivation's own `bangThunkV`) | — | `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM`; the slot used twice and dropped | D4 |
| **P4 `cInst`** (`:307`; `:311`, at `Δ₁`) | `Λ. λy. return y` at `U polyC` [cb→] | — | `AllERowM` at `'a`, in scope (`InScopeOfInterp`); `AppRowM`; `BindRowM` at a `U` slot | D1 |
| **P5 `readFields`** (`RecordPrograms.lean:82`; `:137`) | `readBorrower` (`d_readBorrower`, `:131`) [cb]; the loaders inside it, the field loader and `readCell`'s `Λ. λz. z` [cb] | `withbor` (1) at `Pt.valTy`: NB; `withload` at `Pt.valTy`: NB, gate one cell, top (**the positive control**); `withload` at `B` (`readCell`): NB, gate no cell, deep; `copy` at `Imm '0 Pt.valTy`: NB `CopyRowM`; `alloc`, `free` [G5c] | `LetPairRowM` at `Imm ⊗ Imm`; `BindRowM`, `AppRowM` at `U` slots | D2, D7 |
| **P6 `mutFields`** (`:216`; `:238`) | `mutBorrower` (`d_mutBorrower`, `:224`) [cb]; `swapField`'s closures [t] | `withbor` (2) at `Pt.valTy`: NB `Withbor2RowM`; `withswap` (in `swapField_wf`): NB `WithswapRowM`, with `EntryPayLeaves` at a bound `Mut` read-out (`R1MONO.md` §8); `forgetMut`, `alloc`, `free` [G5c] | `LetPairRowM` at `Mut ⊗ B` | D7 |
| **P14 `exProg`** (`Fundamental.lean:598`; `:601`) | `⟨return (), ⟨⟩⟩` at `U(F 1 & ⊤)` [t] | — | `BindRowM` at a `U` slot, `Proj₁RowM`; `ForceRowM` proved | — |
| **P15 `build3`** (`Lists.lean:61`; `:65`) | — | `alloc` at `L` [G5c] | — (every other node is first-order) | — |
| **P16 `matchSome`** (`RecordPrograms.lean:285`; `:309`) | `matchBorrower` (`d_matchBorrower`, `:292`) [cb]; the branch loaders [cb] | `withbor` (1) at `Opt`: NB; `withload` at `Opt`: NB, gate one cell (the `some` case), top; `withload` at `B` (`readCell`): NB, gate no cell, deep; `alloc`, `free` [G5c] | `BindRowM`, `AppRowM` at `U` slots | D2 |
| **P17 `bagProg`** (`:365`; `:385`) | `pushBorrower` (`d_pushBorrower`, `:374`) [cb]; `pushG` [t] | `withbor` (2) at `Bag`: NB; `withswap` at the list field: NB; `freeNatE`, `freeCE`: NB `FoldOwnRowM` (their algebras [bt]); `forgetMut`, `alloc`, `free` [G5c] | `LetPairRowM` at `Mut ⊗ 1`; `BangERowM`, `LolliERowM` at the folds | D7, D10 |
| **P7 `readFamily`** (`FamilyPrograms.lean:282`; `:322`) | `readCb` (`d_readCb`, `:300`) [cb]; `readOne`, `readBoth` (`d_readOne`, `d_readBoth`, `:229`, `:252`) [cb]; `readOne`'s loader [cb] | `withborF2` at `immM` (`d_withborI2B`, `:292`): NB, `DraftFL` at `withborI2_wf` (`Family.lean:256`), whose nodes are `outer2`, `inner2` at the live linear slot `g` (`AllIRowMAt` at a live `U` slot, D6; its route stopped at `not_readEquivRelend`), `g () (mx, my)` (`AllERowM`, `AppRowM`), `withbor` (1) twice, `ImmSubRowM`, `BoxIRowM`; `withload` at `B` in `readOne`: NB, gate no cell; `copy` at `Imm '0 B`: NB `CopyRowM`; `alloc`, `free` [G5c] | `AllEVRowM`, `LolliERowM` at `readOne ()` and `readBoth ()` (D1, D9); `LetPairRowM` at families | D1, D6, D7, D9 |
| **P8 `swapBothB`**, **P18 `swapBothL`** (`:152`, `:171`; `:154`, `:173`) | `swapCb` (`d_swapCb`, `:77`) [cb]; `swapOut`, `swapIn` [t] | `withborF2` at `mutM`: NB, `DraftFL` at `withborM2_wf` (`Family.lean:247`), as P7; `withswap` twice: NB; P18's `freeCE`: NB `FoldOwnRowM`; `forgetMut`, `alloc`, `free` [G5c] | `LetPairRowM` at families | D6, D7 |
| **P19 `splitFour`** (`:443`; `:522`) | `outerCb`, `innerCb` (`d_innerCb`, `:453`) [cb] | `withborF2` twice: NB, as P8; `MutSubRowM` (`⊑Mut`); the four-leaf allocation [G5c] | `LetPairRowM` at families | D6 |
| **P9 `blockSwap`**, **P20 `nestSwap`**, **P21 `blockRead`**, **P22 `nestRead`**, **P23 `bagBlock`**, **P24 `crossPack`** (`BlockPrograms.lean:113`–`:398`; `:121`–`:407`) | the callbacks `swapCb` (`d_swapCbB`, `:104`), `nestCb` (`:162`), `readCb`, `nestReadCb` (`:266`), `bagCb` (`:339`) [cb]; P23's `pushG` [t] | `withborS` at `σ2`, `σ3`, `bagS` (`d_withborS2`, `d_withborS3`, `d_withborSI2`, `d_withborSI3`, `BlockPrograms.lean:88–100`): NB, `DraftFL` at `withborS_wf` (`BlockBorrow.lean:472`): `innerS` and the outer callback at the live slot `g` (D6), `g () (⇓ mx, my)` (`AllERowM`, `AppRowM`), `withbor` at each leaf, `MutSubRowM`/`ImmSubRowM` in `shortenE`; `withswap` (P9, P20, P23, P24): NB; `allocS`, `freeS` [G5c] | P20's `swapFn ()`, P21's and P22's `readOne ()`, `readBoth ()`: `AllEVRowM`, `LolliERowM`; `LetPairRowM` at families | D1, D6, D7, D9 |
| **P10 `countFoldProg`**, **P11 `anyTreeProg`**, **P25 `anyListProg`**, **P26 `natCopyProg`** (`Folds.lean:375`, `:469`, `:423`, `:511`) | the algebra (`countAlg`, `anyTAlg`, `anyLAlg`; `d_algI`) [bcb]; the free algebra (`freeLAlg`, `freeBTAlg`, `freeBLAlg`; `d_algO`) [bt]; the borrower at `g : fTy M R` (`d_borrowerG`): NB, P10's V2 list | `foldImm`: NB `FoldImmRowM`; `foldOwn`: NB `FoldOwnRowM`; `withbor` (1) at `M`: NB; `alloc`, `free` [G5c] | `progOpen`'s nodes at `g : fTy M R, f : M ⊸ 1` (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`); `BangERowM`, `LolliERowM` at the folds | D1, D4, D5, D9, D10 |
| **P29 `sumProg`** (`CommonList.lean:314`; `:316`) | `sumAlg` (`d_sumAlg`, `:193`) [bcb]; `freeCAlg` [bt]; the borrower: NB, P10's V2 list | `foldImm` twice (`sumCE`; `natCopyE` inside the algebra): NB; `foldOwn` (`freeCE`, `addE` at `N`): NB; `withbor` (1): NB; `alloc`, `free` [G5c] | as P10; inside the algebra `AllEVRowM` at `natCopy []` (`d_natCopyAt`, `:159`), at the algebra's own variable, and `BangERowM` | D1, D4, D5, D9, D10 |
| **P30 `mapProgC`**, **P31 `mapProgR`** (`CommonList.lean:413`; `ReuseList.lean:209`) | `borrowerM` (`d_borrowerMC`, `CommonList.lean:333`) at the live slot `mapInc : U(L ⊸ F L)`: NB, `AllIRowMAt` at a live `U` slot (D6); its `withswap` callback, a closure capturing `mapInc`: NB, `ThunkVRowM` (proved) over a body at a `U` slot (`BindRowM`, `LolliERowM`) | `withbor` (2) at `L`: NB; `withswap` at `L`: NB; `mapIncCE`, `toPureCE` (`foldOwn`), P31's `mapIncRE` (`foldReuse`): NB `FoldOwnRowM`, `FoldReuseRowM`; `forgetMut`, `alloc`, `free` [G5c] | `mapProgOpenC`'s nodes at `ΓMC`'s `U` slots (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`) | D6, D7, D10 |
| **P32 `mapProg`** (`MapMut.lean:462`; `:471`, open at `ΓM`) | R at `ΓM`: NB, glue at `U` slots; the values `mapInc` and `toPure`, at first-order types, which Core proves by hand at every reading (`mapInc_semV`, `MapMut.lean:252`; `toPure_vC`, `:361`): [G5v]; `borrowerM` as P30 | as P30 | as P30 | D6, D7, D10 |
| **P34 `countFreeProg`** (`CountFree.lean:299`; `:258`, open at `ΓC`) | R at `ΓC`: NB, glue at the `!U` and `U` slots; the values: `countFree`, proved by hand on the witness's size (`countFree_semV`): NB `CountFreeW` (not stated); `freeAll` [G5v]; the borrower at `g : countTy`: NB, P10's V2 list | `withbor` (1) at `L`: NB; `alloc`, `free` [G5c] | as P33's root | D1, D5, D9, D10 |
| **P13 `arrProg`** (`ArrayPrograms.lean:47`; `:54`) | `tab10V`, `dropI32V` (`d_tab10`, `:33`; `d_dropI32`, `:42`) [bt] | `arrNew` (a `!(I32 ⇒ A)` argument): NB `ArrNewRowM`; `arrFree` (a `!(A ⇒ 1)` argument): NB `ArrFreeRowM`; `arrReplace`, `arrSize`, their dereliction, `hostOp` [G5c] | `BangERowM` at `arrNew`'s and `arrFree`'s `!` | D4, D10 |
| **P28 `signProg`** (`IntPrograms.lean:317`; `:341`) | — | `hostOp` (`div_s`, `div_u`, `mul`) and their dereliction [G5c] | none: every other node is first-order | — |
| **P12 `counterProg`** (`AffPrograms.lean:235`; `:237`) | the scope callback [cb], its body rebuilt as `d_scopeProg`'s; `cntCb` (`d_cntCb`, `:136`) [cb]; `counterStep` [bt] | `withbor` (1) at `1`, `withbor` (2) at `PC`, `withswap` at `PC` (`callMut`), `unfoldN` (`mkBox`): NB; `alloc`, `free`, `forget`, `swap`, `hostOp` [G5c] | as P39's glue | D4, D7 |
| **P35 `ofFnProg`**, **P36 `onceProg`**, **P37 `dropProg`**, **P40 `retProg`** (`AffPrograms.lean:374`, `:403`, `:424`, `:713`) | `counterStep` [bt]; `incV` (`d_inc`, `:365`) [bt]; `ofFnStep` (`d_ofFnStep`, `AffRules.lean:230`; its state a `!U` value, outside `FOArg`): NB `LamRowM`; P36's `onceE` (`d_once`, `AffRules.lean:266`): NB; P40's `mkCounterV` (`d_mkCounter`, `:706`; its answer `FC` is no first-order type): NB `LamRowM` and `d_mkBox`'s glue | `unfoldN`: NB; `alloc` [G5c]; P37's destructor (`drop_derives`, `Dtor.lean:330`): NB, glue at `FC` | the closures at the top level, at `FC` slots: `BoxERowM`, `Proj₁RowM`, `Proj₂RowM`, `AppRowM`, `LetPairRowM`; `d_mkBox`'s | D4 |
| **P38 `nestProg`** (`:508`; `:510`) | the scope callback [cb]; `counterStep` [bt]; `doubleStep` (its state `FC`, outside `FOArg`): NB `LamRowM` | `withbor` (1) at `1`, `unfoldN` twice: NB; `alloc`, `free` [G5c] | as P35 | D4 |
| **P41 `logProg`** (`:837`; `:842`) | the borrow's callback (`d_logCb`, `:825`) [cb]; `logInner` (`d_logInner`, `:792`; it captures `ml : Mut '0 I32`, a first-order slot) [cb]; `logStep` (its answer holds `[@'w] Mut '0 I32`): NB `LamRowM` | `withbor` (2) at `I32`, `withbor` (1) at `1`, `withswap` at `I32` (in `logStep`), `unfoldN` (`mkBox'w`): NB; `alloc`, `free`, `forgetMut` [G5c] | as P35 | D4, D7 |
| **P42 the BoLo programs** (`EmbeddingExamples.lean:22–54`) | R [G5]: `embed d_X` at `F 1` | every other node: NB, `DraftFLEmbed` (G12) at `d_X` | through G12 | the paper's own programs |

### 3.6 The seeds

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

By G5, `pairLoad`'s root and its callbacks' entries are proved at every index, from Core's own
proof [expected]. The pair's defect is in the `withload` constant's row (`DraftFL` at that node,
K2), not in a judgement of the program's own terms. `LEDGER.md`'s suite section says so beside the
pair's entries.

| entry | node | every index, now | after the block |
|---|---|---|---|
| R | `LifeCtx.empty [] pairLoad (.comp (.ret .unit))` | [G5] | [G5] |
| V1, V2 | the borrower at `borrowerTy pairTy`; `pairLoader` at `Δ₁` | [cb] | [cb] |
| K1 | `withbor` at `axWithbor1Ty 0 _ pairTy .unit` | NB (`Withbor1RowM`) | the same; its empty-stack form attempted (§4.6) |
| K2 | `AccPairLoadWithload` | NB; route blocked: the own push lends one place, and the second reborrowed cell fails the table (`loadGuardFails2`) at the identity instantiation of the answer's `U` clause, at every stack. At the thunked type the answer's `U` clause at a non-identity instantiation moves the push below the cells (`not_withloadPairGapInst`), a route not refuted and not built | gate `LoadGateNilB` [expected PROVED]; at `[]` PROVED if `WithloadNilRowM` closes (§4.6); at every index NB unless `WithloadRowM` does |
| K2′ (`pairLoadU`) | `AccPairLoadWithloadU` | NB; **route blocked at an arising configuration**: `withloadUPairGapReal` (`NxGuardPair.lean:844`). At the stack `[e]` of the enclosing 6.64 lend of the pair, `ArisesI` with the view `ArisesVI`, the program typed at `withloadU` (`PairWithloadUTyped`), the payload reborrowed by `TW.reb` at an own push's lifetime fails the guard at every reading the callback's clause offers (`PairGuardRejectsU`). The entry's own judgement is not refuted: another argument might meet the table at a non-identity instantiation (`PairArgCellsLe`, not built), so it is not a FAILS | as K2, at `WithloadUNilRowM`, `WithloadURowM` |
| K2, K2′ at `[]` | `AccNodeNil` at their nodes | NB. At `withloadU`'s type, after (E1), the route fails at the empty stack too (`withloadUPairGapNilE1`), at a view not shown to arise: no evidence of a defect, and no trigger to revisit (E1). At the thunked type the answer's `U` clause moves the push below the cells (`not_withloadPairGapNilInstE1`) | at `[]`: PROVED if `WithloadNilRowM`, `WithloadUNilRowM` close |

```lean
/-- S1's K2: `withload` of a pair, at every index. -/
def AccPairLoadWithload : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit)))

/-- S1's K2′: the same at `withloadU`'s type at the empty row. -/
def AccPairLoadWithloadU : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (withloadUTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit) []))
```

**S2 `sliceLoad`: `withload` of a slice.** A reduced transcription of `corpus/array-get.bc`:
`withbor` (1) lends `Imm 'x (Array i32)`, and `withload` turns it into the family
`ArrayImm 'y i32` of two leaf views at one lifetime:

    array_new (2, tab10) to a. alloc a to r.
    withbor r (Λ'0. return (λb. withload b sliceLoader to t. return (box t))) to p.
    let (r′, t) = p in free r′ to a′. array_free (dropI32, a′); t

`sliceLoader = Λ'1. return (λf. array_len f to n. return (box n))`. Its argument is
`fam (Imm '1 i32)` (`FOArg`), and its result is flat. To build: `d_sliceLoader` and
`sliceLoad_derives`, reusing `d_tab10`, `d_dropI32`, `CDerives.arrNew`, `.arrLen` and `.arrFree`.

| entry | every index, now | after the block |
|---|---|---|
| R; V (the borrower, `sliceLoader`) | [G5]; [cb] | the same |
| K `withload` at `Array i32` | NB; route blocked (two cells), at a configuration not yet built for the slice (`SliceUGapReal`, not built) | gate PROVED [expected]; row as S1's K2 |
| K `arrLen` at `'1` | [G5c]: `!(ArrayImm '1 I32 ⇒ I32)` is first-order, and G5c reads Core at every reading | the same |
| K `arrNew`, `arrFree` | NB (`ArrNewRowM`, `ArrFreeRowM`, as P13) | the same |

The slice *lend* (`slice_borrow_imm`, `corpus/slice-imm.bc`; `sliceBorrowI`) is optional: its gate
mirrors `LoadGateNil` with the lend's frames (`SliceFrames`, `Nx.lean:278`), as `SliceGateNil`.

**S3 the user's case.** Served by P33 `countProg`, which exists and is user-written on both sides:
`stepV` is a persistent lifetime-polymorphic combinator made at a persistent context (the
producer), and `cbE` and the borrower carry it into a lend's callback and call it at the callback's
own lifetime (the carry side). P10, P11, P25, P26, P27 and P29 serve the carry side only: their `g`
is `foldImm` of an algebra, so their producer is `FoldImmRowM`, not a user-written `∀I` at a
persistent context. No new seed is built. P33's `stepV` and `cbE` entries are NOT BUILT; their
missing lemma is the binder-named push at a persistent context (`VRLMStackRename`, and the
reduction from it), and the carry side also needs `AllEVRowM` and `LolliERowM` (P10's V2 list).

**S4 `reconB′`** (`NxRecon.lean`, `reconB'`, `reconCb`). Tier 2, not floor: no Core derivation
exists, since `wait` resumes inside the lend and the unwinding rules do not admit it.

| entry | node | expected | missing |
|---|---|---|---|
| R | `LifeCtx.empty [] reconB' (.comp (.ret (.tensor Flag Flag)))` | NB | a flat-answer root is Core's semantic acceptance (G7's `CRLMRetNil`); with no Core derivation, only a semantic proof of the run would give it, and that reads no draft clause |
| V | `reconCb` at its callback type | NB | the typing (which rule types `withborUE dFlag` under `wait`); the callback row `CallbackExtImmMF`; the body at the `F_Σ` type at the push (statements 1–3); `reconCb_allI` covers only the `∀I` step |

**S5 `loadKeepsView`, optional (D3).** `cImmBorrow` with the borrower copying its view and the loader
capturing the copy: `let (b₁, b₂) = copy b in withload b₁ (Λ'1. return (λq. forget b₂; …))`. The
loader's context is `b₂ : Imm '0 1`, which is `FOArg` and reaches no `U`, so its V entry is PROVED
by `AllIRowMAt` at that context with G5 [expected]. The K gate at `A = Ref 1` fails `OwnOKI.placeFree`
at the needed entry: the callback deep-holds the reborrowed place's `own` cell under the copy's
`imm` ancestor. `OwnOKB`'s relaxed `placeFree` (§4.2) admits it. So the gate is route-blocked now,
and PROVED after the block [expected].

### 3.7 Not in this suite

- **The effect programs** (class E, §3.4) are tier-1 floor, with abortive operations inside a lend
  and no suspension: `logInBorrow`, `reborrowRaise`, `storeCancel` (`Core/EffPrograms.lean:614`,
  `:385`, `:939`) among them. They read the draft's `F_Σ` clause at the pushed stack (GhostEnd's
  piece) and the unwinding callback rows (`CallbackExt*M` at the `.arr` shape). They belong to the
  next suite, whose seeds they are. After the block, an abortive effect inside a `withload`-of-pair
  callback also reads D12 (§4.2).
- **The codata programs** (class C) read `ν` through Core's `cC`, equal by definition (C11). Their
  other draft nodes are a persistent step (the box, D4) and `unfoldN`, both read by the affine
  programs P12, P35–P41, so they add no row the suite does not read.
- **Corpus programs** have no Lean derivation, so the seeds transcribe them.

### 3.8 `GroundRegress.lean` and the results table

`GroundRegress.lean` imports `ProbeD1.GroundLedger` and the Core program modules. It holds:
- the producer lemmas (§3.2) with their proofs, and G5c's and G5v's uses;
- the gate (§3.3);
- the seeds' terms and derivations (§3.6);
- per program, one `def Acc<Prog><Entry> : Prop` per entry, in P1's form, each at every index
  (`AccNode`). Each has a theorem where PROVED, with its `EntryRead` lemma, and otherwise a
  docstring naming the missing lemma; a "PROVED at `[]`" entry has its `AccNodeNil` theorem.

Also `def Acc<Prog> : Prop`, the entries' conjunction. `LEDGER.md`'s results table has one line per
entry (program, entry, kind, status at every index, status at `[]`, theorem or missing lemma) and
one line per program: "entries: n PROVED, m NOT BUILT; glue rows (§2.6): …, not stated". A
program's line never reads "accepted".

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
`Binder.lean`'s definitions. They are `NEXT.md` §1.6's, with the corrections of §4.3, and with
`StackJ`'s block form split in two: `StackJBase`, the form `SemIdxM` and `SemSMC` read, and
`StackJB`, which adds `StackJM`'s extra conjunct for `SemSM`.

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

/-- **`StackJ` with blocks**: its distinct variables dropped (`StackOKB`'s variable condition
replaces them), its third kind read at the innermost block. `SemIdxM` and `SemSMC` read it. -/
def StackJBase (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (∀ e ∈ σ, ∀ y, VFree y e.T → (∃ u, Δ.find? y = some u) ∨ y ∈ σ.map LEnt.x) ∧
  ∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head?.map LEnt.x = some e.x ∧ CtxFresh e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧ ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)

/-- **`StackJM` with blocks**: `StackJBase` and `StackJM`'s extra conjunct at the innermost block.
`SemSM` reads it. -/
def StackJB (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  StackJBase σ αs δ Δ Γ C ∧
  ∀ e ∈ σ, Δ.find? e.x = none → σ.head?.map LEnt.x = some e.x → (∃ c C', C = .all e.x c C') →
    (∀ a ∈ αs.head?, SubFresh δ a) ∧ ∀ e' ∈ σ, ¬ VFree e.x e'.T

/-- At distinct variables the block forms are the old ones. -/
def StackJBaseIff : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy),
    (σ.map LEnt.x).Nodup →
      ((StackJBase σ αs δ Δ Γ C ↔ StackJ σ αs δ Δ Γ C) ∧
        (StackJB σ αs δ Δ Γ C ↔ StackJM σ αs δ Δ Γ C))
```

`StackJBaseIff` is planned with the gate (§4.4): at distinct variables the block forms are the old
ones, so a statement that reads `StackJ` or `StackJM` at a stack with no block keeps its meaning.

**The edits to existing definitions** (`R1.lean`, after its import of `ProbeD1.Block`), and nothing
else:
- `cRLM`'s `∀` clause (`:210`): the own-lend conjunct pushes a block (the fragment below).
- `SemSM` (`:246`): `StackOK` becomes `StackOKB`, and `StackJM` becomes `StackJB`.
- `SemIdxM` (`:946`) and `SemSMC` (`:803`), which read `StackJ`, not `StackJM`: `StackOK` becomes
  `StackOKB`, and `StackJ` becomes `StackJBase`. Neither gains `StackJM`'s extra conjunct.

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
- **GhostEnd's piece, which cannot be edited, and which splits a block.** `cRLM`'s `F_Σ` clause at
  `binder0` reads `bodyS`, `OpenS` and `stopS` (`GhostEnd/Stacked.lean`). After a stop:
  - the kept entries are re-lent over `ReLend` (`RelendableN`, `:170`; `ReLend`, `:158`), whose chain
    is strict (`List.IsChain (· < ·) αs'`);
  - the ghost-ended entries are re-lent by `openFS` (`:215`) under `List.Forall₂ (· < ·)` with a
    strict chain of the whole vector.

  So every re-lend after a stop gives a block's entries distinct lifetimes, and at a block vector
  the identity is no re-lend [read: the two strict chains]. The continuation (`effRetM`, `bodyS` at the re-lent vector) is read at
  a vector where two entries share a variable and not a lifetime, which `StackOKB` excludes, and
  `extS` there reads the variable at its innermost entry's lifetime. This is a new divergence the
  edit makes in the one draft relation (D12). It reaches no borrow-only program, since none reads an
  `F_Σ` row; it reaches the tier-1 floor at an abortive effect inside a `withload`-of-pair callback
  (§3.7).
- **`InstReLend` fails at a block.** An instantiation of a block vector keeps the block's equal
  lifetimes equal, so it is no strict-chain `ReLend` (`InstReLend`, `Binder.lean:478`, is stated and
  proved at `StackOK`, `instReLend`, `BinderInst.lean:267`). `guardInst` (`BinderPV.lean:563`) is
  proved through `instReLend` and `tabRelend` (`Thunk.lean:185`), so at a block stack it needs a route
  that does not pass `ReLend` (`GuardInstB`, §4.5).

**The forward obligations** (`NEXT.md` §1.6), carried:
- The share at `binder0` must re-lend a block together. Its replacement is the share over
  instantiations (`ShareReLendInst`'s direction, `Binder.lean:549`), which re-lends the ghost-ended
  part as one instantiation and so keeps a block's lifetimes equal. It is owed before any effectful
  callback under a block lend is claimed.
- `InstReLend` at a block (above).
- Statement 2's `SpanLoadRow` at a payload with two leaves becomes attemptable.

### 4.3 Corrections to `NEXT.md` §1.6

1. **`OwnPushBOfM` is false as stated** [unchecked: `NotOwnPushBOfM`, below, is not proved]. At an
   `.arr` type whose argument has its borrow leaves below the top (`(Imm 'x 1 ⊗ Imm 'x 1) ⊸ D`),
   `OwnPushI`'s `ViewAt` is `True`, so `OwnPushM` admits an entry whose payload type matches no leaf
   (`int`). `ViewAtB` rejects that entry. The design's statement is replaced by the form its
   consumers need, the callback rows at `e.T = T` under a top-level `Mut 'y T` or `Imm 'y T`, and
   the counterexample is to be recorded as a fact about our statement:

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
   fewer obligations for the `∀I` row. That it loses nothing a consumer needs is [unchecked]. The
   `.arr`-shape consumers are the unwinding constants' callbacks (`cbUTy`: `withbor1U`, `withbor2U`,
   `withbor3U`, `withloadU`, `sliceBorrowIU`, `sliceBorrowMU`) and user callbacks at an `.arr` type
   (`cInst`'s `polyC`). Each is to be checked against `ViewAtB`.
2. **`foldImm`'s algebra is at the `.ret` shape, not the `.arr` shape.** `NEXT.md` §1.6 lists it
   among the `.arr`-shape consumers "[read: the rule's docstring]". But `algTy` is
   `!(VTy.all y ⊤ (VTy.lolli A_R R))` (`Core/FoldImm.lean:99`), and `VTy.all x b A` is
   `U(∀'x ⊏ b. F A)` (`Core/Types.lean:163`). So the algebra's computation type is
   `∀'y ⊏ ⊤. F (U(A_R ⊸ F R))`, where `ViewAtB` is vacuous, as at the non-unwinding constants'
   callbacks [read]. `withbor` (3)'s callback in `axWithbor3Ty` is at the `.ret` shape too.
3. **`StackJB`'s third kind** reads "the innermost block", `σ.head?.map LEnt.x = some e.x`, where
   §1.6 said "every entry of the innermost block" without a formula. §1.6's `StackJB` is split here
   into `StackJBase` and `StackJB` (§4.2).

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

Then `StackJBaseIff`, `OwnPushBOfMView`, `NotOwnPushBOfM`, and the block gate at the suite's
payloads: `LoadGateNilB` (below) at `pairTy` and `Array i32`, at both shapes, in both of `CohE`'s
cases, and at `Ref 1` under S5's frozen copy.

```lean
def LoadGateNilB (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (W : WRes) (ℓ : BoCa.Loc) (u : Val) (R : WRes) (x : LifeVar)
    (c : Lifetime.Life) (β : Life) (cb ρc ρ : WRes),
    CohE (rsOf ls) ℓ A δ → LoadPay W (rsOf ls) ℓ u R → ¬ VFree x A → δ.find? x = none →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) u cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ τ : LStack, OwnPushB δ (.all x c (C' x)) ρc ([], []) τ β ∧
      vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (A.immReborrow (.var x)) (blockL τ β) ls u cb ∧
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
   `Binder*`/`Gap*` that take `StackOK` are generalized as needed (`viewSlotInstOB`, `cohEInstOB`,
   the `extS` lookups). `guardInst` needs a new route, `GuardInstB`: the table at an instantiated
   block stack read directly, since `instReLend` and `tabRelend` read `ReLend`'s strict chain
   (§4.2) [unchecked: `no_bound_of_stratS`, which `guardInst` also reads, takes the strict chain].
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
11. **`GroundLedger.lean`, `GroundRegress.lean`**: re-checked. G1–G5, G5c and G5v do not read the
    push. The producer lemmas compose the re-proved rows.

**The proved rows that read the piece or `ReLend` at a pushed stack**, which the stop rule watches,
since a block stack's re-lends split the block (§4.2):
- `cRLM_step`'s `F_Σ` case (`R1AllI.lean:132`): `wpG_step`, generic in the postcondition, so the
  piece's re-lends are not read [read]. Expected unchanged.
- `statement0MBesideMono0`'s shared lemmas (`Statement0SharedM`, `R1.lean:1397`): `OpenSFBridge`
  (`openSF_openS`, generic in the stack) and `NilSoundRetM` (at `[]` only). Expected unchanged.
- `guardInst` (`BinderPV.lean:563`), through `instReLend` and `tabRelend`: at a block stack it is
  replaced by `GuardInstB` (item 2); it is the first place the stop rule can fire.
- `NxAllI.lean`'s `ReadEquivRelend` (`:227`) and its refutation `not_readEquivRelend`: stated at
  `StackOK`, a fact about `ReadEquiv` that the block does not change; the route to
  `VRLMReadEquiv` meets the piece's re-lend at a block stack as well.
- `tabRelend` (`Thunk.lean:185`) and the rows of W₀ that read `RelendableS` (§2.10): at `StackOK`,
  unchanged.

### 4.6 The suite after the block, and the rows attempted

**The target**: the gates of S1 and S2 (`LoadGateNilB` at `pairTy` and `Array i32`, both shapes,
both of `CohE`'s cases) and of S5 go PROVED, and three rows at the empty stack are attempted. Every
other entry keeps its status.

**The rows attempted**, in this order, at whichever relation (3)'s edit leaves: with the block, or,
after the fallback, without it.

```lean
/-- `withbor` (1) at the empty stack: `withbor1_compatX` ported, the callback read at the own push
of the lend (`CallbackExtImmMF`). -/
def Withbor1NilRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    VScoped Δ A → ¬ VFree x A → ¬ VFree x B →
    SemSMNil (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))

def WithloadNilRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSMNil (ℍ := ℍ) .binder0 Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))

def WithloadUNilRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSMNil (ℍ := ℍ) .binder0 Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B []))
```

Each follows its Core lemma's route step for step. The draft's own steps, where the port can stop:
- **`Withbor1NilRowM`** (`withbor1_compatX`, `Compatibility.lean:937`):
  - (w1) the own push of the 6.64 lend at the fresh `α`, `[en]` lending `ℓ`: `OwnPushM` at
    `([], [])`, its `OwnOKI` from the frame's freshness and `placeFree` from the callback holding no
    cell at `ℓ`, `payLocal` and `selfFree` from `hfree₁`;
  - (w2) the guard at the push (`tabAtS_start_one`, `pvlStart`);
  - (w3) the callback read at the push (`CallbackExtImmMF`, `Nx.lean:466`, stated): its own-lend
    conjunct at `[en]`, the answer's `U` clause at the identity (`relendJ_id`,
    `R1Mono.lean:1345`), the `⊸` at the view;
  - (w4) the answer `['x] B` brought from `[en]` back to `[]` at the frame's end, by G1 at a flat
    `B` (at a non-flat `B`, not attempted).

  Core's instance of the callback's `∀` at `α` is (w1)–(w3), since (E1)'s first conjunct reads no
  instance not in scope.
- **`WithloadNilRowM`** (`withload_compatX`, `:252`):
  - (l1) the chooser, unchanged: `rebChooseTW_top` or `rebChooseTW_deep`, by `CohE`'s case;
  - (l2) [TR] 6.150 (`wpTS_reborrow`), unchanged;
  - (l3) the callback's own push at the block of the reborrowed places at `β`, where `β` is chosen
    below the records' readings as well (`И` admits every lifetime below a bound): `LoadGateNilB`;
  - (l4) the answer's `U` clause at the identity (`relendJ_id`), and the `⊸` at the reborrowed
    argument;
  - (l5) the answer's return to `[]` at a flat `B`, by G1.
- **`WithloadUNilRowM`** (`withloadU_compatX`, `EffBorrow.lean:548`): the same at the `.arr`
  shape, (l4) without the answer's `U` clause.

**The stop rule for the attempted rows.** At the first step of a row that does not port, stop that
row, record the step as an elaborating `def … : Prop` (its missing lemma), and go to the next row.
The entries that read the row stay NOT BUILT with that lemma: K1 of P1 and of nearly every program
(`Withbor1NilRowM`), and the `withload` K entries of P1, P2, P5, P16, P27, P33 and S1, S2. If a row
closes, its entries go "PROVED at `[]`".

**The stretch: the every-index rows** (`Withbor1RowM`, `WithloadRowM`, `WithloadURowM`, §2.6), the
reading inside a lend. They use `PairGuardHoldsB` at a non-empty stack, the block's form of the
step `withloadUPairGapReal` blocks. They are preferred if the proof is uniform in the stack. If
`WithloadURowM` closes, S1's K2′ goes PROVED at every index, and the arising route block is
answered by the block push lending both places.

### 4.7 The statement-change register

The outcome lists:
- (a) every theorem whose text changed, with the reason;
- (b) every theorem whose proof changed and whose text did not;
- (c) every claim, in the docs, about a theorem whose text did not change but whose meaning did,
  because it reads `vRLM`, `cRLM`, `SemSM`, `SemIdxM` or `SemSMC`:
  - `statement0UFullM`, `allIRowMUFree0`, `callbackExt*M_own`, `forceRowM`, `rollRowM`,
    `unrollRowM`, `muAdjVRLME1`, the box's facts, and the `Ground*` theorems;
  - **`SemIdxM` and `SemSMC`**, and every statement that reads them (the `RetainedPay*Row` rows,
    `PairCfg`, `SliceCfg`, `MonoOwnGMC`, `AllIRowMC`): they now admit block indices (`StackOKB`,
    `StackJBase`). At a stack with no block their index is the old one (`StackOKBOfOK`,
    `StackJBaseIff`);
  - **`cRLM`'s `F_Σ` clause at block stacks**: its text is GhostEnd's and unchanged, but `SemSM` now
    reads it at stacks with a block, where its re-lends split the block (D12, §4.2).

Historical relations (`vRL`, `vRLI`, `vRLJ`) and their results do not change.

### 4.8 Success, the stop rule, the fallback

**Success.** All of the following:
- The gate lemmas of §4.4 are proved.
- With the edit, `lake build ProbeD1` is clean. Every theorem proved before is proved after, with
  its text unchanged unless it is listed in §4.7 (a) with its reason. There is no forbidden keyword,
  and every axiom set is within the three.
- S1's and S2's gates are PROVED at the block relation, and S5's if built.
- `Withbor1NilRowM`, `WithloadNilRowM` and `WithloadUNilRowM` are attempted; each is proved, or the
  outcome names the step (§4.6) that did not port, as an elaborating `def … : Prop`.

The pair and slice entries then read: the gates PROVED; K2 and K2′ at `[]` PROVED if the `withload`
rows close, and otherwise NOT BUILT with the named step; at every index NOT BUILT unless the stretch
closes.

**The stop rule.**
- Gate first. If `StackOKBOfOK`, `InstStackOKB`, `PairGuardHoldsB`, `PVLStartB`, `StackJBaseIff` or
  `LoadGateNilB` at `pairTy` fails, make no edit. Record the failing statement as an elaborating
  `def … : Prop` with its counterexample, if one exists.
- Re-prove in §4.5's order. Stop at the first row whose proof needs a definition change beyond §4.2's
  list, or that reads the piece's or `ReLend`'s strict re-lend at a block stack (§4.5's watched
  rows). Record that row and the change it needs.

**The fallback.** If the stop rule fires after the edit:
- Revert the edits to `cRLM`, `SemSM`, `SemIdxM` and `SemSMC`, so the branch builds clean with every
  earlier result.
- Keep `Block.lean` and `GroundBlock.lean`, beside the relation and not in it, as `NEXT.md` §1.6's
  convention keeps a candidate.
- Record the frontier.
- Attempt the three rows of §4.6 at the reverted relation, where `WithloadNilRowM`'s step (l3) reads
  single pushes (`LoadGateNil`): it can close at payloads with at most one reborrowed cell.

The suite then reports the pair and slice entries as NOT BUILT, with the frontier as the missing
lemma. If `OwnOKB`'s relaxed `placeFree` is what fails, use `OwnOKI`'s strict form for blocks, as
`NEXT.md` §1.6's fallback says. Then record that a callback holding a copy of the view has no block
push, and S5 stays route-blocked.

**The outcome** says, beside the results: the share's block re-lend (`ShareReLendInst`'s direction)
is owed before any effectful callback under a block lend is claimed (D12).

---

## 5. Order of work and the stop rule

1. (0): the doc edits and the box's Lean docstrings, one commit, with a targeted build.
2. (1): `GroundLedger.lean` (G1–G12, `GRestrict`, the rows of §2.6 as statements), then
   `LEDGER.md`'s rows (§2.2–§2.10), one commit.
3. (2): `GroundRegress.lean`: the producer lemmas, the gate, the seeds' derivations, the entries of
   every B program of §3.4 at every index with their `EntryRead` lemmas; then `LEDGER.md`'s suite
   section, the enumeration and the results table, one commit. P39, P27 and P33 first.
4. (3): `GroundBlock.lean`'s gate, then the in-place edit and §4.5's re-proofs, then the three rows
   of §4.6, then the suite re-run, one or more commits. Stretch: the every-index rows.
5. The outcome: `LEDGER.md` §results, CHECKPOINT, README.

**The stop rule.** (0)–(2) are done whatever (3) does. In (2), an entry whose proof does not close is
recorded NOT BUILT with its exact missing lemma; it does not stop the suite. No FAILS is recorded
without an arising configuration (§3.1). In (3), §4.8's rules.

---

## 6. Files

| file | contents |
|---|---|
| `GROUND.md` | this design |
| `LEDGER.md` | the ledger (§2), the enumeration and the suite's results (§3), with the outcome |
| `ProbeD1/GroundLedger.lean` | G1–G12, `GRestrict`, the rows of §2.6, and the floor's statements (`DraftFL`, `DraftFLNil`) |
| `ProbeD1/GroundRegress.lean` | the producer lemmas, the gate, the seeds, the entries |
| `ProbeD1/Block.lean` | the block's definitions (§4.2), imported by `R1.lean` |
| `ProbeD1/GroundBlock.lean` | the block's gate lemmas, the block gates (§4.4), and the rows attempted (§4.6) |
| `ProbeD1/R1.lean` and the files of §4.5 | the in-place edit and its re-proofs |
| `ProbeD1/R1.lean`, `ProbeD1/R1Box.lean`, `ProbeD1/R1Thaw.lean` | part (0)'s docstring edits (§1.4), comment-only |
| `ProbeD1.lean` | imports of the new files |

---

## 7. Report lists (to fill in the outcome)

- **Printed objects read.**
  - [TR] 6.150 (`TW.reb`, `TW.rebDeep`, `wpTS_reborrow`) in the gates and the attempted rows.
  - [TR] 6.172–6.175's compatibility lemmas as the rows' routes (`withbor1_compatX`,
    `withload_compatX`, `withloadU_compatX`).
  - `fundamentalC`, `embed` and `adequacyD` as the grounding theorems' sources.
- **Printed hypotheses unspent.** None expected. The unit proves no printed lemma; every statement is
  ProbeD1's, about the draft, and the printed objects are applied with every premise discharged.
- **Uniqueness and functionality results.** Expected used: `ResU.CompS.functional` in the gates. To
  report: whether the `withload` rows read 6.150's chooser determinacy.
- **Printed lemmas in the run-up that are untranscribed.** None for (0)–(2). For (3)'s rows, the
  draft analog of 6.150 consumed through an own push is ProbeD1's own, not printed.
- **Hypotheses added.**
  - `FOArg`/`FlatTy`/`FOComp`/`FOConstTy` and `NilTy`/`NilVal`/`NilComp` on the grounding theorems.
    Each is non-vacuous at the suite's types.
  - The gate's freshness hypotheses (`ρc.InStratum β`, `RecsOutside [β] ls`, `SubFresh δ β`,
    `β < ⊤`). The row's choice of `β` meets them.
  - The rows' `BindersLow`/`Scoped` hypotheses at their premises' types (§2.6), as each row needs.
  - On the block: §4.3's `OwnPushBOfMView` hypothesis.
- **Technique built.** The grounding theorems follow `vRLM_dataE`'s environment induction (G1) and
  `adequacyD`'s proof (G11). G5c reads Core at each instantiated reading. The attempted rows follow
  `withbor1_compatX` and `withload_compatX` step for step.
