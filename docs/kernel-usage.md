# Kernel usage: which proved pieces the surface and the backend use

An audit (#633) of every kernel rule, constant, derived form and type former. For each it records
whether the checked corpus produces it, whether the backend reads what it proves, and what would
change that. Nothing in this unit changes the compiler or the kernel.

## 1. How the rows were enumerated

The rows come from the definitions themselves, by script, not from a list kept by hand.

| group | source of truth | rows |
|---|---|---|
| `CDerives` rules: the CBPV formers and the axiom-table constants (`swap`, `copy`, `forget*`, `withbor1/2/3`, `withload`, `withswap`, `alloc`, `free`), with the array, slice, loop, `Div` and effect constants | the constructors of `CDerives` (`Core/Fundamental.lean:86`), cross-checked by the generator against the annotations (an assertion fails if a constructor is missing) | 96 |
| `CDerivesP`-only rules (SPEC §29) | the constructors of `CDerivesP` (`Core/PinDerives.lean:97`) not in `CDerives` | 3 |
| derived nodes and `use` | the constructors of `TExpr` (`Frontend/Check/TExpr.lean:263`) that are not rules | 13 |
| type formers | the constructors of `VTy` and `CTy` (`Core/Types.lean:44`) | 23 |
| derived forms with no node of their own | every `Core` declaration that is a theorem concluding with `CDerives`/`CDerivesP`, or a definition of a `VTy`, `CTy`, `Expr` or `Val`, outside the program and example files (`scripts/KernelDecls.lean`; 770 declarations, `docs/kernel-usage/decls.tsv`), grouped into the forms SPEC names | 8 |
| **total** | | **143** |

The 112 `TExpr` constructors are exactly the first three groups, so `TExpr.ctorIdx` gives each node
its row. The 770 Core declarations include each program's own derivation (`d_*` in
`*Programs.lean`, `Folds.lean`, `CommonList.lean`, `Count.lean`, `Stdio.lean`'s model), the
`Splits.lean` weakening helpers, and the auxiliary terms of a rule (`DivReify.lean`'s `rkV`, …).
These are not forms a program can produce, so they get no row. `decls.tsv` lists them with their
users.

### Counting

- **Produced?** `scripts/kernel-census.sh` (`scripts/KernelCensus.lean`, the executable
  `kernel-census`, which is not a default target) checks every program `scripts/check-corpus.sh`
  checks, as `bcc check` does. That is 375 files, of which 374 have a `main`; `corpus/13-1-library.bc`
  has none. It walks `main`'s typed term (`Checked.t`) and prints one line per `TExpr` constructor
  (`docs/kernel-usage/census.tsv`), with these columns:
  - `progs`: the number of programs whose term has the node.
  - `static`: the nodes of the derivations the checker builds. Each `def` body that a `use`
    reaches is counted once per program.
  - `lib`: the part of `static` inside bodies of declarations the elaborated prelude declares
    (below `Elaborated.lib`). A module that a program pulls in with `include` counts as the
    program's own.
  - `expanded`: the nodes of `t.erase`, the term the backend compiles, through every `use` as
    often as it occurs.
  
  The census also counts the type formers of every node's judgment, and the qualifiers of the
  operations at `[handle]` nodes. `corpus/kernel-counts.expected` counts allocations, not rules,
  so it gives no rule counts. The 42 kernel programs (`Backend/Kernel.lean`) are untyped `Expr`s
  and are not in the census; the rows say where a rule is reached only by them.
- **Read by the backend?** This was found by reading `Backend/` (file:line in each row). Two
  checks back it up:
  - `scripts/KernelDecls.lean` lists, for each Core declaration, the `Frontend` and `Backend`
    declarations that mention it. **No lowering code in `Backend/` mentions any Core
    declaration.** The only `Backend` users are the kernel programs (`Backend/Kernel.lean`:
    `cancelKept`, `Shapes.*`).
  - `grep -rnE 'HSite|handleSites|Masks|ClauseKinds|HKind|\bHIn\b|\.sigs|\.pins|TExpr|LifeCtx' Backend`
    finds only `Driver.lean:390` (`pins`, the trusted report) and `Cells.lean:68` (`cells`, the
    diagnostic `bcc-counts --cells`).

Reproduce:

    scripts/kernel-census.sh > docs/kernel-usage/census.tsv
    lake env lean scripts/KernelDecls.lean > docs/kernel-usage/decls.tsv

### What the backend reads, in one paragraph

`Backend/Driver.lean:101–106` compiles `k.main.e`, which is `t.erase` (`Frontend/Check/Program.lean:66`).
Beyond the erasure, the backend reads two booleans from the checked program:
- `Checked.exitsOnDivError` (`Driver.lean:106`). This reads the `HSite` of `handle` nodes, but only
  to find the platform's `main_div_error`.
- `IOMain.loopB` (`Driver.lean:104`), which comes from `main`'s type.

`Backend/Clos/*` and `Backend/Flat/*` do not import `Frontend` at all. So every fact a rule proves
beyond its term is either re-derived from the erasure or dropped:
- the masks, re-derived as copies and drops by `plan2`, `Convert.lean:200`;
- the qualifiers, dropped at `Convert.lean:740`;
- the clause kinds (`tailClause?`, `Capture.lean:625`), the rows (the 0-CFA) and the layout types
  (unification), all re-derived;
- the borrow modes and lifetimes, ignored;
- the derived nodes' facts (`walk`, `divLit`), ignored.

## 2. Classes

- **A**: produced, and its term is all there is to compile. It proves no fact beyond its term that
  a lowering would use, or the backend reads that fact.
- **B**: produced, but the backend ignores what it proves. The fact is one #555 lists for
  compilation (moves and copies, modes, lifetimes, rows, kinds, qualifiers, layouts, reuse,
  bounds), and the backend re-derives it from the erasure or does without.
- **C**: proved, but the checked corpus never produces it. Either the checker has no producer, or
  it has one that no program reaches.
- **D**: produced only through an elaborator workaround (CLAUDE.md, *The elaborator never does the
  kernel's work*).
- **E**: dead: nothing produces it and nothing plans to.

A rule's class is the class of its least-used fact. A row is B when one fact it proves is lost,
even if the rule is otherwise compiled faithfully.

## 3. `CDerives` rules and constants

Links go to the constructor. `§` is the SPEC entry (§1 is the paper's axiom table, from the
baseline).

| # | rule | §  | progs | static | expanded | read by the backend | class | what would change it |
|---|---|---|---|---|---|---|---|---|
| 1 | [`var`](../Core/Fundamental.lean#L87) | §3 | 374 | 115176 | 265193 | erasure only (`Convert.lean:653`) | **A** | — |
| 2 | [`unitI`](../Core/Fundamental.lean#L88) | §3 | 350 | 6286 | 12284 | erasure only | **A** | — |
| 3 | [`tensorI`](../Core/Fundamental.lean#L89) | §3 | 373 | 51243 | 124450 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks (C2b) |
| 4 | [`sumI₁`](../Core/Fundamental.lean#L92) | §3 | 313 | 4274 | 6849 | erasure only | **A** | — |
| 5 | [`sumI₂`](../Core/Fundamental.lean#L94) | §3 | 308 | 4614 | 7190 | erasure only | **A** | — |
| 6 | [`thunkF`](../Core/Fundamental.lean#L97) | §3 | 1 | 1 | 1 | erasure only | **A** | — |
| 7 | [`thunkV`](../Core/Fundamental.lean#L100) | §3 | 302 | 7645 | 17486 | erasure only | **A** | — |
| 8 | [`ret`](../Core/Fundamental.lean#L103) | §3 | 374 | 56109 | 118075 | erasure only (identity) | **A** | — |
| 9 | [`bind`](../Core/Fundamental.lean#L105) | §3 | 371 | 27472 | 52098 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 10 | [`force`](../Core/Fundamental.lean#L109) | §3 | 273 | 4039 | 4461 | erasure only | **A** | — |
| 11 | [`lam`](../Core/Fundamental.lean#L111) | §3 | 366 | 12830 | 32372 | erasure only (`Convert.lean:842`) | **A** | — |
| 12 | [`lamDead`](../Core/Fundamental.lean#L114) | §26 | 53 | 85 | 96 | erasure only | **A** | — |
| 13 | [`app`](../Core/Fundamental.lean#L117) | §3 | 273 | 3143 | 3555 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 14 | [`withI`](../Core/Fundamental.lean#L121) | §3 | 209 | 1428 | 1513 | erasure only; the code's `&` kind is re-inferred by shape (`Code.selShape?`, `Backend/Clos/Types.lean:429`) | **A** | N1 (layouts from types) removes the re-inference |
| 15 | [`proj₁`](../Core/Fundamental.lean#L124) | §3 | 232 | 1589 | 1716 | erasure only | **A** | — |
| 16 | [`proj₂`](../Core/Fundamental.lean#L126) | §3 | 216 | 1412 | 1507 | erasure only | **A** | — |
| 17 | [`topI`](../Core/Fundamental.lean#L129) | §3 | 0 | 0 | 0 | — | **C** | nothing (CBPV basis; the checker has the rule, `Frontend/Check/Rules.lean:57`, and no program reaches it) |
| 18 | [`unitE`](../Core/Fundamental.lean#L130) | §3 | 328 | 4234 | 7179 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 19 | [`tensorE`](../Core/Fundamental.lean#L133) | §3 | 360 | 27848 | 68440 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 20 | [`sumE`](../Core/Fundamental.lean#L137) | §3 | 330 | 11234 | 21732 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 21 | [`zeroE`](../Core/Fundamental.lean#L143) | §3 | 4 | 5 | 5 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 22 | [`allI`](../Core/Fundamental.lean#L146) | §3 | 248 | 4658 | 11645 | erasure only; lifetimes erased | **A** | — |
| 23 | [`allE`](../Core/Fundamental.lean#L152) | §3 | 0 | 0 | 0 | — | **C** | deletion candidate (Growth): the checker emits `allEV` at every use; `allE` at `C` has a checker rule (`Rules.lean:381`) no program reaches |
| 24 | [`bangThunkF`](../Core/Fundamental.lean#L155) | §2 | 0 | 0 | 0 | — | **C** | nothing (the checker has it, `Rules.lean:214`; `bangThunkV` is used instead) |
| 25 | [`bangThunkV`](../Core/Fundamental.lean#L159) | §2 | 361 | 10503 | 27198 | erasure only | **A** | — |
| 26 | [`bangE`](../Core/Fundamental.lean#L163) | §2 | 368 | 30375 | 71457 | erasure only (identity) | **A** | — |
| 27 | [`copyBang`](../Core/Fundamental.lean#L164) | §2 | 0 | 0 | 0 | — | **E** | deletion candidate (Growth): §10's persistent contexts duplicate `!A` by the split; `copy_bang` (`Frontend/Check/Consts.lean:271`) is never written |
| 28 | [`forgetBang`](../Core/Fundamental.lean#L166) | §2 | 0 | 0 | 0 | — | **E** | deletion candidate (Growth): §10's `DeadP` drops `!A`; `forget_bang` (`Consts.lean:283`) is never written |
| 29 | [`boxI`](../Core/Fundamental.lean#L169) | §3, §23 | 262 | 2245 | 4868 | erasure only (identity); the outlives fact is not read | **A** | — |
| 30 | [`boxE`](../Core/Fundamental.lean#L171) | §3 | 23 | 136 | 198 | erasure only (identity) | **A** | — |
| 31 | [`immSub`](../Core/Fundamental.lean#L172) | §3 | 0 | 0 | 0 | — | **C** | nothing (paper rule ⊑imm; checker rule `Rules.lean:245` unreached) |
| 32 | [`mutSub`](../Core/Fundamental.lean#L174) | §3 | 0 | 0 | 0 | — | **C** | nothing (paper rule ⊑mut; checker rule `Rules.lean:250` unreached) |
| 33 | [`alloc`](../Core/Fundamental.lean#L177) | §1, §35 | 121 | 229 | 270 | erasure only (`Op.ofPrim?`, `Convert.lean:218`); a scoped cell is re-recognised from the shape `withbor (alloc v) … free c` (`markScoped`, `Convert.lean:544`) and framed by `frameScopes` (`Flat/Lower.lean:1578`) | **B** | N5: frame slots by rule, from the lend's lifetime |
| 34 | [`free`](../Core/Fundamental.lean#L179) | §1, §35 | 94 | 195 | 232 | erasure only; paired with `alloc` by `markFreeOf` (`Convert.lean:505`) | **B** | N5: frame slots by rule |
| 35 | [`swap`](../Core/Fundamental.lean#L181) | §1 | 19 | 56 | 68 | exact fixed-scheme recogniser `isSwap` (`Convert.lean:283`) | **A** | — |
| 36 | [`copy`](../Core/Fundamental.lean#L182) | §1 | 15 | 28 | 93 | erasure only | **A** | — |
| 37 | [`forgetImm`](../Core/Fundamental.lean#L183) | §1 | 11 | 36 | 141 | erasure only | **A** | — |
| 38 | [`forgetMut`](../Core/Fundamental.lean#L184) | §1 | 12 | 17 | 24 | erasure only | **A** | — |
| 39 | [`forgetUnk`](../Core/Fundamental.lean#L185) | §1 | 0 | 0 | 0 | — | **C** | nothing (paper axiom; `Unk` never occurs as a type in the corpus) |
| 40 | [`lit`](../Core/Fundamental.lean#L187) | §8 | 364 | 18874 | 41499 | erasure only | **A** | — |
| 41 | [`hostOp`](../Core/Fundamental.lean#L190) | §8 | 351 | 12903 | 29850 | erasure only (Flat host op `Flat/Lower.lean:564`) | **A** | — |
| 42 | [`arrNew`](../Core/Fundamental.lean#L193) | §9 | 176 | 880 | 2877 | erasure only (`tab`, `Flat/Lower.lean:567`) | **A** | — |
| 43 | [`arrFree`](../Core/Fundamental.lean#L196) | §9 | 5 | 10 | 10 | erasure only (`drop`, `Flat/Lower.lean:637`) | **A** | — |
| 44 | [`arrSize`](../Core/Fundamental.lean#L199) | §9 | 124 | 400 | 1970 | erasure only | **A** | — |
| 45 | [`arrReplace`](../Core/Fundamental.lean#L201) | §9 | 134 | 902 | 6253 | erasure only; the move it types is compiled with the copies `plan2` inserts: #608's deep copy of a μ value beside this node | **B** | N1 acceptance (#608): moves from the masks, layouts from types |
| 46 | [`arrLen`](../Core/Fundamental.lean#L204) | §9 | 131 | 211 | 784 | erasure only | **A** | — |
| 47 | [`arrGet`](../Core/Fundamental.lean#L207) | §9 | 152 | 335 | 1685 | erasure only (`idx`, `Flat/Lower.lean:604`), bounds-checked at every access | **A** | — |
| 48 | [`arrCopy`](../Core/Fundamental.lean#L210) | §9 | 143 | 1202 | 1675 | erasure only | **A** | — |
| 49 | [`arrForget`](../Core/Fundamental.lean#L213) | §9 | 111 | 588 | 725 | erasure only | **A** | — |
| 50 | [`countFold`](../Core/Fundamental.lean#L217) | §16 | 165 | 1018 | 3377 | erasure only (`count_loop`, `Flat/Lower.lean:1405`) | **A** | — |
| 51 | [`countTry`](../Core/Fundamental.lean#L221) | §16 | 69 | 173 | 456 | erasure only (`count_try_loop`, `Flat/Lower.lean:1439`) | **A** | — |
| 52 | [`boundedFix`](../Core/Fundamental.lean#L226) | §20 | 57 | 146 | 186 | erasure only (`fixValue`, `Convert.lean:243`) | **A** | — |
| 53 | [`iterate`](../Core/Fundamental.lean#L230) | §14 | 0 | 0 | 0 | `expandIter` (`Convert.lean:875`) turns it into a fixed point; reached only by the kernel program `div-residual` | **C** | B2 (the `Div` elaboration as typed schemes), then N4 (`iterate` as an LIR loop). SPEC.md:7574: "the frontend does not elaborate to it yet" |
| 54 | [`divFuel`](../Core/Fundamental.lean#L235) | §14 | 0 | 0 | 0 | generic; reached only by the kernel program `div-residual` | **C** | B2, then N4 |
| 55 | [`reify`](../Core/Fundamental.lean#L240) | §14 | 0 | 0 | 0 | — | **C** | B2/N4 (N4's acceptance "no `drive` outside `reify`" plans it); no checker producer and no typed Core program |
| 56 | [`sliceBorrowM`](../Core/Fundamental.lean#L247) | §9 | 109 | 133 | 139 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5: `noalias` on the leaf borrows (#555 choice 6) |
| 57 | [`sliceBorrowI`](../Core/Fundamental.lean#L254) | §9 | 151 | 655 | 1442 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5: `readonly` on the leaf borrows |
| 58 | [`sliceGetM`](../Core/Fundamental.lean#L259) | §9 | 10 | 11 | 20 | erasure only | **A** | — |
| 59 | [`sliceLenM`](../Core/Fundamental.lean#L262) | §9 | 27 | 30 | 43 | erasure only | **A** | — |
| 60 | [`sliceSplitI`](../Core/Fundamental.lean#L266) | §9 | 120 | 249 | 503 | erasure only (`split`, `Flat/Lower.lean:616`) | **A** | — |
| 61 | [`sliceSplitM`](../Core/Fundamental.lean#L270) | §9 | 101 | 115 | 118 | erasure only | **A** | — |
| 62 | [`sliceEmptyI`](../Core/Fundamental.lean#L273) | §9 | 91 | 189 | 211 | erasure only | **A** | — |
| 63 | [`sliceEmptyM`](../Core/Fundamental.lean#L276) | §9 | 2 | 2 | 2 | erasure only | **A** | — |
| 64 | [`sliceReplaceM`](../Core/Fundamental.lean#L280) | §9 | 22 | 25 | 97 | erasure only | **A** | — |
| 65 | [`sliceSwapM`](../Core/Fundamental.lean#L283) | §9 | 18 | 22 | 29 | erasure only | **A** | — |
| 66 | [`withbor1`](../Core/Fundamental.lean#L285) | §1 | 47 | 74 | 106 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5: `readonly`, lend extent → storage |
| 67 | [`withbor2`](../Core/Fundamental.lean#L290) | §1, §23 | 202 | 583 | 906 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5: `noalias`, lend extent → storage |
| 68 | [`withbor3`](../Core/Fundamental.lean#L294) | §1 | 10 | 14 | 15 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5 |
| 69 | [`withload`](../Core/Fundamental.lean#L297) | §1 | 169 | 494 | 1827 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5: `readonly` |
| 70 | [`withswap`](../Core/Fundamental.lean#L300) | §1 | 60 | 122 | 182 | erasure only (`Paper/S3_Dynamics/Definitions.lean:660`'s λ-term); the in-place update it proves is compiled as a load, a call and a store | **B** | N5 |
| 71 | [`withbor1U`](../Core/Fundamental.lean#L304) | §19 | 1 | 1 | 1 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 72 | [`withbor2U`](../Core/Fundamental.lean#L310) | §19, §23 | 4 | 4 | 6 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 73 | [`withbor3U`](../Core/Fundamental.lean#L316) | §19 | 2 | 2 | 2 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 74 | [`withloadU`](../Core/Fundamental.lean#L322) | §19 | 1 | 1 | 1 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 75 | [`sliceBorrowMU`](../Core/Fundamental.lean#L327) | §19 | 1 | 1 | 1 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 76 | [`sliceBorrowIU`](../Core/Fundamental.lean#L334) | §19 | 1 | 1 | 1 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read; the row is re-derived | **B** | N5, N2 |
| 77 | [`lolliE`](../Core/Fundamental.lean#L342) | §3 | 372 | 37809 | 86887 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`) | **B** | N1: copies/moves from the masks |
| 78 | [`allEV`](../Core/Fundamental.lean#L346) | §3 | 226 | 4660 | 8250 | erasure only | **A** | — |
| 79 | [`ofRet`](../Core/Fundamental.lean#L349) | §3 | 151 | 892 | 1411 | erasure only (identity) | **A** | — |
| 80 | [`roll`](../Core/Fundamental.lean#L352) | §6 | 67 | 471 | 920 | erasure only (identity) | **A** | — |
| 81 | [`unroll`](../Core/Fundamental.lean#L355) | §6 | 48 | 215 | 287 | erasure only (identity) | **A** | — |
| 82 | [`foldImm`](../Core/Fundamental.lean#L362) | §6 | 11 | 15 | 17 | no recogniser: compiled as the generic Z fixed point (`fixBody?`, `Convert.lean:303`) | **A** | — |
| 83 | [`foldOwn`](../Core/Fundamental.lean#L368) | §6 | 15 | 23 | 28 | re-recognised from the erasure (`travShape?`, `Convert.lean:311`; `foldShape?`, `:332`), its shape re-checked against the layout types (`dswOK`), then pointer reversal (`foldPlan?`, `Flat/Lower.lean:891`) | **B** | N1: read `F` from the node, delete `travShape?` |
| 84 | [`foldReuse`](../Core/Fundamental.lean#L373) | §6 | 3 | 3 | 3 | as `foldOwn`; the in-place reuse it proves is re-derived the same way | **B** | N1: ownership → in-place reuse from the node |
| 85 | [`nuIn`](../Core/Fundamental.lean#L377) | §7 | 204 | 768 | 814 | erasure only; the codata scheme is re-recognised on the closure IR (`collapse?`, `Backend/Clos/Collapse.lean:74`) | **B** | N4 (codata and loops) |
| 86 | [`nuOut`](../Core/Fundamental.lean#L379) | §7 | 204 | 2434 | 2604 | as `nuIn` | **B** | N4 |
| 87 | [`unfoldN`](../Core/Fundamental.lean#L383) | §7 | 197 | 634 | 663 | as `nuIn` | **B** | N4 |
| 88 | [`effSub`](../Core/Fundamental.lean#L386) | §19 | 151 | 3024 | 3844 | erasure only; the row is re-derived by the 0-CFA (`SFacts.of`, `Backend/Clos/Capture.lean:469`; `UFacts.solve`, `Backend/Clos/Unwind.lean:386`) | **B** | N2 (effect erasure from rows and static sites) |
| 89 | [`effPerform`](../Core/Fundamental.lean#L389) | §19 | 73 | 269 | 284 | erasure only; the row is re-derived by the 0-CFA (`SFacts.of`, `Backend/Clos/Capture.lean:469`; `UFacts.solve`, `Backend/Clos/Unwind.lean:386`); control vs. abortive re-read from the prim (`Ops.of`, `Capture.lean:178`) | **B** | N2 |
| 90 | [`effRaise`](../Core/Fundamental.lean#L394) | §19 | 108 | 469 | 649 | erasure only; the row is re-derived by the 0-CFA (`SFacts.of`, `Backend/Clos/Capture.lean:469`; `UFacts.solve`, `Backend/Clos/Unwind.lean:386`) | **B** | N2 |
| 91 | [`effLet`](../Core/Fundamental.lean#L399) | §19 | 129 | 784 | 977 | erasure only; the split's masks `u` are dropped and copies/drops are re-derived from free-variable occurrence (`plan2`, `Backend/Clos/Convert.lean:200`); the row is re-derived | **B** | N1 (masks), N2 (rows) |
| 92 | [`effThen`](../Core/Fundamental.lean#L412) | §19, §27 | 79 | 279 | 342 | the finaliser frame is re-recognised (`markUbinds`, `Convert.lean:463`; `finRaises`/`finSuspends`, `Capture.lean:1132`/`:1140`) | **B** | N2 |
| 93 | [`effHandleV`](../Core/Fundamental.lean#L427) | §19, §24 | 148 | 523 | 606 | erasure only; the qualifiers in `qs` are matched `_` and dropped (`Convert.lean:740`); the clause kinds `ks` are re-derived (`tailClause?`, `Capture.lean:625`); `site` is read only for `main_div_error` (`Checked.exitsOnDivError`, `Frontend/Check/Program.lean:59`, via `Driver.lean:106`); `inside` is not read | **B** | N2: kinds (C3) and sites (C3b) read from the node; κ's cell by qualifier |
| 94 | [`effHandleVB`](../Core/Fundamental.lean#L438) | §28 | 16 | 29 | 37 | as `effHandleV`; the box lifetime `d` is not read | **B** | N2, N3 (stored continuations) |
| 95 | [`effHandleT`](../Core/Fundamental.lean#L451) | §14, §19 | 0 | 0 | 0 | — | **C** | B1/B2 (`tick`'s handlers): no checker producer and no typed Core program |
| 96 | [`letPoly`](../Core/Fundamental.lean#L463) | §24 | 0 | 0 | 0 | `polyLet?` (`Convert.lean:606`) recognises its erasure; rows re-derived (`Backend/Clos/Poly.lean`) | **C** | rule table: an elaboration rule for a let used at several rows (pipeline-architecture A11), else a deletion candidate. no checker producer; reached only by the kernel programs `hof-two-rows`, `poly-id` |

## 4. `CDerivesP`-only rules (§29, under `PinLaw`)

| # | rule | §  | progs | static | expanded | read by the backend | class | what would change it |
|---|---|---|---|---|---|---|---|---|
| 97 | [`lendR`](../Core/PinDerives.lean#L483) | §29 | 10 | 16 | 16 | erasure only (`withborUV`/`lendCb`, no recogniser); the PinLaw lend is not read | **B** | N3 (state machines at stored-continuation sites) |
| 98 | [`lendLoopR`](../Core/PinDerives.lean#L504) | §29 | 0 | 0 | 0 | — | **C** | #632 (LoopLend D3) / async U6 (`docs/async-capabilities.md:567`): LoopLend should emit it instead of rebuilding per-turn lends. no checker producer |
| 99 | [`nilDead`](../Core/PinDerives.lean#L520) | §29 | 10 | 16 | 16 | erasure only (identity) | **A** | — |

## 5. Derived nodes and `use`

`Frontend/Check/TExpr.lean`'s nodes for fixed schemes. Each has its typing lemma, and the marked
ones have their run facts (`Frontend/Check/Derived.lean`).

| # | rule | §  | progs | static | expanded | read by the backend | class | what would change it |
|---|---|---|---|---|---|---|---|---|
| 100 | [`dtor`](../Frontend/Check/TExpr.lean#L364) | §12 | 288 | 3498 | 6213 | erasure only (`dtorE`); drops are re-inserted from occurrence (`wrapDrops`, `Convert.lean:192`) | **B** | N1: exact drops from the node |
| 101 | [`allocS`](../Frontend/Check/TExpr.lean#L366) | §5 | 13 | 15 | 43 | erasure only (no recogniser for `allocS`) | **B** | N5: frame slots by rule |
| 102 | [`freeS`](../Frontend/Check/TExpr.lean#L368) | §5 | 1 | 1 | 1 | erasure only | **B** | N5 |
| 103 | [`withborSM`](../Frontend/Check/TExpr.lean#L371) | §5 | 1 | 1 | 1 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5 |
| 104 | [`withborSI`](../Frontend/Check/TExpr.lean#L373) | §5 | 0 | 0 | 0 | — | **C** | nothing (checker producer `Frontend/Check/Consts.lean:382`; no program writes an `imm` block borrow) — or U4 (#593): records over blocks |
| 105 | [`withborF2M`](../Frontend/Check/TExpr.lean#L375) | §5 | 2 | 2 | 2 | erasure only (`withbor`'s λ-term, generic arms `Convert.lean:797–855`); the mode, the lend's lifetime and its extent are not read | **B** | N5 |
| 106 | [`withborF2I`](../Frontend/Check/TExpr.lean#L377) | §5 | 0 | 0 | 0 | — | **C** | nothing (checker producer `Consts.lean:506`, unreached) |
| 107 | [`litFn`](../Frontend/Check/TExpr.lean#L379) | §17 | 53 | 159 | 181 | re-recognised from the erasure (`litTable?`, `Convert.lean:374`) | **B** | N1: read the bytes from the node (C2 acceptance: one node per recogniser) |
| 108 | [`divLit`](../Frontend/Check/TExpr.lean#L382) | §39 | 10 | 15 | 17 | erasure only: the node's fact (`divLit_some32/64/8`, `Frontend/Check/Derived.lean:66–93`: the error arm is never taken) is not read; the arm is compiled | **B** | N1/N5: drop the dead arm from the node |
| 109 | [`walk`](../Frontend/Check/TExpr.lean#L384) | §16 | 60 | 78 | 122 | erasure only: the node's fact (`walk_index_lt`, `Derived.lean:14`: every index is below the view's length) is not read; each access is bounds-checked (`tickBound`, `Flat/Lower.lean:124`) | **B** | N5: bounds checks elided from the node |
| 110 | [`selfCall`](../Frontend/Check/TExpr.lean#L387) | §21 | 51 | 219 | 281 | re-derived: the fixed point is re-recognised (`fixBody?`, `Convert.lean:303`) | **B** | N1: direct self-calls from the node |
| 111 | [`lendCell`](../Frontend/Check/TExpr.lean#L390) | §35, §41 | 26 | 52 | 74 | re-derived: the scoped cell is re-recognised (`markScoped`, `Convert.lean:544`) | **D** | N5 (framing from the node); its producers are workarounds (see class D): `lendBorrow`'s value branch (`Frontend/Sugar.lean:2276`, ergonomics N1) and `withBlk`'s state cell (`Sugar.lean:3526`) → #626/#632 |
| 112 | [`use`](../Frontend/Check/TExpr.lean#L393) | §3 | 347 | 10571 | 19615 | erasure only: `t.erase` holds a copy of the body per use; specialisation keys are not read (pipeline-architecture A6) | **B** | N1: specialisation from `use` keys |

## 6. Type formers

`progs` counts the programs where some node's judgment has the former; `nodes` counts those nodes.

| # | former | progs | nodes whose judgment has it | read by the backend | class | what would change it |
|---|---|---|---|---|---|---|
| 113 | `V.unit` | 368 | 235749 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 114 | `V.tensor` | 373 | 301161 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 115 | `V.zero` | 115 | 18688 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 116 | `V.sum` | 343 | 192352 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 117 | `V.thunk` | 374 | 164879 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 118 | `V.ref` | 275 | 160332 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 119 | `V.imm` | 183 | 71227 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N5: `readonly` |
| 120 | `V.mut` | 227 | 37165 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N5: `noalias` |
| 121 | `V.box` | 264 | 32404 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N5: storage from the lifetime |
| 122 | `V.bang` | 370 | 74631 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 123 | `V.unk` | 0 | 0 | — | **C** | nothing (paper baseline; `Imm̲` of an opaque type) |
| 124 | `V.tvar` | 231 | 65582 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 (specialisation) |
| 125 | `V.mu` | 67 | 26601 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 (#608: layouts from types) |
| 126 | `V.int` | 365 | 431687 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 127 | `V.fam` | 176 | 182998 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1, N5 |
| 128 | `V.opq` | 161 | 75020 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 129 | `C.ret` | 374 | 285966 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 130 | `C.arr` | 374 | 147628 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 131 | `C.amp` | 233 | 49322 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 132 | `C.top` | 2 | 12 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N1 |
| 133 | `C.all` | 248 | 22488 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N5: lifetimes → storage |
| 134 | `C.nu` | 204 | 46531 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N4 |
| 135 | `C.eff` | 154 | 36816 | no: types are erased; layout types are re-derived by unification (`Backend/Clos/Types.lean`, pipeline-architecture B2) | **B** | N2: rows |

## 7. Derived forms with no node

| # | form | where | produced? | read by the backend | class | what would change it |
|---|---|---|---|---|---|---|
| 136 | **`Aff^c A B`**, the affine closure (§22), and its 17 derived rules (`affIn`, `affOut`, `affUnfold`, `d_mk`, `d_callAff`, `d_callMut`, `d_close`, `d_ofFn`, `d_once`, …) | `Core/Aff.lean:32–50`, `Core/AffRules.lean` | **The elaborator never produces it.** Neither module is in the compiler's import closure (with `Core.BlockTrack`, `Core.ReuseList`, `Core.DivRuntime`, `Core.EffSafety`, `Core.EffCancelRuns`, `Core.Embedding` and `Core.DelayApprox`). It reaches code only where a user calls `lib/aff.bc`, in 6 corpus programs (`aff-*.bc`), as `unfoldN`/`nuIn`/`nuOut` nodes. | as `unfoldN` (row 87) | **C** | #605 (unit 22, `Aff` closure state by value). A writing callee called repeatedly is today a callee copy (`mutCap`, class D below); #632's D4 and #626's A2 would elaborate it to `Aff`. |
| 137 | **Records and variants** (§5): `recI`, `recE`, `recEV`, `getAt`, `injAt`, `loadField`, `loadCase`, `modAt`, `swapField`, `vcase`, `dropT`, `tuple`, `recLet` and their `_wf` rules | `Core/Records.lean` | no. No declaration outside `Records.lean` uses them; the surface's blocks use `allocS`/`freeS`/`withborS` instead (rows 101–103) | — | **C** | U4 (#593, data declarations): elaborate data declarations to these forms, or delete them under Growth if U4 takes another route |
| 138 | `fixD`, `unfoldS`, `delayIn`/`delayOut`, `streamIn`/`streamOut` | `Core/Fundamental.lean` (instances of `unfoldN`, `nuIn`, `nuOut`) | yes, as `unfoldN`/`nuIn`/`nuOut` nodes (the checker's `tFixD`/`tUnfoldS`) | as row 87 | **B** | N4 |
| 139 | `effHandle` (two-variable `[handle]`), `effThenA` | `Core/Fundamental.lean`, `Core/PinDerives.lean` | yes, as `effHandleV`/`effThen` nodes (`Frontend/Check/TiedDer.effHandle`) | as row 93 | **B** | N2 |
| 140 | weakening by dead slots: `CDerives.append_dead`, `insert_dead` | `Core/Weaken.lean`, `Core/InsertDead.lean` | yes: the checker places a `def`'s body at each `use` with them (`Frontend/Check/Weaken.lean`, C2) | not needed: a typing fact with no runtime content | **A** | — |
| 141 | `letPoly_copy`, `letPoly_of_fill`, `Expr.unfill` | `Core/LetCopy.lean` | no (`letPoly` is never produced, row 96); used only by `checkProgram_letPoly` (`Frontend/Check/Program.lean`) | — | **C** | with `letPoly` |
| 142 | the Z combinator `selfV` | `Core/Fix.lean:189` | yes, under `selfCall` (row 110) | re-recognised by `fixBody?` (`Convert.lean:303`) | **B** | N1, with `selfCall` |
| 143 | the cancel and unwind frames `ccatch`, `cfin`, `ubind`, and κ's cell (§19 *Laws* 5–6, §25) | `Paper/S1_Syntax/Definitions.lean` (`Prim`), `Core/EffMachine.lean` | `ubind` under `effThen`. `ccatch`/`cfin` only appear in machine steps | `Convert.lean:738–739` rejects `ccatch`/`cfin` as source. `Capture` builds κ with the same cancel arm for every qualifier (`kapBody`, `Capture.lean:261`): no cell, whatever the qualifier | **B** | N2 (κ's cell by qualifier), N3 |

## 8. Class D: elaborator workarounds and the rules they produce

No `CDerives` rule is produced only by a workaround. Every rule a workaround emits is also emitted
by ordinary elaboration. So D is a property of producers, not of rules, and one derived node
(`lendCell`) is D because both of its producers are workarounds. This table lists every producer
found, with the rules it emits, so that each B/A row above whose occurrences partly come from a
workaround can be traced.

| workaround | where | kernel work it does | rules it produces | follow-up |
|---|---|---|---|---|
| §41 R2: write sets | `Frontend/Parser.lean:330` (`frame`), the `assigned` marks `:304`, `:311`, `:1703`, `:1758` | decides mutation | none of its own; feeds R3 | #632 (frames with exits; K1) |
| §41 R3 *Out*: hand-on and join | `Parser.lean:1185` (`handOn`), `:1199` (`joinBind`), `:1208`, `:1217`, `:1068`; `Frontend/Sugar.lean:1095` (`thenGo`), `:2218–2246`, `:4302`, `:4758` | threads and rebuilds state | `tensorI`, `tensorE`, `bind`, `ret`, `sumE`; in loops, the state of `unfoldN`/`nuOut`/`countTry` | #632; #626's place model |
| §41 R3 *In*: `mutCap` | `Frontend/Elab/Effects.lean:1352` (`mutCap`), `:1344` (`threadCap`), `:1520–1551`, `:2388–2436`, keys `:1458`, `copyFor` `:2924` | copies the callee and threads its writes as parameters | `lam`, `app`, `force`, `tensorE`, `bangThunkV` in the copies | #632 D4; `Aff` (row 136, #605); #626 A2 |
| `escapingWriter` | `Effects.lean:1365`, thrown at `:1524`, `:1988` | refuses on escape grounds (`withbor2`'s `'x ∉ FV(B)` should) | — | #632; #626 |
| other R3 refusals | `Parser.lean:1055` (`checkRun`), `:2040`; `Effects.lean:2490–2511` | refuses on mutation grounds | — | #632 |
| `let mut` value lent through a cell | `Sugar.lean:2276` (`lendBorrow`'s value branch, `:2292–2297`) | copies the value into a cell and rebinds it after | `alloc`, `withbor1`/`withbor2`, `free`, under **`lendCell`** | #626 (place model); ergonomics N1 |
| in-place `modify` of a `let mut` value (`io_mu`) | `Sugar.lean:3458–3461` | rebinds with no borrow (a `letPair` where `withswap` belongs) | `tensorE`, `tensorI` instead of `withswap` | #626; #632 |
| a handler's state passed as a value | `Sugar.lean:3526`, `withBlk` (`Effects.lean:2454`) | threads state through a cell | **`lendCell`** | #632; the stateful handler below |
| LoopLend (§14, decision 40) | `Frontend/Elab/LoopLend.lean:388` (`lendBind`), `:439`, `:495` (`lentDef`, which rewrites a def's signature), `:542`, `:257`, `:311`, `:129`; refusals `:283`, `:290`, `:297`, `:424`, `:446`, `:518`, `:524` | decides lend extents, threads the owner through the loop state, and refuses on borrow grounds | per-turn `withbor1`/`withbor2`/`withbor3` and `…U`, `tensorI`. **Not `lendLoopR`** (row 98), which is the kernel rule for it and has no producer | #632 D3; async U6 (`docs/async-capabilities.md:567`) |
| callee copies threading capabilities (§32) | `Effects.lean:2924` (`copyFor`), `:2392–2405`, `forSite` `:2814` | threads a `for` body's locals through `perform` | ordinary formers in the copies | #632; rule table |
| stateful control handler (§19 *Handler state*) | `Effects.lean:2677–2733`, `:1047`, `:2176–2195`; `HInfo.params` (`Frontend/Syntax.lean:366`) | a state-passing transform, by hand | `effHandleV` at a function-typed answer | N2 (handler state as a field, pipeline-architecture A5); #632 |
| capability and lend refusals | `Effects.lean:1711` (`noLend`), `:1962–1966`, `:2453`, `:2512–2515`, `:3572` | refuses on aliasing grounds | — | rule table; #632 |
| sugar refusals that pre-empt a kernel side condition | `escapeError` at `Sugar.lean:3491`, `:3510`, `:3537`, `:3558`, `:3582`, `:3621`, `:3680`, `:3723`; `:2291` (no reborrow, though `withbor3` exists); `:2320`, `:2394`; T1 `:3936`, `:3951`, `:3956`, `:4261–4267`, `:4696`; `:4308`; `:945` | refuses on borrow grounds | — | rule table: let the kernel's rules refuse |

Two pieces were checked and are **not** D:
- §14's machine templates (`Sugar.lean:617`, `:1088`, `:1360`, `:1505`) are sugar into
  `unfoldN`/`nuIn`/`nuOut`/`countTry`/`boundedFix`. #632 lists their exit threading (`normExits`,
  `DivSt.exits`) among the hand-written rules.
- `implicitCopy` (`Frontend/Check/Copies.lean:129`) is a refusal on cost, read off the checked masks.

## 9. Summary

### Counts

| class | rows |
|---|---|
| A, used end to end | 49 |
| B, produced, the backend ignores what it proves | 73 |
| C, proved, never produced | 18 |
| D, produced only through a workaround | 1 |
| E, dead | 2 |
| **total** | **143** |

### Follow-ups, by unit

None is filed as an issue. This list is for the user.

**N1 (new backend, pure fragment; #555 acceptance):**
- Copies, moves and drops from the split masks and `dtor` nodes, not from occurrence (`plan2`).
  Rows: `tensorI`, `bind`, `app`, `unitE`, `tensorE`, `sumE`, `zeroE`, `lolliE`, `effLet`,
  `dtor`, and `arrReplace` (#608).
- Layouts from types. Rows: every former in §6 except `Unk`, and `withI`'s code kind.
- Folds from the node, with in-place reuse: `foldOwn`, `foldReuse` (delete `travShape?`/`foldShape?`).
- The derived nodes read instead of re-recognised: `litFn` (`litTable?`), `selfCall` and
  `selfV` (`fixBody?`), `divLit` (drop the dead arm).
- Specialisation from `use` keys.

**N2 (effect erasure):**
- Rows from the derivation, not the 0-CFA: `effSub`, `effPerform`, `effRaise`, `effLet`, the
  `…U` borrows.
- Clause kinds and sites from the `handle` node, and κ's cell by qualifier: `effHandleV`,
  `effHandleVB`, `effHandle`, the cancel frames.
- Finaliser frames from `effThen`/`effThenA` (delete `markUbinds`).
- `C.eff`.

**N3 (state machines):** `lendR` (R1's PinLaw lend held across a suspension), `effHandleVB`.

**N4 (codata and loops):** `nuIn`, `nuOut`, `unfoldN` and their instances (`fixD`, `unfoldS`, …),
with `Collapse` reading the node. `iterate`, `divFuel` and `reify` once B2 produces them.

**N5 (target facts):**
- Modes and extents of every borrow: `withbor1/2/3`, `withload`, `withswap`, the slice borrows,
  the `…U` forms, `withborSM`, `withborF2M` → `noalias`/`readonly`.
- Storage from lifetimes: `alloc`/`free`, `allocS`/`freeS`, `lendCell` (delete `markScoped`), `V.box`, `C.all`.
- Bounds checks elided by `walk`'s proved fact (`walk_index_lt`).

**B1/B2 (`Div` in the kernel, its elaboration as typed schemes):** `iterate`, `divFuel`, `reify`,
`effHandleT` are proved and the checker has no producer for them. SPEC.md:7574 says so.

**#632 (frames with exits) and #626 (`let mut` as a place):**
- Every class-D producer in §8. These are the R2/R3 joins, `mutCap`, `escapingWriter`, LoopLend,
  `io_mu`, the `let mut` value cell, and the handler state cell.
- `lendLoopR`, which LoopLend should emit and does not.
- `lendCell`, whose two producers are both workarounds.

**U-units:**
- U4 (#593, data declarations): the records and variants forms (row 137), and `withborSI`.
- Unit 22 (#605): `Aff` (row 136).

**Rule table:**
- an elaboration rule for `letPoly`, a let used at several rows, or else delete it with
  `letPoly_copy`;
- the sugar refusals that pre-empt kernel side conditions (§8, last rows).

**Deletion candidates (Growth discipline):**
- `copyBang` and `forgetBang`, which §10's persistent contexts make redundant (class E);
- `allE` at `C`, since the checker emits `allEV` at every use;
- `letPoly` with `letPoly_copy`, if no elaboration rule is wanted.

**Nothing to change:** `topI`, `bangThunkF`, `immSub`, `mutSub`, `forgetUnk`, `withborF2I` and
`V.unk`. These are paper-baseline rules the checker can produce and the corpus does not reach.

### Surprises

1. **The backend reads no typed fact except whether `main` is served `main_div_error`.**
   - `Backend/Clos` and `Backend/Flat` do not import `Frontend`.
   - No lowering code mentions a Core declaration.
   - Every one of C1–C4b's fields is unread by the backend: the masks, the clause kinds, the
     sites, the `inside` frames, the cell classes, `sigs` and `pins`. `Cells.lean` compares
     `cells` with the layout types only as a diagnostic.
2. **Two derived nodes carry proved run facts that nobody reads.**
   - `walk`'s index bound (`walk_index_lt`) proves each counted walk's `array_get`/`slice_split_mut`
     never takes its out-of-bounds arm. 60 programs have such walks, and every access is still
     bounds-checked.
   - `divLit`'s nonzero divisor proves the error arm is dead. 10 programs have one, and the arm
     is still compiled.
3. **The checker has no producer at all for `iterate`, `divFuel`, `reify`, `effHandleT`, `letPoly` or
   `lendLoopR`.**
   - These are six proved rules, five of them with a `TExpr` constructor.
   - The only programs that reach them are the kernel programs `div-residual` (`iterate`,
     `divFuel`), `hof-two-rows` and `poly-id` (`letPoly`).
   - `reify` and `effHandleT` have no typed program anywhere: no Core derivation and no checker
     producer.
4. **Qualifiers.**
   - Over 152 programs, `[handle]` nodes type 573 affine operations, 2 linear ones and no
     unrestricted one.
   - The backend discards all of them (`Convert.lean:740`) and gives every κ the same cancel arm.
5. **`Aff` is not in the compiler's import closure.** Neither are `BlockTrack`, `ReuseList` and
   `DivRuntime`. The elaborator never builds `Aff`. Where R3's callee copies stand in for it, it
   reaches code only through `lib/aff.bc` in 6 user-written programs.
6. **Fold traversals are rare.**
   - `foldOwn` is in 15 programs, `foldReuse` in 3 and `foldImm` in 11.
   - The backend matches the two owned folds by re-recognising the erasure, and does not use the
     node the checker built.
7. **D is not a property of any rule.** Every rule the workarounds emit is also emitted by ordinary
   elaboration. Only the derived node `lendCell` has workarounds as both of its producers. The
   kernel rule meant for LoopLend (`lendLoopR`) is the one LoopLend does not use.
8. **Blocks and families barely reach code.**
   - `withborSM` and `freeS` are each in 1 program, `withborF2M` in 2, `allocS` in 13, and
     `withborSI`/`withborF2I` in none.
   - Records and variants (§5) have no user outside `Core/Records.lean`.
