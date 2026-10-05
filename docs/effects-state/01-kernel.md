# 01 — The effect kernel and toolchain on main

State audited: `origin/main` = `8a1c326` (2026-10-02, "GhostEnd: the stacked lemmas at every stack
(#279) (#283)"). Every `file:line` below is at that commit unless a branch is named. This is an
inventory. It proposes nothing.

**World of every Core result in this file.** Every Lean result in §1 lives at Core's one relation,
`vCE`/`cC`/`cB` over `wpTS`/`wpG`/`ewpTS`, with the typed world `TW` inside `wpG`'s quantifier.
That is the planned Kripke world `W` at `σ = []` and nothing more. No result in §1 is about a
non-empty lend stack. The GhostEnd `vRL*` relations and the sibling calculus
`experiments/EffModelRel` are not in Core. The branches in §4 that touch them say so.

Hygiene: Core has no `sorry` or `axiom` outside comments (grep of `Core/*.lean`), and
`scripts/check-hygiene.sh` covers `Core/` (`Core/README.md`). All Core effect files are imported by
`Core.lean` (`Core.lean:16,66,67,71`).

---

## 1. Effect definitions and theorems in Core

### 1.1 Syntax and machine

The machine has no new `Expr` constructor. Effects are six `Prim`s applied as ordinary terms.

| object | where | what |
|---|---|---|
| `Prim.perform`, `.raise`, `.hnd`, `.ubind`, `.ccatch`, `.cfin` | `Paper/S1_Syntax/Definitions.lean:72-86` | resuming operation; abortive operation; handler frame; finaliser frame; cancel delimiter; cancel-mode finaliser frame |
| `Prim.boundedFix` | `Paper/S1_Syntax/Definitions.lean:69-71` | fuelled fixed point (§20) |
| `hndE`, `ubindE`, `ccatchE`, `cfinE`, `performE`, `raiseE`, `opPayload`, `hndVal` | `Paper/S3_Dynamics/Definitions.lean:331-352` | term formers. A payload is `(n, (i, v))`: name `n`, operation index `i` |
| `cancelVal N err`, `errNext` | `Paper/S3_Dynamics/Definitions.lean:373-381` | a cancel is `raise (0, (0, (N, err)))`. Name `0` is reserved |
| `Kont.HasHnd n`, `Kont.Catches n`, `Kont.hndNames` | `Paper/S3_Dynamics/Definitions.lean:386-416` | `K` has a handler of `n`; `K` has a frame that catches a `raise` of `n` (a handler of `n`, any `ubind`, any `cfin`, `ccatch` at `n = 0`); the names of `K`'s handlers |
| `kappa n H K` | `Paper/S3_Dynamics/Definitions.lean:438-442` | the `[op]` continuation: a `&`-pair `λs. case s {resume: λy. hnd H K[y] ∣ cancel: ccatch (hnd H K[raise (0,(0,(n::names K, none)))])}` |
| head steps `hret`, `hop`, `hunwind`, `uthen`, `ufin`, `ufinC`, `cfret`, `cferr`, `cancel`, `creraise`, `boundedFix` | `Paper/S3_Dynamics/Definitions.lean:445-543` (`Head`) | `[ret]`, `[op]`, `[unwind]`, `[then]`, `[finalise]`, `[finalise-cancel]`, `[cfin-ret]`, `[cfin-raise]`, `[cancel]`, `[cancel-raise]`, `[boundedFix]` |

Handlers are deep. `κ` reinstalls `H`. An operation of another name is not a redex at `hnd`, so
it is forwarded. `K[perform …]`, with `K` free of `n`, is final.

**Unique decomposition and determinism with effects.** These are in `Core/Steps.lean`:

- `head_plug` (:312) and `head_nested` (:517): no redex holds another at an evaluation position;
- `plug_decomp` (:579);
- `head_det_eff` (:596).

Determinism under an allocator is `AStep1.deterministic` (`Core/Demonic.lean:117`). PROVED.

**Interpreter.** `Support/Dynamics/Interpreter.lean` has the §19 steps (:116, :147-195). A
`perform` or `raise` that no handler catches is a stop.

**Cancel outcomes.** `Core/EffCancel.lean` machine-checks both outcomes as runs, at every host:

- `prog_run` (:103): a finaliser raises a name inside the region, the error is suppressed, and the
  cancel answers `()`;
- `prog₃_run` (:113): a finaliser raises a name handled outside the region, and the outer handler
  receives it.

PROVED.

### 1.2 Types

| object | where | what |
|---|---|---|
| `Qual` = `lin`, `aff`, `unr` | `Core/Types.lean:37-41` | the continuation's structural qualifier. There is no `relevant` qualifier |
| `CTy.eff n i q A B C` | `Core/Types.lean:92` | **one operation layer** over `C`. A row is a stack of layers, not a set former |
| `OpSig`; `CTy.effOf : List OpSig → VTy → CTy` | `Core/Types.lean:147-157` | `F_Σ R` = the row's layers over `F R`; `F_∅ R = F R` |
| `CTy.EffFree` | `Core/Types.lean:140-144` | no layer anywhere. The stack semantics (`cB_iff_stacks` `Core/Computation.lean:55`, `cC_iff_stacks` :106) holds only at `EffFree` types |
| `EffLeaf`, `NuLeaf`, `instT` | `Core/Types.lean:1135-1155` | `F_Σ A` is a ν observation leaf when its operation types are closed (`A.Cl 0 ∧ B.Cl 0`) |
| `loopEffBody`, `loopEff` | `Core/Types.lean:1173-1177` | `Loop_Σ A B = νX. F_Σ(A ⊕ U X) & F_Σ B`. Positive at closed operation types: `loopEffBody_nuOk` (:1272) |
| `affEffBody`, `affEffBody_nuOk` | `Core/Aff.lean:155-164` | effectful affine closure `νX. (A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`. **Positivity only.** It has no rules and no programs |
| `Row := List OpSig`; `Row.find` (first match) | `Core/EffRules.lean:33-38` | a row is a first-match list keyed by `(n, i)` |
| `OpSig.abort` | `Core/EffRules.lean:40` | abortive ⇔ `B = 0` and `q ≠ lin` |
| `RowLe`, `Row.NZ`, `Row.Weak`, `Row.Unr`, `Row.abortOnly`, `Row.Uniq` | `Core/EffRules.lean:699-746` | row order; names nonzero; has a weakening op; has an `unr` op; abortive sub-row; keys unique |
| `Row.ofEff`, `kTy`, `clauseTy`, `clausesTy`, `retTy`, `hndTerm` | `Core/EffRules.lean:969-998` | an effect's row at name `n`; `κ`'s type `U((B ⊸ F_Σ R) & ⊤)` / `U((B ⊸ F_Σ R) & F_Σ 1)` / `!U(…)`; clause types (an abortive clause is `!U(A ⊸ F_Σ R)`) |
| `Row.Unwind S x` | `Core/EffBorrow.lean:133-134` | every op abortive, name ≠ 0, `'x ∉ A`, and `A` outlives every lifetime |

### 1.3 Typing (`CDerives`)

The rules are in `Core/Fundamental.lean`. Each is discharged in `fundamentalC` (:434-564), and
the discharging lemma is named in the table.

| rule | where | premises (abridged) | compat lemma |
|---|---|---|---|
| `effSub` `[sub]` | :340 | `RowLe S S'` | `sub_compatC` `Core/EffRules.lean:774` |
| `effPerform` | :343 | `Row.find S o.n o.i = some o`, `o.abort = false`, `V : o.A` | `perform_compatC` :781 |
| `effRaise` | :348 | as above with `o.abort = true`, `o.A.Drop`, at any answer `B` | `raise_compatC` :797 |
| `effLet` `[let]` | :353 | `S.Weak → Γ₂.Drops`, `S.Unr → Persistent Γ₂` | `let_compatC` :896 |
| `effThen` `[then]` | :360 | `S.NZ`, `S.Uniq`, `S.Unr → Persistent Γ₂`, `D : F_{S.abortOnly} 1` | `then_compatC` :928 |
| `effHandle` `[handle]` | :367 | `n ≠ 0`, `∀ o ∈ S, o.n ≠ n`, `|E| ≤ 2³²`, `h_ret`, clauses as variables | `handle_compatC` :1092 |
| `boundedFix` | :196 | at every computation type `C` | `boundedFix_compatX` `Core/BoundedFix.lean:91` |
| `withbor1U`, `withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU` | :258-293 | each takes `hS : S.Unwind x` and a closed finaliser `d` | `Core/EffBorrow.lean:446, 275, 356, 548, 645, 726` |

The pure borrow constants `withbor1/2/3`, `withload` and `withswap` (:239-255) take pure
callbacks. **`withswap` has no unwinding form**: SPEC §19 says it is "not a borrow"
(`SPEC.md:2628-2629`).

Neither `effPerform` nor `effHandle` requires closed operation types. Closedness is required only
by `Row.Unwind` (at borrow callbacks) and by `EffLeaf` (at ν observations).

### 1.4 The relation's effect clauses

| object | where | what |
|---|---|---|
| `forceE` at `.eff` | `Core/Relation.lean:64-67` | a thunk of `F_Σ A` is forced by `()`, as at `F A` |
| `cC (.eff n i q A B C)` | `Core/Relation.lean:165-168` | `ewpTS ls e (opTable (OpTab.ext n i ⟨q, B.isZero && q != .lin, 𝒱⟦A⟧, 𝒱⟦B⟧⟩ (effTab C δ))) (effRet C δ)` |
| `effTab`, `effRet`, `effRetE` | :170-185 | the row's op table; the answer relation `𝒱⟦R⟧` |
| `cB` at `.eff` | :196-199 | the same, with the answer at the ν candidate |
| `cC_effOf` | `Core/EffRules.lean:73` | `cC (F_Σ R) = ewpTS (opTable (Row.tab Σ δ)) 𝒱⟦R⟧` |
| `effTab_effOf`, `effRet_effOf` | `Core/EffRules.lean:49, 60` | |
| `effRetE_mono`, `effTab_instT`, `effRetE_unroll` | `Core/NuRel.lean:43, 115, 120` | the effect leaf under ν's candidate and unrolling |

The Kripke quantifier over `Ext ls ls'` sits at `U` (`Core/Relation.lean:127-128`) and in the op
table's continuation share (`contShare`, `Core/EffDefs.lean:144-149`, and `KapRel`,
`Core/EffRules.lean:569-577`). It does not sit at `⊸` or `∀`.

### 1.5 The effect wp and the op table (`Core/EffDefs.lean`)

| object | lines | what |
|---|---|---|
| `wpG ls e Q` | 27-40 | `wpTS` (`Core/World.lean:186-201`) with the run ending at any term `t` and `Q ls' t`; otherwise verbatim |
| `valPost` | 43-44 | |
| `Table`, `Table.Mono`, `Table.Abortive`, `Table.bot` | 50-65 | a protocol table over stopped terms; `Abortive` = owes no continuation |
| `ewpStep`, `ewpTS` | 68-75 | `ewpTS` is the least fixed point of "`wpG` to a value in `Q`, or to a stop `Tb` admits, owing `P`", in `Prop` |
| `OpEnt`, `OpTab`, `OpTab.empty`, `OpTab.ext` | 104-118 | |
| `errOk`, `cancelTab`, `cancelOwed` | 122-140 | a cancel run's table. Its error is an abortive op of the row with a name outside the region, and nothing is left owned |
| `contShare` | 144-149 | `unr` ⇒ share is `∅`; at every `Ext` future, resumed at every answer in `PB`; with weakening, `cancelOwed` |
| `opTable T` | 157-167 | stops: `K[perform (n,i,v)]` with `K.HasHnd n = false`, non-abortive, `PA ⋆ contShare`; or `K[raise (n,i,v)]` with `K.Catches n = false`, abortive, `(PA ∧ NoOwn) ⋆ NoOwn` |

**Lemmas over the wp** (`Core/EffWp.lean`). All are PROVED at σ = [].

- `wpTS_iff_wpG` (:43).
- Fixed point: `ewp_ind` (:754), `ewp_fold` (:759), `ewp_unfold` (:765).
- `ewp_bot` (:772): `ewpTS · Table.bot = wpTS`. This is effect safety at the empty row.
- `ewp_of_wp` (:785), `ewp_val` (:790), `ewp_mono` (:795).
- `ewp_abortive` (:811): at an abortive table, `ewpTS` is one `wpG`.
- `wpG_step` (:868), `wpG_bind` (:878), `wpG_bind_pure` (:914), `wpG_bind_frame` (:922).
- `ewp_step` (:936), `ewp_bind_pure_frame` (:941), `opTable_mono` (:951).
- `wpG_here` (:962), `wpG_head` (:973), `wpG_ramify` (:978), `wpG_frame` (:1005), `wpG_garbage` (:730).
- `cancelTab_abortive` (:1013).

**[TR] frames at `wpG`.** The proofs of `Core/FrameRules.lean` never inspect the final term
(`Core/EffWp.lean:11-15`):

- `wpG_I_frameX` (6.64, :75), `wpG_M_frameX` (6.65, :363), `wpG_M_antiFrameX` (6.66, :567);
- family and reborrow frames at `wpG`: `wpG_reborrow` (`Core/Reborrow.lean:232`, 6.150);
- `wpG_M_frameList`, `wpG_M_frameFam`, `wpG_I_frameList`, `wpG_I_frameFam` (`Core/SliceFrames.lean:162, 249, 318, 414`).

**Rule-level lemmas** (`Core/EffRules.lean`):

- `ewp_perform_here` (:100), `ewp_raise_here` (:115);
- `OpTab.Le`, `opTable_le`, `ewp_sub` (:126-159);
- `cancel_frame` (:168);
- `ewp_frame_plain` (:193): `[let]`'s frame carried through every stop;
- `OpTab.AbortOnly`, `OpTab.Local`, `opTable_abortive`, `ewp_cfin`, `ewp_cancel_absorb`, `cancel_then` (:247-342);
- `ewp_frame_then` (:369): `[then]`'s finaliser at a cancel or an abortive stop;
- `ewp_kappa_resume` (:493), `ewp_kappa_cancel` (:529);
- `KapRel` (:569), `ewp_ccatch` (:580);
- `ewp_handle` (:615): a handler, by induction on the inner lfp, in the five cases `[ret]`, `[op]` own name, forward resuming, `[unwind]` own name, forward abortive.

### 1.6 Frame/borrow rules at effect rows (the `*U` twins)

**LIFO frames over `ewpTS` at an abortive table** (`Core/EffWp.lean`):

- `ewpTS_I_frameU` (:828), `ewpTS_M_frameU` (:842), `ewpTS_M_antiFrameU` (:854);
- each is `(ewp_abortive hTb).mpr ∘ wpG_*_frameX`;
- each requires `hTb : Tb.Abortive`.

There is no frame lemma over `ewpTS` at a table that owes a continuation.

**Unwinding borrows** (`Core/EffBorrow.lean`):

- `Table.withFr` (:44), `ewp_unwind` (:54), `ewp_end` (:97), `ewp_box_end` (:118);
- `Row.Unwind` with `.nz`, `.abort`, `.tab_extend` (the table does not see `'x`) and `.out` (an argument outlives the frame) (:133-171);
- `cbUTy`, `withborUTy`, `withbor{1,2,3}UTy` (:177-198);
- `withborUE d = λr. λf. (f [] r) then b. (r, b) unwind d r` (:200);
- `withloadUTy`, `sliceBorrow{M,I}UTy`, `cbEnds` (:525-640);
- the six compat lemmas listed in §1.3.

### 1.7 Theorems: adequacy, every run, leak freedom, effect safety

| theorem | where | statement (one line) | world |
|---|---|---|---|
| `fundamentalC` | `Core/Fundamental.lean:434` | every `CDerives` rule, effect rules included, is sound at `SemJ` | σ = [] |
| `adequacyC` | :590 | closed `F 1` runs from empty memory to `()` and empty memory (some run) | σ = [] |
| `fundamentalD` | `Core/Demonic.lean:284` | FP at the demonic `wpTSD` | σ = [] |
| `adequacyD`, `adequacyD_safe`, `adequacyD_val` | `Core/Demonic.lean:312, 325, 334` | every run of a closed `F 1` program, under every allocator, continues to `()` at empty memory; never stuck | σ = [] |
| `adequacyD_obs` | `Core/EffPrograms.lean:41` | the same at a persistent answer type | σ = [] |
| `total_every_alloc`, `total_run_prefix`, `total_every_run`, `total_no_infinite_run` | `Core/Totality.lean:40, 56, 64, 223` | a closed `F A` program terminates on every run | σ = [] |
| `fixSelf_valid`, `boundedFix_compatX` | `Core/BoundedFix.lean:57, 91` | `bounded_fix` is sound at every computation type, rows included, by induction on the budget | σ = [] |

**Leak freedom** is the `NoOwn ρp` conjunct of `wpG`/`wpTS` (`Core/EffDefs.lean:38`,
`Core/World.lean:197`) together with `reclaim` (`Core/Fundamental.lean:534`). There is no
separately named exactly-once/LIFO finalisation theorem.

**Effect safety** has no named theorem. It is the statement of `adequacyD` at `F 1 = F_∅ 1`
(`CTy.effOf [] = .ret`, `Core/Types.lean:156`), together with `ewp_bot`. A program with an
unhandled op is not typed at `F 1`. This reading is mine, not a stated theorem.

**Acceptance programs** (`Core/EffPrograms.lean`). Each is a closed `CDerives` derivation, run by
`adequacyD`/`adequacyD_obs` and by the interpreter (`…_eval`, :1045-1092). All PROVED.

- `logOutside`, `failOutside` (:220, :277);
- `nLogOutside`, `nFailOutside` (:484, :487);
- `logInBorrow` (:578);
- `reborrowRaise` (:345);
- `tickProg n` (:714), `tickAnsProg n` (:995);
- `takeProg n` (:787);
- `storeCancel` (:905).

`Core/EffExamples.lean` has two more handled programs: `prog` (linear resume, :35) and `progC`
(affine cancel, :67).

**Answering-handler laws** (`Core/Handlers.lean`). These are run facts about elaborated terms,
not relation facts:

- `op_tail` (:76), `op_answer` (:133), `handle_fold` (:211);
- `abort_passes` (:153), `return_resumes` (:167), `loop_abort` (:229).

The abort laws are about the pre-§19 sum schema. SPEC says so at `SPEC.md:2206-2208`.

**No handler laws over `hnd`.** No H-ret/H-op/H-fwd lemma is stated over `hnd`/`ewpTS` in Core.
`handle_compatC` is a compatibility lemma.

### 1.8 T1: the stop condition and what depends on it

**The clause.** `wpG`'s postcondition carries
`(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)` (`Core/EffDefs.lean:40`), copied verbatim
from `wpTS` (`Core/World.lean:199`). `wpTS`'s docstring explains it: "a record 6.64 creates inside
a run is ended before the run returns" (`Core/World.lean:176-185`). `wpG` keeps the conjunct at
**every** final term, a stop at `perform` included.

So: **every 6.64 frame and reborrow record opened inside a run is closed at every stop.** No
internal lend spans a suspension. 6.65 `mut` lends leave no trace in `ps` (`TW.mutFold`,
`Core/World.lean:135-139`); they are bracketed by `↭` instead.

This is T1 as SPEC uses it ("a stored κ would hold a lend across a suspension (T1, #172)",
`SPEC.md:2338-2340`). It is the same obligation as theory-index T1, "the spanning lend (K1)"
(`docs/theory-index.md`, §T1; #172).

**What consumes it, in Core:**

1. **The definitions.** `ewpStep`/`ewpTS` are built on `wpG` (`Core/EffDefs.lean:68-75`), so
   every `cC`/`cB` clause at `F_Σ` (`Core/Relation.lean:165-168, 196-199`) inherits the clause.
2. **Composition.** `wpG_bind` chains the two runs' `ps`/`ls` equalities
   (`Core/EffWp.lean:878-911`; the `(kps p).trans (hps' p)` step).
3. **Frames carried through stops.** `ewp_frame_plain` and `ewp_frame_then` take
   `hFs : (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls')` (`Core/EffRules.lean:197`, :371).
   That is a frame stable under the list a stop returns.
4. **Borrows at effect rows.** The frame lemmas at `ewpTS` exist only at abortive tables (§1.6).
   So every borrow callback at a row is restricted to `Row.Unwind` (abortive ops only;
   `Core/EffBorrow.lean:133`). The pure constants take pure callbacks. **No borrow constant
   admits a callback that performs a resuming op.**

**What consumes it at the surface:**

- a resuming op inside a borrow block is rejected (`corpus/reject/gen-self-borrow.bc`; SPEC §15
  *Self-reference*, `SPEC.md:1605-1613`);
- a resuming body in a `for` over `&a`/`&mut a` is rejected (`corpus/reject/for-lend-resumes.bc`;
  `SPEC.md:1880-1887`);
- a borrow block's body may perform only abortive ops (SPEC §18, `SPEC.md:2159-2163`);
- loops lend per observation (SPEC §14, `SPEC.md:1397-1404`).

**Status.** That the stop condition holds is true by definition. Lifting it is OPEN (#172, and the
tier-2 issues #275–#280).

- The user's rule, 2026-10-02: tier 2 proceeds on a frozen list. If an item spawns a new unknown,
  "tier 2 halts. The language ships at **tier 1**: T1 kept"
  (memory `hard-stop-on-regress`). Refinement, same day: "If the new work is n+1 and we are done,
  it's fine. If it's 3 and then 4 and then 5, no."
- The audit (origin/effects-audit `docs/effects-audit.md` §1 item 4, §4.1 C1) locates T1 in this
  one clause. Its reading that "the ghost-end line … works around it from outside" is the
  audit's, `[read]`, not Lean.

---

## 2. SPEC.md entries touching effects, against the Lean

Section numbers are SPEC's `§N`; entry numbers are `N − 1`.

| § (entry) | specifies | Lean matches? |
|---|---|---|
| §11 (10) Externs and standard I/O, `SPEC.md:732` | capabilities are externs; `read_byte`/`write_byte` are `withswap` on a lent cell; end-to-end `externs_every_run` | Matches. The capabilities are `withswap` code (`Core/Stdio.lean:146-161`). No op table checks them: answering effects never become a row |
| §12 (11) Destructors, :1026 | `dtorE`, used as the unwinding forms' finaliser | Matches (`Core/Dtor.lean`; finaliser premise `hd` at `Core/Fundamental.lean:260`) |
| §13 (12) Every run is safe, :1119 | allocators, `wpTSD`, `adequacyD` | Matches (`Core/Alloc.lean`, `Core/Demonic.lean`). Effects add the capture cases to determinism (`head_det_eff`) |
| §14 (13) Divergence as an effect, :1190 | `A ⇒ div B ≜ U(A ⊸ F(U(Loop B R)))`; `div_bind`/`div_fuel`/`div_defer` library code; inference; one state machine per body; totality | No `CDerives` change, as stated. Totality theorems present (`Core/Totality.lean`). "`div_fuel` is `driveE` by construction, not by a proved equation" (:1494) |
| §15 (14) Generators, :1497 | `Yield` library effect; `for` as a handler site; stored generators `pull`; adapters; no kernel change | No `CDerives` change, as stated. `pull` has no Core counterpart (SPEC says so, :1585) |
| §16 (15) Counted loops, :1705 | `count`, `count_try`; *Effectful bodies* (:1870): a resuming body makes the `for` a div loop | Kernel matches. **Stale:** §16 Open (:1917-1919) still says such a body "is rejected"; only the "loops" half is |
| §18 (17) Effects and handlers, :2064 | surface; answering effects as capabilities; control effects as §19 sites; laws in `Core/Handlers.lean` | Laws present as stated. The `Handlers.lean` docstring (:8) still calls decision 48 current (see §5) |
| §19 (18) Native capture, :2270 | machine, cancels, `F_Σ`, six rules, `wpG`/`ewpTS`/op tables, LIFO frames, unwinding borrows, `Loop_Σ`, theorems, programs, lowering | Substance matches §1. Differences below |
| §20 (19) Recursion as an effect, :2985 | `bounded_fix`; groups; `Exhausted`; heap driver; lowering. "Revised by §21" | Kernel matches (`Core/BoundedFix.lean`) |
| §21 (20) Fixed point of a generator, :3134 | groups as `bounded_fix[1, R]` of a generator; layers; handler clauses after/with state | No kernel change, as stated. The spike's `boundedFixEnv_compatX` is cited as an instance in `experiments/SecondClass` |
| §22 (21) Affine closure, :3288 | `Aff^c`; effectful closure positive | Pure `Aff` matches (`Core/Aff.lean`, `AffRules.lean`, `AffPrograms.lean`). The effectful form has positivity only (`affEffBody_nuOk`): no rules, no program |
| §23 (22) Non-strict outlives, :3463 | side conditions `⊑`, incl. at `Core/EffBorrow.lean` | Matches (`VOutlivesLe` premises on the `*U` twins) |

**§19 against Lean: differences.**

- **Row former.** SPEC writes `F_Σ A` "(`CTy.eff Σ A`)", with `Σ` a finite set of names
  (:2532-2535, :2407). Lean has one constructor per operation layer and rows as first-match lists
  (`Core/Types.lean:92`, `Core/EffRules.lean:33-38`). SPEC's *As built* (:2582-2588) records the
  list reading.
- **"Operation types are closed in lifetimes"** (:2418-2419, :2537). This is not a premise of
  `effPerform` or `effHandle`. It is enforced only by `Row.Unwind` and `EffLeaf` (§1.3). The
  audit flags the same (M13).
- **Context predicates.** SPEC's `Kont.NoHnd`/`Kont.NoUbind` (:2454-2459) are
  `Kont.HasHnd`/`Kont.Catches` in Lean. `Catches` also counts `cfin` and `ccatch`.
- **Theorem names in *Theorems* that have no Lean declaration** (grep of `Core`, `Support`, `Paper`):
  - `ewp_perform` (Lean: `ewp_perform_here`);
  - `ewp_bind` and `ewp_bind_pure` (Lean: `wpG_bind`, `ewp_bind_pure_frame`, `ewp_frame_plain`);
  - `ewp_ubind` (Lean: `ewp_frame_then`);
  - `ewp_head`;
  - `wpTS_I_frameU`, `wpTS_M_frameU`, `wpTS_M_antiFrameU` (Lean: `ewpTS_*`);
  - `cancel_compatC` (Lean: `ewp_ccatch`, `cancel_frame`, `ewp_kappa_cancel`).

  The names `cB_iff_stacks`, `cC_iff_stacks`, `node_ok`, `head_det_eff`, `head_nested` and
  `head_plug` do exist.
- **Status is stale.** "Entry 18 (§19) is in progress (#186)" (:3665). #186 closed on 2026-10-01,
  and the Status itself lists stages 1–5 and the lowering (#205) as implemented. "Entry 19 …
  `Backend/Clos/Capture.lean` (`unwindClause?`" (:3644) is also stale: §21 removed it (:3246,
  :3649), and no code has it.

---

## 3. Frontend, checker, backend

The frontend inventory was gathered by a delegated read of the tree. I spot-checked the anchors
(`Capture.lean:542 tailClause?`, `:940 machine`, `Convert.lean:228 fixValue`, `:448 markUbinds`,
`Effects.lean:418 rowV`, `:1398 withCtl`).

### 3.1 What compiles and runs

| feature | SPEC | issue / PR | where |
|---|---|---|---|
| effect declarations `fn`/`ctl`/`linear ctl`/`multi ctl` | §18 | #214, dec. 55 | `Frontend/Parser.lean:1884-1916`; checks `Frontend/Elab/Effects.lean:2222-2240`. No corpus program uses `linear ctl` or `multi ctl`; multi-shot is exercised only by the kernel program `multi-shot` |
| answering handlers, `with h(e)`, `with h(&mut c)` | §18 | S1a #152/#164, kept by #214 | `clauseDef` Effects.lean:2055, `withBlk` :1363, `opCall` :1292. Elaborate to `withbor` + `withswap` |
| control handlers, static name per `with` site | §18–§19 | #214 | `withCtl` :1398, `ctlCall` :1311, `hndCtlC` `Frontend/Sugar.lean:3437` |
| clauses with state; abortive clauses after the handler | §21 | #232 (#216, #229), dec. 59 | `resumeCall` Effects.lean:1238; `HInfo.after` Sugar.lean:3478-3483 |
| rows: inferred, written, copies per site | §18 | #214 | `rowV`/`rowC` Effects.lean:418/454; `copyFor` :1763, `copyOf` :2015 |
| `Fail` with `to_result`/`default`/`map_err` | §18 | #214 | `lib/fail.bc:17-29` |
| unwinding borrow blocks | §18–§19 | #214 | `Const.unwinding`/`unwindingC?` Sugar.lean:2578/2588 |
| drop glue | §18–§19 | #214, dec. 55 | in the checker: `Frontend/Check/Steps.lean:586-639` |
| `Yield`, push `for`, stored `pull` generators, adapters | §15 | #220 (#188 stage 2), dec. 56 | `lib/yield.bc:13`; `forSite` Effects.lean:1666 → `forYield` Sugar.lean:3871; `pullSite` :1706 → `pullView` Sugar.lean:4075; `lib/adapters.bc` |
| div loops, `div_bind`/`div_fuel`/`div_defer` | §14 | #81, dec. 35 | `lib/div.bc:43, 71, 111` |
| effectful `for` over data → div loop | §16 | #227 | `forDataDiv` Sugar.lean:3766 |
| recursion: `bounded_fix`, `Exhausted`, `deep`, layers | §20 as revised by §21 | #227 (dec. 58), #232 (dec. 59) | `recGroupsOf` Effects.lean:2111, `groupCopy` :1846, `selfCall` :1192, `recBudget` :271 (10000), `exhEff?` :240, `driver?` :250, `isLayerTy` :260, `layerCopy` :1794, `recMachine` Sugar.lean:2841 |

**Stages.** S1 (#152–#154) is closed. #188 stages 1–3 merged as #214, #220 and #227 on
2026-10-01, and #232 merged on 2026-10-02. #188 is OPEN; owner comment of 2026-10-01: "Stages 4–5
on hold until the second-class / System C spike reports." Still open: S2 (#155, #156), `|>`
(#157, which has no lexer support), S4b/c (#160, #161) and S5 (#162).

**Two row computations.**

- Rows by effect **name** in `Frontend/Elab/Effects.lean` (`Inst`, :81; `rowV`/`rowC`).
- Rows by `(n, i)` in `Sugar.opsC`/`opsV` (:2530/:2545), in the kernel and in the backend
  (`OpKey`, `Backend/Clos/Unwind.lean:37`).

No lemma relates the two. Recognition is by **shape**, not name: `Env.iterEff` (:229), `exhEff?`,
`driver?`, `isLayerTy`.

**`io_bt`** is a reserved variable name used as a cross-pass marker (`Parser.lean:1146, 1213`,
:832; `Sugar.lean:1938`, :3705-3708). `stdin`/`stdout`/`stderr` are hard-coded
(`Parser.lean:1142, 1210`; `Sugar.lean:72`; `Check/Externs.lean:96-100`; `Backend/Driver.lean:78`).

**Rejected, with a message.** Each item has a corpus reject unless noted.

- an op in a closure not run in place: `effect-in-closure.bc`;
- a function with a row as a value: `effect-fn-value.bc`;
- an op in an answering clause: `effect-clause-op.bc`;
- a resuming op across a borrow: `gen-self-borrow.bc`;
- recursion through a site: `rec-through-site.bc`;
- a loop in a recursive body: `rec-loop.bc`;
- a resuming body over `&a`: `for-lend-resumes.bc`;
- without a reject file: generic recursion (Effects.lean:2215); an answering effect with type
  parameters (:2233); an effect with both kinds (:2231); an effect under `deep` (:1965).

### 3.2 Checker

`Frontend/Check/Checker.lean` handles the effect forms:

- `.unwind` :272;
- `.perform` :282, which refuses abortive ops;
- `.abort` :288;
- `.handle` :291.

`Frontend/Check/Rules.lean` maps them to the six `CDerives` rules: `rEffSub` :231, `rPerform`
:236, `rRaise` :242, `rEffLet` :249, `rEffThen` :258, `rEffHandle` :270.

The six `*U` constants are `Frontend/Check/Consts.lean:137-209`, and `bounded_fix` is :391-394.
`Row.unwindB` (`Frontend/Check/Decide.lean:798`) has its soundness at :801.

### 3.3 Lowering

Effect handling is erased: there is no handler stack, no search and no stack switching
(`Backend/Clos/Capture.lean:5-9`; `Backend/Clos/Unwind.lean:33-34`; SPEC §19 *Lowering*). This
meets the user's requirement of 2026-09-30, "Part of 18 needs to be effect handling is erased"
(memory `effect-handling-is-erased`).

- **Pipeline.** `convert → capture → unwind → collapse` (`Backend/Driver.lean:88, 238`). The
  closure interpreter throws on an un-lowered effect node (`Backend/Clos/Interp.lean:458-460`).
- **Abortive ops: branch per call** (`Unwind.lean`: `UFacts.raises` :123, `finalise` :206,
  `Prog.unwind` :375).
- **Control ops: state machines** (`Capture.lean`: `machine` :940, `resumeArm` :861, `cancelArm`
  :893). Cancel is the state's destructor. Masks reject a handler named ≥ 64 (:986-994).
- **Tail-resumptive op: direct call** (`tailClause?` :542, `tailResumptive` :631).
- **Suspension per projection** (`Ops.selArg` :357, `SFacts.keysAt` :363).
- **Rejected:** a name that has both control and abortive ops (:165).
- **`bounded_fix`** becomes two codes (`fixValue`, `Convert.lean:228`). A finaliser frame's
  clauses become one code (`markUbinds` :448).
- **`bcc kernel`** compiles 23 kernel programs (`Backend/Kernel.lean:136-158`). Their counts are in
  `corpus/kernel-counts.expected`, for example `take` 2/2/0, `store-cancel` 2/0/0, `multi-shot`
  0/0/0 and `recursive-yield` 20.

### 3.4 Corpus exercising effects

Counts are allocations / dispatched / copies, from `corpus/counts.expected`.

- **effects-\*:** `effects-map` 11 (equal to `effects-map-hand`), `effects-fold` 7 (equal to
  `-fold-sum`), `effects-borrow-raise` 2, `effects-log-fail` 3, `effects-map-fail` 3,
  `effects-generic` 1.
- **core-effects-\*:** hand-written core.
- **capture-\*-hand:** hand-written equivalents of kernel programs.
- **clause-captures:** 6/3/0.
- **gen-\*:** most 0/0/0. `gen-close` is 4 with no copy.
- **rec-\*:** `rec-fib` 0, `rec-parser` 17, `rec-overflow` 10101 (a million levels, `live 0`),
  `rec-deep` 60040.
- **Other groups:** `for-data-div`, `lend-*`, `io-*`.
- **Pending, effect-related:**
  - `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io`: a capability across an affine
    `yield`; a cancel has no residual;
  - `yield-callback`: #161;
  - `raise-in-fold`: K4, #178;
  - `async-borrow`: #52;
  - `backtrack-multishot`: its stated blocker is stale (§5).

---

## 4. Unmerged effect-related branches

These were gathered by a delegated read. I checked `lift-stage1`'s tip and `Gen.lean:158/199`, and
PR #233's close date. No unmerged branch touches `Core/Eff*`, `Core/Handlers.lean`,
`experiments/EffModelRel` or `Backend/Clos/*`. None of the changed `.lean` files contains `sorry`
or `axiom`. Every worktree is clean.

| branch | tip | contents | world | status |
|---|---|---|---|---|
| `lift-stage1` (worktree `~/repos/borrow-core-lift-stage1`) | `c9b3694` 2026-10-02 "WIP (#274, not for merge): [gen] transcription in progress, stopped" | `Core/AffTy.lean` (+108, a move of Aff's type/relation/`cC_aff_iff`/`aff_coind` before `CDerives`); `Core/Gen.lean` (+242): `genE`, `Qgen` (D14.4, :158), `ewp_gen` (L14.3, :199), from `ewpTS` at `[genOp]` to `ewpTS` at `OpTab.empty` with answer `Qgen`, taking a `hdone` premise | Core σ = [] | `ewp_gen` PROVED. T14.4 (`affBox_of_kapRel`), T14.6 (`gen_compatC`) and the `CDerives.gen` rule are named in the docstring (:27-38) and absent: OPEN, stopped. `Gen.lean` is imported by nothing. No PR. Plan: #274 owner comment 2026-10-02T23:07 |
| `effect-callbacks` | `c321bd2` 2026-10-01 | elaborator only (`Frontend/Elab/Effects.lean` +1125, ports, `cbCopyOf`, …), SPEC §22 draft, ~30 corpus files; no theorems | none | REJECTED by the owner. PR #233 closed 2026-10-02: "It solves the first-order case only, and the higher-order cases … were left pending behind workarounds. The goal was the general form, so we're stepping back to restate what we're trying to do before building again." #161 OPEN |
| `loophandle` | `51772c1` 2026-10-01 | `docs/handlers-over-div.md`: a derived `d_handleLoop` design | none | PAPER-ONLY. The doc says (:5-10): "Parked by the user before any Lean or probe was written: handlers around loops are not a priority" |
| `borrow-core-188` worktree | detached `d1c2f6d` 2026-10-01 (#220) | an ancestor of main | — | merged; nothing unmerged |
| `gfp` (PR #284, OPEN) | `daf56c0` 2026-10-02 | `experiments/GhostEnd/GhostEnd/Below.lean`: `not_gfpAt_below` (:196), `not_gfp` (:282) | GhostEnd stacked `vRLs`/`cRLs` | REFUTED: D16.1/D16.2 as we stated them, over every valid configuration. The witness **does not arise** (shown on `gfp-arising`). Owner on #279, 2026-10-03: "whether its witness arises was not checked" |
| `gfp-arising` (PR #285, OPEN) | `d31cbb3` 2026-10-02 | `Arising.lean`: `tabAtS_comp`, `wpG_tabAtS_one`, `wpG_below_not_arises` (:139), guarded `vRLa`/`cRLa`, `vRLa_nil`/`cRLa_nil` (σ = [] reduces to `vC`/`cC`), `lam_RLa`, `allI_RLa` | GhostEnd guarded `vRLa` | rows `lam` and `allI` PROVED; GFPA as a whole OPEN |
| `borrow-callbacks` (PR #287, OPEN) | `5cfe062` 2026-10-02 | `Extend.lean`: `vRLk`/`cRLk`, `all_elimK`, `callback_ext`, `callback_ext_one`; `docs/effects-tr/17-borrow-callbacks.md` | GhostEnd Kripke-extended `vRLk` | PROVED pieces; GFP at `vRLk` OPEN (needs Kripke monotonicity along stack extension); no `vRLk_nil` |
| `decision-48-wording` (worktree `d48`, PR #234, OPEN) | `3a3ec7d` 2026-10-02 | rewords decision 48 as superseded | none | OPEN, no comments |
| `effects-audit` (PR #289, OPEN) | `6db9b86` 2026-10-02 | `docs/effects-audit.md` | none | read-only audit; verdict CONSOLIDATE |
| `effects-calculus-spec` (PR #461, draft) | `8296ab0` 2026-10-03 | `docs/effects-calculus/` | none | PAPER-ONLY; failed validation; a list of questions |
| older design-only: `iteration-design` (PR #133), `interfaces-research` (#169), `platform-design` (#140), `type-declarations` (#141) | — | docs | none | open PRs, no Lean |

#279 and #275 were closed on 2026-10-03T09:04 as superseded by #290. They were reopened at 11:24:
"The plan issues this was closed in favour of have been withdrawn." There is no owner decision yet
on merging #284, #285 or #287.

---

## 5. Known gaps and stale records

### 5.1 Gaps recorded in SPEC *Open* sections

- **§19 Open** (`SPEC.md:2960-2983`):
  - generative names (T2, #173);
  - a tail-resumptive clause with captures;
  - **a non-abortive op crossing a borrow (T1, #172)**;
  - finaliser policies (K3, #162), including non-abortive ops in a finaliser;
  - a native handler parameter;
  - shallow handlers (covered by ν);
  - μ with `X` under `⊸` (T15, #182);
  - interfaces (#169).
- **§19 *Finalisers***: `D : F_{Σ^abort} 1` (:2600-2606). A finaliser cannot perform a resuming op.
- **§18 Open** (:2250-2268):
  - named instances #155; bundles #156;
  - effectful callbacks #161;
  - borrow-answering ops #160;
  - K4 (#178);
  - an error holding an owned value (#215; `[raise]` asks `A.Drop`);
  - a control `with` handing back `let mut`s;
  - a capability through `for` over `&a`.
- **§15 Open** (:1683-1703):
  - a capability across `yield` (a cancel has no residual);
  - callbacks that yield (#161);
  - stored generators over a row: "a generator that performs another effect besides its iteration
    effect … is not stored".
- **§20/§21 Open** (:3120-3132, :3270-3286):
  - `memo` (#211);
  - the budget per driver;
  - a recursion whose body loops ("a handler around a div computation is not provided for any
    effect");
  - effects under `deep`; generic recursion;
  - recursion through a site or values.
- **§22 Open**: the effectful affine closure has positivity only (§1.2 above).

### 5.2 Gaps visible in the Lean, not recorded as one item

- **No frame lemma over `ewpTS` at a non-abortive table** (§1.6). Hence no borrow at a resuming
  row, and no `withswap` unwinding form.
- **No handler laws over `hnd`**: H-ret, H-op and H-fwd are not stated in Core. The only algebraic
  laws in the project are in `experiments/EffModelRel`, the sibling calculus (audit C3, `[Lean]`
  per the audit).
- **No op-name renaming lemma over `CDerives`** to justify copies per site. Decision 57 says
  "a renaming lemma would let the checker derive once", and lists "when to build the renaming
  lemma" as Open (`docs/decisions.md:706-714`).
- **No signature object shared by kernel and frontend.** The kernel has `OpSig`/`Row`; the frontend
  has `Inst`, string-named. Answering effects never become a kernel row (§2, §11 row).
- **The stack semantics covers effect-free types only** (`cC_iff_stacks` at `EffFree`).

### 5.3 Stale records (with evidence)

| record | says | evidence it is stale |
|---|---|---|
| `SPEC.md:3665` Status | "Entry 18 (§19) is in progress (#186)" | #186 closed 2026-10-01; stages 1–5 and #205 listed as done in the same Status |
| `SPEC.md:3644` Status | `Capture.lean` has `unwindClause?` | removed by §21 (:3246); no code hit |
| `SPEC.md:1917-1919` §16 Open | a resuming body in a `for` over data "is rejected" | `forDataDiv` (`Sugar.lean:3766`), `corpus/for-data-div.bc`, §16 *Effectful bodies* (:1870) |
| `SPEC.md` §19 *Theorems* | names `ewp_perform`, `ewp_bind`, `ewp_ubind`, `wpTS_*_frameU`, `cancel_compatC` | no such declarations (§2) |
| `Core/Handlers.lean:8` | "A handler is defined by its elaboration into core terms (SPEC §18, decision 48)" | control handlers are kernel `hnd` (§19). User, 2026-09-30: "I want effects to be core to the language, we aren't going to be able to implement them correctly with sugar" (memory `effects-are-core`, which records that it supersedes decision 48's "rows never enter the core") |
| `docs/decisions.md:603` decision 48 | "Effect rows never enter the core"; "abort as a sum exit" | superseded in practice by §19 and decision 55; not marked. PR #234, which rewords it, is OPEN |
| decisions 51, 52, 53 | S1a spellings; `Fail` as a sum computation type, `try`/`catch` keywords; acceptance by the sum-schema laws | replaced by decision 55 / #214; not marked. User, 2026-09-30, on S1b's special case: "yeah i hate that" (memory `no-effect-ish-approximations`) |
| decision 47's last bullet | handlers and layers out of scope | handlers and layers are built |
| decision 42 | `gen-adapters-io.bc` "one file again" | the file is in `corpus/pending/` |
| `Frontend/Elab/Effects.lean:13, 26`, errors at :2246, :2264 | old `handler h(s: S) for E { op(x) -> e }` spelling | the parser accepts only decision 55's forms (`Parser.lean:1917-2007`) |
| `Backend/Driver.lean:28` | the budget is "`lib/rec.bc`, `rec_budget`" | it is `recBudget`, `Effects.lean:271` |
| `Backend/README.md:55-61` | every fixed point is the Z combinator | omits `fixValue`, `wrapRaise`, `markUbinds` |
| `book/src/guide/planned/effects.md:3-17` | only S1 landed; "Effect rows never enter the core" | `Yield` (#220) and kernel rows (§19) landed |
| `docs/effects-scoping.md:3` | "Stage S1 is being built from it" | S1 and #188 stages 1–3 done |
| `corpus/pending/backtrack-multishot.bc:8, 29` | "no handlers in the surface"; "the parser stops at `cap`" | surface handlers and `multi ctl` parse; what is missing is the surface program |
| `corpus/pending/async-borrow.bc` | cites `corpus/pending/borrow-across-loop.bc` | no such file |

### 5.4 Not stale, for the record

- `docs/effect-polymorphism.md:4` "Nothing here is built" and :234 "`|>` is not parsed yet" are
  still accurate.
- `lib/rec.bc:20`: `on_exhausted` takes `!(1 => A)` while `default` takes an owned value since
  #232. This matches decision 58's spelling; it is an inconsistency, not a stale record.

### 5.5 User decisions bearing on this file (quoted, with strength)

- 2026-09-30, **decided**: "I want effects to be core to the language … build them on a
  mathematical foundation backed by the literature." (`effects-are-core`)
- 2026-09-30, **requirement**: "Part of 18 needs to be effect handling is erased." The criterion is
  cost parity with the hand-written program. (`effect-handling-is-erased`)
- 2026-09-30, **decided**: "error is a control flow effect full stop." (`errors-are-control-flow-effect`)
- 2026-09-30, **decided**, after `prog_stuck` (#191): cancellation is not interceptable.
  (`errors-are-control-flow-effect`)
- 2026-10-02, **hard stop**: tier 2 runs on a frozen list; on a new unknown, "tier 2 halts. The
  language ships at tier 1: T1 kept". (`hard-stop-on-regress`)
- 2026-10-02, **priority, not a ban**: "we also don't need multishot unless we get it for free."
  (`multishot-only-if-free`)
- 2026-10-02, **scope**: "I only want to focus on what gets us to a full safe effect algebra."
  Kernel-level equations are out of scope "unless they become necessary for safety".
  (`effects-are-core`)
- 2026-10-01, **current**: "recursion is an effect was more a pretty idea than a hard req."
  (`structured-recursion-only`)
- 2026-10-01, **priority**: totality — "i don't really care about totality in general unless we
  need it for something specific". (`div-is-an-effect`)

---

## Sources read

- Core:
  - `Core/README.md`, `Core.lean`;
  - `Core/EffDefs.lean`, `EffWp.lean`, `EffRules.lean`, `EffBorrow.lean`, `EffCancel.lean`,
    `EffExamples.lean`, `EffPrograms.lean`;
  - `Core/Handlers.lean`, `Alloc.lean`, `Demonic.lean`, `BoundedFix.lean`, `Totality.lean`;
  - `Core/Types.lean` (:30-160, :1130-1280), `Relation.lean` (:1-215), `Fundamental.lean`,
    `World.lean` (:110-201), `Aff.lean` (:140-168), `NuRel.lean`, `Nu.lean`, `Steps.lean`
    (declaration list), `Stdio.lean` (declaration list), `Computation.lean` (declaration list).
- Paper and Support: `Paper/S1_Syntax/Definitions.lean` (:60-95),
  `Paper/S3_Dynamics/Definitions.lean` (:300-560), `Support/Dynamics/Interpreter.lean` (grep).
- SPEC.md §13–§23 and Status (:1119-3700).
- Docs:
  - `docs/decisions.md` (48, 51-59);
  - `docs/theory-index.md` (T1, T10-T13);
  - origin/effects-audit `docs/effects-audit.md`;
  - `~/repos/borrow-core-effects-spec/docs/effects-calculus/00-structure.md`, `01-scope.md`
    §5 (read as a list of questions).
- GitHub: issues #172, #186, #274 (with comments), the issue list; PR #233 state.
- Memory: `hard-stop-on-regress`, `effects-are-core`, `effect-handling-is-erased`,
  `no-effect-ish-approximations`, `multishot-only-if-free`, `laws-first`, `div-is-an-effect`,
  `errors-are-control-flow-effect`, `alloc-is-an-effect`, `structured-recursion-only`,
  `portable-lowerings`, `no-function-coloring`.
- Delegated reads, with anchors spot-checked:
  - Frontend, checker, backend and corpus at 8a1c326;
  - unmerged branches and worktrees `lift-stage1`, `effect-callbacks`, `loophandle`, `188`, `gfp`,
    `gfp-arising`, `borrow-callbacks`, `d48`, `effects-audit`, `effects-spec`.
