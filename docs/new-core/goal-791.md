# #791's end goal: the statements, planned backwards

*History: the tree track's plan for #791. #839 landed on the chain relation instead, with `goal791N : HandlerLawN → Goal791N` (decision 75); the current design is `chain-interpretation.md` and SPEC §62. The text below is kept as the record.*

Part of #771, the tree track. Branch `goal-791`, from `tree-core` (35fc7c0e). The Lean is
`Core/TreeGoal791.lean`. Every `def … : Prop` there elaborates, and every theorem there is
proved, with axioms within `[propext, Classical.choice, Quot.sound]`. Nothing here is a build of
#791. This is a map of what #791 must prove, and what the evidence says about each piece.

**The end goal.** Writable (`mut`) borrows, and reborrows of fields of borrowed data, held by a
suspended continuation, and returned on resume or on cancel. Sound for every well-typed program.

## 0. Four facts that set the plan

1. **No rule of `CDerives` lets a lend's callback suspend.**
   - The pure constants (`withbor2`, `withbor3`, `withload`, `withswap`, `sliceBorrowM/I`) take a
     pure callback.
   - The unwinding forms (`withbor1U`…`sliceBorrowIU`) take a callback at a row of abortive
     operations only (`Row.Unwind`, `Core/EffBorrow.lean:134`).
   - So "a `mut` lend whose callback awaits a handler outside the lend" is not a program of
     today's judgment. The end goal needs new rules, or else a condition that keeps every
     suspension inside the lend. That is condition C1 in §5.
2. **No rule gives a `mut` borrow of a boxed field.**
   - `Mut @a (Ref A)` gives `Mut 'x A` of the field only through `withswap`, whose callback is
     pure.
   - Core's chain lemma `erwp_withbor3` covers the inner frame at a cell of the content, but no
     typing rule uses it.
   - The hardest case, as specified, needs a new constant: the field reborrow `withborFE`
     (`TreeGoal791.lean:60`).
3. **`forget` of a `mut` borrow needs a garbage part, or a carrier change, under either
   candidate.**
   - Every callback of a `mut` lend ends by `forget` on its borrow, or abandons it at a raise.
     `['x] B` holds no cell at `'x`.
   - At `twp` as it stands, a run that ends holding nothing frees every location its frame holds
     nothing at (`endT_drop_frees`, :686).
   - The lender can hold nothing at `ℓ` beside the borrower's token: two cells at one location
     compose only as `imm` copies (`compS_both_imm`, :667).
   - So the token cannot vanish at `forget`, and it cannot be merged into a lender's piece. It has
     to stay where the end world reads it, which is Core's `ρ⁺`, or the carrier needs a new
     clause.
   - This is root 2 (D4) for `mut`, and it binds candidate B as much as candidate A.
4. **With the payload clause of `Row.Suspend`, I found no program refuting the natural top
   statement.** A continuation holding a `'x` borrow is captured with the lend's own frame inside
   it. The payload of an operation outlives every lifetime, so a borrow-holding thunk cannot be
   handed to `spawn`. Not derived, and no obstruction verified. The conditions in §5 are about
   what is provable at a reasonable cost, not about truth.

## 1. The top statements

| Statement | file:line | Reading |
|---|---|---|
| `Row.Suspend` | :49 | `Row.Unwind` minus its abort clause. No unrestricted operation; payload and answer free of `'x`; the payload outlives every lifetime. Decidable. |
| `Const791` (`.ty`, `.val`, `.OK`) | :75, :83, :91, :102 | The new constants, as data: `withbor2U`/`withbor3U`/`withloadU`/`sliceBorrowMU` with `Row.Suspend` in place of `Row.Unwind`, plus the field reborrow `wF`. A program uses them as `!`-typed constants in `ctx791 cs`, closed by `vals791 cs`. No judgment is added. |
| **`Goal791Top`** | :259 | Every program typed at `F 1` from the constants is `OrDiverges`. The scheduler is a typed handler inside the program (#792). |
| **`Goal791Sched`** | :268 | A task typed at `F_Σ 1` from the constants, run by a scheduler meeting `SchedOKT` at the row's table `rowTab S`, is `OrDiverges`. This is the `poolSchedAdequacyT` form. The scheduler is semantic. |
| `FundamentalT`, `ConstsT`, `BridgeT` | :282, :286, :291 | The decomposition: fundamental over `CDerives`, the constants as values of `!` their types, and the adequacy bridge (I16). |

**The interpretation** (`vT`/`cT`/`tabT`/`retT`, :182–:228; `gT` :230; `SemJT` :246). These are
`STy`/`SCmp`'s formers. Choices and stand-ins:
- `F_Σ R` is a run at the table of the row's layers, each entry `entT` (:147):
  - abortive as Core's;
  - `fin = capB` (D15);
  - `fd = fdJoinT`;
  - frame conditions `FV` (valid frames), which meet `poolSchedAdequacyT`'s premises (`fv_base`,
    `fv_present`).
- `F A` is the same at the empty table. `SCmp.retAt` reads every index up to `n`, so it is
  downward closed without a table proof.
- `Mut` at a payload with a store code (`toCode`, E1/#790).
- Empty at `μ`, type variables and `ν`. These are outside #791's fragment (I10, I11).
- `Δ.Models δ` is the chain's (I2, open).

## 2. The rule-level statements (§4 of the file, :304–:396)

Pure: `Withbor2T`, `Withbor3T`, `WithloadT`, `WithswapT`, `SliceBorrowMT`, `SliceBorrowIT`.
Unwinding: `Withbor2UT`, `Withbor3UT`. New: `Withbor2ST`, `Withbor3ST`, `WithborFST`,
`WithloadST`, `SliceBorrowMST` (each a `ConstT`, :358). Supporting: `ReleaseMutT`, `MutSubT`,
`EffPerformT`, `EffLetT`.

## 3. The hardest case (§5 of the file)

- **Task A** (`taskA` :434):
  - `c ↦ own(loc k) ● k ↦ own(())`;
  - a `mut` lend of `c` (`withborUV dRec`);
  - inside it, the field reborrow of `k` (`withborFV dFwd`), whose callback `cbField` parks while
    holding the field's borrow, then forgets it;
  - both lends end, and `dRec` frees both cells.
- `rootMut` (:440) spawns B (`thL`: B's own lend, parked, ended after A parks), then runs A.
- `rootMutC` (:444) also spawns the canceller `thC`, so A is cancelled while it holds the field's
  borrow.
- `HardestCase791` and `HardestCase791C` (:450, :453) are `OrDiverges` of `progOf` each, under
  the spawn scheduler `HS`.
- `hardest_of_root` and `hardestC_of_root` (:463, :468) are proved. Each reduces its closed
  statement to `RootAt` (the root at `cerwpT (opTableT TJ) QV`) through `poolSchedAdequacyT`, every
  premise discharged as for `progLoan_safe`.
- The lends open at fresh children inside `RootAt`'s proof. `RootAt` itself is not proved.
- `taskScoped` (:476) is condition C1's variant: the scheduler runs as the record's lend's
  callback.

## 4. The backward map

**Status:** **T** = proved on `tree-core`; **P** = available in Core (or a chain spike) to port;
**N** = new; **U** = unknown.

**PinLaw column:** is the statement a sensible candidate for a named assertion taken as a
headline hypothesis? (It must be self-contained, believed true, and used at few places.)

| Statement | Needs | Status | PinLaw candidate? |
|---|---|---|---|
| `Goal791Sched` | `FundamentalT`, `ConstsT`, `poolSchedAdequacyT` (**T**), `fv_*` (**T**, here) | — | no: it is the headline |
| `Goal791Top` | the same, plus `BridgeT`, plus `[handle]` for every typed handler (#792) | — | no |
| `FundamentalT` | every `CDerives` rule at the tree (#789's 67 ports, 13 new, 23 blocked) | **P/N** (≈30–76k, checklist) | no: too broad |
| `vT`/`cT`/`gT`/`SemJT` | the formers' laws (`STy.mono`/`down` per former: **T**); `gT` split/mono lemmas (I3) | defined here; laws **P** | — |
| `BridgeT` | `topAdequacyT` (**T**); `SCmp.retAt` at the empty frames | **P** (I16, 0.15–0.5k) | no: small |
| `Withbor2T`/`Withbor3T` | A1 `TwpGMFrame`, A2 `TwpGAntiFrame`, the garbage layer, PinExt | **P** (`withbor2/3_compatX`, `wpTS_M_frameX`, `wpTS_M_antiFrameX`) | A1/A2: yes, see below |
| `WithloadT` | `twp_reb`/`rebDeep` with per-record templates (#791's `imm` half, O1–O7) | **P/U** (scope-791 §0) | `TWC.templ` (O6): no, it is the invariant every reborrow reads |
| `WithswapT` | A2 | **P** | as A2 |
| `SliceBorrowMT`/`IT` | family lends (I8c) | **P** | no: mechanical |
| `Withbor2UT`/`3UT` | A1/A2, abortive stops at `cerwpT` (I5), `withborU` at the tree (N7) | **P/N** | I5: no, it is infrastructure |
| `Withbor2ST`/`3ST`/`WithborFST`/`SliceBorrowMST` | A3 `CerwpTGMFrame`, A4 `CerwpTGAntiFrame`, I5 (the callback's cancel raise), `withborFE`'s step lemmas | **N** (chain: `erwp_M_frame(C)`, `erwp_M_antiFrame(C)`, `erwp_withbor3` on `tree-inv`) | A3/A4: plausible, see below |
| `WithloadST` | `erwp_reborrow(Deep)` ported, the `imm` half of #791 | **P** (chain) / **U** | no |
| `ReleaseMutT` | the garbage layer (`twpG_forget`, `roots-791`) | **P** (on `roots-791`); refused at `twp` without it (fact 3) | no: provable |
| `MutSubT` | a lifetime-subsumption lemma at codes | **P** (checklist row, 20–60 lines) | no |
| `EffPerformT`, `EffLetT` | bind across stops (I4), `[let]`'s `hW` at the tree (I6) | **P/N** (0.8–2k) | no |
| `RootAt rootMut` | `Withbor2UT`/`ST`, `WithborFST`, `twp_extend` (**T**), the pool's `contShareT_resume`/`KeepRel.trans`/`stepKeepsFdEsc` (**T**), `thL_ok` (**T**) | **N** | no: it is the instance |
| `RootAt rootMutC` | as above, plus the cancel branch through `then` frames (D15, **T** for `ubind` in programs) | **N** | no |
| A1 `TwpGMFrame` (:561) | `twpG` (`roots-791`), `UpdA.of_mut_own`/`InvKeptA.of_mut_own`/`lower_mut_own_iff` (`tree-791`, proved), `ResUT.six27` (**T**), `TWNT.mutFold/Unfold` (**T**, no rule uses them), PinExt or start re-typing (`RetypeRecInv`, **U**) | **P/U** | **Yes.** Self-contained; Core proves the chain analogue (6.65, `wpTS_M_frameX`); used at the `mut` constants only. But the plain-`twp` form is refuted (`not_cerwpTMFrameC`). Only the garbage-and-pin form is believed true, and no configuration was tried at it. |
| A2 `TwpGAntiFrame` (:576) | as A1; PinExt avoids `antiInnerVal_retypes` | **P/U** | Yes, as A1 (6.66, `wpTS_M_antiFrameX`) |
| A3 `CerwpTGMFrame` (:591) | A1; strong induction on the index through `cerwpTG`; fold at a stop, re-lend at the resume and at the cancel branch (option (b), `KeepsShare`) | **N** (chain: `erwp_M_frame`, must-resume; `erwp_M_frameC` via the claim at an abortive raise) | **Plausible, weaker evidence.** The must-resume form has a chain proof. The cancellable form by option (b) has none (Core's is the claim at the raise). An assertion here would hide whether option (b) is sound. |
| A4 `CerwpTGAntiFrame` (:608) | A2; the guard `CellFoldT`, produced by the inner Mut Frame's fold (`erwp_M_frameF`) | **N** (chain: `erwp_M_antiFrame(C)`) | as A3 |
| A5 `TopAdequacyG` (:623) | A6, `cerwpT_adequacy`'s route | **N** (0.3–0.6k) | no: small and provable |
| A6 `ReclaimT` (:632) | `TaggedT` at `[]`: no borrow cell without a record | **P** (Core's `reclaim`) | no: small |
| PinExt (:513) | `TWd.Ext` replaced in `twp`, `EndT`, `contShareT`, `TVal.Mono` | **N** (a definition change; every `Core/Tree*` proof re-checked, +3–8k) | not an assertion |
| B1 `semRec` (:645) | a `mut` record constructor for `TWNT`, `TIT` clauses, coverage read through records, `STy.mut` reading `ls` | **N/U** | no |
| B2 `TokenBackT` (:655) | false direction: the step `endT_drop_frees` refuses it at every start where the frame holds nothing at `ℓ` | not refuted (no `mut`-token start world built) | no |

**Unspent hypotheses** of the chain lemmas these port:
- `MFPost`'s `ρ′ ∈ Res_α` is now carried (`MFPostG`).
- `LendOK.pa/pb` (what crosses a stop outlives the lend) is not carried by A3/A4. `Row.Suspend`'s
  payload clause is its typing face.

**Unused uniqueness results:** `RR.func`, `RR.inj_of`, `chain_unique_recT`, `ExclUniqueT.parent`.
They are not used here; they belong to the `imm` half (O3, O7).

**Run-up lemmas untranscribed at the tree:**
- 5.33's `ρ⁺` (on `roots-791` only);
- 6.64 at a general payload;
- 6.65 and 6.66 at `twp` (A1, A2);
- 6.150's chooser;
- 6.148/6.149's `mut` half.

## 5. Candidates A and B, and the conditions

### A: Core's fold-and-seal, over `twpG` and PinExt

- **Root 1.** PinExt removes the extensions that `not_cerwpTMFrame` and `antiInnerVal_retypes`
  start from (`not_pinExt_wU_wE`) and keeps location reuse (`pinExt_retypes_unheld`); both are on
  `roots-791`. A `Ref A` value at a code payload then needs `STy.ref` to read `Θ ℓ` as `STy.mut`
  does, so that the Mut Frame finds the code (`toCode`).
- **Root 2.**
  - `twpG` meets Core's `MFPost` (`twpG_admits_borrow_in_garbage`, `roots-791`).
  - It refuses an end that keeps the borrow (`mfPostG_of_mut_false`).
  - Top-level adequacy at `twpG` also needs the run to end owning no records (A5's `O = []`).
    Otherwise `twpG_ends_record_live` is a leak.
- **The Anti-Frame's callback post** is restated (`MFPostGK`, reseal at the end). `tree-791`'s
  `MFPostTK` composed the end with a second `own(u)` and held vacuously.

### B: the pinned borrow

- The lend record pins the code (`semRec`). That replaces PinExt only for recorded locations.
- **The lend's end does not take the token back.** The lender holds nothing at `ℓ`
  (`compS_both_imm`). A run cannot drop a cell its frame does not hold
  (`endT_drop_frees`). So the token stays in the run until something folds it, which is A's fold
  (6.27/6.28 along the walks, `UpdA.of_mut_own`), or it is garbage.
- `twp_lendEnd` ends `imm` lends at their composed copies. A `mut` borrow has no copy to compose,
  so `twp_lendEnd` does not accept a returned `mut` borrow without a new carrier clause.
- **Not derived:**
  - whether coverage read through `semRec` breaks `UpdA`'s ancestor (`Beneath`) cases or `TIT`.
    No configuration was built either way;
  - B's records would be masked at the run's stops (`recMask`), so `UpdA` would not read the
    token's location there. That much fits.
- **Verdict on B:** B is A's root-2 work plus `mut` records (a `TWNT` constructor, `TIT`,
  coverage). It saves only PinExt and fold-and-seal.

### The conditions, as candidates for the user, ranked by what they give up

**C2. Same-task suspension, the lend's row `Row.Suspend`.** Gives up the least.
- What it is:
  - the new constants of §1 (`withbor2S`, `withbor3S`, `withborF`, `withloadS`, `sliceBorrowMS`);
  - `withswap` stays pure: the Anti-Frame's opened content never crosses a stop, so A4's guard
    `CellFoldT` comes from the inner fold;
  - no unrestricted operation in a lend's row (already Core's rule).
- Gives up:
  - holding the opened content of a `mut` borrow (a `withswap`/`modify` body) across a
    suspension;
  - lending to another task under an outer scheduler (O9). That is already excluded by the
    payload clause.
- Inside it: the hardest case as specified (`rootMut`, `rootMutC`).
- Needs A1–A6 and I5.
- The configurations it avoids: none beyond what A avoids. Its risk is A3/A4, the cross-stop
  induction, plus option (b)'s unchecked cancel.

**C3. C2, with every operation of a lend's row must-resume (`lin`).**
- Gives up cancelling a task while it holds a `mut` borrow (`rootMutC` is outside).
- Avoids `not_mustResume_TP`'s gap: the chain proof `erwp_M_frame` ports as it stands.
- The fallback if option (b) fails.

**C1. Scoped suspension (the coordinator's hypothesis): every lend's callback at a pure or
`Row.Unwind` row.**
- What it is: today's rules, unchanged (`suspend_of_unwind`, :702). A `mut` borrow held across a
  suspension is held by a continuation whose handler runs inside the lend, and the κ's type
  mentions `'x`.
- Gives up suspending to a handler outside a lend the task holds:
  - a top-level scheduler holding a task with a live `mut` borrow of its own;
  - detached spawn holding a borrow.
- **The hardest case as specified is outside C1:** its scheduler is at the top. The variant
  inside C1 is `taskScoped`:
  - the scheduler is the record's lend's callback;
  - A holds `Mut 'a (Ref 1)` across `park`;
  - the field is reborrowed and its borrow ended within one segment;
  - B ends its own lend while A is parked.
  This is `async-field-await-mut.bc`'s shape, which has its scheduler inside the borrow.
- **What it avoids:**
  - every cross-stop obligation: A3, A4, I5 for lend callbacks, option (b), and `CellFoldT`;
  - the Mut Frame is LIFO (A1, A2) around one run of the handler.
- **What it does not avoid:**
  - root 1 (A3's and A6's configurations are at the start world, not at a stop);
  - root 2 (fact 3).
- **New cost:** `[handle]` at the tree for a typed handler inside a lend (#792), with κ shares
  holding `mut` tokens. `KapSchedT` already carries shares holding resources.
- **It does not give up writable borrows across suspension.** It gives up only suspension past
  the lend's scope.

## 6. Verdict

- **Possible with named exclusions.** No condition is shown necessary, and no refuting program
  of the natural statement was found (fact 4).
- **Under every condition,** the garbage part and pinned codes are needed:
  - root 2 (D4) is now shown to bind `mut` at `forget` (`endT_drop_frees`, `compS_both_imm`);
  - root 1 is shown by `not_cerwpTMFrame` and `antiInnerVal_retypes`.
- **Recommended candidate: A**, Core's fold-and-seal over `twpG` and PinExt. B needs A's garbage
  part anyway (§5), and adds `mut` records.
- **Recommended order:**
  1. C1 first: A1, A2, A5, A6, PinExt and `[handle]` inside a lend, to `taskScoped` under a typed
     scheduler.
  2. Then C2's A3 and A4, to `rootMut`.
  3. C3 only if option (b) fails at A3's cancel case.
- **Size, #791's own share** beyond #789's general ports (estimates, same basis as the
  checklist):

  | Piece | Lines |
  |---|---|
  | interpretation and `SemJT` laws | 1.5–3k |
  | garbage layer through `twp`/`cerwpT` rules | 2–4k |
  | PinExt | 3–8k |
  | A1/A2 | 1.5–3k |
  | A5/A6 | 0.5–1k |
  | `withborF` rule (chain and tree) | 0.5–1k |
  | `taskScoped` instance | 1–2k |

  That is **C1 ≈ 10–22k** plus #792. C2 adds A3/A4 (2–4k), I5 (1–2.5k) and the two `rootMut`
  instances (1.5–2.5k): **≈ 15–31k**.
- **To the top statements themselves** (`Goal791Top`/`Goal791Sched` over every `CDerives` rule),
  #789's 30–76k applies. #791's share is the above.

## 7. Not verified

- **B2 is not refuted.** Building a valid start world holding a `mut` token was not done, so
  `TokenBackT` and `ReleaseMutT` at `twp` are not refuted by configuration. `endT_drop_frees`
  is the step such a configuration would close with. Not derived, and no obstruction verified
  for the instance.
- **The hardest case is not checked against the judgment.** `rootMut` and `taskScoped` were not
  given `CDerives` derivations.
- `RootAt` is unproved.
