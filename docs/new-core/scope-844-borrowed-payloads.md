# #844: borrowed payloads to handlers (a borrow lent to the handler for the duration of a stop)

Kernel target: a scope for lifting `Row.Suspend`'s closed-payload condition, so that an
operation's payload or answer may carry a borrow at the suspending lend's lifetime. Measurement
only: the merged relation (`erwpK`/`KW`, `goal791N : HandlerLawN → Goal791N`, #839) is unchanged.
The spike is `Core/Chain/Spike844N.lean`. Every result in it is proved with every hypothesis
discharged, and its axioms are `[propext, Classical.choice, Quot.sound]`.

Read at `main` e52174e1 (worktree `borrow-core-scope844`, branch `scope-844`).

## 0. Summary

- **There are two cases, and they cost very different amounts.**
  - **Tier 1, outer borrows.** The payload or answer holds a borrow of a lend that encloses the
    suspending lend, and the handler sits between the two lends. This case needs no change to the
    relation's stop clause. It needs the constants to be polymorphic in lifetimes, so that their
    bound is no longer `⊤`, plus a generalisation of three laws from `∅` to `Δ`.
    **Additive, about 4 units.** As built (SPEC §62, 1.39–1.40), Tier 1 generalises payloads
    only; answers stay at a closed bound (`Row.AnsC`), for the reason in §1.3's Tier 1 paragraph.
  - **Tier 2, the callback's own borrow passed to a handler outside the lend.** This is #844's
    actual ask, and it is the hard form of both grounding programs. Three layers block it today:
    1. **Typing.** The row is shared between the callback's type and the lender's, and `'x` is
       not bound at the lender (`lender_mut_payload_empty`).
    2. **The Mut Frame's premise `pa`.** It fails at the callback's own borrow
       (`lendOKCR_pa_fails`).
    3. **The relation.** `↭` is asked at every stop, and it refuses a lender's segment that
       starts owning `ℓ` and stops with a borrow of `ℓ` in its payload. This holds whatever
       premise replaces `pa` (`erwpK_refuses_borrowOut`, `not_crossTaskMLendK`).

    The third layer is the stop clause of the relation. Changing it is #821's stage 1–2 mask and
    loan, which is built on `erwpX` on branch `cross-821` and not on `erwpK`/`KW`.
    **A rebuild of the stop clause, plus a kernel type change** (`OpSig` gains a lifetime binder,
    and `kTy`'s cancel component takes the borrow back). About 8 units. Two of them are design
    units that need the user's sign-off.
- **Verdict.** Tier 1 is easy and additive. Tier 2 is a rebuild. On the relation side it is a
  strict subset of #821 stage 2, which handles a loan returned at a later join rather than at this
  stop's resumption. It should be built on #821's stop clause, not beside it.

## 1. Why the payload and answer are closed today

### 1.1 The clauses and where they are read

`Row.Suspend S 'x @bnd` (`Core/TreeGoal791.lean:73`) asks, of every operation `o`:
- `o.q ≠ unr`;
- `o.n ≠ 0`;
- `¬ VFree x o.A` and `¬ VFree x o.B`;
- `VOutlives ∅ bnd o.A` and `VOutlives ∅ bnd o.B`;
- that the cancel row meets `CTy.SuspendC` (`:49`), recursively.

`Const791.OK` (`:138`) fixes `LifeCtx.empty.Defines bnd`, so `bnd` is `⊤` at every `δ`
(`interp_top_of_defines_empty`, `:179`). At `⊤`, `VOutlives ∅ ⊤ T` excludes every `Imm`/`Mut`,
every `U C` and `Unk`, and every box at a variable lifetime. So **no borrow of any lifetime** may
be a payload or an answer, outer borrows included.

Every reader goes through `layer_suspend` (`Core/Chain/Cancel791N.lean:230`):

| Clause | Read by | What it gives |
|---|---|---|
| `¬VFree x A`, `¬VFree x B` | `tabNK_foldTwin` (`Core/Chain/TabK835N.lean:266`, `:277`); `vN_lend_eq` (`Core/Chain/ReindexK835N.lean:109`); `tabNK_lendOKCR` (`TabK835N.lean:250`, `:256`) | the callback's entry, read at `δ['x ↦ α]`, equals the lender's twin entry read at `δ` (`en'.PA = en.PA`, `en'.PB = en.PB`) |
| `VOutlives ∅ bnd A` | `tabNK_lendOKCR.pa` (`TabK835N.lean:250–254`, through `ValRelOK.inStratum`); `vN_add_eq` (`ReindexK835N.lean:74`) | the payload is in `Res_α`; the payload reads the same at the lend's world and the lender's |
| `VOutlives ∅ bnd B` | `tabNK_lendOKCR.pb` (`:255–259`); `tabNK_lend_comap` (`ReindexK835N.lean:178`, `:190`); `consistentX_of_outlivesN` (`:100`) | the answer is in `Res_↓α`; it moves between worlds; it is consistent with every view, because it lies in `Res_⊤` |
| the cancel-row clause | `tabRK_canK` (`TabK835N.lean:288`), `tabNK_lend_comap`'s recursion, `TabKW835N`/`FrameListKW835N`/`SliceKW835N` | the same facts at every layer of a cancel run under the lend |

The same reads appear in the anti-frame's and the list frame's tables
(`Core/Chain/TabKW835N.lean:169`, `:364–370`, `:485–491`; `FrameListKW835N.lean:86–92`;
`SliceKW835N.lean:70`, `:123`).

### 1.2 The steps that consume them

The Mut Frame across Kripke stops is `erwpK_M_frameGen` (`Core/Chain/SI/MFrameK.lean:194`). It
reads `OpTabK.LendOKCR` (`:148`) in three places:

- **`pa` at a stop** (`:270`). The payload `ρa` is in `Res_α`, so the lent cell
  `ℓ ↦ mut(α, …)` is not in it (`:271–275`, the `lt_irrefl` case). The cell is therefore in the
  continuation's share `ρk`, where the fold turns it back into `own` for the lender (`extF_fold`,
  `foldTwin_owed`). **This is the step a borrowed payload breaks.**
- **`pb` at a resume** (`:303–304`). The answer `σB` is in `Res_↓α`, so the re-entered borrowed
  resource meets the frame's `houtb`.
- **The return** (`:252`) is 6.65's end. It reads no payload.

`answer_not_inStratum` (`Core/Chain/ConfigsKW835N.lean:692`) is why the answer clause exists: a
`U(F 1)` value can hold a short `mut` cell as garbage, so it lies outside every stratum. No
configuration on `main` shows why the payload is closed. The argument is the `pa` step above, and
the spike now backs it in Lean (§1.3).

### 1.3 What breaks without the clauses (the spike)

`Core/Chain/Spike844N.lean`. Each result is a configuration with every hypothesis discharged.

1. **`lender_mut_payload_empty`** (`:63`) is a typing fact. At the lender's `δ`, `'x` is unbound,
   and `vN (Mut 'x A) δ Θ n v ρ` is `False`. The constants use one row `Σ` both in the callback
   type `∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)` and in their result `F_Σ(…)`. So a `Σ` that names
   `'x` gives the lender an entry with no payload values. The twin equality `en'.PA = en.PA` of
   `tabNK_foldTwin` cannot hold, and the outer type is not well scoped. Relaxing `¬VFree x` inside
   `Row.Suspend` alone therefore does nothing: the typing needs a binder (§2.1).
2. **`lend_mut_payload_not_inStratum`, `lendOKCR_pa_fails`** (`:72`, `:93`) concern the frame's
   premise. At the lend's world `Θ + (ℓ, α)`, the callback's own borrow is a `Mut 'x 1` value
   (`lend_mutL`), and its resource is not in `Res_α`. So `LendOKCR.pa` fails at any entry whose
   payload admits it.
3. **`CrossStop.erwpK_refuses_borrowOut`, `CrossStop.not_crossTaskMLendK`** concern the
   relation. They port `cross-821`'s `Core/Chain/CrossStopN.lean` (bbf8f16a) to `erwpK`, the
   relation `goal791N` reads.
   - `erwpK`'s segments are `rwpG`'s (`erwpK_eq`), and `rwpG` asks `ρ ↭ π` at every end, a stop
     included (`EndOKG`, `Core/Chain/SI/RwpG.lean`).
   - So a segment whose start holds `ℓ` only as `own` cannot stop holding a borrow of `ℓ` in its
     payload, at any world index (`erwpK_refuses_borrowOut`).
   - `CrossTaskMLendK` is `erwpK_M_frame`'s statement at the typed world `KW`, the view
     `Θ.view c` and the posts `KW.PostK`, with `LendOKCR.pa` dropped and every other premise
     kept. It is refuted at a table whose payload is the borrow itself.

So for Tier 2, writing a new frame lemma is not enough. The lender's segment, seen from outside,
really does stop with the borrow in its payload, because the handler receives it, and `↭` refuses
that stop. The stop clause has to change.

For Tier 1 none of the three fires:
- The payload's borrows are of enclosing lends, so they are in `Res_α`, and `pa` holds.
- The inner lender's segment started holding them, so `↭` holds (copies and `mut` cells are
  unchanged across the segment).
- `'x` is not named.

**The answer's view is the exception (T1.3).** The comap from the lender's view `c` to the lend's
view `setLife c ℓ α` needs the answer to hold no `mut` cell at `ℓ` (`NoMutAt ℓ`,
`consistentX_setLife_iff`). `pb`'s `Res_↓α` does not give it: `not_noMutAt_inStratum_down` is a
resource in `Res_↓α` with a `mut` cell at `ℓ`. At a closed answer bound it follows from the type
(`noMutAt_of_outlivesN`). At a non-closed one it is carried as `AnsNoMut` and not derived: a
`LocTy` may hold keys at `ℓ` at several lifetimes, so the type alone does not exclude a `mut`
value at `ℓ`; ownership of `ℓ` (the share, or validity of the composite) would have to supply it.
Not derived; obstruction not verified. So the built Tier 1 keeps answers closed (`Row.AnsC`) and
generalises payloads.

## 2. What "lend to the handler for the duration of the stop" needs (Tier 2)

### 2.1 Typing

- **The operation's lifetime has to be bound in its signature.**
  - `OpSig` (`Core/Types.lean:154`) has no lifetime binder, and a row is fixed per type.
  - Option (a) in the brief, "payloads at lifetimes `≥ @bnd`", is Tier 1. It does not cover the
    callback's own borrow.
  - Option (b), "at the callback's `'x`", needs `o : ∀'r. A['r] ↠ B['r]`. The binder is
    instantiated at `[perform]` with the callback's `'x`, and it is rigid in the handler's clause.
  - Then `Σ` names no free `'x`, and the lender's entry reads the payload at the lend's world under
    an existential lifetime (§2.2).
  - This changes the kernel types: `OpSig` and `CTy.eff` each gain a field. The counts are
    `scope-835-qualifier.md` R2's (309 `.eff` patterns on the branch).
- **What the handler may do with a `Mut 'r A` payload.**
  - Rigid, `'r` is unrelated to every lifetime in the clause's context. So `mutSub` cannot make a
    `Mut 'r A` from another borrow, and the payload is the clause's only `Mut 'r A`.
  - `forget` (`releaseMut`) still drops it. If the answer type has no `Mut 'r A`, a clause can
    resume `κ` without returning the cell. The relation cannot follow that: the lender's frame
    looks for its cell in the borrowed run's resource or in that run's own garbage (6.65's return,
    `MFrameK.lean:248–256`), and a cell the clause drops is garbage of the clause's segment, framed
    outside `κ`'s.
  - So a borrow-carrying operation must carry the borrow back in its answer (`B['r] ⊇ Mut 'r A`),
    or the relation must hand the clause's garbage to the resumed segment (Core's global `ρ⁺`;
    candidate A in `TreeGoal791.lean` §6). R1.
- **Cancellation.** `kTy`'s cancel component is `cancelTy S F` (`Core/EffRules.lean:1191`,
  `:1197`), a computation with no argument. A handler that holds the borrow cannot pass it back
  when it cancels `κ`. At a borrow-carrying operation, the cancel component becomes
  `Mut 'r A ⊸ cancelTy S F`: the borrow goes back, then `κ`'s cleanup runs (`K†`, the lend's
  finaliser), and that cleanup may perform effects, as it does today.
- **`imm` payloads.** An `Imm 'r A` copy may be dropped by the handler: `imm` cells are copies,
  and the Imm Frame's end does not need them back. So the return obligation is `mut` only, which
  is what the issue states.
- **Escape.** A clause can close over the payload in a thunk `U C` and store it in its state
  (`U` carries no lifetime). For a parking handler this is the intended use: the IO layer holds
  the buffer until completion. It is safe because the lender is inside `κ`, and `κ` is linear
  (`q ≠ unr`). The borrow can come back only through `κ`'s resume or cancel component, which must
  receive it. `effLet`'s `hW` (`S.Cancels → Γ₂.OwnFree`) already stops a clause context that holds
  a `U` from being abandoned at an abort.

### 2.2 The relation

- **The stop clause.** While the borrow is out, the lender's segment must stop with the cell in
  its payload, and `↭` must accept that.
  - #821 stage 2 (`cross-821:docs/new-core/scope-821-loans.md` §2) does exactly this: "a `mut`
    cell in a payload is accepted exactly at `xm` locations", and the lender is masked at `ℓ`
    while the loan is out.
  - That needs #821 stage 1 (the mask as an index of the one relation, `erwpX`) and stage 1.5
    (the access guard G).
  - Both are on `erwpX`, not on `erwpK`/`KW`.
- **Which side holds the claim while the task is parked.** The handler's segment holds the cell,
  in its resources or its state. `κ`'s share holds nothing at `ℓ`. This is the reverse of today's
  fold, where `κ`'s share holds `ℓ` as `own`.
- **The lender's entry.** For a borrow-carrying operation it differs from its callback twin:
  - the payload is read at the lend's world, `∃ α F. vN A['r↦α] (x.lend ℓ α F)`;
  - the answer is the typed answer, holding the cell back at `ℓ`;
  - the cancel obligation receives the cell.
- **The frame.** `erwpK_M_frameGen` gets a third stop case, a loan out: no fold, and the payload
  passes through. At the resume, the frame is re-entered with the cell taken from the answer
  (`BM = ρbB ● ℓ ↦ mut(α, …)`, as at `:303`, the cell's source changed). `pb` keeps `Res_↓α`: a
  cell at `α` is in `Res_↓α` (`CellU.inStratum_mutOf` asks `α ⊐ ↓α`), so `pb` already admits the
  returned cell.
- **The answer's view.** `consistentX_of_outlivesN` reads `Res_⊤`. A returned `mut` cell at `α` is
  consistent with the callback's view `setLife c ℓ α` and not with the lender's. The callback
  twin's `ConsistentX y.c` has to be read at the lend's view, not moved by the comap.

### 2.3 The handler side

- **Proved handlers (tail, last).** `erwp_handle_tail`/`erwp_handle_last` (`HandleTKW835N`,
  `Core/Chain/HandleLKW835N.lean:110`) through `erwpK_handle_leI`
  (`Core/Chain/HandleK835N.lean:614`) give the clause the payload at `vN`.
  - At a borrow-carrying operation the payload is read at the stop's lend world, so the clause runs
    at a world that has the key `(ℓ, α)` (§2.4).
  - The answering function returns the cell in the answer, and then `κ` is resumed in place.
  - For the last handler, the work's exit cancels `κ` with the cell (§2.1).
  - Both are restatements at the new entry. The proofs' shape is unchanged.
- **`HandlerLawN`** (`Core/Chain/HandlerLawN.lean`).
  - Its three fields are stated over `clausesTy`, which changes with the binder.
  - What it asserts grows: a κ-keeping handler (a scheduler, a stored generator) that also holds
    the borrow is under the assertion.
  - Read against `assert-boundary.md` §2.2: while the borrow is held, the handler's state holds a
    cell at `α`, so `ExtR` at that state protects `(ℓ, α)`. In the E10 mismatch, by contrast, `κ`'s
    share holds nothing at `α`. It is possible that a borrowed payload sits on the easier side of
    E10. I have not derived this.

### 2.4 The per-lend world

The KW world is per run, and the fold forgets the lend (`assert-boundary.md` §2.2). A handler that
holds the borrow must read `(ℓ, α)`: `mutL` asks `Θ ℓ α = some (famL α P Θ)`.

- **It is not a new edge in the lifetime tree.**
  - The floor the stop chooses (`f ≤ α`, `KW.Owed`) already puts the handler's later lends below
    `α`.
  - What is new is that the handler's world carries a key at `α` that the handler did not open.
  - Adding `(ℓ, α)` to a world that holds a key at `γ < α`, with a cell at `γ` in the resource, is
    not an `ExtR` move: `ExtR` keeps `above γ`, and `α ∈ above γ` (`Core/Chain/SI/LocTy.lean:303`,
    §2.2 of `chain-interpretation.md`).
  - So the key has to be carried with the payload from the lender's side. The lender's entry
    reads the payload at `x.lend ℓ α F`, and the handler's run continues at that world. This is
    what the frame's re-entry already does at `y.lend ℓ α F` under `FoldInv α`.
  - Whether the handler's continuation from that world meets `KW.Owed` at the floor it was
    resumed at: I have not derived this, and I have not verified that any obstruction is real.
- **It is a loan, in #821's sense:**
  - the lender is masked at `ℓ`;
  - the cell travels in a payload;
  - the cell comes back in an answer (#821's `PBv` "each `mut ℓ β P̂` entry's cell") or through
    the cancel path.

  #844 needs no token count, no handle and no registry. The loan comes back at this `κ`'s resume
  or cancel, not at a join.

## 3. What carries over

| Piece | Tier 1 | Tier 2 |
|---|---|---|
| lend frames (`erwpK_M_frameGen`, CR/CRG, anti-frame, list, field) | unchanged | new stop case (loan out) in the generic frame; every variant re-instantiated |
| `LendOKCR` | unchanged (`pa`, `pb` hold) | `pa` split: payloads in `Res_α` or holding the lent cell |
| `KW`, `KW.Owed`, `ExtP`, `FoldInv` | unchanged | unchanged as definitions; a new world step for the handler holding the key |
| `↭` at a stop (`UpdVN`, `rwpG`) | unchanged | changed: the lender masked at a loaned location (#821 stage 1/2) |
| tables (`tabNK`, `tabRK`, `tabGK`, `tabListK`), `tabNK_foldTwin`, `tabRK_canK`, `tabNK_lend_comap` | `∅ → Δ` in their side conditions | new entry shape for borrow-carrying operations; twins differ at them |
| `vN_add_eq`, `vN_lend_eq`, `vN_inStratum_bnd` | generalised from `∅` to `Δ` with `δ ⊨ Δ` | as Tier 1, plus the payload at the lend's world |
| `consistentX_of_outlivesN` | a corollary of `consistentX_setLife_iff` at `NoMutAt ℓ`; `NoMutAt` from a closed answer bound (`Row.AnsC`); non-closed answers open (§1.3) | replaced: the answer is read at the lend's view |
| fold results (`extF_fold`, `foldTwin_owed`, `kw_owed_fold`) | unchanged | unchanged for the share; unused at a loan stop |
| `erwpK_handle_leI` | unchanged | unchanged as a lemma; its clause premise reads the new entry |
| tail/last handler proofs | unchanged | restated at the binder and the cancel component |
| `HandlerLawN` | unchanged | restated; scope grows |

Tier 1 is additive. Tier 2 rebuilds the stop clause and touches every frame and table statement,
though not their proof architecture.

## 4. Spike (question 4)

- **Statement.** `RowSuspendB S x bnd substL` (`Spike844N.lean:49`) is `Row.Suspend` with the
  payload and answer allowed to name `'x`. The rest outlives `@bnd` once `'x` is read away.
  `rowSuspendB_of_suspend` shows that today's row meets it.
- **Compat lemma.** I did not attempt `withbor2S` with `read(m)` as its payload: three earlier
  steps already fail, and each is in Lean (§1.3). In order:
  - the lender's row cannot carry the payload (typing);
  - `pa` fails (the frame's premise);
  - `↭` refuses the lender's stop (the relation).

  The first obstruction is the typing one, `lender_mut_payload_empty`. The deepest is the
  relational one, `not_crossTaskMLendK`, at `erwpK` and `KW` (§1.3).

## 5. Relation to #821 and #783

- **#821 (cross-task loans).**
  - On the relation side, #844 Tier 2 is a strict subset of #821 stage 2. It is a `mut` cell (or
    an `imm` copy) in a payload, accepted by `↭` at a masked lender, and returned in an answer.
  - #844 drops #821's tokens, handles, registry and `TokPost`, because the loan comes back at the
    same `κ`.
  - #821 would reuse the loan-out frame case and the answer that returns the cell.
  - #821 stage 2 also keeps "must-resume for a task holding … a `mut` authority, with loans out"
    (`scope-821-loans.md` §7). If #844 inherits that, a task whose borrow is held by the IO layer
    could not be cancelled (R2).
  - #821's scope does not design the typing (its headlines are pool-level programs). The binder of
    §2.1 would be shared.
- **#783 (borrow handoff, the streaming parser).**
  - Program 1's reader hands the parser a borrow of the chunk in an answer. That is the mirror
    case: a borrow from a lend of the handler's, chosen by the handler. In types it is `∃'r` in the
    answer, against #844's `∀'r` in the payload.
  - It is not a subset. It shares the binder and the answer-at-a-lend's-view reading.
  - Program 4 and the yielded views of the chunk are #844 Tier 2 when the handler is outside the
    parser's lend, and Tier 1 or today's rules otherwise (§6).

## 6. Grounding

- **`let n = read(sock, &mut buf).await` inside a task**, with IO through the built-in scheduler
  and an IO handler.
  - **Today it does not type.** The `&mut buf` lend's callback performs `read` with payload
    `Mut 'x Buf`, so `Row.Suspend`'s `¬VFree x o.A` fails.
  - This is the case whether the handler is the scheduler (parks `κ`) or a blocking IO handler that
    answers in place: both sit outside the task's lend.
  - **What types today:** owned-buffer passing, `let (buf, n) = read(sock, buf).await`, with
    payload and answer `Ref Buf ⊗ …`, closed data, if the task owns `buf`. A `buf` that the task
    itself borrowed from its caller cannot be passed this way.
  - Tier 1 does not help: the scheduler is outside the lend. **Tier 2 is required.**
- **A parser yielding `&str` slices of a borrowed input to an in-program handler.**
  - **Handler inside the input's lend** (`&input` lent around the `for`): **types today**.
    - The yield is handled inside the callback, so no lend's `Row.Suspend` sees it.
    - Rows at `Δ` may name the callback's `'x`: `effHandleT` (`Core/Fundamental.lean:531`) places
      no clause on `E`'s payloads.
    - `parse : ∀'y. Imm 'y Str ⊸ F_{yield : Imm 'y Str ↠ 1} R`, instantiated at `'x`.
    - The surface must lend outside the handler, not as the argument inside it.
  - **The parser's own suspending lend between yield and handler** (a scratch-buffer lend, a cursor
    reborrow), yielding slices of the outer input: **Tier 1**. The payload is `Imm 'y Str` with
    `'y` enclosing the inner lend. `scope-835-qualifier.md` §8.3's "a payload borrowed from data
    outliving the lend's bound may be yielded" holds once the bound is not closed. With
    `Const791.OK` at the empty context, the bound is `⊤` and nothing borrowed passes.
  - **Slices of the parser's own lend, or the handler outside the input's lend:** **Tier 2**.
- **Completion IO cancelled mid-read.**
  - **Today, with owned buffers,** the scheduler holds the `Ref Buf` in its pending table. To
    cancel the task it cancels the host operation and waits for that cancellation to complete,
    which is effectful cleanup on the handler's side. Then it frees or returns the buffer and
    cancels `κ`. `Ref` is linear, so a scheduler that drops it does not type.
  - **Under Tier 2, if the handler gives the borrow back before cancelling `κ`, the borrow is
    returned safely.** Because the cancel component takes the borrow (§2.1), the scheduler must
    hold it to cancel `κ`. While the read is pending, the borrow sits behind the host's
    completion, so the extern contract must make "pending read" a linear token at `'r` that yields
    the `Mut 'r Buf` only on completion or on completed cancellation (trusted at the extern
    boundary). Then `κ`'s cancel run executes the lend's finaliser with the cell back. Cleanup in
    `κ` may perform effects, as today.
  - The unsafe ordering is to release the borrow, or `forget` it, and cancel `κ` while the host
    still holds the pointer. Rigid `'r`, the answer and cancel components that take the borrow,
    and a linear pending token together rule that ordering out at the type level. Without them,
    the lowering would free the buffer under a live host write. That is the risk R1 names.

## 7. Verdict and unit plan

**Tier 1: easy, additive, about 4 units.**

| Unit | Content | Done-when |
|---|---|---|
| T1.1 | `Const791` polymorphic in lifetimes: `Const791.OK` at the constant's own context `Δc`, type `!∀'y⃗. ty`, `Δc.Defines bnd` | `Const791.OK` inhabited at a `bnd` with a variable |
| T1.2 | `vN_inStratum_bnd`, `vN_add_eq`, `vN_lend_eq`, `tabNK_lendOKCR`, `tabNK_lend_comap` at `VOutlives Δc bnd`, `δ ⊨ Δc` | the five `*S_compat` restated, `∅` instances as corollaries |
| T1.3 | the answer's view: `consistentX` across `setLife c ℓ α` for a resource with no exclusive cell at `ℓ` | replaces `consistentX_of_outlivesN` at a non-closed bound |
| T1.4 | instance: an outer `imm` lend's slice yielded across an inner suspending lend to a handler between them | a closed program, resumed and cancelled, at `goal791N` |

**Tier 2: a rebuild, about 8 units, two of them design.**

| Unit | Content |
|---|---|
| T2.0 (design, sign-off) | the binder `∀'r. A ↠ B` on `OpSig`/`CTy.eff`; the cancel component `B_back ⊸ cancelTy`; the return rule for `mut` (R1); the pending-IO token at the extern boundary |
| T2.1 (design, sign-off) | the stop clause: port #821 stage 1/1.5/2's mask and loan-out `↭` to `erwpK`, or rebase `KW` on `erwpX`. Start from `not_crossTaskMLendK` |
| T2.2 | `erwpK_M_frameGen` with the loan-out stop case; the CR/CRG/anti/field/list variants re-instantiated |
| T2.3 | the world step: the handler's run at the lend's world while holding the key; resume at a world keeping `(ℓ, α)` with its family |
| T2.4 | tables: the borrow-carrying entry in `tabNK`/`tabRK`/`tabGK`/`tabListK`, `foldTwin`, `canK`, `comap` |
| T2.5 | handlers: `effHandleT`/`effHandleL` at the binder; `HandlerLawN` restated |
| T2.6 | `withbor2S` with `read(m)` in its payload, resumed and cancelled (the cancel with handler-side effectful cleanup before `cancel κ`), then `w3`, `wF`, `wl`, `sm` |
| T2.7 | the grounding programs at `goal791N` |

**The hardest case** is a `mut` borrow held by a κ-parking scheduler across other tasks' runs, and
then the task is cancelled mid-read. It goes in T2.6's done-when and stays there.

Recommended order: Tier 1 now, if wanted, since it is independent. Tier 2 after #821 stage 1–2
lands (or is ported to `erwpK`), on its stop clause. Building a second loan-out stop clause beside
#821's would duplicate it.

## 8. Risks

- **R1. `forget` of a `mut` payload.** With `forget`, a clause can drop the borrow and still resume
  `κ` if the answer type has no `Mut 'r`. The relation then loses the token (§2.1). There are two
  ways out:
  - a typing rule that the answer returns the borrow (decidable on the signature, but a new rule);
  - garbage handed to the resumed segment (Core's global `ρ⁺`, a relation change).

  I have not derived which one the relation needs. I have not built a configuration showing that
  the dropped-token case fails at `erwpK`, so I have not verified that this obstruction is real.
- **R2. #821's must-resume restriction.** It is kept for a lender with `mut` loans out. If it
  carries over, cancelling a task whose buffer the IO layer holds is excluded. The completion-IO
  case needs that cancel, so T2.1 must not inherit the restriction unchanged.
- **R3. A kernel type change** (`OpSig`, `CTy.eff`, `kTy`) under the one-typing-judgment rule and
  #798's freeze. The size is that of `scope-835-qualifier.md` R2.
- **R4. `HandlerLawN` grows** to cover borrow-holding κ-keeping handlers. A possible synergy with
  E10 (§2.3) is not derived.
- **R5. The world step (§2.4)** is not derived. If the handler's world cannot carry the key under
  `KW.Owed`, T2.3 becomes the "global world" option of `assert-boundary.md` §2.4, which that
  document ranks as not cheap.

## 9. Bookkeeping

- **Unspent hypotheses.** None in the spike.
- **Unused functionality results.** `compS_both_imm` (`TreeGoal791.lean:779`) is relevant to R1
  (the token cannot be merged into a lender's piece) and is not used.
- **Not built on `main`.**
  - #821's mask and loan (`cross-821`, stage 1–2).
  - A configuration for R1's dropped token.
- **Spike results.** These are the full names; §1.3 and §4 use the short ones. The first four are
  in `BoCa.Fig16.LogRel.Core.Chain.SI.Spike844N`, the last two in its `CrossStop` namespace:
  - `RowSuspendB`
  - `rowSuspendB_of_suspend`
  - `lender_mut_payload_empty`
  - `lend_mut_payload_not_inStratum`
  - `lendOKCR_pa_fails`
  - `erwpK_refuses_borrowOut`
  - `not_crossTaskMLendK`

  Each has axioms within `[propext, Classical.choice, Quot.sound]`. `rowSuspendB_of_suspend` uses
  `propext` only.
