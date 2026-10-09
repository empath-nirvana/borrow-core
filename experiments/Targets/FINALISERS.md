# Finalisers with effects, under frame deadness (decisions D1–D4 of 2026-10-08)

The design of the finaliser unit: M1 (the machine), M2 (the typing, SPEC §27), and the plans for
M3–M5. It reads the decided algebra (`research/effects/src/decisions.md`, *The decided algebra*
with its three 2026-10-08 entries, and *Hard stop*) and the user's decisions of 2026-10-08:

- **D1, deadness by frame.** A cancel kills the cancelled region's handler frames. A dead frame
  catches nothing, no raise and no operation, so a finaliser's raises and operations reach the
  nearest *live* instance. The machine never silently drops a finaliser's error. This replaces
  SPEC §19's by-name suppression (`N`, `errNext`'s middle case) and the backend's cancel mask.
  Non-interceptability and first-wins are kept.
- **D2.** Finalisers may perform ordinary operations of live handlers, not only raise. Option A
  (`[then]`'s finaliser at `F 1`) is lifted.
- **D3.** A finaliser's raise or operation of a name with no live instance outside the dying
  region is a type error. `prog` (`cancel-suppressed`) becomes ill-typed and moves to the untyped
  shapes, with its new run recorded.
- **D4.** Algebraicity keeps kept errors' values in the observation. Where `unr` continuations get
  in the way, it is proved at contexts with no `unr` operation, never by observing less.

Design only: no proof, and no change to `Core/`, BoLo, SPEC, the machine or the relation. Branch
`tier1-effects` at `45c2021`. The stash "F4 guard frame" is a rejected approach and is read for
nothing. Notation: `⊥` is the reserved cancel name `0`; `err ∨ e` is `err` when `err ≠ none`, else
`e` (the first error wins); `K†` is `Kont.dead K` (§1.2).

## 0. Outcome

- **The previous design's §0 STOP is resolved by D1.** It found that `[cfin-raise]` drops, by
  name, an error whose site the region re-enters (`P_re`), while `finally`'s law sends it to the
  live outer instance. D1 removes the name list: `P_re`'s error reaches the outer instance (§1.5),
  and `P_re` types (§2.6). The previous `pass` annotation is not needed.
- **No STOP in this design.** One candidate rule would have needed one: a blanket *closure*
  condition (every effect of a region's finalisers must also be recorded for each capturable
  operation a finaliser performs). It is sound but rejects a lawful program, `progNC₁` (§2.7), so it
  would be hard stop 4. The rule chosen records the nested cancels' effects precisely (the cancel
  rows of §2.3) and rejects only what D3 rejects.
- **M1, the machine.** κ's cancel branch tears down the region with its handler frames and cancel
  delimiters removed (`Kont.dead`). The cancel state is the kept error alone (no `N`), the first
  winning. One new rule, `[cfin-cancel]`, gives a cancel that reaches a running finaliser's `cfin`
  its meaning (merge, the earlier error winning), where today the inner `cfin` intercepts it.
  Unique decomposition and determinism extend by one case. Every typed program runs as before
  (same answers, steps, memory and counts). `prog` ends at an unhandled raise of `2` and leaves the
  compiled kernel list. Two compiled shapes, `cancel-reentered` (`P_re`) and `cancel-propagated`
  (`prog` under a live outer `2`), show propagation. The lowering keeps the first error (the mask
  is removed). Core's relation changes only where the cancel state did; `fundamentalC`,
  `adequacyC` and `adequacyD` keep their statements.
- **M2, the typing (SPEC §27).**
  - Each capturable row entry carries a *cancel row*: what cancelling a continuation captured
    there may raise or perform. Each capturable operation in it carries, in turn, its own cancel
    row for a cancel nested inside; `⊤` means unknown.
  - `[then]` records its finaliser's row in the cancel rows of `M`'s capturable entries by `⋈`
    (§2.4). `⋈` adds the finaliser as a leftover of every nested cancel below it, and the errors
    kept below it as pending for its own operations.
  - κ's cancel entry is typed at the handler's outer row extended by the cancel row (`S ⊕ F`), or
    is `⊤`. `[sub]` at the cancel's use carries the D3 check, and `[handle]` gains no premise.
  - Every existing derivation types at the default (empty) cancel rows.
  - `prog` and `e7c` are rejected (D3). `e7b`, `e7d`, `e8b`, `e9c`, `cancelKept`, `P_re`,
    `progOut`, `progFinOp` and `progNC₁` type.
  - The lowering of finalisers that suspend (M2c) is part of M2.
- **M3.**
  - S5's cancel trace is restated into line with D1: first-wins with no name list, and a `pend`
    step for a running finaliser's `cfin` in the region. `CancelsNoCtl` and `CancelsNZ` are then
    not needed: `dead` removes every handler and `ccatch` frame from the cancel run. So
    `noIntercept_J₁` is planned outright.
  - `CfinQuiet` is false once M2 types `e7b`; it is retired. Algebraicity is planned given
    `KeptKapFree`, the fact `AlgSim` reads, and its run-level obligation is stated.
  - "No typed run drops an error" is a run property provable from the machine and `adequacyD`.
- **M4.** E7 (E7c restated as its rejection, D3), E8 and E9 at `J₁`. `FinRaise.lean`'s
  refutations and `I.not_tier1_J₁` go. Tier 1 at `J₁` becomes open, not refuted.
- **M5.** AT08 is rewritten so that only the continuation rule rejects it, as the previous design
  (§7 there) has it. Then the `tier1_J₁_of_ESU` table (§5).

## 1. M1: the machine

### 1.1 What the machine does today, and what D1 changes

Today (`Paper/S3_Dynamics/Definitions.lean`):

    [op]               hnd (n, H) K[perform (n, v)] ↦ h_op (v, κ)
                       κ's cancel branch: ccatch (hnd (n, H) K[raise (⊥, (N, none))]),  N = n :: K.hndNames
    [finalise-cancel]  ubind (N', D) K'[raise (⊥, s)] ↦ cfin s (D ())
    [cfin-raise]       cfin (N, err) K''[raise (m, v)] ↦ raise (⊥, (N, errNext N err m v))
                       errNext: err if err ≠ none; none if m ∈ N; (m, v) otherwise
    [cancel]           ccatch K[raise (⊥, (N, none))] ↦ ()
    [cancel-raise]     ccatch K[raise (⊥, (N, E))] ↦ raise E

Three things are at odds with D1:

1. **Suppression by name.** `errNext`'s middle case drops an error whose name is in `N`. `N`
   holds the reinstalled `n` and every handler of `K`: those above the fired finaliser and those
   below it, which `M` installed around the operation.
2. **The region's handlers are live.** The cancel branch reinstalls `hnd (n, H)` and keeps `K`'s
   handler frames. A finaliser's raise never reaches them, because `cfin` catches it first. A
   finaliser's *operation* does reach them: `perform` passes `cfin` and `ccatch`, and the first
   handler of its name catches it, which may be a dying one. Its clause then runs inside the
   cancelled region. If it answers without resuming, `ccatch` holds a value and has no step
   (`progFinOp`, §1.5).
3. **Nested cancels are intercepted.** Suppose a finaliser's operation is caught outside its
   cancel and that continuation is cancelled. The outer `⊥` raise then meets the inner cancel's
   `cfin`, which catches it as an "error" of name `⊥` (`[cfin-raise]` at `m = ⊥`), and the inner
   `ccatch`, which catches every `⊥`. This is the previous design's scenario NC.

### 1.2 The change

- **`Kont.dead : Kont → Kont`**, the region made dead:
  - it removes every handler frame `hnd (m, …) [·]` (the frames `Kont.HasHnd` reads) and every
    `ccatch [·]`;
  - it keeps every other frame, `ubind` and `cfin` among them.

  It is structural, so it commutes with `Kont.comp` and `Kont.shift`.
- **κ.** `κ = ⟨λy. hnd (n, H) K[y], λ_. ccatch (K†[raise (⊥, none)])⟩`.
  - The resume branch is unchanged.
  - The cancel branch no longer reinstalls `hnd (n, H)` and no longer reads `K.hndNames`.
  - In `kappa`, `kappaC` and `kappaCBody`, the cancel branch is
    `ccatch ((K.shift d 0).dead.plug (raise (cancelVal none)))`, after the cell's `free` at a
    linear or affine operation as today.
- **The cancel state is the kept error alone.** `cancelVal err = opPayload 0 0 (errVal err)`.
  `namesVal`, and the `N` argument of every rule and definition, are removed.
- **First wins.** `errNext err m j w = err ∨ some (opPayload m j w)`.
- **The rules** (only the cancel rules change):

      (μ, ubind (N', D) K[raise (⊥, err)])  ↦ (μ, cfin err (D ()))      K catching nothing of ⊥   [finalise-cancel]
      (μ, cfin err v)                        ↦ (μ, raise (⊥, err))                                [cfin-ret]
      (μ, cfin err K[raise (m, v)])          ↦ (μ, raise (⊥, err ∨ (m, v)))  m ≠ ⊥, K catching nothing of m   [cfin-raise]
      (μ, cfin err K[raise (⊥, err')])       ↦ (μ, raise (⊥, err ∨ err'))    K catching nothing of ⊥   [cfin-cancel]  (new)
      (μ, ccatch K[raise (⊥, none)])         ↦ (μ, ())                       K catching nothing of ⊥   [cancel]
      (μ, ccatch K[raise (⊥, some E)])       ↦ (μ, raise E)                  K catching nothing of ⊥   [cancel-raise]

  - In Lean: `Head.ufinC`, `cfret`, `cancel` and `creraise` take `cancelVal err`. `Head.cferr`
    gains `hm : m ≠ 0`. `Head.cfcancel` is new.
  - `[cfin-cancel]` keeps `err`, the inner (earlier) cancel's error, over `err'`, the passing
    cancel's: first wins, in time (reading 1).
- **Unchanged:** `[ret]`, `[op]` (but for κ), `[unwind]`, `[then]` and `[finalise]`;
  `Kont.HasHnd` and `Kont.Catches`; every non-effect rule; the capture cell (§25).

### 1.3 Why this form

- **Deadness is decided where the region is known.** `[op]` builds κ from `K`. Removing the dead
  frames there makes every cancel rule local: no rule reads a name, and a dead frame cannot catch
  because it is not there.
- **A dead frame and no frame cannot be told apart.**
  - A dead frame catches nothing.
  - Its body never becomes a value. The only `⊥` raise inside the region is the region's own
    cancel, which nothing in the region catches, and `cfin` always yields a `⊥` raise.
  - So removing it needs no primitive, no step for a dead frame at a value, and no change to
    `HasHnd` or `Catches`.
- **`ccatch` frames in `K` are delimiters of cancels in progress.**
  - They occur only when `K` was captured inside a running finaliser, an operation of a finaliser
    caught outside its cancel.
  - They belong to the region being cancelled, so they are dead. Removing them is what lets the
    outer cancel reach its own `ccatch`, the non-interceptability D1 keeps.
- **`cfin` frames in `K` stay.**
  - A `cfin` holds an inner cancel's kept error, which a finaliser raised. D1 forbids dropping
    it, so `[cfin-cancel]` merges it into the passing cancel's state.
  - The inner region's remaining finaliser frames are frames of `K`, so they run under the outer
    cancel: "every finaliser runs, so the teardown completes".
- **Alternatives, and why not:**
  - *Immediate propagation.* A finaliser's raise would leave `cfin` as an ordinary raise and
    unwind the rest of the region. The later finalisers' raises would then supersede it by
    `finally`'s law, so the last error would win, and D1 keeps first-wins.
  - *A dead-handler primitive (`dhnd`).* Equivalent, but it adds a primitive, a `HasHnd` and
    `Catches` case, and an unreachable form with no step.
  - *A depth counter in the cancel payload, to skip inner `ccatch` frames.* Equivalent to removing
    them, with more state.
  - *Deadness by name.* The decided algebra says deadness is a property of frames (`P_re`).
- **Not a runtime block (hard stop 3).** Nothing is made stuck. `[cfin-cancel]` gives a step to a
  configuration that today steps wrongly.

### 1.4 Unique decomposition and determinism (`Core/Steps.lean`, `Core/Demonic.lean`)

- **`dead` is a function**, so `[op]` stays deterministic.
- **`[cfin-raise]` and `[cfin-cancel]` are told apart by the payload's name**: `m ≠ 0` against
  `cancelVal err'`, whose name is `0` (`opPayload_inj`).
- **`head_plug`.** The new redex holds `K.plug (raise …)` at a `cfin` catcher position, which
  `CatcherPos` already lists, so the new case is `cferr`'s.
- **`head_not_opPlug` and `head_nested`.** The `cfin` branch gains the `cfcancel` case, by
  `nested_op` with `payloadName_cancelVal` and `OpFree true 0 K`.
- **`head_det_eff`.**
  - `(cfcancel, cfcancel)`: the same `err` and `err'`.
  - `(cferr, cfcancel)`: the names are equal, against `hm`.
  - `(cfret, cfcancel)`: `plug_raise_ne_val`.
  - `cancelVal_inj` now reads `err` alone.
- **`Prim.Inert` and `Kont.Plain` are unchanged.**

### 1.5 The regression programs under the new machine

`H₁` cancels its `κ`, as `prog`'s `c₁` does. Every operation is `unr`, so there are no cells.

| program | term | old run | new run |
|---|---|---|---|
| `prog` | `hnd 1 (hnd 2 ((perform 1) then x. x unwind raise 2))` | 10 steps to `()` (error suppressed) | 10 steps to `raise (2, (0, ()))`, which no handler catches: a final configuration (`prog_run` restated) |
| `prog₃` | `hnd 3 prog[3/2]` | `inj₂ ()` | `inj₂ ()`, the same steps |
| `cancelKept` | `prog₃` with `H₃`'s answer `inj₁` | `inr ()` | `inr ()` |
| `progRe` (`P_re`) | `hnd 3ₒ (hnd 1 ((f ()) then x. x unwind raise 3))`, `f = λ_. hnd 3ᵢ (perform 1)` | `inl ()`: `3` is in `N` (the inner `3` is below `D`) | `inr ()`: `dead` removed `3ᵢ`, the error is kept and re-raised at `H₁`'s clause, and `3ₒ` catches it |
| `progOut` | `hnd 2ₒ prog` | `inl ()`: `2` is in `N` (the inner `2` is above `D`) | `inr ()` |
| `progFinOp` | `hnd 4ₒ (hnd 1 (hnd 4ᵢ ((perform 1) then x. x unwind perform 4)))`; `H₄ᵢ`'s clause answers `inr ()` without resuming, `H₄ₒ`'s resumes | stuck: the dying `4ᵢ` catches the finaliser's `perform 4`, answers, and `ccatch` holds a value | `inl ()`: the operation passes the removed `4ᵢ` and `ccatch`, `4ₒ` resumes it, the finaliser returns, and the cancel answers `()` |
| `progNC₁` | `progFinOp` with `H₄ₒ`'s clause cancelling its κ | intercepted (old `[cfin-raise]` at `⊥`) | `H₄ₒ`'s answer: κ₄'s region `[cfin none] [ccatch₁] [H₁'s clause context]` is dead, `ccatch₁` is removed, and the `⊥` raise meets `cfin none` (`[cfin-cancel]`) and then `ccatch₄` |

Every run is checked in Lean as `Core/EffCancel.lean` checks `prog_run` today: explicit `Steps`
with `Head` constructors, one theorem each.

### 1.6 SPEC §19 changes

- ***Terms and machine*, the κ bullet.**
  - κ is `⟨λy. hnd (n, H) K[y], λ_. ccatch (K†[raise (⊥, none)])⟩`.
  - `K†` is the region with its handler frames and its `ccatch` frames removed (`Kont.dead`).
  - The `N` bullet is removed.
  - Unique decomposition gains `[cfin-cancel]`, and `head_det_eff` its case.
- ***Cancels*, rewritten.** The rule table of §1.2, then:
  - A finaliser's raise during a cancel is re-raised at the canceller, after every frame of the
    region has finalised, and meets the nearest live instance of its name, as any raise does.
  - No error is dropped because of its name. A name handled only inside the region has no live
    handler at the canceller, and typing rejects such a finaliser (§27). A name the region
    re-enters reaches the live instance outside it (`progRe`, `progOut`).
  - Several failures: the first is kept (policy).
  - A finaliser's operation passes the dead region and `ccatch` and reaches the nearest live
    handler. Its continuation holds the `cfin`, the region's remaining frames and the canceller's
    context. Resumed, the finaliser and then the cancel go on.
  - A cancel of that continuation removes the inner `ccatch` and passes the inner `cfin` by
    `[cfin-cancel]`. The inner region's remaining finalisers run under it.
  - Ordinary unwinding is unchanged.
  - *Why this rule*: §1.3.
- ***Typing*.** Unchanged in M1 (option A). The finaliser paragraph's "a non-abortive operation
  of a finaliser could reach a dying handler of the region" becomes "the machine sends it to the
  nearest live handler (*Cancels*); option A still types a finaliser at `F 1` until §27".
- ***Finalisers that perform operations*.** States the machine's behaviour: raises kept first-wins
  and re-raised at the canceller, operations to live handlers, `[cfin-cancel]`. "Non-abortive
  control operations in a finaliser" is removed from *Open*.
- ***Programs*, *As built*.** `Core/EffCancel.lean`'s six programs, with their runs as in §1.5.
- ***Lowering*.**
  - The cancel paragraph: the resume code takes `inr ()`. The first error a finaliser raises is
    kept and re-raised (`reraise`), and every later one is suppressed. The region's drivers are
    not on the cancel's call path, so its handlers are dead as *Cancels* asks.
  - The mask sentence is removed, and so is the rejection "under a handler site reached from its
    own body, or under a handler named 64 or more".
  - *As built*: the kernel list of §1.11.
- **Status and changelog.**
  - The Status paragraph for Entry 18 gains the change.
  - Changelog **0.44** (2026-10-08): "§19 (decisions D1–D4 of 2026-10-08): deadness by frame.
    κ's cancel branch tears down the region with its handler frames and cancel delimiters removed
    (`Kont.dead`), so a dead frame catches nothing. The cancel state is the kept error alone, the
    first winning (`N` and the by-name suppression removed). A cancel that reaches a running
    finaliser's `cfin` keeps that cancel's error, the earlier winning ([cfin-cancel]). `prog` now
    ends at a raise no handler catches. The lowering keeps the first error (the mask removed). No
    change to the statements of the relation's theorems or to any borrow rule."

### 1.7 The interpreter (`Support/Dynamics/Interpreter.lean`)

- **`catchOp`.**
  - The `ccatch` case matches the new payload `(0, (0, err))`.
  - The `cfin` case matches `cfin (0, (0, err))` and splits on the stop's name: `m = 0` (a
    cancel, payload `(0, (0, err'))`) answers `raise (cancelVal (err ∨ err'))`; otherwise it
    answers `raise (cancelVal (errNext err m j w))`.
  - `[op]` calls `BoLo.kappaAt`, so κ is built dead with no change here.
- **`namesOf` is removed.** `errOf` is kept.
- **Targets' mirror** (`Base/Look.lean`, `Base/LookMem.lean`: `catchOp`, `look`, `look_sound`,
  `runM`) changes the same way and gains the `cfcancel` case.

### 1.8 The backend (D1's half: the mask)

- **`Backend/Clos/Capture.lean`.**
  - `errNext` keeps the first error with no mask test.
  - `cancelArm` loses the mask variable `z` and its copies.
  - The resume code's cancel arm takes `inr ()`.
  - `kapBody` calls `k (inr ())` and `reraise eq`.
  - `masks` and the two rejections are deleted.
  - The module doc's *Cancels* paragraph is rewritten.
- **`Backend/Clos/Syntax.lean`.** `reraise (p : Var)`, with no mask.
- **`Backend/Clos/Unwind.lean`.** A `reraise` raises the keys every `catchAll` catches (`F.rr`),
  unfiltered.
- **Pattern updates** in `Flow.lean`, `Interp.lean`, `Collapse.lean`, `Types.lean` and
  `Backend/Flat/Lower.lean`.
- **Frame deadness is already the backend's behaviour.** A cancel runs from the canceller's call
  of κ. The cancel arm runs only the point's `fin` frames and drops its `catch` frames, so a
  finaliser's raise meets `catchAll`, never a region handler.
- **Counts.**
  - The mask is an `i64` literal that κ passes to the resume code (`0` when no finaliser may raise,
    `anyRaise`), tested by host operations. It costs no allocation, no indirect call and no deep
    copy, and `inr ()` in its place costs none either.
  - The mask test runs only where a finaliser may raise: in no corpus program, and in no kernel
    program but the two cancels.
  - So no count changes. A finaliser that suspends is M2c (§2.9).

### 1.9 Core: the relation at option A, and the lemmas re-proved

The relation changes only where the cancel state does. M1 keeps option A, so the cancel run's
error table is the empty one: no typed finaliser raises or performs past its `cfin`.

- **`Core/EffDefs.lean`.**
  - `errOk T ls err` loses `N` (the kept error is an abortive entry of `T`).
  - `cancelTab T` loses `N`.
  - `cancelOwed ls K := ewpTS ls (K†.plug (raise (cancelVal none))) (cancelTab OpTab.empty)
    (fun _ _ _ => False)`. The `∀ N` quantifier and the arguments `T` and `n` are gone.
  - `contShare`'s cancel part is `cancelOwed ls' K`.
- **`Core/EffWp.lean`.** `cancelTab_abortive` loses `N`.
- **`Core/EffRules.lean`.**
  - `errOk_le`, `cancelTab_le`, `cancelOwed_le` and `opTable_le` are restated without `N`.
  - New `dead` lemmas: `dead_comp`, `dead_hndK` (`(hndK H).comp K` goes to `K.dead`),
    `dead_plain` (a context with no handler frame that catches nothing is its own `dead`),
    `dead_shift`, `hasHnd_dead`, and `catches_dead` (`dead K` catches only at `ubind` and `cfin`).
  - `cancel_frame`: the plain frame survives `dead`.
  - `ewp_frame_plain` loses its `hN : K.hndNames = []` premise (from `dead_plain`). Its callers in
    `EffRules` and `Core/Nu.lean` drop the argument.
  - `ewp_cfin`, `cancel_then` and `ewp_frame_then`: the finaliser is at the empty table, so `cfin`
    ends only by `[cfin-ret]`. The perform case's obligation goes through
    `dead (ubindK ∘ K₁) = ubindK ∘ K₁†`.
  - `kappa_cancel_subst`, `ewp_kappa_cancel`, `kappaCBody_subst` and `ewp_kappaC_cancel`: `dead`
    commutes with shifting and substitution (`dead_shift`, `plug_shift_subst`).
  - `ewp_ccatch` loses the handler frame and the `Tin`/`Tout` map. At the empty error table the
    state is `none`, so `[cancel]` applies.
  - `ewp_handle`.
    - Own operation: κ's cancel through `ewp_ccatch` at `K₁†`.
    - Forwarding: `dead (hndK ∘ K₁) = K₁†`, so the inner obligation *is* the outer one.
      `hmap`/`hmapE` are deleted.
  - `then_compatC` is restated with `D` at the pure row. Its old statement (`D` at
    `F_{Σ^abort} 1`) is false under D1's machine at `prog`'s `[then]`, because it relied on the
    suppression. `thenA_compatC` becomes `then_compatC`, and M2 generalises it (§2.8).
- **`Core/Steps.lean`, `Core/Demonic.lean`.** §1.4.
- **`Core/EffCancel.lean`.** Rewritten with the six programs of §1.5 and their runs.
- **`Core/EffBorrow.lean`, `Core/Fundamental.lean`.** No statement changes. The unwinding forms'
  finalisers are closed at `F 1`, and `fundamentalC`'s `effThen` case still reads `thenA_compatC`.
- **`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`.** Its case lists over `Head` gain
  `cfcancel`. These are proofs, not printed definitions.
- **`scripts/AxiomCheck.lean`.** Names.
- **Statements unchanged:** `fundamentalC`, `adequacyC`, `fundamentalD`, `adequacyD`,
  `adequacyD_obs`, and every compatibility lemma except `then_compatC`.

### 1.10 Targets and the experiments (mechanical, with three items to re-check)

- **Mechanical.** `cancelVal` without `N`, `cancelOf` and `capture`'s cancel branch at `K†`, and
  `Head.cfcancel` cases:
  - `Base/Machine.lean`, `Base/Runs.lean`, `Base/CoreCancel.lean` (`CancelRun`, `cancelOf`),
    `Base/Look.lean`, `Base/LookMem.lean`, `Base/Rows.lean`, `Base/RunProps.lean`;
  - `B/BumpSim.lean` (`head_image`'s new case: no allocation, and renaming commutes), the other
    `B/` files that name the cancel;
  - `Instance/Machine.lean` (`labelOf` reads `[cfin-cancel]` as `finEnd` of the inner error;
    reading 1 of §3.1), `Instance/Core.lean`, `Instance/AlgSim.lean` (`AlgRel.head`'s new case,
    `AlgRelK.dead`), `Instance/CancelRuns.lean`, `Instance/HandlerCell.lean`
    (`CancelCellLaw` at `K†`), `Instance/CellRuns.lean`, `Instance/ContUse.lean`,
    `Instance/E*.lean` (the `runM` runs recompute), `Instance/Theories.lean`,
    `Instance/UnaryLaws.lean`;
  - `I/World.lean`, `I/Interface.lean`, `I/Device.lean`, `I/Restricted/*` (`Device.lean` reads
    `ewp_ccatch`), `I/GhostCoupling.lean`, `I/ContUseJ1.lean`, `Status.lean`, `AxiomCheck.lean`.
- **Re-check 1: `Instance/Checks.lean`, `noIntercept_needs_finRow`.**
  - These are the teeth of S5's `FinRow` premise at `J₄`. Its witness is a finaliser whose
    operation the dying handler catches, and D1 removes exactly that interception.
  - Expected (to be machine-checked when M1 rebuilds Targets): the witness's run now stops at the
    unhandled operation, which is a prefix of a cancel trace, so the statement no longer holds.
  - It is then retired with a note, into line with D1. New teeth for `FinRow` come after M2
    (§3.1).
- **Re-check 2: `I/CancelsNZ.lean`, `kappa_cancel_run` and `hasHnd0_of_knz`.** They read `K` off
  the cancel term `ccatch (hnd H K[…])`, which now holds `K†`. The handler half of `CancelsStd`
  then comes from κ's resume branch `λy. hnd H K[y]`, which still holds `K`. The proof is reworked
  and the statement kept; M3 retires it (§3.1).
- **Re-check 3: the experiments that import Core's effect files.** `GhostEnd` (`Drop.lean` reads
  `cancelOwed … n …` and `N`), `SecondClass`, `Grades`, `LoopBorrow`, `FrameTheorems` and
  `Optics` are each built with `lake build <lib>` before and after. A file that names a changed
  definition is updated, and a result that was about the name list is recorded as such. None of
  them is a default target or a gate step.
- **Statements.** No Targets statement changes in M1. `CancelsNoCtl` stays a hypothesis until M3,
  and S5 at `noFinRaise` never meets a kept error under option A.

### 1.11 Kernel programs: behaviour and counts

| kernel program | answer | counts (`allocs indirect copies`) |
|---|---|---|
| every program in `corpus/kernel-counts.expected` but `cancel-suppressed` | unchanged | unchanged rows |
| `cancel-reraised` (`cancelKept`) | `inr ()`, `live 0` | `0 0 0`, unchanged |
| `cancel-suppressed` (`prog`) | leaves the compiled list: its run ends at a raise no handler catches, so no stage prints a value | row removed |
| `cancel-reentered` (`progRe`), new shape | `inr ()`, `live 0` | measured when added; `0 0 0` expected (no cell at `unr`, and `f` is known) |
| `cancel-propagated` (`progOut`), new shape | `inr ()`, `live 0` | measured when added; `0 0 0` expected |
| `cancel-perform` (`progFinOp`), `cancel-nested` (`progNC₁`) | in Lean and the interpreter in M1; compiled in M2c (§2.9) | rows added in M2c |

- `Backend/Kernel.lean`'s doc lists `prog` among the untyped terms and records its new run.
- The corpus and its goldens are unchanged: drop glue is typed at `F 1`, so no corpus finaliser
  raises.

### 1.12 The hard stop, M1

| check | finding |
|---|---|
| (1) a law | none changed. D1–D4 are the decided algebra, and the rules implement them |
| (2) behaviour or counts | `prog` only, which is exempt (D1/D3). Every typed program takes the same steps: the removed frames were passed in the same single step that drops them. Answers, memory and counts are unchanged |
| (3) runtime block | none. `dead` removes frames that catch nothing, `[cfin-cancel]` gives a step, and the mask, a suppression, is removed |
| (4) rejection | none. The typing is unchanged (option A) |
| (5) weakened target | none. `then_compatC`, an internal lemma, is restated because the relation's cancel state changed. `noIntercept_needs_finRow` is a non-vacuity record whose witness D1 removes |

## 2. M2: the typing (SPEC §27)

### 2.1 What a finaliser's effects meet

A finaliser `D` of `M then x. N unwind D` runs in three settings. Each says where its effects must
find a live handler.

1. **Ordinary unwinding** (`D (); raise p` at the `[then]`'s position). The frames outside are
   live, so `D`'s effects need handlers outside the `[then]`. If `D` performs a capturable `z` and
   `z`'s handler cancels, the region is `D`'s rest, the pending raise (abandoned with the
   continuation: algebraicity, reading 2), and the `[then]`'s context up to `hnd z`. Their
   finalisers are the enclosing `[then]`s.
2. **A cancel of a continuation captured at a capturable `o` inside `M`.** `D` runs under `cfin`
   with the region dead. Its effects need live handlers outside the region, at the canceller.
3. **A cancel nested in a cancel.** In setting 2 `D` performs a capturable `z`, and `z`'s live
   handler cancels `D`'s continuation. The nested region is:
   - `D`'s rest, whose internal finalisers come from `D`'s own typing;
   - the `cfin` of the cancel in progress, whose kept error (*pending*) came from finalisers
     *below* `D` in `o`'s region, fired before it;
   - the region's frames *above* `D` (*leftovers*);
   - the canceller's context up to `hnd z`.

   All of these must find live handlers outside `hnd z`. Deeper nestings repeat the pattern.

The typing below records, for each capturable operation, what its continuation's cancel may do,
nested to every depth.

### 2.2 Why the rule lives in rows (the separation lemma, kept)

- `e7b 1 2 = toResult 2 (timeoutH 1 (bodyF 1 (raise 2)))` and
  `e7c 1 2 = timeoutH 1 (toResult 2 (bodyF 1 (raise 2)))` hold the same `[then]` subterm at a row
  with the same entries.
- D3 rejects `e7c` and accepts `e7b`, so no premise confined to `[then]` can decide.
- The difference is the canceller's row: `2` is live outside `1` in `e7b`, not in `e7c`. That row
  is visible where κ's cancel entry is used.
- So the rule records `D`'s effects in the row entry of the operation that captures, carries them
  outward through function types and `[sub]`, and checks them where the cancel is invoked.
- To build first: `e7c_of_then` (previous design §2.1), any derivation of the `[then]` subterm
  gives one of `e7c`. It holds as stated, since `[sub]` still reorders rows.

### 2.3 Cancel rows

- **Capturable entries.** A row entry `o = ⟨n, i, q, A, B, fin⟩` is *capturable* when it is not
  abortive and `q ≠ lin`, so its κ has a cancel branch. `fin` is read only there.
- **A cancel row** is `⊤` (unknown), or a row whose capturable entries carry cancel rows in turn.
  It is a finite tree.
- **Defaults are `[]`**, and every existing derivation uses them.
- **Order.** `F ≤ ⊤`, and `R ≤ R'` when each entry of `R` is `R'`'s at its key (`n i q A B` equal)
  with its cancel row `≤`, recursively. `[sub]`'s `RowLe` is this order on rows: an entry's cancel
  row may only grow outward.
- **Join.** `F ⊔ F'` is entrywise. `⊤` absorbs, and an entry's cancel rows are joined.
- **`aborts F`** is `F`'s abortive entries, at the top level.
- **`F ⋈ E`**, the combination `[then]` uses, where `F` is what the finalisers below `D` may do and
  `E` is `D`'s row:

      ⊤ ⋈ E = ⊤
      F ⋈ E = { x with fin := x.fin ⋈ E   | x ∈ F capturable }
            ⊔ { x                           | x ∈ F not capturable }
            ⊔ pend (aborts F) E
      pend P E = E with every capturable entry, at every depth, gaining P in its cancel row

  - The first line makes `D` a leftover of every cancel nested below it (setting 3's "above"),
    recursively.
  - `pend` makes the errors kept below `D` pending for every cancel of `D`'s own continuations
    (setting 3's `cfin`), at every depth, because the nested cancels inside `D`'s rest pass the
    same `cfin`.
  - The recursion is on `F`'s depth, so it terminates.
- **`S ⊕ F`**, κ's cancel entry row: `S` joined with `F`.
  - At `F = []` it is `S`, so κ's type is unchanged for every existing derivation.
  - At `F = ⊤`, κ's cancel entry is `⊤`.
- **As built.** `OpSig` and `CTy.eff` gain the field: `eff n i q A B fin C`, with `fin` encoded
  as a `CTy` or a list of entries. `CTy.effOf` passes it, the order and `⋈` are functions on it,
  and `strip` erases it. About 140 pattern sites in `Core/`, `Frontend/Check/` and
  `experiments/Targets/`. Every function over `CTy` passes `fin` unchanged, because operation types
  are closed.

### 2.4 The rules

    Γ = Γ₁, Γ₂    Δ; Γ₁ ⊢ M : F_{S_M} A    Δ; x : A, Γ₂ ⊢ N : F_S B    Δ; x̸, Γ₂ ⊢ D : F_{S_D} 1
    S_M ≤ S    S_D ≤ S    for every capturable o ∈ S_M:  S_M(o).fin ⋈ S_D ≤ S(o).fin
    ─────────────────────────────────────────────────────────────────── [then]  (with §19's hNZ, hUq, hU)
    Δ; Γ ⊢ M then x. N unwind D : F_S B

    §24's [handle], with E's entries carrying their cancel rows, and
    K_i = U((B_i ⊸ F_S R) & C_i) (aff),   !U((B_i ⊸ F_S R) & C_i) (unr),   U((B_i ⊸ F_S R) & ⊤) (lin)
    C_i = F_{S ⊕ F_i} 1   (F_i the i-th operation's cancel row),   ⊤ when F_i = ⊤

- **`S_D ≤ S`** is setting 1: `D`'s effects, and its operations' cancel rows, are the `[then]`'s.
- **`S_M(o).fin ⋈ S_D ≤ S(o).fin`** is settings 2 and 3, at every capturable operation `M` may
  hand a continuation of.
- **`[handle]` gains no premise.**
  - The D3 check is `[sub]` at the cancel's use: `S ⊕ F_i ≤ S_c`, where `S_c` is the canceller's
    row. It holds exactly when every entry of `F_i` is live at the canceller (in `S_c`) and every
    nested cancel row is recorded at the canceller's entries.
  - If κ's cancel is never invoked, nothing is checked. A handler that always resumes may hold a
    region whose finaliser raises a name handled inside it.
- **Every other rule passes rows unchanged**, `[perform]` and `[raise]` at any cancel rows.
  - Forwarding needs nothing, because a forwarded entry is the outer row's.
  - `[let]`'s side condition is unchanged.
  - The borrow callbacks' rows are `Row.Unwind`, which has no capturable entry.

### 2.5 Soundness under the new machine (the semantic plan)

1. **Entries.** `OpEnt` gains `fin`, the semantic cancel row at `δ`: `⊤` or a table whose
   non-abortive entries carry cancel rows. `Row.tab` maps it, `OpTab.Le` grows it, and
   `cC_effOf_strip` is not needed, since `effTab` reads `fin`.
2. **The continuation's cancel share** (`contShare`). The cancel part is
   `cancelOK en.fin ls' (K†.plug (raise (cancelVal none)))`, or nothing at `⊤`.
3. **`cancelOK F`**, for `F` a row, by recursion on `F`'s depth. It is `ewpTS` at `cancelTab F`,
   which stops:
   - at the cancel's end `K₀[raise (⊥, err)]`, with `K₀` catching nothing of `⊥`, `err` none or an
     abortive entry of `F` at its argument relation, and nothing owned left;
   - or at a non-abortive operation `z` of `F` under a context `K'` free of `z`, owing resume (the
     fixed point's continuation) and cancel: `cancelOK F(z).fin (K'†[raise (⊥, none)])`.

   At M1's instance `F = []` this is M1's `cancelOwed`.
4. **`ewp_ccatch`.**
   - From `cancelOK F` of the run, `ccatch` of it is in the relation at `F_{S ⊕ F} 1` with answer
     `()`. At the end, `[cancel]` gives `()` and `[cancel-raise]` gives a raise of an abortive
     entry of `F`.
   - An operation passes `ccatch`, which catches only `⊥`. The main level's obligation is at
     `(S ⊕ F)(z).fin ⊇ F(z).fin`, and `dead` removes the `ccatch` from the nested region, so the
     nested run is the same term.
5. **The `[then]` frame in a cancel** (`ewp_frame_then`'s cancel case, by induction on `F_M`'s
   depth). From `M`'s obligation at `F_M` and `D`'s relation at `S_D`, the `[then]`'s obligation
   holds at `F_M ⋈ S_D`:
   - the run reaches the `ubind` with `err ∈ aborts F_M`, and `[finalise-cancel]` gives
     `cfin err (D ())`;
   - a raise of `D` gives `err ∨ (m, w)` by `[cfin-raise]`, and `m ∈ S_D`;
   - `D` returning gives `[cfin-ret]`;
   - an operation `z` of `D` is a stop at `z ∈ S_D`. Its cancel runs `D`'s own cancel obligation
     at `S_D(z).fin`, then `[cfin-cancel]` merges `err ∈ aborts F_M`. This is `pend`;
   - a stop below `D`, at `x ∈ F_M`, now passes the `ubind` in its own nested cancel, which fires
     `D`. This is `x.fin ⋈ S_D`, by the induction.
6. **`[cfin-cancel]`'s lemma.** `cfin err` around a nested cancel run at `F'` is a cancel run at
   any `F ⊇ F' ⊔ {err}`.
7. **`ewp_handle`.**
   - Own operation: κ's cancel through `ewp_ccatch`. `KapRel`'s cancel part is at
     `opTable (Tout ⊕ en.fin)`, or nothing at `⊤`.
   - Forwarding: the same entry, and `dead (hndK ∘ K) = K†`.
8. **`[sub]`.** `cancelOK` is monotone in `F`, and `opTable` in the order.
9. **Ordinary unwinding** (`ewp_frame_then`'s raise case). `D` is at `S_D ≤ S`, its operations'
   obligations at `S(z).fin ⊇ S_D(z).fin`. Supersession is as today.

No new semantics: every case follows the machine of §1. Nothing changes `wpTS`, `wpG`, `ewpTS`'s
definition, BoLo's world or a borrow lemma.

### 2.6 What it accepts

Cancel rows are written `o⟨F⟩`.

| program | derivation | κ's cancel used at | run |
|---|---|---|---|
| `e7a lw` | `D = ret ()`, `S_D = []` | `S` | `inr ()`, `[fire, finEnd none]` |
| `e7b lw lo` | `lw⟨{lo}⟩` | the `timeout` clause, at `{lo}` (`toResult lo` outside) | `inr ()`, `finTr lo` |
| `e7d` | inner `lw⟨{la}⟩`, outer `lw⟨{la, lb}⟩` (`aborts` adds nothing, since `lb` is not capturable) | `{la, lb}` | `inr ()`, `finTr la ++ finTr lb` (first wins) |
| `e8a`, `e8b` | ordinary unwinding: `S_D ≤ S` | — | as stated |
| `e9c ly lo` | `ly⟨{lo}⟩` | inside the stored closure, applied under `toResult lo` | `inr ()`, `finTr lo` |
| `cancelKept` | `1⟨{3}⟩`, `[handle] 3` outside | `H₁`'s clause at `{3}` | `inr ()` |
| `progRe` (`P_re`) | `f ()` at `{1⟨[]⟩}`, `[sub]` to `{1⟨[]⟩, 3}`, `[then]` gives `1⟨{3}⟩` | `H₁`'s clause at `{3}` (`3ₒ`) | `inr ()` |
| `progOut` | `1⟨{2}⟩`; the inner `2`'s outer row lacks `2` (`hnS`) | `H₁`'s clause at `{2}` (`2ₒ`) | `inr ()` |
| `progFinOp` | `1⟨{4⟨[]⟩}⟩` | `H₁`'s clause at `{4⟨…⟩}`; `H₄ₒ` resumes | `inl ()` |
| `progNC₁` | `1⟨{4⟨[]⟩}⟩`; `4`'s entry gets nothing more (no `[then]` encloses a `perform 4`) | `H₁`'s, then `H₄ₒ`'s at `[] ⊕ []` | `H₄ₒ`'s answer |

- **Every lawful finaliser types.** Take each capturable entry's cancel row to be the least
  solution of the `[then]` premises. A cancel's `[sub]` then holds exactly when what that cancel
  may run has a live instance at its canceller (D3), at every nested level.
- **The approximations are those of any row typing.**
  - A cancel row is a union over the program's `[then]`s, not over what one run holds.
  - A region whose nested cancels would need unboundedly many outer instances (recursion through a
    finaliser's capturable operation) gets `⊤` at the cycle, and its continuation cannot be
    cancelled (reading 3).

### 2.7 What it rejects

- **`prog`** (D3).
  - `1⟨{2}⟩` comes from the `[then]` inside `hnd 2`.
  - `H₁`'s clause invokes κ's cancel at `F_{S ⊕ {2}} 1`, and `[sub]` to the clause's row `S`
    needs `2 ∈ S`.
  - At `F 1`, or any row without `2`, there is no derivation.
  - `not_der_prog`, by inversion through `[handle] 1`, the clause tuple, and `[sub]`'s order:
    cancel rows only grow, and `[then]` is the only rule at a `ubind` term (`der_then`).
- **`e7c lw li`** (D3). `lw⟨{li}⟩`, and `timeoutH`'s clause row has no `li`.
- **Not rejected: `resumer lw (toResult li (bodyF lw (raise li)))`.** κ's cancel is never
  invoked, so nothing is checked. A `[handle]`-time check would reject it (hard stop 4).
- **Not rejected: `progNC₁`.** The blanket closure rule considered first (`F_o ≤ F(z).fin` for every
  capturable `z ∈ F_o`) counts the performing finaliser among its own leftovers, so it rejects
  `progNC₁`. `⋈` tells the two apart:
  - a recursive or doubly nested region, whose leftovers perform `z` again, gets `z ∈ z.fin`
    through `M`'s row (the recursive call carries `S_D`), and is rejected as it must be (D3);
  - the single finaliser gets `z⟨[]⟩`.
- **Checked when M2 lands:** `progNCrec`, two `[then]`s whose finalisers both `perform z`, under
  `z`'s cancelling handler, is rejected, and its untyped run ends at an unhandled operation. This is
  the soundness witness for the leftover clause.

### 2.8 `CDerives`, `fundamentalC`, the checker, Targets

- **`CDerives`.**
  - `effThen` takes `S_M`, `S_D` and the premises of §2.4.
  - `effHandleV`'s effect list carries cancel rows, and `kTy`/`clausesTy` read them.
  - `effSub`'s `RowLe` is §2.3's order.
  - Theorems keep the old shapes for existing uses: `CDerives.effThenA` (option A's rule, `D` at
    `F 1`, `S_M = S`) and `effHandleV₀`/`effHandle` (default cancel rows). The checker's `rEffThen`
    and `rEffHandle` call these, and its `CRow` gains the field at `[]`.
- **`fundamentalC`.**
  - `effThen`: `then_compatC`, from §2.5's cases 5 and 9.
  - `effHandleV`: `handleV_compatC`, case 7.
  - `effSub`: `sub_compatC`, case 8.
  - `fundamentalC`, `adequacyC`, `adequacyD`, `adequacyD_obs` and every other compatibility lemma
    keep their statements.
- **Targets.**
  - `CDerivesAt` and its inversions (`TiedKernel.lean`, `Inversion.lean`, `I/Rejects.lean`) gain
    the premises. The tie compares stripped entries.
  - The open types (`OVTy`, `OCTy`, `effF`, `ORow`) carry cancel rows, and `J₁`'s reading maps
    them.
  - `RowAt` ignores them.

### 2.9 The lowering of finalisers that suspend (M2c)

Under option A a finaliser never suspends, and the backend cannot lower one that does. D2 needs it
in two places.

- **The cancel arm.**
  - When a finaliser's code may suspend (the closure flow's `skeys`), point `j`'s cancel arm is
    generated as a code of its own: cancel the callee, run `d₁`, run `d₂`, …. Its error so far is
    a variable live at its points, and `machine` lowers it, so each finaliser call is a resumption
    point.
  - κ's cancel entry (`kapBody`) calls it and so may suspend. The caller's call of κ's cancel is
    then a call point, as for any code that may suspend.
- **Cancelling such a state** is `[cfin-cancel]`. Its cancel arm cancels the suspended finaliser's
  `k` first, merges the state's error with the one that cancel returns (the state's first), then
  runs the remaining finalisers.
- **Ordinary unwinding.** `fin dd b` with `dd` able to suspend is rewritten in `Capture`, before
  `machine`, to `case catchAll b {inl v ⇒ v | inr p ⇒ dd (inr ()); raise p}`. The finaliser's
  call is then a call point. A raise of `dd` supersedes `p`, as `finally`'s law says.
- **Kernel shapes.** `cancel-perform` (`progFinOp`) and `cancel-nested` (`progNC₁`), each at
  every stage with `live 0`. Counts are measured and recorded. No existing count may change,
  because programs whose finalisers do not suspend take today's path.
- **Fallback, if the construction does not fit this unit.** The two shapes stay Lean and
  interpreter runs, and `Capture` rejects a finaliser that may suspend with a message. This
  departs from "every feature lands with its lowering", and the step reports it to the user. It is
  not a hard-stop item.

### 2.10 SPEC edits for M2

- **§27, Entry 26: finalisers with effects.**
  - *Motivation*: D1–D4.
  - *Typing*: §2.3–§2.4.
  - *Semantics*: §2.5.
  - *Theorems*: the statements unchanged.
  - *Programs*: §2.6–§2.7.
  - *Lowering*: §2.9.
  - *Baseline*: no BoLo or borrow rule change.
  - *Open*: reading 3's `⊤` approximation, S5 at D2's endings (§3.1), and `KeptKapFree` (§3.2).
- **§19.** *Typing*'s `[then]` line and κ's types point to §27. "A finaliser lets no operation
  escape it" is rewritten. *Finalisers that perform operations* points to §27.
- **§24.** `[then]` at option A is marked superseded by §27. It stays a derived rule
  (`effThenA`).
- **Status, and changelog 0.45.**

### 2.11 The hard stop, M2

| check | finding |
|---|---|
| (1) a law | none: §27 implements D2 and D3 |
| (2) behaviour or counts | none. Terms, machine and counts are unchanged, and M2c adds shapes. The checker emits default cancel rows |
| (3) runtime block | none: a typing rule |
| (4) rejection | `prog` and `e7c` (D3, recorded). Reading 3's `⊤` is the approximation of a finite type, not a designed restriction, and it is put to the user as a reading. The closure rule that would have been a stop is not adopted (§2.7) |
| (5) weakened target | none |

## 3. M3: `CancelsNoCtl`, algebraicity, and no dropped error

### 3.1 S5's cancel trace under D1; `CancelsNoCtl` and `CancelsNZ` retired

**Why the hypotheses go.**
- `CancelsNoCtl` (no `ccatch`, no `cfin` in a cancelled continuation's context) and `CancelsNZ`
  (no handler named `0` there) were what `noIntercept_of_core` needed: a `ccatch`, a `cfin` or a
  handler of `0` in `K` would have caught the cancel.
- The cancel run is now `ccatch (K†[raise (⊥, none)])`, and `K†` holds no handler and no
  `ccatch`. A `cfin` in `K†` is a running finaliser whose cancel the region holds, and it is
  passed by `[cfin-cancel]`.
- Neither hypothesis is needed once the trace has a step for `cfin`. Whether `CancelsNoCtl` holds at
  `J₁` after M2 is not claimed here. Nested cancels make it doubtful, but no witness is built.

**The restatement (A-level, into line with D1; not a weakening).**
- `keep` loses its name argument: `keep err r = err ∨ r`. `Region` is no longer read.
- A region's *actions*, innermost first, replace its finalisers. A finaliser frame is `fire D`,
  and a running finaliser's `cfin` is `pend e` (`A.EffectSystem.acts`; at instances with no
  nested cancels, `acts = map fire fins`).
- `CancelTrace` consumes actions. Its new constructor `pend` takes a `finEnd e` step and keeps
  `e ∨ err`, the earlier error winning. `labelOf` reads `[cfin-cancel]` as `finEnd` of the inner
  error.
- `NoIntercept`'s premise (`FinRow FR` of the fired finalisers) and S5's parameter `noFinRaise`
  are unchanged. S5 at D2's endings is reading 4.

**The proof plan.**
- `cancel_pfx` and `fin_pfx` (`Instance/CancelRuns.lean`) are re-run at `K†`, with a `pend` case
  from `[cfin-cancel]`.
- `noIntercept_of_core` loses `CancelsStd`.
- So `I.noIntercept_J₁` and `I.cancellation_J₁` are PROVED outright at every admissible context,
  and the same holds at `tier1Open`.
- `CancelsStd`, `CancelsNoCtl`, `CancelsNZ` and `cancelsNZ_J₁` are kept as records or deleted
  (the user's choice; deletion is the default, since they are not read).
- New teeth for `FinRow`, after M2: `e7b` is typed at `J₁`, and its finaliser raises `lo`. Its run
  from the cancel's start shows `finEnd (some lo)`, which no trace at `noFinRaise` admits.

### 3.2 Algebraicity (D4)

- **`CfinQuiet` is false once M2 types `e7b`.** Its run reaches `[cfin-raise]`. `not_cfinQuiet_J₁`
  is to be machine-checked by `runM`, and `CfinQuiet` is retired.
- **What `AlgSim` reads.**
  - `AlgGood.cfin` asks that a cancel-mode finaliser's kept error hold no λ, so that the two sides'
    `finEnd` events are equal terms.
  - What it needs is weaker, `KeptKapFree`: kept and pending errors hold no captured
    continuation. Only a continuation can hold the law's frames, so `AlgRel`-related kept values
    without one are equal.
  - `AlgRel.head` gains `[cfin-cancel]`, and `AlgGood.cfin` is restated as `KeptKapFree`.
  - `I.algLaw_J₁_of` takes `KeptKapFree` in place of `CfinQuiet`. The observation is unchanged:
    kept values are observed, as D4 asks.
- **`KeptKapFree` at admissible contexts.**
  - Its source is typing. Admissible contexts have no resuming `unr` operation (`AdmEff`'s `NU`),
    so every κ is linear or affine and owns a cell. A raise's argument drops (`VTy.Drop`: data,
    borrows, `!`), and a `!` captures only persistent slots, so a raised value holds no κ.
  - The obligation is to carry that from the terms a derivation types to the values a run reaches.
    Core's relation proves it inside `ewp_cfin` (the argument relation at a `Drop` type), but no
    lemma exposes a fact of the relation at a configuration of a run (`wpG` sees a run's segments
    whole).
  - Candidate routes:
    - the restriction technique of `platData_of_start` (`lamFree_io_of_coreClosed`), transposed
      from the platform's protocol to the cancel's error table;
    - the guard proxy (previous design §5.3).
  - Outcome of M3: algebraicity PROVED at `J₁` at every admissible context given `KeptKapFree`,
    and `KeptKapFree` either proved by one of these routes or stated as the exact remaining
    obligation, with its non-vacuity at `e7b`. It is never replaced by observing less.

### 3.3 "No typed run drops an error"

`NoDroppedError J`, for every typed closed program `P` and every run from it:

1. **Kept first.** At every `[cfin-raise]` step the next state is `err ∨ (m, v)`, and at every
   `[cfin-cancel]` step it is `err ∨ err'`. An error leaves a cancel's state only by first-wins.
   This is a fact of the machine (`Head.cferr`, `Head.cfcancel`).
2. **Re-raised.** A cancel whose state is `some E` ends by `[cancel-raise]`, raising `E` at the
   canceller (`Head.creraise`).
3. **Caught.** No run of a typed closed program at `F 1` ends at a raise. This is `adequacyD`:
   every run reaches `()` and is never stuck. An unhandled raise would be a final non-value.

The only other ways an error leaves a configuration are the algebra's: a handler catches it
(`[unwind]`), a finaliser's raise supersedes it in ordinary unwinding (`finally`'s law), or a
cancel abandons a continuation that holds a pending ordinary raise (reading 2). So the property
is PROVED outright, from the machine and `adequacyD`. Its A-level form is a predicate on runs, and
the step lemmas are by `cases` on `Head`. The previous design's `CfinRegionQuiet` (open behind
configuration typing) is not needed: D1's machine has no suppressing rule left to exclude.

## 4. M4: E7, E8, E9 at `J₁`; `EProps`

- **E7 restated** (into line with D3).
  - `CancelPolicy` keeps E7a, E7b and E7d, with their typings and runs as stated.
  - E7c's two conjuncts become `∀ C, ¬ S.der [] (S.e7c lw la) C`. Docstring: "E7c: a finaliser
    that raises a label the cancelled region handles is rejected".
  - E8 and E9 are unchanged.
- **Derivations at `J₁`.** In the tied kernel with §27 (§2.6), and at A-level as `noColouring_J₁`
  does (`labelsAt`, `der_*_J₁`).
- **Runs**, by `runM` and `rfl` under M1's machine, as `I.accepts_J₁` does:
  - E7b: `inr ()`, `finTr lo`;
  - E7d: `inr ()`, `finTr la ++ finTr lb`;
  - E8b: `inl (inr ())`, `[fire (raise lb)]`;
  - E9c: `inr ()`, `finTr lo`.
- **E7c's rejection.** One inversion: `[handle] lw`'s κ cancel is used in `timeoutH`'s clause at a
  row without `li`, while `lw⟨…li…⟩`. It reuses `FinRaise.lean`'s `derAt_hnd`, `derAt_then` and
  `derAt_let_arg`, re-aimed.
- **Status.**
  - E7, E8 and E9 are PROVED at every admissible context.
  - `FinRaise.lean`'s refutations (`not_der_e7b_J₁` …, `not_eProps_J₁`) are of option A, and false
    under §27. They are replaced, and so is `I.not_tier1_J₁`, whose proof reads them.
  - `EProps` at `J₁` is not refuted.
  - E2a–c, E3, and E10's `retry` and loop are not derived; no obstruction has been verified.
  - E5 and E2d are proved where no `exn` signature, or no operation, is `unr`.
  - `status_eProps_J₁` and `status_tier1_J₁` are rewritten.

## 5. M5: AT08 rejected by the continuation rule; what tier 1 then needs

- **AT08** (previous design §7, kept).
  - κ is read out of its cell with `swap`, the copy is put back, κ is read again with `free`, and
    both are resumed.
  - `k₁` is live on both sides of a split, so its slot must be persistent, and `kTy` at `lin` or
    `aff` is not.
  - `not_der_at08` follows `not_der_at05`/`not_der_at13`: the clause tuple, `der_lam`, `der_bind`
    through `alloc` (`kview`), `der_app` at `swap`, `der_seq`, then `splitP_both` and `kview_not`.
  - §27 leaves `kTy`'s resume entry and qualifiers alone, so the rejection does not depend on M2.
    It reads `kTy` at default cancel rows.
- **`I.tier1_J₁_of_ESU`'s premises after the unit:**

| premise | after M1–M5 |
|---|---|
| `hE`: A's (E) properties at every admissible `Ξ` | E7 (restated), E8, E9 PROVED. Open: E2a–c and E10's `retry` (a `!U C` forced); E3 and E10's loop (`unfold`'s value); E5 and E2d at contexts with an `unr` `exn` or `unr` operation |
| `hS4`: S4 | PROVED (re-checked after M1 and M2) |
| `hC`: S5 (`noFinRaise`) | PROVED outright (§3.1) |
| `hU`: S6 | OPEN: `OnlyOwnerFrees`, `NoDanglingUse` (not this unit) |
| `Accepts`, `Rejects` | PROVED; AT08 restated |

So tier 1 at `J₁` is **open, not refuted**: (E)'s four remaining parts and S6's two ownership
properties. Beside done: `AlgLaw` given `KeptKapFree` (§3.2), and `NoDroppedError` proved (§3.3).

## 6. The hard stop, step by step

| step | (1) law | (2) programs | (3) runtime block | (4) rejects lawful | (5) weakens target |
|---|---|---|---|---|---|
| M1a machine, Core, interpreter, SPEC §19 | no: implements D1 | `prog` only (exempt); same steps, memory and answers elsewhere | no | no | no (`then_compatC`: internal, restated with the relation) |
| M1b backend mask, kernel list | no | `cancel-suppressed` row removed (exempt); counts unchanged | removes a suppression | no | no |
| M1c Targets, experiments | no | no | no | no | `noIntercept_needs_finRow`: a record whose witness D1 removes (re-checked) |
| M2a typing, relation, SPEC §27 | no | no: default cancel rows | no | `prog`, `e7c`: D3. `⊤`: reading 3 | no |
| M2b derivations, `not_der_prog` | no | no | no | D3 | no |
| M2c lowering of suspending finalisers | no | new shapes only | no | no | no |
| M3 S5 trace, hypotheses retired | no | no | no | no | into line (D1); hypotheses dropped, not the target |
| M3 algebraicity | no | no | no | no | D4: kept values observed; obligation stated |
| M3 `NoDroppedError` | no | no | no | no | no |
| M4 E7–E9 | no | no | no | E7c: D3 | into line (D3) |
| M5 AT08, status | no | no | no | AT08 was already rejected | into line with AT08's intent |

## 7. Order of work and size

1. **M1a** (medium): `Paper/S3_Dynamics/Definitions.lean`, `Core/Steps.lean`, `Core/Demonic.lean`,
   `Core/EffDefs.lean`, `Core/EffWp.lean`, `Core/EffRules.lean`, `Core/EffCancel.lean`,
   `Core/Nu.lean`, `Paper/LiteralReadings/…`, the interpreter, and SPEC §19 with changelog 0.44.
   Check: `lake build`, targeted.
2. **M1b** (small): the backend's mask, `Backend/Kernel.lean`, `corpus/kernel-counts.expected`.
   Check: `scripts/compile-kernel.sh`.
3. **M1c** (wide, mechanical): Targets and the experiments (§1.10). Check:
   `lake build Targets` (AxiomCheck, Audit).
4. **M2a** (large): cancel rows on `OpSig`/`CTy.eff`, the order, `⋈`, the rules, the semantic
   `fin` and `cancelOK`, §2.5's lemmas, `fundamentalC`'s cases, the checker's defaults, SPEC §27.
5. **M2b** (medium): derivations of `cancelKept`, `progRe`, `progOut`, `progFinOp`, `progNC₁`;
   `not_der_prog`; `progNCrec`'s rejection; Targets' `CDerivesAt` and its inversions.
6. **M2c** (medium–large): §2.9.
7. **M3** (medium): §3.1–§3.3.
8. **M4** (medium): §4.
9. **M5** (medium): §5. Then TIER1-PLAN's outcome, the register rows and `Status.lean`.
10. **`make gate` once**, as the separate stage.

Each step is committed on `tier1-effects` with the session trailer.

## Readings for the user to confirm

1. **`[cfin-cancel]`'s order.** When a cancel passes a running finaliser's `cfin`, the inner
   cancel's kept error, the earlier one, wins. First-wins is read in time.
2. **A pending ordinary raise in a cancelled continuation is abandoned with it.** A finaliser
   running during ordinary unwinding (`D (); raise p`) performs an operation, and its handler
   cancels the continuation. The continuation's code, `raise p` included, does not run
   (algebraicity). Only a cancel's kept error, which is machine state, is never dropped.
3. **`⊤` cancel rows.** A continuation whose cancel would need unboundedly many outer handler
   instances (recursion through a finaliser's capturable operation) cannot be cancelled. This is
   the approximation of a finite type, not a designed restriction.
4. **S5's parameter stays `noFinRaise`.** Finalisers that raise to live handlers or perform are
   outside its premise in this unit. Restating S5 at D2's endings needs a trace step for a
   finaliser's operation answered outside the region, and that step is not built here.
5. **`KeptKapFree` replaces `CfinQuiet`** as algebraicity's hypothesis, and its run-level
   obligation stays open if neither route closes (§3.2).
6. **`prog` is not compiled.** Its run ends at a raise no handler catches. `cancel-propagated`
   (`prog` under a live outer `2`) is compiled in its place.
7. **The M2c fallback** (§2.9), if it is needed, departs from "every feature lands with its
   lowering". It is the user's call.

## Unspent hypotheses, unused results, untranscribed in the run-up

- **Unspent.**
  - `then_compatC`'s old semantic slack (a finaliser at the whole abortive row) is replaced, not
    spent. §27 types exactly what §2.5 proves.
  - κ's cancel entry at `S ⊕ F` over-approximates by `S`, which keeps `kTy` unchanged at
    `F = []`.
  - `AdmEff`'s `ClosedLife` and `Rich` are read by nothing here.
- **Unused uniqueness results.** `det_ourInst` and `rstep_det` are read by no step of M1–M2. M3's
  traces read `rstep_det` and `innerCatch_unique`, as F3's did.
- **Untranscribed in the run-up.**
  - The separation lemma (`e7c_of_then`).
  - The terms `progOut`, `progFinOp`, `progNC₁` and `progNCrec`.
  - The A-level `acts` and `pend` (§3.1).
  - S5's trace for a finaliser's operation answered outside the region (reading 4).
  - The run-level carry for `KeptKapFree` (§3.2).
  - The backend's cancel code (§2.9).
