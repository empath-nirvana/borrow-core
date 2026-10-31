# #750 unit A — the cancel-by-resume kernel rules

Issue #750, plan items 1 and 2 (comment 6528120064). The rules are rebuilt on `main` from the spike
`spike-cancel-resume` @1294661b, which predates #746 steps 2–3 (`Qual.aff` is now `Qual.cancel`) and #743 B1
(`PinLaw` as the schemas `lendFrame` and `loopFrame`). Nothing is merged from the spike branch.

Kernel target: on `main`, each rule below as a proved rule or as a named schema of `PinLaw`.

## 1. The rules

### 1.1 The cancellable marker (replaces the shape test `OpSig.awaitB`)

The spike decided "cancellable" by shape: operation `0`, `lin`, answering `1 ⊕ 1`, at a name other than
`Div`'s. That shape is also `Div`'s `tick` (`tickB`), and it is also any user operation `1 ↠^lin 1 ⊕ 1`
(a yes/no question), which the shape test would force into `await` form. A real marker is a datum of the
operation's signature.

- `OpSig` gains a field `rc : Bool := false`, meaning the operation is cancelled by resuming it.
- `CTy.eff` gains the same datum, `CTy.eff n i q A B fin rc C`. It has to live in the type: a judgment's
  type is a `CTy`, so a marker absent from `CTy` could be dropped by `[sub]`, and then `[perform]` could
  perform the operation plainly. `CTy.rowOf` and `CTy.effOf` carry it, so `rowOf_effOf` still holds.
- `OpSig.Sig` compares `rc`. `[sub]` therefore neither adds the marker nor drops it.
- **Neither the relation nor the machine reads `rc`.** `OpSig.ent` (the `OpEnt` of an operation table)
  has no marker, and `effTab`, `divAt` and the step relation ignore it. The marker is a typing discipline
  on the performer only. That is why it is a `Bool` beside `q`, and not a fourth `Qual`: `Qual` is read
  by the machine (`qualsVal`, `kappaCell`) and by every effect compatibility lemma.
- The handler rules (`effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL`) take the body's row as
  `Row.ofEff n E 0 fs cs ++ S`. `cs : Nat → Bool` gives each declared operation's marker, the same way
  `fs` gives each one's cancel row; its default is `fun _ => false`. Their compatibility lemmas are
  unchanged, and the body's relation is moved across the marker by `semC_effOf_rc`. That lemma says the
  relation at `F_Σ A` depends on `Σ` only through `Row.tab` and `Row.divB`, and neither of those reads `rc`.
- The marker test is `OpSig.Cancellable o : Prop := o.rc = true ∧ o.q = .lin ∧ o.B = .sum .unit .unit`.
  Its decision is `OpSig.cancellableB`, with `OpSig.cancellableB_iff`.

### 1.2 `[await-c]`: `CDerives.effAwait`, proved (`await_compatC`)

    Γ dead   Σ(n, 0) = a   a.Cancellable   a.A = 1   Σ(n, 1) = c   c abortive   c.A = 1
    ─────────────────────────────────────────────────────────────────────────────────── [await-c]
    Γ ⊢ await_n ≜ perform_n (0, ()) to r. case r {inl u. return u | inr u. raise_n (1, u)} : F_Σ 1

- `[perform]` gains `hac : o.rc = false`, so a marked operation is performed only as `await_n`.
- **The cancel target is marked too.** `c` carries `rc = true` (`OpSig.CancelTarget c : Prop := c.rc = true ∧
  c.abort = true ∧ c.A = .unit`), and `[raise]` gains `hrc : o.rc = false`. So `cancelled` is raised only by
  `[await-c]`, on the answer `inr ()`, and never spontaneously. The marker reads uniformly: an operation with
  `rc` is part of a cancel-by-resume pair, and only `[await-c]` performs or raises it. `[await-c]` asks for
  `c.CancelTarget`.
- A cancel is `(force κ).1 (inr ())`, which is a resume. No machine step is added.
- `await_compatC` composes `perform_compatC`, `sumE_compatC`, `raise_compatC` and `let_compatC`, and
  `fundamentalC` keeps its statement with no hypothesis.
- The same rule is added to `CDerivesAt` (with `RowAt`, which does not tie `rc`), to `CDerivesP` (which
  is generated) and to `TDerivesAt`/`TDerivesP`/`TExpr` (also generated).

### 1.3 The cancel row of a marked operation is read by typing

`OpSig.finRead o := capB o.q o.B || (o.rc && !o.abort)`. The marked `cancelled` is abortive and has no
continuation, so its cancel row is not read. `FinLe`, `OpSig.LeF` and `[then]`'s `hfin` read the cancel row at
`finRead` instead of `capB`, so `[then]` records its finaliser's row in a marked operation's cancel row. The
cancel unwinds through that finaliser, as a raise of `c`. `then_compatC` still takes `capB`, and the
callers pass `OpSig.finRead_of_capB`. The relation still reads `fin` only at `capB` (`OpSig.ent`).

### 1.4 `Row.ResumeOC`, `[lend-R]`'s premise (PinStop's premise)

    Row.ResumeOC Σ 'x ≜ ∀ o ∈ Σ,
        (Row.ResumeO's conjuncts at o)
      ∨ (o.Cancellable ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ (∀ Δ a, VOutlives Δ a o.A) ∧ NoThunkT o.A)
      ∨ (o.CancelTarget ∧ o.i = 1 ∧ o.q = .cancel ∧ o.n ≠ 0 ∧ ∃ a, Row.find Σ o.n 0 = some a ∧ a.Cancellable)
    ∧ Row.divB Σ = false

- The conjunct `Row.divB Σ = false` is explicit. `divAt` ignores `rc`, so a marked `tick` at
  `(divEff, 0)` would otherwise pass the second disjunct. `Row.ResumeO` excludes `tick` only through
  `B = 1`.
- The third disjunct admits exactly `[await-c]`'s pair: a marked abortive operation at index `1` whose
  name's operation `0`, found through `Row.find`, is `Cancellable`. Since `[raise]` refuses a marked
  operation, the only raise of it inside the lend is `[await-c]`'s, on a cancel.
- `Row.ResumeO.toC`: every row R1 admitted, it still admits. `ResumeO` already implies `divB = false`,
  because every entry answers `1` and `tick` answers `1 ⊕ 1`.
- `CDerivesP.lendR`, `PinStop` and `LendFrame` take `Row.ResumeOC` where they took `Row.ResumeO`.
  `LendFrame` is the schema that `PinStop` is derived from (`PinLaw.stop`), so widening `PinStop` widens
  `LendFrame`'s asserted domain by the same amount. **This strengthens an existing assertion, so it is a
  trusted-base change.** It is authorised only by the kernel target's line "`Row.ResumeOC` as PinStop's
  premise". It is raised explicitly on #750 and recorded in SPEC §29's trusted base, with exactly the
  domain it admits: a lend held across a marked `await` and across `[await-c]`'s raise of `cancelled` on
  a cancel. No field is added for it.
- Semantically, the relation ignores `rc`. So the widened domain is OQ-1 option (a)'s belief
  (`docs/async-capabilities.md` §8): an abort, at an operation handled outside the lend, after a
  suspension inside the lend. The evidence is the evidence already cited for OQ-1(a). The LIFO frame
  lemmas (`wpTS_M_frameU`) with GhostEnd's `Drop` are proved; that they compose across the suspension
  is not checked. It is restricted syntactically
  to `[await-c]`'s raise of the marked `cancelled`. SPEC §29's trusted base says this, and
  `docs/async-capabilities.md` §8 OQ-1, §3.4 item 3 and row `n4` are updated to say that OQ-1(a) is now
  taken for the cancel path only. SPEC §29's "none abortive" is amended in the same way.
- No other abortive operation is admitted, so OQ-1 stays closed except for `cancelled`.
- The checker: `Row.resumeOCB` with `Row.resumeOCB_sound`. It is sound only, not `_iff`, because
  `outlivesAllB` is sound only, exactly as for `Row.resumeOB` today.

### 1.5 `CDerivesP.effThenDiv` and `PinLaw.fin : PinFin`

`effThenDiv` is `effThen` without `hSD : Row.divB SD = false`, so the finaliser's row may hold `Div`. It
adds `hcap : ∀ o ∈ SM, capB o.q o.B = false`: the body has no capturable operation, so no cancel run
(`κ.2`, which is a least fixed point) reaches the finaliser. A cancel at a marked operation does reach it,
on the ordinary unwind of the `cancelled` raise. It lives in `CDerivesP` and not in `CDerives`, and
decision 69 ("finalisers are total") still holds for `CDerives.effThen`.

`PinFin` is `effThenDiv`'s compatibility lemma, stated as a B1 schema: the rule's premises, plus `M`, `N`
and `D` as `CDerivesP` derivations together with their relations, imply the relation at `F_Σ B`.

- `pinFin_divFree` (proved): when `Row.divB SD = false` the conclusion is `then_compatC`. When `PinFin` is
  asserted, it carries the premise `Row.divB SD = true`, so the asserted content is exactly what
  `pinFin_divFree` leaves unproved. `effThenDiv`'s case in `fundamentalC_pin` splits on `Row.divB SD`.
- **Proof first.** The case where `Σ_D` holds `Div` (and so `Σ` holds it too, at `cwp`) needs
  `cwp_then`, with a raise through the frame running `D` at `cwp (Row.tab SD)` across segments. The
  current `seq_raise_run` runs `D` within a single `ewpTS` segment. The plan:
  - a coinduction whose candidate is `cwp_then`'s candidate together with the configurations "inside
    the frame's finaliser run, raise pending";
  - each tick of `D` owes its continuation to `owe`, and the pending raise is a stop of `Σ`.

  Exit point: the named intermediate lemma (`seq_raise_cwp`: a raise's finaliser run at `cwp`, then
  the raise, lands in the outer `cwp`) has a fixed budget, about a quarter of the unit. If it is not
  closed in that budget, `PinFin` is asserted.
  If that closes, `PinFin` is a theorem (`pinFin`), `PinLaw` gets no `fin` field, and `fundamentalC_pin`'s
  `effThenDiv` case uses the theorem. If it does not close inside the unit, `PinLaw` gets the third field
  `fin : PinFin`. The report then states what was tried and says "not derived, obstruction not verified",
  unless a named `def … : Prop` is built.
- `pinLaw_iff : PinLaw ↔ PinStop ∧ PinLoop ∧ PinFin` (when asserted), and `PinLaw.of_stop_loop` gains
  the third argument.
- `bcc trusted` (`Backend/Driver.lean` `typingReport`) maps a `Fin` pin to `PinFin (PinLaw.fin)`. The
  checker does not emit `effThenDiv` in this unit: finalisers at the surface are typed at `F 1`
  (`effThenA`). Emitting it is unit B.

### 1.6 `Row.CancelTotal`

    CancelTotalC F ≜ F.isTop = false ∧ Row.divB F.rowOf = false ∧ ∀ o ∈ F.rowOf, o.finRead → CancelTotalC o.fin
    Row.CancelTotal Σ ≜ ∀ o ∈ Σ, o.finRead → CancelTotalC o.fin

This is recursive over nested cancel rows, by the same recursion as `FinLe`. It is a typing-only predicate,
since the relation does not read `fin` at a marked operation.

This is the premise that termination-sensitive code (a bounded scheduler's cancel-at-budget, `run_in`)
asks of its tasks' row. Unit A defines it, decides it (`Row.cancelTotalB` and `_iff`), and shows it is
non-vacuous. There are two examples:
- a row whose marked `await` has cancel row `F 1`;
- a row whose cancel row holds `Div`, which is refused.

No consumer exists in unit A. `run_in` is unit B. That a `CancelTotal` cancel terminates stays open, as
decision 69's "finalisers are total" does.

### 1.7 A cancel cannot be intercepted (decision D3 under cancel-by-resume)

> **PENDING the Trio spike (2026-10-31).** The user is considering replacing this route (refusing
> interception) with Trio-style level-triggered cancellation. Under that design the cancelled state belongs
> to the task's scope, every cancellable wait in a cancelled scope raises `cancelled`, and shielded waits
> work normally. This section stands only if the spike's answer keeps route (i). Nothing in it has been
> built.
>
> **The targeted check found holes in this section as written.** They are recorded here and not
> applied, since the section may be replaced.
>
> **Fatal**
> 1. **A `⊤` cancel row makes `hRC` vacuous.** `ThenLe _ _ ⊤` always holds, and `⊤.rowOf = []`.
>    Fix: `AvoidsD m F` requires `F.isTop = false` at every depth.
> 2. **`effHandleL`'s work frame is an unwind finaliser, and `finRead` does not reach it.**
>    `LastFinOK`'s `hfin`-like conjunct (`Core/DivHandleLast.lean` ~358) is gated at `capB`. Fix: read it
>    at `finRead`, and state the completeness argument over every frame that runs code on the unwind:
>    - `[then]`;
>    - handle-last's work;
>    - the lend's `d`, which is pure.
>
> **Major**
> 3. **`divFuel` and `reify` handle `Div` and carry no `hRC`.** Fix: the same premise at `divEff`, and
>    list all six places where a name becomes handled.
>
> **Minor**
> 4. **`AvoidsD`/`CancelTotal` recurse where `ThenLe`/`PendLe` (still at `capB`) write nothing.**
>    Either extend `finRead` there, or argue at the top level and call the recursion conservative.
> 5. **Gate `hRC` at `o.Cancellable`, not `o.rc`.**
> 9. **`hRC` also refuses resuming handlers inside a task.** Unit B's message must name the fix: move
>    the handler outside the scheduler, or move the effect out of the finaliser.

The rule is decision D3 of 2026-10-08 (SPEC §27): a finaliser may not raise or perform a name that is
handled only inside the cancelled region. Under κ.2, the region's frames are dead, and D3 is checked by
`[sub]` from `κ`'s cancel row to the row of the code that cancels. Under cancel-by-resume, the region is
live. A finaliser on the cancel's unwind runs inside it, so a handler inside the task would catch that
finaliser's raise, or abandon its continuation, and the pending `cancelled` would be lost.

The kernel states the rule at the place where a name becomes "handled inside": the handler rules.

    [handle] at name m, body row Row.ofEff m E 0 fs cs ++ Σ:
        ∀ o ∈ Σ, o.rc = true → Row.AvoidsD m o.fin                    (hRC)
    Row.AvoidsD m F ≜ ∀ o' ∈ F.rowOf, o'.n ≠ m ∧ (o'.finRead → Row.AvoidsD m o'.fin)

This premise goes on `effHandleV`, `effHandleVB`, `effHandleT` and `effHandleL`, in `CDerives`,
`CDerivesAt`, `CDerivesP` and `TDerives`. `Row.avoidsDB` decides it, with an `_iff`. It is a typing-only
premise, so the compatibility lemmas ignore it.

**Why it is complete.**
- An `await` that reaches a handler outside `handle_m` is an entry `o` of `handle_m`'s outer row `Σ`.
- Every `[then]` between that `await` and `handle_m` has recorded its finaliser's row in `o.fin`, via
  `hfin` at `finRead`. `[sub]` and function types only grow that record.
- So every operation that such a finaliser may raise or perform is a name of `o.fin`. A handler of one of
  those names inside the region is refused.
- A finaliser outside `handle_m` is not caught by it. It is checked at any handler further out that is
  still inside the region, against the record as grown by then.

**The second route** is a finaliser that performs `p` at a name `m` whose inner handler returns without
resuming. `p` is in `Σ_D`, and `ThenLe` puts each entry of `Σ_D` into `o.fin`, so `m` is a name of
`o.fin` and `hRC` refuses `handle_m`. `hRC` checks names, whatever the operation's qualifier or answer,
so raise, perform-and-abandon and perform-and-resume are all refused alike. That is D3's own over-
approximation ("a raise or operation of a name with no live instance there is a type error").

**Non-vacuity.** In `Core/AwaitCancel.lean`, for the program
`handle_m ((await_n then x. return x unwind raise_m e)) with …`:
- `hRC` is refuted when the handler is inside the region;
- `hRC` holds for the same body with `handle_m` outside the scheduler's handler of `n`;
- the perform-and-abandon variant is refused.

**What a task can still do.** A task can still handle its own effects inside, around code that does not
await. It cannot raise `cancelled` itself (`[raise]` refuses marked operations); self-cancel is a
scheduler operation.

### 1.8 A value with no derived drop must be closed on every exit, the cancel included

The user's requirement (2026-10-31): a function holds a file handle that must be closed, and it can be
cancelled. It must close the handle on every exit, including the cancel ("not everything needs to be
automatic/derived").

The kernel already has the rule, and cancel-by-resume reaches it with no new premise.
- `[await-c]` needs the abortive `cancelled` in the row, and an abortive operation has `q ≠ .lin`
  (`OpSig.abort`). So the row `Row.Cancels`.
- `[let]`'s `hW : Σ.Cancels → Γ₂.OwnFree` then refuses any value live across the `await` that is not
  `OwnFree`. A declared type with no derived drop (`declTy`, a `must_close` field: `A ⊗ Tok`) is not
  `OwnFree` (`decl_not_ownFree`).
- The way out is a `[then]` whose finaliser consumes the value (`finally close(f)`). `Γ₂` goes to both `N`
  and `D`, so the value is closed on the normal exit and on the `cancelled` unwind.
- A clause that handles `cancelled` is not available inside the task. The reason is not §1.7: `hnS`
  (a `handle_n` inside a task handles its own body's awaits, which makes it a nested scheduler)
  together with `[raise]`'s `hrc`.
- The lend frame is also an exit. Under the widened `ResumeOC`, `cancelled` unwinds through `lendR`, and
  its `d` closes the lent place.
- **Scope.** `hW` refuses every value that is not `OwnFree` held across an `await`: `Ref`, `Array`, thunks,
  and not only `declTy`. This is unchanged from κ.2, where `await` at `.cancel` already made the row
  `Cancels`.

Unit A proves this:
- `Row.cancels_of_await`: a row that admits `[await-c]` at some name `Cancels`;
- `not_ownFree_live_across_await`: at such a row, `[let]` refuses a `declTy` in `Γ₂`, through
  `decl_not_ownFree`;
- non-vacuity: `Tok` live across `await_n` under `[then]` with `burn` as the finaliser is derivable.

**Unit B's done-when**, since the surface `await` is not built here:
- the refusal message names the fix ("close or consume it on every exit, including cancel, e.g.
  `finally close(f)`");
- `corpus/async-close-on-cancel.bc` runs the fixed version with `live 0`;
- `corpus/reject/async-close-on-cancel.bc` is the refused version, its `expect` line naming the fix.

### 1.9 Non-vacuity

In `Core/AwaitCancel.lean`:
- a derivation of `await_n` at a row `{await⟨rc⟩, cancelled}`;
- `[perform]` refusing the marked operation (`hac` cannot be met);
- `ResumeOC` admitting `{await, cancelled}`, and refusing a row with any other abortive operation and a
  row with a marked `tick` (`{tickSig with rc := true}`);
- `[raise]` refusing the marked `cancelled` (`hrc` cannot be met);
- `effThenDiv` at a finaliser row holding `Div`;
- the two `CancelTotal` examples.

Each comes with `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.

## 2. Proved vs asserted

| item | status |
|---|---|
| marker, `Sig`, `cancellableB_iff`, `semC_effOf_rc` | proved |
| `[await-c]` (`await_compatC`), `fundamentalC` hypothesis-free | proved |
| `finRead` in `FinLe`/`LeF`/`hfin` | proved (then_compatC unchanged) |
| `Row.ResumeOC` in `lendR`/`PinStop`/`LendFrame` | asserted: inside `LendFrame` (widened domain) |
| `effThenDiv` at `Div`-free finaliser rows | proved (`pinFin_divFree`) |
| `effThenDiv` at `Div` finaliser rows | proof attempted first; otherwise asserted as `PinLaw.fin : PinFin` |
| `Row.CancelTotal`, `cancelTotalB_iff` | definition plus proved decision |
| `hRC` on the handler rules (§1.7), `avoidsDB_iff` | typing premise; proved decision |

## 3. NOT in this unit

- The surface `await`, the non-cancellable completion wait (plan item 4), `lib/async.bc`'s `cancelled`
  clause and `run_in` (unit B).
- The checker emitting `effAwait` or `effThenDiv`. It refuses a plain `perform` of a marked operation,
  but no surface operation is marked yet, so no corpus program changes.
- The nursery: `tick` in `ResumeOC` (#743).
- The lowering of a suspending finaliser (Backend2), and machine steps.
- An `await` with an argument. `[await-c]` is at `a.A = 1`, as in the spike.
- Any change to the derived drops or to a task's destructor.
- Any change to `Qual`, the relation or the machine. `CDerives.effThen` changes only by reading `hfin` at
  `finRead`. That is a premise strengthening at marked operations, and none exist yet.
- A premise refusing marked operations in a finaliser's row (`∀ o ∈ SD, o.rc = false`). It is not added
  (§6.3).

## 4. Tempting shortcuts (each a STOP)

- **A handler inside a task's region whose name is in a marked operation's cancel row** (§1.7). Any
  rule that lets it through is a STOP. So is stating D3 twice, once at `[then]` and once at the
  handler.
- **Routes (b) and (c) of §6.1, or keeping the κ.2 drop as a fallback.** STOP.

- **Keeping the shape test** (`lin ∧ i = 0 ∧ B = 1 ⊕ 1 ∧ n ≠ divEff`) and calling it a marker. STOP.
- **Putting the marker in `OpSig` but not in `CTy`.** `[sub]` could then forget it. STOP.
- **Making the marker a fourth `Qual`.** The machine and the relation read `Qual`, and the marker must
  stay a typing datum. STOP.
- **Leaving `rc` out of `OpSig.Sig`, or letting `RowLe` drop it.** STOP.
- **Generalising the handler compatibility proofs case by case.** The transport is one lemma
  (`semC_effOf_rc`); a per-handler patch is a STOP.
- **Adding `effThenDiv` to `CDerives`, or dropping `hSD` from `CDerives.effThen`.** Either would end
  decision 69 for the unconditional fragment. STOP.
- **Stating `PinFin` pointwise over code with no `CDerivesP` premises**, unlike B1's schemas. STOP.
- **Any `PinLaw` change other than the third field.** STOP. The `ResumeOC` widening of `LendFrame` is the
  kernel target's own and is listed in §1.4; a widening beyond §1.4's domain is a STOP.
- **Admitting abortive operations other than `cancelled` in `ResumeOC`** (OQ-1). STOP.
- **Letting finalisers intercept a cancel**, or letting a finaliser's raise be swallowed (the finaliser
  algebra). STOP.
- **Touching a task's derived drop** (cross-flag). STOP and report. See §6.1 for unit B.
- **`ResumeOC` admitting a row with `Row.divB = true`.** STOP.
- **`[raise]` admitting a marked operation.** STOP.
- **Copying or dropping a linear or owed value without a rule.** HARD STOP.
- **Putting `_iff` on `resumeOCB` by weakening `outlivesAllB`.** STOP. It stays sound only.

## 5. What breaks, and why

- Every `.eff n i q A B fin C` pattern and every `OpSig` literal `⟨n, i, q, A, B, fin⟩` gains the marker
  argument. This is mechanical. It reaches Core, Frontend/Check (Decide, Steps, Elab, Cells),
  Backend2 (Convert, Types) and `scripts/KernelCensus.lean`.
- `OpSig.Sig`'s destructurings gain a sixth component.
- Every `.effPerform` and `.effRaise` call site gains `rfl` for `hac`/`hrc`.
- The inversions: `AppBase` gains an `[await-c]` disjunct, `der_letJ` gains a premise that excludes
  `await`'s body, and `der_bind_split` needs a witness for `await`'s term. All are as in the spike.
- The handler rules gain `{cs}` and `hRC`. `hRC` is `rfl`-like (`Row.avoidsDB`) at every existing
  derivation, since nothing is marked. The checker and every existing derivation use the default.
- `CDerivesP.lendR`, `PinStop` and `LendFrame` are stronger in what they admit. `PinLaw` gains `fin`
  if `PinFin` is asserted.
- Two corpus rejects, `async-r1-spawn-captures.bc` and `async-r1-unr.bc`, change their `expect` line,
  because the R1 error message names the cancel path.
- `SPEC.md`:
  - §19: `OpSig.rc`, `CTy.eff`, `[perform]`/`[raise]`'s premise, and the handler rules' `cs`;
  - §27: `finRead` in `FinLe`/`LeF`/`hfin`;
  - §24: `[then]`'s `hfin`;
  - §29a, new;
  - §29's trusted base: the widened `LendFrame` domain, `PinLaw.fin`, `pinLaw_iff`.
- `Decide.rowLeB` tests exact entry equality, so it compares `rc` already. It is sound only, so no `_iff`
  is at stake.
- `docs/async-capabilities.md` §8 OQ-1, §3.4 and row `n4` (§1.4).
- Frontend/Check/Pin.lean: `resumeOB` → `resumeOCB` at the R1 site. The gen-pin.py templates. The
  `KernelCensus`/kernel-counts goldens if they enumerate rules. `corpus/*.out` for `bcc trusted` only
  if a program's pins change, and none do.
- Experiments are not built by the gate. Their `OpSig` literals will break, and they are left alone.


## 6. Decisions (user, 2026-10-31)

General principle: "I am okay with the type checker refusing linearity violations for programs that
should work as long as there is a way to fix it, even if it involves explicitly handling a match or
whatever."

1. **The derived drop: route (a).**
   - Under cancel-by-resume, a task that holds borrows has no derived drop. It must be awaited or
     cancelled explicitly, and the five accepted leak shapes become refusals.
   - Decision 1 (derived drops are pure) stands. The κ.2 drop does not stay as a fallback.
   - `Cancellable`'s `q = .lin` is therefore as intended. Unit A changes no derived drop.
   - **Unit B obligation:** each refusal message names its fix (await it, or cancel it), so every refused
     program has a written fix.
   - The nursery (#750 item 3, via #743) is the later convenience and is not built.
2. **A cancel cannot be intercepted**, kept by refusal (D3 under a live region, §1.7). **Pending the
   Trio spike**, which may replace this with level-triggered cancellation.
3. **`await` inside a finaliser.** Once §1.7 holds, a finaliser's `await` reaches only the scheduler, and
   its second `cancelled` propagates there, which is "finaliser raises propagate". No further premise is
   added.
4. **OQ-1(a) is taken for the cancel path only** (§1.4), under the kernel target's line "`Row.ResumeOC`
   as PinStop's premise". This is a trusted-base change.
5. **Where the marker is declared.** `cs` is chosen per handler (sound: marking only restricts). Unit B's
   checker reads it from the effect declaration and never chooses it (STOP).

## 7. Review record

1. **Review 1.** One Fatal: `ResumeOC` admitted a marked `tick`. Fixed in §1.4. Its Majors and Minors
   are applied.
2. **Review 2 (full).** Its Fatal was interception through a live region. Fixed in §1.7, after the user's
   decision 2. Its derived-drop finding is closed by decision 1. Its Major (OQ-1(a)) is in §1.4 and §5.
   Its Minors are applied:
   - `finRead` skips abortive operations;
   - the non-vacuity tests cover a marked `tick` and `[raise]`;
   - `rowLeB` is noted;
   - self-cancel is noted;
   - the sections are renumbered.
3. **Targeted check** (§1.7, §1.8, §6). It found 2 Fatal, 1 Major and 5 Minor findings in §1.7. They are
   recorded there and not applied, pending the Trio spike. Its Minors on §1.8, §1.4 and §3 are applied.
   Under the exit rule, a further full review is due once §1.7's route is settled.
