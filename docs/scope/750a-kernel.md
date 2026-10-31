# #750 unit A — the cancel-by-resume kernel rules

Issue #750, plan items 1 and 2 (comment 6528120064). The rules are rebuilt on `main` from the spike
`spike-cancel-resume` @1294661b, which predates #746 steps 2–3 (`Qual.aff` is now `Qual.cancel`) and #743 B1
(`PinLaw` as the schemas `lendFrame` and `loopFrame`). Nothing is merged from the spike branch.

Kernel target: on `main`, each rule below as a proved rule or as a named schema of `PinLaw`.

## 1. The rules

### 1.1 The cancellable marker (replaces the spike's shape test `OpSig.awaitB`, never on main and not ported)

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

    Row.ResumeOC Σ 'x ≜ (∀ o ∈ Σ,
        (Row.ResumeO's conjuncts at o)
      ∨ (o.Cancellable ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ (∀ Δ a, VOutlives Δ a o.A) ∧ NoThunkT o.A)
      ∨ (o.CancelTarget ∧ o.i = 1 ∧ o.q = .cancel ∧ o.n ≠ 0 ∧ ∃ a, Row.find Σ o.n 0 = some a ∧ a.Cancellable))
    ∧ Row.divB Σ = false          -- outside the ∀ and the disjunction

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
  domain it admits. No field is added for it. It relaxes `Row.ResumeO` in three ways:
  1. the abortive `cancelled` is admitted (OQ-1(a), cancel path only);
  2. the `await` answers `1 ⊕ 1`, not `1`. This is OQ-5's restriction ("as GhostEnd and Law 2 do"),
     relaxed for marked waits. The answer is reached only through `[await-c]`'s `case`, since `hac`
     refuses a plain `perform`;
  3. any cancel row is allowed (`o.fin` free).

  SPEC §29's trusted base lists all three. `docs/async-capabilities.md` OQ-1 and OQ-5 are updated.
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
- **Reachability.** `effThenDiv` at a `Div` finaliser forces `Row.divB Σ = true`, so `effHandleV`/`VB`'s
  `hdv` refuses it inside a task body. The term is reachable under `divFuel`/`reify` (the handlers of
  `Div`). Before `PinLaw.fin` is asserted, one closed `CDerivesP` derivation that uses `effThenDiv` at a
  `Div` finaliser under `divFuel` is given (`d_thenDivFuel`). Without it the schema is not added.
- **The nursery** (a finaliser that loops awaiting children) also needs `hdv` (decision 68) relaxed for
  task handlers. That is #743's widening, not this unit.
- `bcc trusted` (`Backend/Driver.lean` `typingReport`) maps a `Fin` pin to `PinFin (PinLaw.fin)`. The
  checker does not emit `effThenDiv` in this unit: finalisers at the surface are typed at `F 1`
  (`effThenA`). Emitting it is unit B.

### 1.6 `Row.CancelTotal` and `Row.CancelEnds`

    CancelTotalC F ≜ F.isTop = false ∧ Row.divB F.rowOf = false ∧ ∀ o ∈ F.rowOf, o.finRead → CancelTotalC o.fin
    Row.CancelTotal Σ ≜ ∀ o ∈ Σ, o.finRead → CancelTotalC o.fin
    Row.CancelEnds Σ ≜ Row.CancelTotal Σ ∧ ((∃ o ∈ Σ, o.Cancellable) → Row.divB Σ = false)

These are recursive over nested cancel rows, by the same recursion as `FinLe`, and typing-only: the
relation does not read `fin` at a marked operation. Each is decided (`cancelTotalB`, `cancelEndsB`) with an
`_iff`.

Under level-triggered cancellation (§1.7), a marked operation's cancel row does not cover code that runs
after a catch, so `CancelTotal` alone does not bound a cancel. `Row.CancelEnds` adds "no `Div` where the
row has a cancellable wait".
- A task handled by `effHandleV`/`VB` already has a `Div`-free row (`hdv`), and those are the rules the
  state-passing scheduler fits. So at a task row `CancelEnds` reduces to `CancelTotal ∧ Div-free`.
  `Div` can sit beside a marked wait only under `effHandleT`.
- The relation never reads a marked operation's cancel row. So `CancelTotal` and §1.3's `finRead`
  bookkeeping have no semantic consumer under level-triggered cancellation. They are kept because the
  kernel target names them. This is raised with the user (§6.7).

**`CancelEnds` is a theorem target, not a typing restriction.** No rule asks for it.

- **The target** (`stickyScope_ends`): `hnd (n, H_sticky) e` at the cancelled flag, typed under
  `effHandleV` (so `hdv` holds). Every run reaches the handler's answer, through finitely many stops of
  `Σ`, with no suspension at a marked wait.
  - The closed instance (`d_stickyScope`) follows from `adequacyC`/`adequacyD`, and is proved.
  - The general statement over every task body `e` is proved if that is tractable. Otherwise it is
    recorded as unproved, with no assertion.
- Rows with `Div` carry no termination guarantee, which is what `Div` means. That is not a finding.
- `run_in` (unit B) may cite the theorem only once it is proved.

Non-vacuity:
- `CancelTotal`: holds where the marked `await` has cancel row `F 1`; fails where the cancel row holds
  `Div`;
- `CancelEnds`: holds at the swallowing row; fails at the swallowing row with a `tick` (`CancelTotal`
  still holds there).

### 1.7 Level-triggered cancellation (user decision, 2026-10-31)

The user chose Trio-style level-triggered cancellation, without refusal (i) on top. The Trio spike
(`spike-trio-cancel` @4df2a9e7, `experiments/spike750/Spike750/Trio.lean`) found that it needs **no new
kernel rule, step or premise**. The cancelled state belongs to the task's handler, not to the kernel.

- **The mechanism.**
  - The task handler of name `n` carries the cancelled flag as its state.
  - `await`'s clause (operation `0`) reads the flag:
    - live: it hands `κ` to the scheduler;
    - cancelled: it resumes `κ` with `inr ()` at once, and `[await-c]` raises `cancelled`.
  - The canceller sets the flag, then resumes the stopped `κ` with `inr ()` (round 2's cancel).
  - No clause clears the flag, so every later cancellable wait in the scope raises again.
- **Shielded waits.** An unmarked operation of the same name, `complete : 1 ↠^lin 1`, whose clause does
  not read the flag. Finalisers that wait use it. An `await` in a finaliser of a cancelled task raises
  at once. Round 2's rollback target is written with `complete`.
- **What a cancel row means now.** A marked operation's cancel row, recorded by `[then]`'s `hfin`,
  accumulates every finaliser around the wait out to the task handler, including ones whose raises are
  caught inside. It does not cover code that runs after a catch. Typing is unchanged (`ResumeOC`'s `await` branch
  admits any cancel row). Only the reading changes (§1.6).
- **No refusal of interception.** A handler inside the task may catch a finaliser's raise that
  supersedes `cancelled`. The cancel is then deferred to the next cancellable wait, not lost.
  - `cancelled_n` itself is never caught inside the task: `[op]` needs the context free of `n`, and
    `hnS` makes any inner handler of `n` a nested scheduler of its own body.
  - Route (i)'s premise `hRC` is dropped. The targeted check's two Fatals, its `divFuel`/`reify` Major
    and its `hRC` Minors (4, 5, 9) were findings against `hRC`, and they are moot.

**To be ported onto main and rebuilt** (not merged), in `Core/AwaitCancel.lean`. Typed terms:
`d_swallow`, `sem_swallow`, `d_stickyScope`. The rest are machine runs.

- `stickyAwait`, the level-triggered clause, together with the laws:
  - `await_cancelled`: at a memory where the flag holds `inr ()`, `hnd (n, H) K[await_n]` steps to
    `hnd (n, H) K[raise_n (1, ())]`, with the memory unchanged, for every `K` free of `n` and every
    `K₀`;
  - `await_cancelled_inst`: its premises are satisfiable;
  - `shield_catch` and `shield_catch_inst`: a shielded wait's catch does not read the flag.
- The swallowing example
  `handle_3 (await_1 then x. x unwind raise_3) with {3 _ → ()}; await_1`:
  - typed at main's rules (`d_swallow`);
  - in the relation (`sem_swallow`);
  - its row admitted by `ResumeOC` (`resumeOC_swallow`).
- **The scheduler's clause, typed by passing the state along** (as `take n` does), not by capturing a
  cell. This is the *immediate* scheduler: the flag is passed in and not changed between suspensions.
  It shows the clause's typing and the start-cancelled scope. A *suspending* scheduler (live: hand `κ`
  out; the driver sets the flag and resumes) needs an answer holding the suspended `κ`, such as
  `μX. R ⊕ U(Flag ⊸ F X)`. Its typing under main's rules is not verified here. It is unit B's
  (lib/async's rewrite), and the claim "no new kernel rule" is made only for the immediate scheduler.
  The cell-reading `stickyAwait` laws cover the suspend-then-cancel run at the machine level only.
  - The handler's answer is `U(Flag ⊸ F R)`. `await`'s clause is
    `λ(_, κ). return (λc. case c {inl _ ⇒ resume κ (inl ()) to g. g c | inr _ ⇒ resume κ (inr ()) to g. g c})`,
    `lin` at `1 ↠ 1 ⊕ 1`.
  - `d_stickyScope`: a closed `CDerives` derivation of that handler around the swallowing example, run
    from the cancelled flag. By `adequacyC`/`adequacyD` it ends at the `cancelled` answer with every cell
    freed.
  - `stickyScope_eval`: `Support`'s `eval` agrees.
  - The cell-reading `stickyAwait` is the spike's machine-level form. The typed form passes the flag.
- **Runs**, by `decide` on `eval`, with `live 0` where the spike had it:
  - the swallowing example;
  - retry-inside-the-task;
  - a finaliser closing a `must_close` cell on the cancel exit;
  - a shielded `complete` in a cancelled task's finaliser, which completes;
  - the same finaliser with `await`, which raises at once.

**Not built**:
- cancel scopes inside a task, which need a forwarding rule (spike §5);
- a timeout that sets a suspended scope's flag.

### 1.7a Laws

- **Law 5** (a cancel is not interceptable; the cancelled region's frames are dead) and the
  *first error kept* sentence of law 6 (`CancelRun`) stay as they are for κ.2 cancels of `cancel`
  operations: generators, `deadline`, `take`.
- **Law 5c, for cancellable waits.** It replaces law 5 and the `CancelRun` sentence there: *a cancel is
  not lost*. In a cancelled scope every cancellable wait is `raise cancelled` (`await_cancelled`).
  - 5c is a law of the task handler's clause (lib/async, unit B), not of the kernel.
  - The kernel's part is that `cancelled_n` is raised only by `[await-c]`, and only on `inr ()`
    (`[perform]`'s `hac`, `[raise]`'s `hrc`).
  - It is never caught inside the task: the raise happens in the same `K` as the wait, and the catch
    needs `K` free of `n` (`catch_step`, `catch_abort`). Stated as `cancelled_not_caught`.
- **Law 6's *Finally* and *Unwinding* clauses apply unchanged to the `cancelled` raise.** A finaliser's
  raise supersedes it. The canceller learns how the task ended, not which errors its finalisers raised.
- **Text to update:**
  - SPEC §19 *Cancels*' opening sentence (~line 2990) and *Laws* item 5 and law 6's `CancelRun`
    sentence: scope them to κ.2, and add 5c;
  - SPEC §29a;
  - `docs/effect-lowering.md` §2.4 and the §2.8 row. For cancellable waits, "a cancel lowered as an
    ordinary raise" is now the semantics: a call that resumes the task's state machine with `inr ()`,
    then an ordinary raise. The exclusion stays for κ.2 cancels.
- **Decision 2 overrides the brief's "cancel can't be intercepted" for marked waits.** A handler inside
  the task may catch a finaliser's raise that supersedes `cancelled`. It cannot catch `cancelled_n`
  itself.

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
- A clause that handles `cancelled` is not available inside the task: `hnS` (a `handle_n` inside a task
  handles its own body's awaits, which makes it a nested scheduler) together with `[raise]`'s `hrc`. A
  handler that catches a superseding finaliser raise exits through that handler's clause, which is an
  ordinary exit typed by the same `hW`.
- **Only values with no derived drop need written code.** An owned `Ref`, `Array` or thunk held across an
  `await` gets its derived drop as a finaliser on the cancel unwind, exactly as for errors. The checker
  inserts that drop at a `dtor` node (`TDerivesP.dtor_hasDtor`), and nothing new is needed: the cancel
  unwind is an ordinary raise. A value with no derived drop (`declTy`, `must_close`, a borrowing task
  under route (a)) has no `dtor` node, so the program must close it.
- The lend frame is also an exit. Under the widened `ResumeOC`, `cancelled` unwinds through `lendR`, and
  its `d` closes the lent place.
- **Scope.** `hW` asks every value held across an `await` to be `OwnFree`, or to be under a finaliser.
  This is unchanged from κ.2, where `await` at `.cancel` already made the row `Cancels`.

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

(The §1.7 runs and laws are listed there.)

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
| level-triggered laws `await_cancelled`, `shield_catch`, `d_swallow`, `d_stickyScope` (§1.7) | proved (machine and typing at main's rules) |
| `Row.CancelEnds`, `cancelEndsB_iff` | definition plus proved decision |
| `cancelEnds_ends` (§1.6) | theorem target: proved if tractable, else recorded unproved (no assertion) |

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

- **Adding a refusal of interception on top of level-triggered cancellation** (route (i), `hRC`). The
  user chose level-triggered alone. STOP.
- **Making `Row.CancelEnds` (or `CancelTotal`) a premise of any rule, or asserting `cancelEnds_ends`.**
  STOP.
- **Typing the scheduler by capturing the flag cell in a clause.** `[handle]`'s `DeadP` refuses it, and
  the typed form passes the state. Any workaround is a STOP.
- **An `await` in a target's finaliser where a shielded `complete` is meant.** STOP.
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
- **A seal or `[then]` frame swallowing a finaliser's raise, or a handler inside the task catching
  `cancelled_n` itself.** STOP. Catching a finaliser's superseding raise is allowed (decision 2).
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
- The handler rules gain `{cs}`. The checker and every existing derivation use the default.
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
- `resumeOB` → `resumeOCB`: defined in Frontend/Check/Pin.lean; the R1 call site is
  Frontend/Check/Checker.lean (~662/676); `scripts/AxiomCheck.lean` prints `resumeOB_sound`. The gen-pin.py templates. The
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
2. **Level-triggered cancellation** (§1.7), without refusal (i). A cancel is not lost: it is re-raised
   at every cancellable wait in the cancelled scope.
3. **Waiting inside a finaliser.** Finalisers that wait use the shielded `complete`. An `await` there
   raises at once in a cancelled scope. No premise is added.
4. **Termination.** "It is sort of obv that we can't make guarantees about div functions."
   `Row.CancelEnds` is a theorem target (§1.6), not a typing restriction.
5. **OQ-1(a) is taken for the cancel path only** (§1.4), under the kernel target's line "`Row.ResumeOC`
   as PinStop's premise". This is a trusted-base change.
6. **Where the marker is declared.** In the kernel judgment, `cs` is chosen per handler. Marking restricts
   `[perform]`/`[raise]` and widens what `ResumeOC` (so `LendFrame`) admits.
   - The tied judgment does not tie `rc` today: `RowAt` compares `(q, A, B)` with `Ξ`.
   - In unit A no effect context declares a marked operation, and the checker emits none, so nothing
     depends on the tie yet.
   - **Unit B obligation (STOP until done):** before the surface declares a cancellable wait, `EffCtx`
     carries the marker (`Ξ n` giving `(q, A, B, rc)`), `RowAt` compares it, and the tied handler rules
     derive `cs` from `Ξ`. Then the marker is never correct by convention.
7. **For the user:** under level-triggered cancellation, `finRead` (§1.3) and `Row.CancelTotal` (§1.6)
   have no semantic consumer. They are kept because the kernel target names them. Whether to drop them
   is a question for the user.

## 7. Review record

1. **Review 1.** One Fatal: `ResumeOC` admitted a marked `tick`. Fixed in §1.4. Its Majors and Minors
   are applied.
2. **Review 2 (full).** Its Fatal was interception through a live region. It is addressed by the user's
   decision 2 (level-triggered: the cancel is deferred, not lost). Its derived-drop finding is closed by decision 1. Its Major (OQ-1(a)) is in §1.4 and §5.
   Its Minors are applied:
   - `finRead` skips abortive operations;
   - the non-vacuity tests cover a marked `tick` and `[raise]`;
   - `rowLeB` is noted;
   - self-cancel is noted;
   - the sections are renumbered.
3. **Targeted check** (§1.7, §1.8, §6). It found 2 Fatal, 1 Major and 5 Minor findings against
   route (i)'s `hRC`. They are moot now that §1.7 is level-triggered and `hRC` is dropped. Its Minors on
   §1.8, §1.4 and §3 are applied.
4. **Full review of the level-triggered scope.** No Fatal; 7 Major and 7 Minor findings, all applied.
   The scheduler claim is limited (§1.7). The laws text is fixed (§1.7a). The termination target is
   restated (§1.6). The `finRead`/`CancelTotal` question goes to the user (§6.7). `PinFin` gets a
   reachability witness (§1.5). The trusted base lists three relaxations (§1.4). The `Ξ` tie is unit
   B's STOP (§6.6). The Minors are applied.
