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

`OpSig.finRead o := capB o.q o.B || o.rc`. `FinLe`, `OpSig.LeF` and `[then]`'s `hfin` read the cancel row at
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

### 1.7 Non-vacuity

In `Core/AwaitCancel.lean`:
- a derivation of `await_n` at a row `{await⟨rc⟩, cancelled}`;
- `[perform]` refusing the marked operation (`hac` cannot be met);
- `ResumeOC` admitting `{await, cancelled}` and refusing a row with any other abortive operation;
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
- A premise refusing marked operations in a finaliser's row (`∀ o ∈ SD, o.rc = false`). See §6, open
  decision 2.

## 6. Open, for the user (not decided here)

1. **Forward cross-flag: a task's derived drop.** Today `await : 1 ↠^cancel 1` is capturable, and a
   task's derived drop is `κ.2`, which the leak-freedom of borrowing tasks rests on. When unit B moves
   `await` to the marked `1 ↠^lin 1 ⊕ 1`, the task's `κ` becomes `U((1 ⊕ 1 ⊸ …) & ⊤)`, which has no
   derived drop (the spike found the same: `not_hasDtor_task`). The five accepted leak shapes would
   become refusals unless the kernel gains a drop `κ.1 (inr ())` at a `Cancellable` operation. That drop
   runs finalisers, so it is effectful, which collides with "derived drops are pure at the row".
   **Unit A changes no derived drop.** Unit B's switch of `await` is a STOP until this is decided.
2. **`await` inside a finaliser.** A second cancel raises `cancelled` from inside the finaliser and skips
   the rest of the cleanup. That fits "finaliser raises propagate", but it makes cleanup cancellable,
   which is the reason for plan item 4. One option is a premise on `[then]` refusing marked operations in
   `Σ_D`. It costs nothing today, but it is a design choice, so it is not made here.
3. **Where the marker is declared.** `cs` is chosen at each handler, as `fs` is, and `RowAt` does not tie
   it to `Ξ`. The kernel has no declarations, so the handler is the declaration. Soundness does not
   depend on it: an unmarked operation is an ordinary `lin` operation. The alternative is a fourth
   component of `E` (`Qual × VTy × VTy`), read by `Row.ofEff` and tied by `RowAt`. That would rewrite
   every clause list and the machine's tuple handling, and it is not done here. Unit B's checker must read
   `cs` from the effect declaration and never choose it (STOP).


## 4. Tempting shortcuts (each a STOP)

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
- Frontend/Check/Pin.lean: `resumeOB` → `resumeOCB` at the R1 site. The gen-pin.py templates. The
  `KernelCensus`/kernel-counts goldens if they enumerate rules. `corpus/*.out` for `bcc trusted` only
  if a program's pins change, and none do.
- Experiments are not built by the gate. Their `OpSig` literals will break, and they are left alone.

## 7. Scope review outcome: STOP before the build

There were two full reviews. Each found a Fatal issue.

The first was that `ResumeOC` admitted a marked `Div` `tick`. That is fixed above with the explicit
`Row.divB Σ = false`. The same review's Major and Minor findings are applied in §1–§6.

The second review found two problems, and the brief makes both of them STOPs.

1. **Fatal: drift from the decided finaliser algebra ("cancel can't be intercepted").** Under
   cancel-by-resume, the task's region stays live, and the cancel is an ordinary raise of `cancelled`.
   A finaliser on that unwind can raise (or abort) to a handler *inside* the task, and that handler then
   discards the pending `cancelled`. For example:

       handle_m ((await_n then x. return x unwind raise_m e)) with {m e → return v}

   This types under §1's rules. On a cancel it continues as if the task had finished normally. Today's
   κ.2 cancel runs in a dead region, and D3 makes this a type error. Nothing in §1 refuses it.

   The reviewer proposes a fix: every handler rule for a name `m` asks
   `∀ o ∈ S, o.rc → ∀ o' ∈ o.fin.rowOf, o'.n ≠ m`, which carries D3's typing to live regions. That is a
   new kernel premise on all four handler rules. It is a design choice, and it has not been checked to be
   sufficient (a finaliser that performs an operation whose inner handler returns without resuming
   is the second route). So it is raised for the user, not adopted here.
2. **Cross-flag (derived drop).** `OpSig.Cancellable` fixes `q = .lin`, and that conjunct is what removes a
   task's derived drop (`κ` at a `lin` operation is `U((B ⊸ …) & ⊤)`, which has no `κ.2`). "Derived drops
   pure at the row" is DECIDED (decision 1, kept 2026-10-30). Unit A's definitions therefore already
   choose between three routes:
   - accept the five leak shapes as refusals;
   - reopen decision 1 (an effectful drop `κ.1 (inr ())`);
   - a capturable marked `await` (`q = .cancel`, answering `1 ⊕ 1`, with a κ.2 fallback). On this route,
     `Cancellable`, `ResumeOC`'s second disjunct and `finRead` all change.

Also recorded:
- **Major.** `LendFrame`'s widened domain is semantically OQ-1(a)'s belief (an abort at an operation
  handled outside the lend, after a suspension inside it). SPEC §29 and `docs/async-capabilities.md` §8
  OQ-1, §3.4 and row `n4` must say so.
- **Minor.** `finRead` should be `capB || (rc && !abort)`. The non-vacuity tests should cover a marked
  `tick` and `[raise]` of a marked `cancelled`. `rowLeB`'s change is semantic (it reads `finRead`).
  A task cannot raise `cancelled` itself.

The mechanical marker plumbing (`OpSig.rc`, `CTy.eff`'s argument, `Sig`, `Row.ofEff … cs`) was started and
does not build yet. It is saved as `scratch-archive/linear-types/750a-wip-marker-plumbing.patch` and is not
committed.
