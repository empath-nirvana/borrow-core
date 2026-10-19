> **Where the code is.** Promoted into the library by B1 (#563): `Core/DivDefs.lean` through
> `Core/DivRuntime.lean` (SPEC §14). This experiment's code is at commit `f661c7b`; check it out to
> build it (`lake build DivEffect`). Its `omega_cwp0` and `omega_not_closing`, the reason for
> `Closing`, and the open `handle_general` and `sim_loop` are there.

# DivEffect: `Div` as a handled effect, the kernel unknowns (S0, #554)

**Question** (`docs/pipeline-architecture.md` §4.1). `Div` is an effect with one linear
operation, `tick : 1 ↠ Next`. A loop is `iterate`, which ticks at each back edge, and its
consumers are handlers: the runtime around `main`, `div_fuel` and `reify`. `ewpTS` is a least
fixed point, so a computation that ticks forever is not in it. Which relation holds such a
computation, does it carry the rules, and what do `div_fuel` and `reify` need from it? Does a
loop closed early hand back its residual by a resume, not a cancel? Do ticks stand where
today's machine observes?

Build: `lake build DivEffect`. Run: `lake env lean --run experiments/DivEffect/Run.lean`. The
library imports `Core`; `Run.lean`, outside it, imports `Backend` too. Nothing imports either. `Paper/`,
`Support/`, `Examples/`, `Core/`, `Frontend/` and `Backend/` are unchanged.

Every claimed result's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`
(`lake env lean experiments/DivEffect/Axioms.lean`). There are two `sorry`s, each a statement
not claimed proved: `handle_general` and `sim_loop` (below).

| file | contents |
|---|---|
| `Defs.lean` | the effect, `Closing`, the segment table `divTab`, `cwp` and its coinduction; `cwp ⊆ Closing`; `Closing` is Core's `ewpTS` at a row (`closing_row`) |
| `Frame.lean` | `ewp_frame_plain_or` (Core's `ewp_frame_plain` at `opTable T ∨ Π`); one segment under a plain frame (`cwpF_frame`); bind (`cwp_bind`) |
| `Rules.lean` | `[sub]`, `[perform]` of `tick` and of other names, `[let]`, at the judgment `SemD` |
| `Iterate.lean` | `iterate` and its compatibility (`cwp_iterate`) |
| `Fuel.lean` | `div_fuel` and its totality (`fuel_total`); an operation of another name passes a handler of `d` (`hnd_fwd`) |
| `Reify.lean` | `reify` and `𝒱⟦U(Loop_Σ B R)⟧` (`reify_compat`) |
| `Handle.lean` | `[handle]` of another name at a tail-resuming clause (`handle_tail`); the general clause (`handle_general`, `sorry`) |
| `Then.lean` | `ewp_frame_then_or` (Core's `ewp_frame_then` at `opTable T ∨ Π`); `[then]` (`cwp_then`, `then_compatD`) |
| `Safety.lean` | `div_fuel n` of a closed program, every run (`fuel_every_run`); `total_every_run` unchanged |
| `Runtime.lean` | the runtime's clause: every prefix of every run (`runtime_every_run`) |
| `Residual.lean` | unknown 2's program and its runs (`prog_every_run`) |
| `Plain.lean` | §4.1's candidate without `Closing` admits `Ω` (`omega_cwp0`), which `Closing` excludes (`omega_not_closing`) |
| `Placement.lean` | unknown 3: the placement, the counted programs, the simulation (`sim_loop`, `sorry`); `tick` is in no borrow callback's row (`tick_not_unwind`) |
| `Run.lean` | the programs at every stage, today's machine against `Div` |

## The relation

    cwp T Q   ≜  gfp W. ewpTS · (opTable T ∨ Π_W) Q
    Π_W(tick)  =  λ_. λκ. ∀ n : Next. W (κ n) ∧ Closing (κ n)
    Closing   ≜  ewpTS · (opTable (tick : 1 ↠ 0 ⊕ 1, T)) Q

A segment, up to the next tick, is an `ewpTS` run. A tick stops it and owes its continuation,
at each answer, to the candidate and to `Closing`. `Closing` is the least fixed point at the row
where a tick may only be answered *close*: after a close, the computation ends through finitely
many ticks, each answered close. `cwp` is written in `Prop` as `∃ W`, as `𝒞⟦νX. C⟧` is. It is
monotone by `ewp_mono`. **No step-indexing is used**: the tick is the guard.

**`Closing` is needed; §4.1's candidate is too weak for item 4.** Without it (`Plain.lean`,
`cwp0`), `Ω = fix self. tick (); self ()` is in the candidate (`omega_cwp0`): each segment ends
at a tick, and either answer leads to `Ω` again. `div_fuel 0 Ω` answers every tick *close*, and
with a linear `κ` it has no other move, so it never ends (`Run.lean`: out of fuel). With
`Closing`, `Ω` is outside the relation (`omega_not_cwp`). No typed program is `Ω`, since
`iterate` closes at its back edge. But `div_fuel`'s totality is proved from the relation, so the
relation has to say that close is honoured. It also lets `reify`'s *close* observation
terminate.

`Closing` is the relation at a row, `tick : 1 ↠ 0 ⊕ 1` in front (`closing_row`), so Core's
`ewp_frame_plain`, `ewp_frame_then` and `ewp_handle` apply to it as they are.

## Results

| item (§4.1) | status | Lean |
|---|---|---|
| 1. `[let]` and bind | proved | `cwp_bind`, `let_compatD` |
| 1. `[sub]` | proved | `cwp_sub`, `sub_compatD` |
| 1. `[perform]` of `tick` | proved | `cwp_tick`, `tick_compatD` |
| 1. `[perform]` (and `[raise]`, every rule) of other names | proved | `cwp_of_ewp`, `lift_compatD` |
| 1. `[then]` | proved | `cwp_then`, `then_compatD` |
| 1. `[handle]` of another name, `tick` forwarded, clause resuming `κ` in tail position | proved, the rest of the row linear | `handle_tail` |
| 1. `[handle]` of another name, a clause given `κ` | **not proved** | `handle_general` (`sorry`) |
| 2. `iterate` | proved | `cwp_iterate` |
| 3. safety under the runtime's clause, every prefix of every run, every allocator | proved | `runtime_every_run` |
| 3. the same through `div_fuel n`, as `externs_loop_every_run` | proved | `fuel_every_run` |
| 4. `div_fuel n M` total | proved | `fuel_total` |
| 5. `reify M ∈ 𝒱⟦U(Loop_Σ B R)⟧` | proved | `reify_compat` |
| 6. `total_every_run` unchanged | proved (its statement, unchanged) | `total_every_run_unchanged` |
| unknown 2: the residual | proved, runs `live 0` at every stage; no tied derivation | `prog_every_run`, `Run.lean` |
| unknown 3: placement | evidence at the `while` schema (`n = 0, …, 6`); simulation **not proved** | `Run.lean`, `sim_loop` (`sorry`) |

`iterate`, `div_fuel`, `reify` and the runtime's handler are terms over the existing machine (the
Z combinator, `hnd`, `perform`), so `Run.lean` runs them through the backend unchanged. B1 makes
`iterate` one constant with one machine step.

### Unknown 2

`Residual.lean`'s program allocates a cell, loops forever incrementing it, and is closed by
`div_fuel 3`. The cell is the loop's state and its residual: nothing drops it, and the close path
hands it back. The tick's `κ` is linear, so the loop is closed by `κ close`, a resume. The program
frees the cell and answers its count. Every run, under every allocator, continues to a count at
the empty memory (`prog_every_run`, by `fuel_total`, `cwp_iterate` and `cwp_bind`). The source,
closure and flat interpreters and WebAssembly each print `inr (inr (inr (inl ())))` (three) and
`live 0`. "The canceller sees `()`" is not touched: there is no cancel.

There is no tied derivation (`CDerivesAt`): `CDerives` has no rule for `iterate` or `div_fuel`,
which the design makes constants with their own rules. The derivation is B1's.

### Unknown 3

The placement is §3.2's. At the empty row, a forward move to a loop's head is an explicit
`tick ()`, and the move back is `iterate`'s own tick. Then `div_fuel n` runs `n` turns, as
today's machine observed by `driveE n` does. `Run.lean` runs the `while` schema both ways at
`n = 0, …, 6`, with the same answers. `sim_loop` states the simulation at that schema, and is not
proved. The design asks for more: joins, direct-style calls, the row, and the effects in order.
Each of those needs today's machine as a Lean term. Today's machine is `Frontend/Sugar.lean`'s
string templates (§9.2 defect 2). The counted programs, B2's acceptance, are listed in
`Placement.lean`.

## `[handle]` of another name: what the relation does not carry

`hnd_m H e`, `e` ticking, `H`'s clause for `m`. The handler forwards ticks: `e`'s tick stops the
whole, with continuation `hnd_m H K[n]`.

- **A clause that resumes `κ` in tail position** (`h_m (v, κ) ↦* κ (N v)`, `N v` not given `κ`)
  is proved (`handle_tail`). This is the class that lowers to a direct call. `N v` may tick. The
  candidate is the handled computations together with the resume frame around a computation of
  `cwp`. A `for` body that resumes is in this class, and so is an answering clause.
- **A clause given `κ`** to store or pass on is not proved (`handle_general`). The clause is
  opaque, and its relation (what the Fundamental Property gives it) asks `κ` to resume into
  `cwp`. Here `κ` resumes into `hnd_m H K[n]`, the object the coinduction is building, which is
  a member of the candidate and not yet of `cwp`. `unfold`'s rule excludes the same shape ("the
  step … cannot observe the codata it is building", SPEC §7), and the clause here does observe
  it. There are two known ways to carry it. Each puts a parameter into `𝒱⟦·⟧` at every thunk of a
  `Div` row, since `κ` is a value the clause may store:
  - **Parametrized coinduction**: the relation at a `Div` row carries an accumulator, and the
    clause's relation is given at every accumulator. See Hur, Neis, Dreyer, Vafeiadis, *The Power
    of Parameterization in Coinductive Proof*, POPL 2013. Monotonicity in the accumulator fails at
    negative positions, which is what a higher-order relation needs.
  - **Step-indexing at ticks**: `cwp_n` with `Closing` at `0`, the clause's relation at every
    index. Then the tail-resuming argument works at each index. `reify` must meet `ν`'s greatest
    fixed point, though. That needs `ν` indexed as well, or the open `WpChainCommutes` (SPEC §7).
  I have not derived `handle_general`, and I have not verified that any obstruction is real.

This decides what choice 3 must restrict (below).

## Choices 3 and 4: a coinductive `[handle]` rule

**The rule.** `[handle]` at a handled row holding `Div`, `tick` forwarded:

    Γ = Γ₁, Γ₂   Δ; Γ₁ ⊢ H : clauses at F_{Σ,Div} R   Δ; Γ₂ ⊢ e : F_{Σ, m:E, Div} A   m ≠ Div
    ───────────────────────────────────────────────────────────────────────────── [handle-div]
    Δ; Γ ⊢ hnd_m H e : F_{Σ,Div} R

and, for `div_fuel` and `reify` as ordinary handlers, the handler of `Div` itself:

    Δ; Γ₁ ⊢ H : (tick's clause, h_ret)   Δ; Γ₂ ⊢ e : F_{Σ, Div} A
    ──────────────────────────────────────────────────── [handle-of-div]
    Δ; Γ ⊢ hnd_Div H e : F_{Σ'} R           Σ' = Σ or Σ, Div

**Its obligations on FP and adequacy.**
1. `[handle-div]`, a tail-resuming clause: `handle_tail`'s argument, at every row. Here it is
   proved with the rest of the row linear. An abortive or affine operation of `N v` abandons the
   resume frame and `κ` with it, as Core's `[let]` side condition says. B1 needs the general row,
   the abortive and affine cases being Core's `ewp_handle` cases with the frame dropped or
   cancelled.
2. `[handle-div]`, a clause given `κ`: `handle_general`, which needs the parameter above in the
   relation, at every type, with every compatibility lemma restated over it. This is the cost.
3. `[handle-of-div]` with `Div ∈ Σ'` (choice 3's recommended restriction): the clause's own ticks
   are the result's. With a tail-resuming clause this is item 1 again, the tick as the handled
   operation. A clause that keeps `κ` is item 2.
4. `[handle-of-div]` with `Div ∉ Σ'` (`div_fuel` as an ordinary handler, a total result): the
   conclusion is a least fixed point from a greatest-fixed-point premise. It needs a measure the
   clause's state decreases at each *next*, and the clause must answer *close* where the measure
   ends. `div_fuel`'s counter is that measure (`fuel_total`'s induction on `n`). As a typing rule
   it is a termination premise, a variant on the handler's state, which the kernel has no form
   for. Without one it contradicts `total_every_run`, as §4.2 says.
5. Adequacy is unchanged in form: `runtime_every_run` and `fuel_every_run` read only `cwp`.

**Borrows.** Neither rule touches the borrow calculus. `tick` is linear, so it is in no
unwind-only row (`tick_not_unwind`). A borrow's callback never ticks, and no borrow frame spans
a segment. The frame lemmas are used within one segment, at `ewpTS`, unchanged (`Then.lean`
uses Core's `ewp_frame_then`). With the parameter of item 2, a mut cell whose payload is a thunk
of a `Div` row stores a parametrized predicate. Its frame is still entered and left within one
segment, at one parameter. That is a hypothesis, not checked.

**Cost against the constants.** The constants are built here: `div_fuel` (`Fuel.lean`, about 400
lines with its steps) and `reify` (`Reify.lean`, about 450). Each is a proof that reads its own
clause. `handle_tail` is about 300 lines and covers the tail-resuming class of items 1 and 3.
Item 4 needs a measure premise and its soundness: a new kind of typing premise. Item 2 is the
large one: a parameter through `vC`/`cC` and every lemma over them (`Core/Relation*`,
`Compatibility`, `Fundamental` and the files they feed), comparable to restating the
relation. So:

- **Choice 4: the constants (recommended, as the design says).** They need no parameter, and
  they are proved here.
- **Choice 3: a program's handler of `Div` typed only where `Div` stays in its row, and only at
  a clause that resumes `κ` in tail position.** That is the class proved. A handler of another
  name around a ticking computation needs the same clause restriction (`handle_tail`), unless B1
  takes on item 2. A clause that stores `κ` of a divergent computation then goes through `reify`
  (a loop value, consumed one observation at a time, as stored generators are today). This
  restriction is new, beyond §8 choice 3. It rejects a handler that stores `κ` around a ticking
  body (a scheduler that parks a divergent task) unless that program is written through
  `reify`. It needs a recorded decision (hard-stop item 4).

## Hard stops and defects

**Hard stops: none triggered.**
- *Cancel*: unknown 2 closes by `κ close`, a resume. No cancel answers a residual. Kill
  criterion 2 is not met.
- `div_fuel`'s counts: at the `while` schema, today's machine and the `Div` elaboration give the
  same answers at `n = 0, …, 6`. Not proved in general (unknown 3). Kill criterion 3 is not met.
- Kill criterion 1 (a step-indexed borrow frame) is not met: no step-indexing is used. The open
  case (`handle_general`) is reported above with what it needs.
- The clause restriction under choice 3 is a typing restriction to record, not a runtime rule.

**Defects and corrections.**
1. **§4.1's candidate relation is too weak for item 4** (`Plain.lean`). The fix is `Closing` in
   the tick's obligation. It strengthens the relation, and no target changes.
2. **`[handle]` around a ticking computation needs more than §4.2 says.** §4.2 has "FP and
   adequacy restated over `cwp` at rows that hold `Div`, by S0's lemmas". A clause given `κ` is
   not covered (above).
3. **`reify` needs the residual of a result**, `res : B ⊸ F_Σ R`. A computation may finish after
   a close, and `done b`'s close hands back `res b`. Today's terminal-before-the-first-state
   already hands back "the components of `v` that have no destructor" (SPEC §14). §3.2's table
   does not mention it.
4. **Core's frame lemmas are at `opTable T`.** `ewp_frame_plain_or` and `ewp_frame_then_or` are
   their proofs with one more case, a stop of an extra table that owes nothing to the least
   fixed point. B1 should state Core's lemmas at `opTable T ∨ Π` once, with the current ones as
   instances (*Generalize by deleting*), not keep two copies.
5. SPEC §19 *Divergence* says "there is no second fixed point: a greatest-fixed-point `ewp` would
   be a second mechanism for what `ν` already is". The design reverses this. B1 rewrites the
   paragraph.

## What B1 should know

- Use `cwp` with `Closing` (`Defs.lean`), not §4.1's candidate.
- The relation clause at `F_Σ A` with `Div ∈ Σ` is `cwp` at the rest of the row. Every Core rule
  at the rest of the row lifts (`cwp_of_ewp`), and the compatibility lemmas are `Rules.lean`,
  `Then.lean`, `Iterate.lean`, `Fuel.lean`, `Reify.lean`.
- Generalize `ewp_frame_plain`, `ewp_frame_then` (and `ewp_handle`, for `handle_tail` at every
  row) to `opTable T ∨ Π` in Core. Do not copy them.
- `[handle]` around a ticking body: decide choice 3 first (`handle_tail`'s class, or the
  parametrized relation).
- `reify` takes `res`, the residual of a result, read off its type.
- `div_fuel`'s state is a counter answered by a tail resume: the backend's direct call. `Run.lean`
  compiles the term as written today.
- The `cwp` side of FP for `iterate`'s step at a row: the step is an ordinary computation of `cwp`
  (`hstep`). A step that ticks is covered.
