# Targets: what you are asked to agree

This page summarises `RESTRUCTURE.md` and `Targets/Status.lean` so that you can read and agree
them. The targets are now two systems and the rules of their interaction: an effect system (A), the
borrow calculus (B), the interaction (I), and our calculus as one instance of A. The Lean in
`experiments/Targets` states every target as a `def … : Prop`. `lake build Targets` is clean, with
no `sorry` and no forbidden axiom. The axiom check covers every theorem and definition, and the
step-index audit passes with its nine negative tests. It does not yet scan `Type`-valued
ℕ-indexed families (see the verification box). **Done itself is OPEN**: the tier-2 typing
system `J₂` and the world `W` do not exist yet.

> [!WARNING]
> **Verification of this restructure: NOT ready to agree.** Three independent verifiers checked
> the build. Two passed with minor findings only. One failed with a **blocker**. Until the blocker
> is resolved, the B5 route and the tier-1 guarantees below rest on a premise that Lean refutes.
>
> **Blocker: `BumpSim` is refutable as written** (`Targets/Base/Machine.lean:286`, `:309`).
> `BlocksAffine` reads `∀ ℓ n, … → ∀ j < n, g (ℓ + j) = g ℓ + j` with `n` unbound. Its docstring
> means `n` to be an array value's length. As written, it forces `g'` to shift every location
> above each named location by the same amount. Since the bump step must also avoid an arbitrary
> finite `X`, no `g'` exists at an ordinary reuse step. A verifier checked this in Lean:
> `¬ BumpSim` compiles with axioms ⊆ [propext, Classical.choice, Quot.sound], in the session
> scratchpad file `v/BumpSimCheck.lean` (heap `{5 ↦ loc 5}`, term `alloc ()`, `g = id`,
> `X = {3}`). Consequences:
>
> - `releasedOnceReuse_of_bumpSim` (`B/Routes.lean:163`) and `tier1Core_guarantees_of`
>   (`I/Combined.lean:219`) hold only from a false premise, so they establish nothing yet.
> - The claims "B5 PROVED from B4′ given `BumpSim`" and "B's tier-1 guarantees follow from
>   adequacy and `BumpSim`" overclaim. They appear here, in `Status.lean` (the B5 row, the Done
>   paragraph, `status_tier1Core_guarantees_of`), in `README.md` (lines 80 and 112), and in the
>   notebook (register P1, `properties/soundness.md`, `system-b.md`, `tracks/log.md`). Those
>   files are **not yet corrected**. This page is.
> - B5's statement (`ReleasedOnceReuse`) is not affected.
> - Fix: tie `n` to an array value `(ℓ, c)` that the term or a stored value mentions. Then
>   re-check `bump_follows` and `releasedOnceReuse_of_bumpSim`, and add a Lean sanity lemma
>   showing that `BumpSim`'s conclusion can be met at a reuse step.
>
> **Minor verification findings**, all open:
>
> - *The audit skips `Type`-valued ℕ-indexed families.* `familyAudit` (`Audit.lean:177-194`)
>   keeps only `Prop` families. A scratch world that uses
>   `inductive LaterT : ℕ → Type` through `Nonempty` passed every report. Every `Prop`-valued
>   variant the verifier tried was caught. Fix: drop the filter or report these families
>   separately, and add a tenth negative test.
> - *`Report.rejects` is unused and says nothing* (`Audit.lean:313-316`). It is true for every
>   world whose closure reaches Core, `coreW` included. The per-constant negative-test check is
>   sound.
> - *Stale names.* `Instance/Rows.lean:102` cites `EndStateAt` (now `I.Combined`).
>   `foundations/freeze-binder.md` still says `EndStateBinder` (now `CombinedBinder`).
> - *`AxiomCheck.lean`'s docstring overclaims.* It says every source theorem has a `#print`
>   line, but four do not: `eq_two`, `eq_three`, `eq_four` and `eq_hole_of_plug_prim`. The
>   `run_meta` covers them, so the gate itself holds.
> - *Status understates hypotheses.* The "E3 needs divergence" row omits that
>   `divInTypes_of_loops` also takes Safety (S2) and `DataDiv`.
> - *Abstractly, divergence shows in types only on the pure row* (`DataDiv`, E3f). This is weaker
>   than decision 35. It holds at `ourInst`. E3f types `hof` with its own `∃ A'`, so it does not
>   use E1's one typing (Q3).
> - *Most feature justifications are prose.* Lean checks only row variables
>   (`not_*_of_monoCallback`) and divergence (`not_loops_of_total`). Deep handlers (E4, E5),
>   linear continuations with cancel (E7–E9) and S6's witnesses R1–R4 have no lemma.
> - *The extern hypothesis is stated against W's relation*, and W is unbuilt (Q8).
> - *S4's store-free `capture` excludes OQ-50 (b)*, which needs your call (Q9).
> - *The composite acceptance list lacks `reconB` and the real async-read-into-buffer program.*
>   `at04` stands in for the latter until OQ-56 is chosen (Q5).
>
> **Apart from the verification**, five more things are open. The first three are review
> findings and departures that no one has checked. The fourth is what the build has not reached.
> The last is the earlier minor findings.
>
> **1. The third review's findings, answered in the design and not reviewed again**
> (RESTRUCTURE §9.0 and §Unresolved U.1). The build implements each answer as written.
>
> - *Blocker: A's matchers never matched a driven configuration.* Answer: the driver is a
>   context, `driveF`, with `plug driveF M = drive M`, catching and stopping nothing. Built in A's
>   laws. **Unchecked at our instance**: the bridges that would prove `Congr` and `DriveLaws`
>   there, the drive-phase run correspondence and `effSafeDriveOfFL` are not built.
> - *Major: E6 used `PolyUseOpen`, which allows the accidental handling E6 excludes.* Answer:
>   `PolyUseLacks`. Built, and `not_tunnel_of_monoCallback` is proved against it. **Unchecked**:
>   `fwrap`'s type at `J₁`.
> - *Major: done did not bind the effect context Ξ or the row form `RF`.* Answer:
>   `Combined RF J M Adm c`, with A's properties at every admissible Ξ (`AdmEff`). Built.
>   **Unchecked**: whether `AdmEff` is the right range.
>
> **2. `FIX-RUN-END.md`'s two major findings, revised and not reviewed again** (its §Unresolved).
> Its recorded text chose a representation for OQ-9 (a); it now names both. Two impossibility
> claims about a 6.64 lend had no Lean; the configuration is now built at AT02's run
> (`at02_imm_end`).
>
> **3. The build's departures from the design, not reviewed** (RESTRUCTURE §Unresolved U.2, 30
> items). These change what a target says, and you should look at them before agreeing:
>
> - A's laws that assert a step (`AppLaw`, `LoopLaws`, `DriveLaws`, `HandlerSem`) hold only at
>   configurations reached from a typed closed program (`Live`). A's values include variables, and
>   no machine steps an open redex.
> - Two abstract lemmas take one more hypothesis each: `divInTypes_of_loops` takes `RowAlgebra`;
>   `not_reconciler_of_monoCallback` takes `LiftExt`, which our rows meet.
> - At our instance the driver is a Core frame around the program, not a phase mark. A phase would
>   be lost in a stored finaliser.
> - `BumpSim`, the machine lemma B5 rests on, has a body of the builder's: a finite set the bump
>   step avoids, and maps that move array blocks as blocks. That body is refutable as written
>   (the blocker above).
> - A₃'s `LoweringCorrect` and `ZeroCost` are relational, through `PlatformSim`. `refCost` is
>   `(0, 0)` with no reference program written to check it.
> - `Tier2Programs` has five programs: `reconB` is not built.
>
> **4. A is checked at no instance of ours** (RESTRUCTURE §Unresolved U.3).
>
> - Proved: A's non-vacuity lemmas, abstractly at every instance. An instance with no typing,
>   with no effects, without effect polymorphism, or total fails the (E) properties that need each.
> - Not built:
>   - the semantic bridges from Core to A's laws, so it is not verified that our calculus meets
>     A's (S) properties;
>   - §6.1's concrete lemmas: that today's kernel fails E1, E2, E6 and E10
>     (`monoCallback_tier1Open`), that tier 1 rejects the tier-2 programs, that R1–R4 break S6 at
>     our machine, and the positive (E) runs.
>
> **5. Minor findings still open.**
>
> - Targets declares names in Core's namespaces (`BoCa.Expr.mapLoc`, `BoCa.Expr.MentionsLoc`, …),
>   so a future addition to Core could clash with them.
> - In `I4a`, `ImplTyped` is a dead hypothesis, and the non-vacuity witness exercises no operation.
> - No tier-1 rejection of the tier-2 programs is proved, so `Tier2Programs`' discrimination is
>   unchecked.
> - η has no unary form in I5; it lives only in A₂'s binary laws.
> - `FreezeBinder` has no instance half, and its lifetime half is forward instantiation, not
>   equivariance.
> - `DivFree` reads decision 35 (divergence lives in `Loop`); its docstring says so, and
>   RESTRUCTURE §7 Q3 asks whether that is the intended reading.

---

## The two systems, in a few lines each

### A: an effect system, on its own

A is judged on its own terms, with no borrows in sight. An `EffectSystem` is a call-by-push-value
calculus over an effect algebra (Yoshioka–Sekiyama–Igarashi Def. 3.5). It has handlers,
continuations that are resumed or cancelled, finalisers, a loop vocabulary with the runtime's
driver, a labelled machine and a typing.

- **(S) soundness**, upper bounds that say nothing goes wrong:
  - S0, the machine's shape and the let law;
  - S1, the row algebra (lawful, safe, rows as sums of signatures);
  - S2, safety, and termination at data answers on the pure row;
  - S3, effect safety;
  - S4, the handler laws in every context, deep;
  - S5, cancellation as SPEC §19 builds it: finalisers innermost first, each once, the first
    outside error re-raised, no interception;
  - S6, linear and affine use of continuations, observed from the run.
- **(E) expressiveness**, lower bounds that say what must be accepted and run. E1–E10 are
  concrete programs with their answers and observable traces, and schemas of effect polymorphism
  in Zhang–Myers' shape:
  - E1, no colouring;
  - E2, higher-order polymorphism;
  - E3, loops and the driver;
  - E4, deep handlers;
  - E5, nested handlers;
  - E6, tunnelling;
  - E7 and E8, the cancel and unwind policies;
  - E9, stored continuations;
  - E10, the reconciler.

  A decided feature enters A only through an (E) property that needs it.
- **Read in good faith.** The targets state what we are building, as the literature states its
  theorems. A contrived instance that would meet one is not a finding (RESTRUCTURE, introduction).

### B: the borrow calculus, given

B states BoLo's guarantees over a typing system and a borrow world `BWorld`, which has borrow
fields only:

- B0, BoLo's programs stay typed;
- B1, the fundamental property;
- B2, adequacy;
- B3, no use after free and no double free;
- B4, leak freedom;
- B4′, B3 and B4 with externs meeting W's contract;
- B5, release exactly once, location reuse included;
- B6, exclusive mutable borrows;
- B7, lifetimes respected;
- the bounds.

Each is proved at BoLo by citing `Core` and `Paper`, at the restrictions in the table below.
"Nothing breaks the borrow calculus" is `B.Guarantees`. **B5 has content now**: every complete run
is, step for step, the image of a run that reuses no location (`ReleasedOnceReuse`).
`ReleasedOnceAll`, which done used to hold, is a tautology about runs and is kept only as a lemma.

### I: the interaction

I is the only place where A and B meet. Its world `SemWorld` extends `BWorld` with what
suspensions hold, the stop condition and the continuation's share. I states:

- how rows are read in the world (`Bounds`), and what the world reaches (`Interface`);
- what the composite's typing must contain (`Pins`, with I4: answering effects are borrows);
- the composite's programs (`Accepts`) and its rejections (`Rejects`);
- the combined theorem.

Every conjunct that would fix an option of OQ-8 or OQ-9 is in the **proof device**, beside done,
so done picks neither.

### The Instance: our calculus as one instance of A

`ourInst RF Ξ J` reads Core as an `EffectSystem`, at a row form `RF`, an effect context Ξ and a
typing system `J` over open types with row variables. `tier1Open` is today's kernel over those
types, and its reading is exactly today's unr-free rules (`tier1Open_read`).

## What "done" means

```lean
def I.Combined (RF : RowForm) (J : OurTyping RF) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  (∀ Ξ, AdmEff Ξ → (ourInst RF Ξ J).Props)   -- nothing breaks the effect algebra, whatever effects are declared
  ∧ B.Guarantees J.read M.toBWorld            -- nothing breaks the borrow calculus
  ∧ Bounds M ∧ Interface M                    -- the interaction's option-neutral rules at the world
  ∧ Pins J Adm c                              -- what the composite's typing must contain
  ∧ Accepts J.read c ∧ Rejects J.read         -- the composite's programs, and the rejections that pin soundness
```

- **Done** is `Combined orowRF J₂ W admClosedOp .any` at a named `J₂` and a named `W`, with
  `audit_W`. It is fixed at `admClosedOp` until OQ-56 is chosen, and at `orowRF` until OQ-13's
  remaining question is answered.
- **Tier 1** is `Combined orowRF J₁ coreW admClosedOp .abortive`. `J₁` is today's rules with row
  variables, because A's (E) properties need effect polymorphism at every tier (Q1 below).
- **Status.** Done and tier 1 are OPEN. The restricted reduction `Tier1Core`, at today's kernel
  and Core's world, has its world conjuncts and device proved. `tier1Core_guarantees_of` derives
  B's guarantees there from adequacy at BoLo and `BumpSim`. **`BumpSim` is refutable as written**
  (the blocker above), so the guarantees there are not established. It also lacks A's (S)
  properties at our instance and `I4a` at today's unr-free kernel.

## The targets

Status words come from `Status.lean`. **σ=[]** is Core's relation and typing; **generic** is every
world or typing system; **every instance** is every `EffectSystem`.

| system | target | status |
|---|---|---|
| A | S0–S6, E1–E10, `Props` | stated; at our instance OPEN (the bridges) |
| A | an instance that types nothing, has no effects, lacks effect polymorphism or is total fails the (E) properties that need each; effect safety has teeth | PROVED (every instance) |
| A | A₂ (binary laws, abstraction), A₃ (erased lowering, zero cost) | stated, out of the first pass; A₃'s reference programs not written |
| B | B0, B1, B6, B7, the bounds | PROVED AT σ=[] |
| B | B2, B3, B4 | PROVED AT A RESTRICTION (no platform operation, data answers); in full OPEN |
| B | B4′ (externs at W's contract) | PROVED (generic, from B1 and B2) |
| B | B5 | statement not a tautology (`not_releasedOnceReuse_staleFree`); the route `releasedOnceReuse_of_bumpSim` rests on `BumpSim`, which is **refutable as written** (blocker above); B5 NOT established |
| I | `Bounds`, `Interface`, the device at `coreW` | PROVED AT σ=[] (abortive rows) |
| I | the corollaries of `Combined`; a reachable leak breaks it | PROVED (generic) |
| I | the composite programs | run by the interpreter (evidence); `CompositeT1` at tier 1 PROVED AT A RESTRICTION; `Tier2Programs`, `Rejects` at a typing system OPEN |
| I | `I4a` | PROVED AT A RESTRICTION (tier 1, abortive rows) |
| Instance | `tier1Open.read = tier1NU`; A's syntactic laws at our instance; our rows' algebra | PROVED |
| Instance | A's semantic laws at our instance; today's kernel fails E1, E2, E6, E10; R1–R4 | OPEN |
| meta | the step-index audit at `coreW`, nine negative tests | passes |

## Deliberately out of the first pass

- **Binary and cross-language targets**: A₂ and A₃, I4.c.
- **Multi-shot** (decision 63): the composite's typing is unr-free, and the survey's multi-shot
  programs are dropped.
- **Beside done, stated and not required**: the proof device; the run-end laws; the freeze binder
  (`CombinedBinder`); `Conservative` at every type; `I4Typing`; `FLOpen`.
- **Not built in this pass**: `W` (and `audit_W`); `J₁` and `J₂`, which wait on Q1 and Q2.

## Decisions you are asked to confirm

From RESTRUCTURE §7.

1. **Tier 1 needs row variables.** E1, E2, E6 and E10 are A properties, so tier 1's typing is
   `J₁`: today's unr-free rules over open rows with a rank-1 row `∀`, and no spanning. Is `J₁` the
   intended tier-1 milestone, or should E1, E2, E6 and E10 wait for tier 2?
2. **Rank.** Done requires rank 1, and no polymorphism over value types. Should done add a rank-2
   program, or does rank n stay with OQ-13?
3. **Loops.** Is "a loop runs without bound only at the top, under the runtime's driver" the
   intended reading? Should divergence be a row effect, so that E1's one typing serves div
   callbacks? `DataDiv` claims termination only at data answers on the pure row; under "codata"
   it would become every row.
4. **B5 and OQ-43.** B5 is in done, and that excludes OQ-43 (a) for done. The intended route is
   the step-for-step simulation `BumpSim`. **As written, `BumpSim` is refutable** (blocker above),
   so what B5 costs is not known until `BlocksAffine` is restated and the route is re-checked.
   Confirm that B5 belongs in done. Do not read this as a confirmed one-lemma cost.
5. **OQ-56.** Done is fixed at `admClosedOp`. When OQ-56 is chosen, should done move to that
   `Adm`, and `asyncRead` join `Tier2Programs` (with `at04` its stand-in until then)?
6. **"No sum for failure."** A carries failure as an effect at an unchanged answer type. Is #168's
   "no API returns a sum for failure" outside A?
7. **The earlier `AGREE.md` decisions.**
   - Positions the design takes, which you are asked to confirm:
     - externs carry W's contract as a stated hypothesis, `ContractsW` (old AGREE 4, Q8 below);
     - B5 is in done (old AGREE 5);
     - done is split from the proof device (old AGREE 6).
   - Still open, unchanged:
     - the σ = [] reading (old AGREE 1);
     - conservativity's scope: done holds no conservativity statement, `ConservativeWB` and
       `EmbedsNil` are in the device, and `WBCore` is a companion lemma (old AGREE 2);
     - the freeze binder beside done (old AGREE 3);
     - T1's scope: data answers, with main's row the platform's (old AGREE 7);
     - whether the survey stays on `targets` (old AGREE 8);
     - whether `UpdReclaim` belongs in done (old AGREE 9);
     - the `→` half of the nil-slice `Upd` pin, which constrains OQ-44 (old AGREE 10).
8. **Externs at resuming rows.** Their contract is W's, as a stated hypothesis. Is that the
   intended reading of "outside the proofs by design"? The SPEC's row-abortive externs at Core's
   contract follow from done together with the device's `EmbedsNil`
   (`soundnessContractsAR_of_combined`), not from done alone. Is that acceptable?
9. **OQ-50.** Done states the continuation's use count (S6). With S4 and `capture` as a value,
   that excludes OQ-50 (b), the one-shot-cell machine. Confirm, or should A carry the
   continuation's cell?
