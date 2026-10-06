# Targets: what you are asked to agree

This page summarises `DESIGN.md` and `Targets/Status.lean` so you can read and agree them. The
Lean in `experiments/Targets` states every target as a `def … : Prop`. It contains no `sorry`
and no forbidden axiom, and `lake build Targets` is clean. It proves the first wave of
restricted instances, mostly at Core's own world (σ = []). **Done itself is OPEN**: the tier-2
typing system `J₂` and the world `W` do not exist yet.

> [!WARNING]
> **Do not agree to these targets yet.** Three independent verifiers checked them. One passed
> with minor findings only. Two failed, reporting one blocker and six major findings, listed
> below. Each of these changes what "done" says, so the end state should be revised and
> re-verified before you agree it. The earlier statement review's ten major findings were
> answered in DESIGN.md, but the answers were never reviewed again.
>
> **Blocker**
>
> 1. **W's wp fixes an open design option (OQ-9).** Every `SemWorld`'s one-run wp (`wpGW`)
>    has Core's `↭` built in as a fixed conjunct (`ResU.UpdV`), not as a field. Under `↭` a
>    run cannot end holding a `mut` cell it created (LoopBorrow's `not_upd_of_new_mut`). So
>    no W can represent a lend carried open across a stop, which is OQ-9 option (a). That
>    silently picks the alternative, which the task forbade. DESIGN says the opposite: it
>    puts OQ-9 inside `held`/`Fam`/`Stop` and says the printed-shape frames "decide OQ-9 for
>    (a)" in one case. In that case `EndStateAt` could be unsatisfiable at every W. *Proposed
>    fix:* make the run-end relation a `SemWorld` field, pin it to Core's `↭` only on the nil
>    slice, and check the claim in Lean against an `at02`-shaped lend. The verifier has not
>    yet built that configuration in Lean.
>
> **Major**
>
> 2. **Exactly-once release in done has no content.** `ReleasedOnceAll` assumes its own
>    conclusion. `NoReuse` already gives at-most-once, and `Final`'s empty memory already
>    gives at-least-once. It is proved at *every* typing system and ignores typing, `SafeRuns`
>    and `Terminates`. The content that matters, at-most-once on runs that *reuse* locations,
>    is `ReleasedOnceReuse`, which sits beside done rather than in it. DESIGN D9, §9, I3 (a),
>    the notebook's `i3-drop.md` and `continuation-linearity.md`, and README rows A6/T4/T6
>    all still present `ReleasedOnceAll` as carrying the guarantee.
> 3. **Soundness with externs no longer comes from the fundamental lemma alone.** Correction
>    C2 is right that `ExternsMeet` admits an extern at any persistent type. As a result,
>    `SoundnessContracts` (a conjunct of done) has a route at W only through `Conservative W`.
>    That is A7 in full, which is beside done and which the survey calls open. This
>    contradicts "one proof method: the fundamental lemma" and DESIGN §4.1's "FL is the only
>    hard theorem". You are asked to choose a fix (decision 4 below).
> 4. **Row variables in the kernel (decision 62) are not required by any target.** Row
>    variables exist only as Lean-level families. The types (`VTy`/`CTy`) have no row-variable
>    former, there is no rule for generalising or instantiating rows, and `RowLink` never
>    connects the row algebra to `J`'s types. A kernel with no row variables meets done. The
>    prenex reading also ties the target to Core's current lack of a row former.
> 5. **T4 (zero cost) is not stated.** It is one of your four top-level theorems, and the
>    task said to state it and mark it out of the first pass. The file has only
>    `inductive LowClass`. "Effect handling is erased at runtime" has no target anywhere. The
>    stated reason is missing backend definitions, but W has the same problem and is handled
>    as an abstract parameter.
> 6. **Done contains conjuncts that constrain OQ-8 and OQ-9, and mixes the proof device into
>    the guarantees.** `Mono` rules out placing the future-world quantifier inside the binder
>    clause, unless `EwpMono` holds, and nothing proves it. `ShareResume` and `ShareCancel`
>    fix Core's placement of that quantifier. The printed-shape `FramesW` can decide OQ-9.
>    These are requirements on BoLo's text, not program-level guarantees, yet `FL`, `WLaws`
>    and `FramesW` are conjuncts of `Guarantees`. The task asked for the fundamental lemma at
>    W to be a *separate* target. *Proposed fix:* split done into a program-level end state
>    and a proof-device target, or state the option-sensitive conjuncts as disjunctions over
>    the options.
> 7. **The step-index audit can be fooled.** The audit is part of done (decision 7), but it
>    scans only definition bodies for recursors. A step index carried by an ℕ-indexed
>    inductive family passes it, and so does one carried by a library function outside our
>    modules. So "the audit passes" does not establish "no step-indexing". It needs to flag
>    ℕ-indexed inductives and come with a negative test (a toy step-indexed world it must
>    reject).
>
> The minor findings are listed at the end of this page.

---

## The definitions, in a few lines each

- **Effect.** An effect is a name together with a signature: a list of operations `A ↠^q B`.
  The qualifier `q` says how the continuation may be used: `lin` (exactly once), `aff` (at most
  once, otherwise cancelled) or `unr`. An operation with `B = 0` that is not `lin` is
  *abortive*. Names are static, one per handler site. A **row** is a finite list of operation
  signatures, read by first match. A **row variable** stands for a closed row and is
  constrained by a class and an admissibility condition. The rows form an effect algebra
  (Yoshioka–Sekiyama–Igarashi Def. 3.5) that must be *safe* (their Def. 5.1). (See major
  finding 4: J's types do not yet have row variables.)
- **Handler.** A handler is Core's `hnd (n, (h_ret, hs))`: a return clause plus one clause per
  operation, typed by `[handle]`. It is a model of its signature, and handling is the map that
  model induces. The machine's `[ret]`, `[op]` and `[unwind]` steps carry it out.
- **Suspension.** A suspension is the continuation value `κ = kappa n H K` that the `[op]` step
  hands to a clause. Its type `kTy` follows the qualifier: `U((B ⊸ F R) & ⊤)` at `lin`,
  `U((B ⊸ F R) & F 1)` at `aff`. A suspension can be **resumed** with an answer, or
  **cancelled**. Cancelling runs `cancelOf n H K`, which fires the frozen `[then]` finalisers
  (`Kont.fins`) innermost first. Nothing can forget a `lin`/`aff` continuation: discard is an
  explicit cancel.
- **Platform.** The platform is a comodel (Ahman–Bauer). It answers at the top the operations
  that no handler catches. It may only access its own state, never touches program memory, and
  serves linear, resuming data operations.
- **Effect safety (`EffSafe`).** A typed program at row `S` either runs to a value, keeps
  stepping, or stops at an operation of `S` that nothing catches. It never stops anywhere else.
- **Soundness (T1).** Take every allocator and every platform that keeps its protocol. Every
  run of a typed program is never stuck: no use after free, no double release, no unhandled
  operation. At a data answer, every run terminates with the memory empty. A program that
  returns a loop is safe at every finite prefix of its drive. Termination is claimed only at
  div-free answers, since div is an effect.
- **Finalisation exactly once.** Every allocated cell is released exactly once. On a cancel or
  an unwind, finalisers fire once each, innermost first (`FinaliserOrder`). No typed program
  can intercept a cancel (`NoInterception`). (See major finding 2: the conjunct in done that
  states this is currently empty.)
- **The invariant.** The invariant is W's family of configurations, `SemWorld.Fam`, which at
  Core is the typed worlds `TW`, together with what suspended computations hold
  (`SemWorld.held`). **Arising** says that every configuration a W-run ends in is a typed world
  over the visible frames plus the held ones, so `TW.inv` and `TW.valid` apply to it. This is
  "every wp run ends in a TW world plus TW.inv", extended to W.
- **W.** W is not built. It enters only as the parameter `M : SemWorld`, which has fields for
  the world, the stop condition, the relation at rows, `held` (OQ-9) and `payStk` (OQ-46).
  `coreW` is Core's relation, the instance with a one-point lend stack. (See the blocker: `↭`
  is fixed, not a field.)

## What "done" means

Done is `theorem endState_W : EndStateAt J₂ W Adm RF` at a **named** tier-2 typing system `J₂`
(the kernel's unr-free judgment) and a **named** world `W`, together with `audit_W`, the
step-index audit of W's definition, passing. `Adm` is the admissibility that OQ-56 settles, and
`RF` is the row form that OQ-13 settles.

`EndStateAt` consists of three parts:

- T0, the row-algebra conjuncts, and `AdmExtends`;
- the typing pins `Tier2Pinned`, `AcceptsTier2` and `I4a`;
- `Guarantees`, the program-level guarantees and the W-level device/interface at one fixed `J`
  and one fixed `M`.

The tier-1 milestone `Tier1End` is separate from done. It is the same `Guarantees` at Core's
typing and `coreW`, restricted to abortive rows.

**Status:** done is OPEN. `Tier1End` is OPEN, but it follows from two open statements,
`Adequate coreW` and `FinaliserOrder tier1` (`status_tier1End_of`). Every other conjunct of it
is proved.

## The targets

Worlds: **prog** means runs and typing only, with no semantic world; **W** means the parameter
`M`; **Core** means σ = [] (`coreW`/`tier1`). Status words come from `Status.lean`.

| id | one-line statement | world | status | depends on |
|---|---|---|---|---|
| **done** | `EndStateAt J₂ W Adm RF` + `audit_W` | W | OPEN | everything below |
| `Tier1End` | every guarantee for Core's typing at Core's relation, lends spanning abortive rows | Core | OPEN | `Adequate coreW`, `FinaliserOrder tier1` |
| **T1** `Soundness` | every run safe; data answers terminate with memory empty; driven loops safe | prog | return conjunct PROVED AT A RESTRICTION (`Platform.none`); full OPEN | FL + `Adequate` (`soundnessOfFL`, proved) |
| T1 `SoundnessContracts` | T1 with externs meeting their contracts, under platform operations | prog | OPEN | FL, `ExtPre`, `Conservative`, `Adequate` (major 3) |
| **T2** `Laws` | handler equations as contextual equivalences | prog, binary | stated, OPEN; out of first pass | binary world (named-only) |
| **T3** `Abstraction` | tunnelling, representation independence, encapsulation | prog, binary | stated, OPEN; out of first pass | binary FL (named-only) |
| **T4** `LoweringCorrect`, `ZeroCost` | lowering preserves output; handling costs no more than hand-written C/Rust | prog + backend | **not stated** (major 5); out of first pass | backend interpreter, reference encodings |
| T0 `RowAlgSafe`, `RowLink` | the row algebra is lawful and safe, and is the one typing uses | prog | PROVED AT A RESTRICTION (`orowRF`) | — |
| `AdmExtends` | admissibility contains R-CLOSEDOP | prog | PROVED AT A RESTRICTION (`admClosedOp`) | — |
| `Tier2Pinned`, `AcceptsTier2` | tier 2 has the spanning rules and types `at02`, `at04`, `at12`, `at17` | prog | OPEN (no tier-2 typing); the four terms run | `J₂` |
| `ExtendsNU`, `OutExtends` | the typing extends Core's unr-free rules and outlives judgments | prog | PROVED AT σ=[] | — |
| `ReleasedOnceAll` | exactly-once release on complete no-reuse runs | prog | PROVED for every `J` (**empty**; major 2) | — |
| `ReleasedOnceReuse` | exactly-once release on runs that reuse locations | prog | OPEN; beside done | `BinderMachine` |
| P2 `EffSafe` | stops only at an uncaught operation of the row | prog | PROVED AT σ=[] | — |
| I3.c `NoInterception` | no typed program catches a cancel | prog | PROVED AT σ=[] | — |
| I3.b `FinaliserOrder` | cancel/unwind fire finalisers once each, innermost first | prog | OPEN; two-frame instance PROVED | — |
| `FL` | every typing judgment holds in W's relation | W | PROVED AT σ=[] | `WLaws` |
| `Adequate` | a closed computation in W's relation runs safely and terminates | W | return conjunct PROVED AT A RESTRICTION (`Platform.none`); full OPEN | `WLaws` (`AdequateOfLaws`, OPEN) |
| `WLaws` | the laws every W satisfies (bounds, `Mono`, nil-slice shape, …) | W | PROVED AT σ=[] | — |
| **I1** | a suspension is a value of the resource world at its `kTy` | W | PROVED AT σ=[] | — |
| **I2** | capture and resume preserve the invariant, spanning lends included (preservation, no termination) | W | PROVED AT A RESTRICTION (abortive rows) | `Arises`, `FramesW`, `SpanBorrows` |
| **I3** (I3.a) | the cancel run preserves the invariant and leaves nothing newly held | W | PROVED at `coreW` (label says "restriction: nothing held"; minor) | — |
| **I4** (I4.a) | an answering effect's borrow form is typed by the borrow rules | prog | PROVED AT A RESTRICTION (tier 1, abortive rows) | — |
| `I4Typing`, `I4c` | the control form types its borrow form; the two are equivalent | prog / binary | OPEN; beside done / out of pass | OQ-1 |
| **I5** | capture laws: β, hiding (6.66 at W), frame | W | PROVED AT σ=[]; `I5beta` generic | — (η only in T2; minor) |
| P9 `LifetimeSound` | 6.60 at W at every type, suspension types included | W | PROVED AT σ=[] | `J.out` |
| P10 `Exclusive` | every reached configuration satisfies aliasing, counting held loans | W | PROVED AT σ=[] | `Arises` |
| P11 | `[handle]` sound at W; reduction is semantic identity | W | PROVED AT σ=[] | — |
| P14.b `ConservativeWB` | Core-valid values at row-abortive types stay valid in W | W | PROVED AT σ=[] | — |
| `Conservative` | the same at every type (A7 in full) | W | OPEN; at `coreW` PROVED AT σ=[]; beside done | — |
| `FreezeBinder`, `BinderMachine` | freeze as a binder: equivariance under renamings | W / prog | OPEN; beside done | — |
| `CancelCloses`, P8.b | a cancel ends every lend it holds; each continuation is used as its qualifier says | W / prog | named-only (no statement) | OQ-57, OQ-50 |
| step-index audit | no step index in W's definition | meta | passes on `coreW` (blind spots; major 7) | — |

## Deliberately out of the first pass

- **Binary and cross-language targets.** T2 (laws), T3 (abstraction), T4 (lowering and zero
  cost), I4.b's rejections and I4.c's equivalence. They are stated but drive nothing; T4 is not
  yet stated.
- **Multi-shot** (decision 63). Done pins only the unr-free fragment, W is unconstrained at
  resuming `unr` rows, and the survey's multi-shot programs are dropped.
- **Beside done (stated, not required).** The freeze binder (`EndStateBinder`), `Conservative`
  at every type, `ReleasedOnceReuse`, and `I4Typing`. `CancelCloses` and P8.b are named-only.
- **Scope limits of T1.** Main's row may hold only platform operations, so an error must be
  handled before the top (OQ-51 (a)); exit-with-error is not stated. Termination is claimed
  only at data answers.

## Decisions you are asked to confirm

1. **"vC/cC are the σ = [] instance."** DESIGN reads this as "the nil slice has Core's
   structure, and Core's relation embeds into W". It does not read it as an equivalence at
   every type, because that would put every tier-2 computation starting at σ = [] inside
   today's `cC` and so decide OQ-9 for (b). Was the equivalence meant?
2. **Conservativity's scope.** Done holds the row-abortive form (`ConservativeWB`), and the
   every-type form (`Conservative`, A7 in full) is beside done. Should done hold the
   every-type form? This interacts with decision 4.
3. **The freeze binder.** It is beside done, because the notebook lists its unifications as
   hypotheses to check. Should done require it once the form of its lifetime half is settled?
4. **Externs in T1 (major 3).** Choose one:
   - (a) done holds `SoundnessContractsAR`, externs at row-abortive types, which is proved
     from FL; the every-type form stays beside done.
   - (b) `Conservative` moves into done.
   - (c) `ExternsMeet` is restricted to the SPEC's extern types.
5. **Exactly-once release (major 2).** Should `ReleasedOnceReuse`, at-most-once on every run,
   move into done in place of the empty `ReleasedOnceAll`?
6. **Shape of done (major 6).** Should done split into a program-level end state and a
   separate proof-device target (FL, `WLaws`, `Mono`, `FramesW` at W)?
7. **T1's scope.** Is it acceptable that T1 covers only data answers, and only mains whose row
   is the platform's? The other option is to state an exit-with-error conjunct (memory empty
   at an unhandled raise, OQ-51 (b)) and soundness at any persistent answer.
8. **The survey.** The 1472-line `research/effects/survey.md` was committed on `targets` in
   0180b67. Should it stay?

## Minor findings

- `AxiomCheck` fails the build only on *theorems*. Proof-carrying `def`s are not checked. A
  manual scan of all 1824 constants found no forbidden axiom.
- `status_I3_core` proves the unrestricted `I3 coreW` but is labelled "PROVED AT A
  RESTRICTION". It should read PROVED AT σ=[].
- Targets declares names in Core's namespaces (`BoCa.Expr.renameLoc`, …) and imports other
  experiments, so future additions to Core could clash with these names.
- `UnwindOrder` covers only unwinds through contexts with no handler frame. It should use
  `K.Catches n = false`, or record this as a scope limit.
- `CancelOrder`/`UnwindOrder` are stated over platform-free `Steps` from empty memory, so they
  are vacuous for programs that perform platform operations. They should be over `PSteps P`.
- In `I4a`, `ImplTyped` is a dead hypothesis, and the non-vacuity witness exercises no
  operation.
- `AcceptsTier2` has no tier-1 rejection proved, so its discrimination is unchecked. Several
  reachability premises lack Lean witnesses.
- The notebook's P1 text was narrowed to data answers to fit the Lean, without recording this
  as a scope decision.
- η has no unary form in I5; it lives only in T2. Status, README and the I5 notebook do not
  say so.
- `FreezeBinder` has no instance half, and its lifetime half is forward instantiation, not
  equivariance under order-isomorphisms.
- `StopVisible` forces every lend that spans a stop into `held`, which is a representation
  choice.
- "No forget" for `lin`/`aff` continuations is not pinned. `J` is only bounded from below, so
  it could add weakening at thunk types without any conjunct failing.
- `DivFree` depends on decision 35 (divergence lives in `Loop`). Status should list that
  dependence.
