# 99 · The register of open questions

Every open question of the specification, boxed, with a stable id. This file is the register:
sections cite a question by its id and never restate it, and a new question is added here first
(00 §7). The named restrictions that the defaults impose are 00 §7.2.

**Tags.** **[user decision]**: settled by the user's decision. **[settle by proof]**: settled by
a named Lean `def … : Prop` proved or refuted, or by a configuration built in Lean with every
hypothesis discharged. **[settle by literature]**: settled by reading a primary source. A
question with two tags needs both, in the order its *What settles it* gives.

**Cross-references.** "audit Q*k*" is question Q*k* of `docs/effects-audit.md` §7; "critic *k*"
is correction *k* of the audit's critic, carried as 00 §0.3; "audit M*k*", "m*k*", "C*k*" are
the audit's findings. The audit's Q1-Q7 are OQ-1 to OQ-7. "Carried by" names the sections whose
constructs the question bears on (00 §8).

**Order of work.** Unknowns first. Two probes come before any other relation work,
and neither depends on the other:

1. OQ-9's: one Lean configuration at `[handle]` + cancel over an open **6.64** frame (05 §12.1).
   It informs OQ-10, OQ-57, OQ-2 and OQ-33. The 6.65 configuration (05 §12.2) is OQ-44's probe
   and comes after it.
2. OQ-58's: a thunk built at `σ = []` forced at a one-entry stack (`def NilAgreesU : Prop`,
   05 §7 T-NIL). It decides whether Core is the `σ = []` instance of the relation at `W` at all.

OQ-8 is settled before any relation work at `W`, and OQ-58 is part of its criterion (i). OQ-15 and
OQ-67 are raised in priority because R-HDIV restricts the reconciler chain (01 §3.2, U5); OQ-61 because
R-NOSELFROW restricts the asynchronous program (U7). The user decisions
with the widest reach are OQ-2, OQ-3, OQ-4, OQ-1 and OQ-15.

---

## 1. The table

| OQ | question | tags | cross-ref | carried by | blocks | settled by | user decision? | default if unresolved |
|---|---|---|---|---|---|---|---|---|
| [OQ-1](#oq-1) | One signature, two implementations: how answering and control handlers relate | [settle by proof] [user decision] | audit Q1; critic 1 | 02 | K-CAP, K-SWAP, K-COMODEL, D-COMODEL, T-COMODEL, L-STATE, L-RUN, L-INTER, L-TAIL, T-ELAB; which effects colour a function type (U7) | `def AnsweringIsTailHandler : Prop` proved or refuted, then the user's choice of colouring | yes | (b) both primitive, one protocol |
| [OQ-2](#oq-2) | Tier 1 or tier 2 first | [user decision] | audit Q2; critic 2 | 01 | K-BOR callback rows, K-OP across a borrow, D-STOP, `σ` in D-W, T-FRAME at resuming tables, L-BOR resuming half, L-BETA at `W` | user, after the OQ-9 probe and OQ-8 | yes | (a) first lift at tier 1 under R-T1; the specification is stated without R-T1 |
| [OQ-3](#oq-3) | Does a handler site open a lifetime? | [user decision] [settle by proof] | audit Q3; critic 1 | 03 | K-HND, D-W, D-ORD, T-FRAME at depth, OQ-14, OQ-28 | a configuration of a handler between two lenders at (a) and (b), then user | yes | (b), as R-MID |
| [OQ-4](#oq-4) | Is a binary relation over Core's world in scope? | [user decision] [settle by proof] | audit Q4 | 06, 07 | L-HUNIQ, L-HFUSE, L-HCORR, L-STATE, L-TENSOR, L-ETA, L-HIDE, L-INTER, L-NU, L-NAH, T-ABS, T-BINFP, T-SOUND | user; per-law check of TwoRun's route | yes | (b) every law stated; binary halves not on TwoRun's route marked not proved |
| [OQ-5](#oq-5) | Standing of EffModelRel | [user decision] | audit Q5 | 06, 08 | 06's citations; 08 §3.2 | user | yes | (a) evidence, with a banner |
| [OQ-6](#oq-6) | Typed role declarations or shape recognition | [user decision] | audit Q6 | 08 | 08 only; checklist C-7 | user | yes | (b) shape recognition, ambiguity rejected |
| [OQ-7](#oq-7) | Finalisers at a non-abortive table | [user decision] [settle by proof] | audit Q7 | 03 | OQ-41, OQ-65, K-THEN, K-FINR, K-BOR unwinding half, K-SWAP unwinding form, K-NU (effectful `Aff`), D-DTOR, L-W, T-FIN, L-ASYNC (a parked queue) | T-FRAME at a resuming `TableOK` table, then user | yes | (b), as R-FINAB |
| [OQ-8](#oq-8) | Where the future-world quantifier sits; the representation of entries; `σ.WF` (six candidate clause sets, 05 §8, among them (b0) = `vRLk` as built) | [settle by proof] | critic 3 | 05 | D-REL, D-ORD, D-SHARE, D-KAP, D-W, D-SEM, T-MONO, T-NIL, T-FP, K-BOR, OQ-2 | `def QuantPlacementAgrees (X Y) : Prop` per pair, with criteria (i)-(iv) (05 §8; criterion (i) is OQ-58), or a separating configuration | no | none: the re-index does not start |
| [OQ-9](#oq-9) | Open 6.64 frames handed to a continuation that is cancelled, dropped or resumed between lenders | [settle by proof] | critic 4 (first unknown) | 05 | D-STOP, D-W, OQ-44, OQ-57, D-OWED, K-CANCEL, K-KONT, T-STOP, T-LEAK, T-FIN, T-FRAME, OQ-2, OQ-10 | first probe `def OpenFrameCancel : Prop` at a 6.64 frame (05 §12.1), then `OpenFrameRaise`, `ResumeBetweenLenders` | no | stop unchanged; R-T1 |
| [OQ-10](#oq-10) | The form of the relativised stop | [settle by proof] | critic 4 | 05 | D-STOP, D-WPG, D-EWP, T-STOP, every T-COMPAT row of an effect rule | OQ-9's probe, then T-STOP; SPEC entry E-W first | no | stop unchanged |
| [OQ-11](#oq-11) | Are laws stated over `W`, or at `σ = []`? | [settle by proof] | critic 5 | 05, 06, 07 | every L id, T-MODEL, T-REN | per law, a statement over `W` or a survival lemma from T-NIL and T-MONO | no | (a) stated over `W`; (c) marked where only the `σ = []` proof exists |
| [OQ-12](#oq-12) | Operations that take computations (higher-order and scoped effects) | [user decision] [settle by literature] | decision 57 | 01, 02, 03 | K-SIG (parameter types), K-SCOPE (03 §9.1), L-ALG at such operations, L-SCOPE, OQ-59 | literature check of the options' sources, then user | yes | (a), as R-FO |
| [OQ-13](#oq-13) | Effect polymorphism: a meta-index or an object of the calculus | [user decision] | decision 57 | 02, 03, 07, 08 | O-JDG, K-ROW, K-REN, K-BOR, K-ROWABS, T-REN, L-NAH, T-ELAB, first-class row-generic values, polymorphic recursion across rows, the reconciler chain's generic combinators (U5, 08 §9.1) | user, with T-REN's and (a')'s costs known | yes | (a), as R-NOROWVAR (per-row derivations, no relating theorem beyond renaming) |
| [OQ-14](#oq-14) | Static names or generative instances | [user decision] [settle by proof] | — | 02, 03, 07 | K-NAME, L-NU, L-NAH, T-ABS, recursion through a site | user; for (b), a stale-label configuration at `W` | yes | (a), as R-STATIC |
| [OQ-15](#oq-15) | The kernel reading of divergence | [user decision] [settle by proof] | SPEC entries 13, 19, 20 | 01, 03, 06 | K-DIV, K-NU, K-HDIV, L-DIV, T-TOTAL, O-EQ (the observation) and every law's binary form, OQ-63, OQ-67 | user between the readings; K-HDIV's obligation is OQ-67 | yes | (a) codata; K-HDIV specified in both readings |
| [OQ-16](#oq-16) | Is multi-shot free? | [settle by proof] [settle by literature] | — | 01, 03, 06 | K-KONT, L-P, L-ND, L-NU, T-LOWER's copy class | a census of every rule, law and obligation that mentions `unr`; a check against Affect (POPL 2025) | no | (a) keep `unr`; laws proved at `lin`, `aff` |
| [OQ-17](#oq-17) | The relevant qualifier | [user decision] | — | 02, 03 | O-QUAL, K-KONT | user, when a program needs it | yes | (a) not provided, as R-NOREL |
| [OQ-18](#oq-18) | Sum, tensor, and threads | [user decision] [settle by literature] | critic 6 (threads) | 01, 06 | K-ROW, L-SUM, L-TENSOR, L-SIGNAL, L-ASYNC, OQ-61, OQ-66 | user, at each thread-facing choice | yes | (a) sums; disjoint capabilities tensor; cancel uninterceptable and finalising |
| [OQ-19](#oq-19) | The meaning of "comodel" for a capability | [user decision] | — | 02, 05 | OQ-34, K-COMODEL, D-COMODEL, T-COMODEL, K-HOST | user | yes | (a) state access only |
| [OQ-20](#oq-20) | A co-operation whose callee performs | [settle by proof] [user decision] | U5 | 03, 08 | K-SWAP, K-SWAPΣ, K-COMODEL, T-COMODEL, a fallible capability (the reconciler's `Kube`) | compatibility of (b) or (c) at `W`, then user | yes | (a), as R-PURESWAP |
| [OQ-21](#oq-21) | What a finaliser may perform, and the cancel error policy | [user decision] | — | 04, 06 | K-THEN, K-CANCEL, D-DTOR, L-SIGNAL, L-W | user | yes | (a) as built |
| [OQ-22](#oq-22) | Equations in a signature | [user decision] | — | 02, 06 | K-SIG, K-THEORY, L-HCORR, L-STATE, L-ND | user | yes | (a) the form; no kernel theory carries equations until needed |
| [OQ-23](#oq-23) | Is lowering correctness a theorem? | [user decision] | decision 48 | 08 | T-LOWER | user | yes | (a) per-class laws, counts, reports |
| [OQ-24](#oq-24) | An abortive payload that owns a resource | [settle by proof] [user decision] | #215 | 03, 04 | K-RAISE, D-OPTAB, L-EXC | compatibility of `[raise]`, `[finalise]` at (b), then user | yes | (a), as R-NOOWNERR |
| [OQ-25](#oq-25) | Handler state | [user decision] | — | 03 | K-HND, K-COMODEL, T-LOWER | user, with OQ-1 and OQ-9 | yes | (a) state passing |
| [OQ-26](#oq-26) | Shallow handlers | [user decision] | — | 03 | K-HND, K-NU, L-YIELD | user, when a program needs it | yes | (a) `ν` only, as R-DEEP |
| [OQ-27](#oq-27) | η with cancel at an affine operation | [settle by proof] | — | 04, 06 | L-ETA | a typed term in `CDerives`, or `def ForwardCancelTerm : Prop` refuted | no | L-ETA stated at `lin` only, as R-ETALIN |
| [OQ-28](#oq-28) | How a stored continuation is bounded | [settle by proof] | — | 03 | K-KONT, K-GEN, K-FTY, OQ-14, E-GEN, OQ-67 | compatibility of storing and resuming a `[@c]`-boxed `κ` at `W` | no | (a) `[@c] U C` |
| [OQ-29](#oq-29) | An operation that answers a borrow into the handler's state | [settle by proof] [user decision] | #160 | 02, 03 | K-SIG (answer types), K-CAP, K-BORANS (03 §9.4) | compatibility of K-BORANS at `W`, then user | yes | (a), as R-NOBORANS |
| [OQ-30](#oq-30) | Allocation and I/O in the calculus: which presentation | [user decision] | U20 | 01, 03 | K-HOST, K-ALLOC (03 §9.5), T-ADEQ for host programs, U7 | user; K-ALLOC's obligations are OQ-68 | yes | (b') allocation a capability; lift after OQ-68 (R-ALLOCORACLE until then) |
| [OQ-31](#oq-31) | The cut-offs that keep the relation step-free | [user decision] | TR §16.5 | 01, 03, 05 | T-DEF, K-SIG, K-FIX, K-NU, L-ASYNC (OQ-60) | user | yes | (a) keep all five, as R-NONEGREC |
| [OQ-32](#oq-32) | The TR's moded calculus and the kernel | [settle by proof] | audit M14 | 08 | 08; K-GRADE | a per-fix table, each row checked against a configuration | no | (a) |
| [OQ-33](#oq-33) | How the hard-stop rule applies under this specification | [user decision] | critic 2 | 01 | OQ-2's milestones; the issue plan's gate before lifting R-T1 | user | yes | (a) with (c) |
| [OQ-34](#oq-34) | Is the BoLo world itself a comodel (the heap-runner architecture)? | [user decision] [settle by literature] | — | 01 | K-HOST, OQ-19, OQ-30 | user; for (b), a literature check (PLDI 2022) and the host protocol at `W` | yes | (a) neither depended on nor excluded |
| [OQ-35](#oq-35) | Are operation types closed in lifetimes? | [settle by proof] [user decision] | audit M13 | 02, 03 | K-SIG, K-NAME, K-HND, K-OP, K-NU, OQ-29, OQ-31, T-DEF, T-CONS, T-REN | census; `def ReentryLifetimeOpen : Prop`; then user | yes | (b) as built, no premise |
| [OQ-36](#oq-36) | How the typing judgement identifies equal rows inside types | [settle by proof] | — | 02 | K-ROW, K-FTY, `[sub]`, T-CONS, T-REN | conservativity of the chosen option; for (b), the congruence lemma | no | (a) canonical rows |
| [OQ-37](#oq-37) | Handler carriers at every computation type | [settle by proof] [user decision] | — | 02, 03 | K-MODEL, K-HND, K-KONT, K-CARRIER (03 §9.3), T-MODEL, OQ-25, T-LOWER | `ewp_handle`, `handle_compatC` at `S ⊸ F_Σ R` and `C & D`, then user | yes | (b), as R-RETCARRIER |
| [OQ-38](#oq-38) | Is site freshness a premise of `[handle]`? | [settle by proof] [user decision] | decision 57 | 02 | K-NAME, K-REN, T-NAH, T-ABS, L-NAH | `def AccidentalHandlingTyped : Prop`, T-REN's cost, then user | yes | (b) freshness in the elaborator |
| [OQ-39](#oq-39) | Qualifier subsumption in `[sub]` | [settle by proof] [user decision] | — | 02 | K-ROW, `[sub]`, L-ALG at mixed qualifiers | compatibility of (a) at `σ = []`, then user | yes | (b) exact qualifiers, as R-EXACTQ |
| [OQ-40](#oq-40) | The syntactic row class of a borrow callback | [settle by proof] | audit C4 | 03 | K-BOR, K-CAP, L-BOR, T-SUMOK, OQ-2, OQ-56 | `theorem borOK_tableOK` at the chosen class | no | (a), the full class `Σ.NZ`; with R-T1 and R-CLOSEDOP imposed it is `Row.Unwind x` |
| [OQ-41](#oq-41) | A continuation captured inside a cancel run | [settle by proof] | — | 04 | K-CANCEL, D-OWED, L-W, T-FIN, OQ-7 | a closed configuration under OQ-7 (a), or `def NestedCancelDelimits : Prop` refuted | no | (a) keep R-FINAB; `ccatch`/`cfin`-free captures |
| [OQ-42](#oq-42) | The constructs the lowering rejects | [user decision] [settle by proof] | U6 | 04, 08 | T-LOWER, 08 §6 | user; for (a), T-LOWER.machine with a run-time mask | yes | (b) lowering gaps listed in 08; the calculus keeps every construct; restricts U6 and "compiler never stale" |
| [OQ-43](#oq-43) | Determinism up to renaming at every step, and two-run facts with array steps | [settle by proof] | critic 6 (TwoRun) | 04, 06, 07 | T-2RUN, T-DET, T-SOUND, T-NAH, L-REN, L-NU, L-STATE, OQ-4 (b) | `head_rename` at every constructor; `def BlockRenameRun : Prop` | no | (a) |
| [OQ-44](#oq-44) | What the open-lend component `σ` holds | [settle by proof] | — | 05 | D-W, D-ORD, D-STOP, D-ARISE, T-ARISE, T-FRAME | its own probe, `def OpenMutFrameCancel : Prop` at a 6.65 frame (05 §12.2), after OQ-9's; `def MutLendRecorded : Prop` | no | (a) GhostEnd-form entries |
| [OQ-45](#oq-45) | Does the arising guard stay in the clauses? | [settle by proof] | — | 05 | D-ARISE, D-REL, D-SEM, T-FP | `theorem tabAt_of_TW` (05 T-ARISE.0) proved or refuted; `def GuardFreeAgrees : Prop` | no | (a) keep `guard_W` as a guard; D-ARISE's invariant reading not in force |
| [OQ-46](#oq-46) | The world a stored payload is read at | [settle by proof] | — | 05 | D-REL (`Imm`, `Mut`), T-MONO, K-NU, OQ-28 | T-MONO at `Mut` and `wpG_M_frameX` at `W`; a stored-callback configuration | no | (a) longer-lived entries |
| [OQ-47](#oq-47) | Is reduction in every context contained in `≡`? | [settle by proof] | — | 06 | binary forms of the reduction-shaped laws; OQ-4 (b); T-2RUN | `def StepInclusion (D) : Prop` per `D` | no | binary forms stated and marked not proved |
| [OQ-48](#oq-48) | Answering/control commutation at an affine operation, on the kernel | [settle by proof] | audit m2 | 06 | L-INTER, T-COMODEL | two closed `CDerives` programs with different `Obs_A`, or a proof at `aff` | no | L-INTER at linear `o` only, as R-INTERLIN |
| [OQ-49](#oq-49) | The composite handler as a kernel term | [settle by proof] | — | 06 | L-HFUSE; fusion in the lowering | a `CDerives` derivation of `H₂ ∘ H₁`, or `def CompositeClauseTerm : Prop` refuted | no | (b) L-HFUSE at tail-resumptive clauses and `n₂`-free bodies only, as R-FUSETAIL |
| [OQ-50](#oq-50) | How the linear use of a continuation is observed | [settle by proof] [user decision] | — | 07 | T-LIN, T-FIN (1), L-C, L-P, T-LOWER's resume-once class | (b) a configuration; (a) user | yes | (c) resource form, marked, as R-LINRES |
| [OQ-51](#oq-51) | Adequacy observed at a row | [settle by proof] | — | 07 | T-ADEQ for host programs, T-LEAK at a closed stop | (b)'s statement proved | no | (a) adequacy at `F 1`, as R-ADEQF1 |
| [OQ-52](#oq-52) | Is a syntactic subject-reduction theorem part of the calculus? | [user decision] | — | 07 | OQ-50 (a); T-LOWER if needed | user | yes | (a) not part |
| [OQ-53](#oq-53) | Is the elaborator proved, or each program checked? | [user decision] | — | 08 | T-ELAB; #188 | user | yes | (a) per-program check plus per-schema theorems |
| [OQ-54](#oq-54) | The lend stack `σ` under a fork | [settle by proof] | critic 6 (threads) | 08 | nothing now; the form of D-W | a fork under an open 6.65 frame at (a) and (b) | no | (a) |
| [OQ-55](#oq-55) | The declaration kind at the surface | [user decision] | decision 55 | 08 | T-ELAB; checklist C-7; #188 | user, after OQ-1 | yes | (a) |
| [OQ-56](#oq-56) | Operation types that mention the lend's variable or the site's lifetimes, at a borrow callback | [settle by proof] [user decision] | finding on K-BOR's row class | 01, 03, 05 | K-BOR, D-TABLEOK (3)-(4), OQ-40, the tier-2 programs of 01 §5.3 | `def LifetimePolyOpTableOK : Prop` (03 §6), then user | yes | (a), as R-CLOSEDOP |
| [OQ-57](#oq-57) | The closing-obligation list `τ` as an index beside `W` | [settle by proof] | 00 §0.2 item 1 | 05 | D-WPG, D-STOP, D-TABLE, D-EWP, D-SHARE, D-OWED, D-OPTAB, D-CANCELTAB, T-FRAME, OQ-44 | `def ClosingInW : Prop` (05 §4) proved or refuted | no | (a) `τ` an explicit index of `wpG_W` and `ewp_W`, recorded as a defect against 00 §0.2 item 1 |
| [OQ-58](#oq-58) | Is Core the `σ = []` instance at `U` (and at `share`, `KapRel`)? | [settle by proof] | finding on T-NIL | 01, 05, 07, 08 | T-NIL, T-CONS.2-3, T-FP's corollaries, OQ-8 criterion (i), every Core theorem's transfer | first probe `def NilAgreesU : Prop` (05 T-NIL) | no | none: until proved, Core is not claimed to be the `σ = []` instance at `U` |
| [OQ-59](#oq-59) | How a handler reaches into the scope of a scoped operation | [settle by literature] [user decision] | OQ-12 | 03, 06 | K-SCOPE's clause type and step, L-SCOPE | literature check (scoped effects as parameterised theories; latent effects; hefty algebras), then user | yes | none: K-SCOPE's handling of the scope is unspecified until settled |
| [OQ-60](#oq-60) | The asynchronous scheduler against the negative-recursion cut-off | [settle by proof] [user decision] | U7, U16 | 01, 06, 08 | L-ASYNC, the async program of 08 §9, OQ-31, OQ-28, OQ-46 | `def DeepSchedulerCarrier : Prop` (06 L-ASYNC), then user | yes | (b) scheduler over `Loop_Σ` codata; the deep-handler scheduler excluded by R-NONEGREC |
| [OQ-61](#oq-61) | Operation types that perform their own effect (effect-recursive signatures) | [settle by proof] [user decision] | finding on L-ASYNC | 01, 02, 03, 05, 06, 08 | K-SIG, K-ROW, K-INT, T-DEF, OQ-31, L-ASYNC, 08 §9.2, OQ-60, OQ-18 | `def SelfRowPositiveLFP : Prop` (03 §9.12), then user | yes | (a), as R-NOSELFROW |
| [OQ-62](#oq-62) | Folds and counted loops at a row | [settle by proof] [user decision] | finding on 03 §2 | 01, 03, 06 | K-FOLDΣ, L-FOLD, SPEC §16/§18 K4 iteration with effects, 08 §6 | compatibility of each constant at a row, then user | yes | (a), as R-PUREFOLD |
| [OQ-63](#oq-63) | A partial-correctness `wp` beside `ewp_W` | [settle by proof] | 00 §0.2 item 1 | 05 | OQ-15 (b), K-HDIV under (b), L-DIV (b), D-EWPP | `def EwpModeUniform : Prop` (05 D-EWPP) | no | (a) `ewpP_W` as written, defect recorded |
| [OQ-64](#oq-64) | The effect-dependent laws of rows | [settle by literature] [settle by proof] | finding on 06 | 06 | L-DISCARD, L-COPY, L-COMMUTE, T-LOWER's dead-call and reordering facts | Kammar-Plotkin POPL 2012 read; unary halves at `W` | no | (a), citation marked [R] |
| [OQ-65](#oq-65) | An operation form with an explicit cancel continuation | [settle by proof] [user decision] | finding on L-ALG | 06 | L-ALG's binary form at finaliser frames | `[then]` derivation at a resuming row (needs OQ-7 (a)), then user | yes | (a), as R-ALGPLAIN |
| [OQ-66](#oq-66) | Is cancel an instance of Ahman & Bauer's signal? | [settle by literature] | finding on L-SIGNAL | 02, 06, 07 | the classification in L-SIGNAL, 02 §11, T-FIN, 08 §7, OQ-18 | A-B §4, §6 read against K-CANCEL | no | (b) not classified; no law depends on it |
| [OQ-67](#oq-67) | The proof obligation of a handler that spans observations of a div computation | [settle by proof] | U5 | 01, 03, 06, 08 | K-HDIV's lift, the reconciler chain's whole-loop handlers, L-DIV | `def HndLoopSpanCompat : Prop` (03 §9.2), or `handle_compatC` at `ewpP_W` | no | construct specified; lift deferred, as R-HDIV (a restriction of U5) |
| [OQ-68](#oq-68) | The proof obligations of allocation as an effect | [settle by proof] | U20 | 01, 03 | K-ALLOC's lift, K-HOST, T-ADEQ for host programs | host handler `IsModel`; an arena configuration at `W` | no | construct specified; lift deferred, as R-ALLOCORACLE (a restriction of U20) |

---

## 2. The questions

<a id="oq-1"></a>

> [!IMPORTANT]
> **Open question OQ-1: One signature, two implementations: how answering and control handlers relate** (audit Q1; critic 1) **[settle by proof]** **[user decision]**
> *Why open:* The sign-off fixes the direction: handlers are models and capabilities are comodels of one `Sig`, checked against one `opTable`. Today they are unrelated: control effects are `hnd`/`perform` checked against `opTable` (`Core/EffDefs.lean:157`); answering effects are `withswap` calls that no table checks (SPEC §18 *Elaboration*); `handle_fold` (`Core/Handlers.lean:211`) and `ewp_handle` (`Core/EffRules.lean:615`) are not related. `experiments/HandlersAsBorrows` shows an answering handler is `withbor` form (2).
> *Options:* (a) an answering handler is `[handle]` with a tail-resumptive state clause, proved equal, so the comodel is a derived form; (b) both stay primitive and T-COMODEL proves they meet the same protocol; (c) a recorded split (excluded by the sign-off).
> *What settles it:* first, a named `def AnsweringIsTailHandler : Prop` (an answering handler's run equals the `[handle]` run of its tail-resumptive translation, under `ewp_W`), proved or refuted by a separating configuration. Then the user's choice, because the options give different rows to the same program (03 K-CAP): under (a) every answering effect appears in the row of every function that uses it, so a function over a capability is coloured by it; under (b) a capability's operations appear in no row, and only control effects colour a function type. A proof can show that the two readings agree in meaning; it cannot choose which colouring the language adopts, and no function colouring is the user's lead axis (01 §4, U7).
> *Blocks:* K-CAP, K-SWAP, K-COMODEL, D-COMODEL, T-COMODEL, L-STATE, L-RUN, L-INTER, L-TAIL, T-ELAB; which effects colour a function type.
> *Default if unresolved:* (b).

<a id="oq-2"></a>

> [!IMPORTANT]
> **Open question OQ-2: Tier 1 or tier 2 first** (audit Q2; critic 2) **[user decision]**
> *Why open:* Tier 1 keeps T1 (no internal lend spans a suspension; only abortive operations cross a borrow's scope, `Row.Unwind`, `Core/EffBorrow.lean:133`). Tier 2 lets a continuation hold a lend opened inside it. #284, #285 and #287 were user-directed continuations, not a halt by rule. The calculus specified here is the full one; this question decides what the first kernel lift implements.
> *Options:* (a) the first lift implements tier 1 with R-T1 imposed, and removing R-T1 is a separate milestone gated on OQ-8, OQ-9 and OQ-10; (b) the first lift targets tier 2; (c) tier 1 permanently.
> *What settles it:* the user's decision, informed by the outcome of the OQ-9 probe and OQ-8.
> *Blocks:* K-BOR (callback rows), K-OP crossing a borrow, D-STOP, D-W's `σ`, T-FRAME at resuming tables, L-BOR's resuming half, L-BETA at the kernel lift.
> *Default if unresolved:* (a). The specification still states every construct without R-T1, and marks R-T1 where it applies.

<a id="oq-3"></a>

> [!IMPORTANT]
> **Open question OQ-3: Does a handler site open a lifetime?** (audit Q3; critic 1) **[user decision]** **[settle by proof]**
> *Why open:* An answering handler opens a fresh lifetime, because it is `withbor` form (2) (`handle_is_shift`, `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:115`). `effHandle` opens none (`Core/Fundamental.lean:367`), so a handler between two lenders (#278) has no place in a lifetime-ordered `σ`, and the stacked line excludes it by `AllCross`, discharged only by constant `true` (`experiments/GhostEnd/GhostEnd/StackStep.lean:182`).
> *Options:* (a) every handler site opens a stratum, as a borrow does, so control handlers are borrows the same way answering handlers are; (b) "a handler between two lenders" is a named restriction; (c) only answering handlers open one.
> *What settles it:* a Lean configuration at `W` of a handler between two lenders, with every hypothesis discharged, at (a) and at (b); and the user's choice between them.
> *Blocks:* K-HND, D-W, D-ORD, T-FRAME at intermediate depth, OQ-14, OQ-28.
> *Default if unresolved:* (b), as R-MID.

<a id="oq-4"></a>

> [!IMPORTANT]
> **Open question OQ-4: Is a binary relation over Core's world in scope?** (audit Q4) **[user decision]** **[settle by proof]**
> *Why open:* Every equational law needs `≡`. No binary relation exists on Core (audit T16). `experiments/TwoRun` derives two-run facts from the unary relation and determinism up to renaming (`freshRun_det`, `run_sim`), which may carry some laws without a binary relation. EffModelRel's binary relation has no resources and no machine. The user's position (2026-10-02; 01 §4, U22): kernel-level equations (a binary relation on BoLo's carrier, η as an equation, optimiser correctness) "are optional and don't get pursued unless they become necessary for safety"; the sign-off of 2026-10-03 asks for the handler laws over the kernel relation, which their unary halves (06 §1.4) meet without a binary relation.
> *Options:* (a) one binary relation `≈` over pairs of worlds `W` (D-BIN); (b) laws that reduce to determinism by TwoRun's route, and (a) only for the rest; (c) out of scope, and every binary half stays sibling-calculus evidence.
> *What settles it:* the user's decision; for (b), a per-law check of which laws follow from `run_sim`/`freshRun_det` plus a unary fact.
> *Blocks:* L-HUNIQ, L-HFUSE, L-HCORR, L-STATE, L-TENSOR, L-ETA, L-HIDE, L-INTER, L-NU, L-NAH, T-ABS, T-BINFP, T-SOUND.
> *Default if unresolved:* (b). Every law is stated in its binary form; its binary half is marked not proved.

<a id="oq-5"></a>

> [!IMPORTANT]
> **Open question OQ-5: Standing of EffModelRel** (audit Q5) **[user decision]**
> *Why open:* EffModelRel (S2-S4 in the audit) proves the H-laws, tensor, the ν laws and no accidental handling on carriers with no resources, no machine and unmoded contexts. No result transports to `CDerives`.
> *Options:* (a) keep as evidence with a banner, "model of a sibling calculus"; (b) archive.
> *What settles it:* the user's decision.
> *Blocks:* 06's citations of EffModelRel; 08.
> *Default if unresolved:* (a).

<a id="oq-6"></a>

> [!IMPORTANT]
> **Open question OQ-6: Typed role declarations or shape recognition** (audit Q6) **[user decision]**
> *Why open:* The elaborator recognises iteration, exhaustion, heap drivers and layers by shape (`iterEff`, `exhEff?` takes the first declared match). A typed role declaration is surface syntax, a one-way door.
> *Options:* (a) typed role declarations; (b) shape recognition with ambiguity rejected.
> *What settles it:* the user's decision.
> *Blocks:* 08 only. The kernel calculus does not depend on it.
> *Default if unresolved:* (b), with ambiguity rejected.

<a id="oq-7"></a>

> [!IMPORTANT]
> **Open question OQ-7: Finalisers at a non-abortive table** (audit Q7) **[user decision]** **[settle by proof]**
> *Why open:* A finaliser's row is `Σ^abort` (SPEC §19 *Typing*); the unwinding forms exist only at abortive callback rows; `withswap` has no unwinding form; the effectful `Aff`'s `close` and the `close` residual are open. These limits follow the abortive frame lemmas, not the destructor law L-W.
> *Options:* (a) state L-W and D-DTOR at every `TableOK` table and lift the restriction with T-FRAME; (b) keep finalisers abortive-only.
> *What settles it:* T-FRAME at a resuming `TableOK` table, then the user's decision.
> *Blocks:* OQ-41, OQ-65, K-THEN, K-FINR (03 §9.8), K-BOR's unwinding half, K-SWAP's unwinding form, K-NU (effectful `Aff`), D-DTOR, L-W, T-FIN; L-ASYNC (a scheduler that performs an affine or abortive outer operation while threads are parked needs the queue finalised by a finaliser at a resuming table).
> *Default if unresolved:* (b), as R-FINAB, decided together with OQ-2.

<a id="oq-8"></a>

> [!IMPORTANT]
> **Open question OQ-8: Where the future-world quantifier sits; the representation of entries; `σ.WF`** (critic 3) **[settle by proof]**
> *Why open:* The kernel quantifies over future record lists at `U` (`Core/Relation.lean:127`), in `contShare` (`Core/EffDefs.lean:147`) and in `KapRel` (`Core/EffRules.lean:573`); `⊸` (`Core/Relation.lean:156`) and `∀` (`:161`) quantify over resource extensions only, through `─⋆`. The audit proposes keeping the quantifier at these CBPV points, moved to `∀ W' ⊒ W` (prose only). #287 places it at the binder clauses (`⊸`, `∀`, and `U`) over stack extensions `τ ++ σ`, with Lean at `∀`: `vRLk`/`cRLk` (branch `borrow-callbacks`, `experiments/GhostEnd/GhostEnd/Extend.lean:62, 81`), `callback_ext` (`:131`), `callback_ext_one` (`:167`); `vRLk` has no `σ = []` lemma, and neither candidate's is definitional: candidate (a)'s `U` clause also quantifies over `⊑`, which at `σ = []` ranges over non-empty extensions (05 T-NIL), so criterion (i) below is an obligation of both candidates at every rule that introduces a `U` value, not a point of difference between them. That obligation is boxed separately as OQ-58.
> *Options:* (a) CBPV points: `U`, `share`, `KapRel` at `∀ W' ⊒ W`, nothing at `⊸`/`∀`; (b0) `vRLk`/`cRLk` exactly as built: `U` clause `RelendableS` at the fixed stack, `⊸` over resources only, `∀` over stack extensions `τ ++ σ` (`Extend.lean:62-105`), the only placement with Lean behind it, whose criterion (iii) is the existing `callback_ext` (`:131`); (b) binder clauses: `⊸`, `∀` and `U` at every extension (§17.6's recommendation, prose); (c) both. Each composes with OQ-9's choice, giving six candidate clause sets, listed in 05 §8 ((b0) already carries OQ-9 (b)'s `Relendable_W` at `U`; the others are taken with and without it, the "-rebase" sets of 05 §7). Two representation items are decided with this question: whether `σ`'s entries carry the binder's variable `x` or lifetimes only, with `δ` binding the variables (05 D-W, *Representation note*; `borrow-callbacks:docs/effects-tr/17-borrow-callbacks.md` §17.7); and whether D-SEM's `σ.WF Δ` becomes a freshness condition under (b), where a transported context may meet entries named by later binders (§17.6, cost 3).
> *What settles it:* for each candidate, a Lean relation over `W` with (i) its `σ = []` lemma (equal to `cC`), (ii) T-MONO by one induction on types, (iii) the analogue of `callback_ext` at the `withbor` row, (iv) the `thunk`, `lam` and `allI` rows (the Lean statements are written out in 05 §8); or a separating configuration: a closed derivation whose conclusion holds at one candidate and fails at the other, every hypothesis discharged. The named statement is `def QuantPlacementAgrees (X Y : Candidate) : Prop` (two candidates coincide at every `W`), stated for every pair of the six clause sets and proved or refuted per pair (05 §8 lists the pairs). The representation of entries is settled by which representation states criterion (iii) at the chosen candidate; `σ.WF` by T-FP's `allI` row at the chosen candidate.
> *Blocks:* D-REL, D-ORD, D-SHARE, D-KAP, D-W (representation of entries), D-SEM (`σ.WF`), T-MONO, T-NIL, T-FP, K-BOR, OQ-2.
> *Default if unresolved:* none: the re-index does not start, and the relation stays the `σ = []` kernel.

<a id="oq-9"></a>

> [!IMPORTANT]
> **Open question OQ-9: Open 6.64 frames handed to a continuation that is cancelled, dropped or resumed between lenders** (critic 4; the first unknown) **[settle by proof]**
> *Why open:* Relativising the stop (D-STOP) lets a stop leave 6.64 frames open (`ps ⊊ ps'`, `TW.immFrame` records) and hand them to the table. D-STOP concerns 6.64 frames only: 6.65 and 6.66 leave `ps` unchanged (`TW.mutFold`, `TW.mutUnfold`, `Core/World.lean:135-144`), and how a 6.65 lend open across a stop is recorded is OQ-44. Every path the continuation can take must still close them: resumed and run to a value; cancelled (`[cancel]`, `cancelOwed`, `Core/EffDefs.lean:138`); dropped at an abortive operation (`opTable`'s `NoOwn` continuation, `Core/EffDefs.lean:167`); resumed by a handler that sits between two lenders. If any path leaves a frame open, `NoOwn`, T-LEAK or LIFO finalisation fails.
> *Options:* (a) `share`/`owed` carry the open frames, and cancel and unwind close them through the unwinding borrows and T-FRAME at `cancelTab`; (b) capture rebasing: end internal lends at the stop and reopen them at fresh lifetimes on resume (TR §14.3, L14.4/O5; the sketch L1-L6 on #251); (c) R-T1: no internal lend spans a stop.
> *What settles it:* **first probe**, before any other relation work: one Lean configuration at `[handle]` + cancel (05 §12.1). A body lends a place by `withbor1U` (a 6.64 frame, a `TW.immFrame` record in `ps`), performs an affine operation under it, and its handler cancels `κ`. The relativised stop is D-STOP's proposed clause at this one table, with `τ' = [e]` and `ps' ↔ frames [e] ++ ps`. Prove `def OpenFrameCancel : Prop` (05 §12.1, every term and table bound) or refute it, every hypothesis discharged. Then the same for the abortive drop and for a resume between two lenders. The 6.65 configuration is OQ-44's probe, not this one.
> *Blocks:* D-STOP, D-W, OQ-44, OQ-57, D-OWED, K-CANCEL, K-KONT, T-STOP, T-LEAK, T-FIN, T-FRAME, OQ-2, OQ-10.
> *Default if unresolved:* the stop condition is unchanged (`Core/EffDefs.lean:40`) and R-T1 holds.

<a id="oq-10"></a>

> [!IMPORTANT]
> **Open question OQ-10: The form of the relativised stop** (critic 4) **[settle by proof]**
> *Why open:* `wpG` requires `ps' ↔ ps ∧ ls' ↔ ls` at every final term, a stop included (`Core/EffDefs.lean:40`). This is where T1 comes from. The value case is the printed `wp` and stays. The stop case must say what the table receives.
> *Options:* (a) `ps ⊆ ps'`, the extra frames and their records passed to the table, which says what the continuation owes; (b) the table receives `ls'` only, and the frames are re-derived from types at resume (with OQ-9 (b)).
> *What settles it:* OQ-9's probe, then T-STOP (conservativity) for the chosen form. It is a kernel definition change: its SPEC entry is written before kernel work.
> *Blocks:* D-STOP, D-WPG, D-EWP, T-STOP, every T-COMPAT at a row.
> *Default if unresolved:* unchanged.

<a id="oq-11"></a>

> [!IMPORTANT]
> **Open question OQ-11: Are laws stated over `W`, or at `σ = []`?** (critic 5) **[settle by proof]**
> *Why open:* Graded algebraicity, the H-laws, `Sig` and renaming were proposed over today's `cC`. Stated there, they may not survive the re-index.
> *Options:* (a) every law over `W`; (b) a law at `σ = []` with a proved survival lemma; (c) a law at `σ = []` only, marked.
> *What settles it:* per law, a statement over `W`, or a survival lemma from T-NIL and T-MONO.
> *Blocks:* every L id; T-MODEL; T-REN.
> *Default if unresolved:* (a) for the statement; (c) marked, where only the `σ = []` proof exists.

<a id="oq-12"></a>

> [!IMPORTANT]
> **Open question OQ-12: Operations that take computations (higher-order and scoped effects)** (decision 57) **[user decision]** **[settle by literature]**
> *Why open:* Effectful closures, generators and recursions are in the calculus, and an operation with a thunk *parameter* is algebraic and in the calculus as built (02 K-SIG). Operations whose argument computations are delimited by the operation (scoped operations: Lindley, Matache, Moss, Staton, Wu & Yang, ESOP 2024 [via #235, abstract]) are not: decision 57 puts them out of scope ("scoping constructs are functions over passed computations that install ordinary handlers"). The full construct is written in 03 §9.1 (K-SCOPE, not adopted), with the part that cannot be specified yet boxed as OQ-59.
> *Options:* (a) decision 57 stands; (b) scoped operations as parameterised algebraic theories in `Sig` (Lindley et al., ESOP 2024 [via #235, abstract]); (c) latent effects (van den Berg, Schrijvers, Bach Poulsen & Wu, "Latent effects for reusable language components", APLAS 2021 [R: named, not read]); (d) hefty algebras, higher-order operations elaborated into algebraic ones (Bach Poulsen & van der Rest, POPL 2023 [R: named, not read]).
> *What settles it:* a literature check of (b)-(d) against K-SCOPE's form, upgrading the [R] marks, then the user's decision.
> *Blocks:* K-SIG (parameter types), K-SCOPE, L-SCOPE, L-ALG at such operations, OQ-59.
> *Default if unresolved:* (a), as R-FO.

<a id="oq-13"></a>

> [!IMPORTANT]
> **Open question OQ-13: Effect polymorphism: a meta-index or an object of the calculus** (decision 57) **[user decision]**
> *Why open:* Decision 57: no row variables in the kernel; a computation parameter's row is served at ports, the rest tunnels, and copies per name assignment are typing artefacts that a renaming lemma would justify. The TR's calculus has instance and row abstraction (`Π`, `∀r`, TR D1.5-D1.7). The row-generic borrow (K-BOR) is a schema over a meta-level `Σ`, as `withbor1U` already is (`Core/Fundamental.lean:258`), so it needs no row variable. T-REN relates copies that differ by a permutation of names (07 T-REN, *Corollary*); it does not relate copies at structurally different rows, such as `timeout_Σ` and `timeout_Σ'` for different signatures `Σ`, `Σ'`, and no theorem of the specification does. Under a meta-index a row-generic value cannot be stored or passed first-class and instantiated later, and a recursion cannot change its row at a recursive call (polymorphic recursion across rows): an effectful callback is stored and called at one fixed row.
> *Options:* (a) rows stay a meta-index: each copy at each row is a separately checked derivation, with no relating theorem beyond T-REN's renaming case; (a') (a) with a meta-level substitution lemma: a derivation generic in a row parameter, instantiated at each row, the instances related by it (a lemma about the schema, not a kernel rule); (b) row and instance abstraction in the kernel (K-ROWABS, 03 §9.6: `∀r. C`, its introduction, instantiation, model clause and laws).
> *What settles it:* the user's decision, with T-REN's cost and the cost of (a')'s substitution lemma known.
> *Blocks:* O-JDG, K-ROW, K-REN, K-BOR, K-ROWABS, T-REN, L-NAH, T-ELAB; first-class row-generic values and polymorphic recursion across rows (U7, no colouring of stored callbacks); the reconciler chain `timeout |> retry |> log |> kube` (01 §4, U5), whose generic `timeout` and `retry` are functions over computations at every row and are, under (a), one separately checked copy per row (08 §9.1).
> *Default if unresolved:* (a), as R-NOROWVAR: per-row derivations with no relating theorem except at a renaming; no first-class row-generic value; no polymorphic recursion across rows.

<a id="oq-14"></a>

> [!IMPORTANT]
> **Open question OQ-14: Static names or generative instances** **[user decision]** **[settle by proof]**
> *Why open:* Names are static per site (SPEC §19 *Names*). Recursion through a site and Staton's `ν` laws need generative instances, which need a continuation confined to its handler's scope (T2, #173). Re-entry of a site is resolved dynamically, the one place resolution is not lexical.
> *Options:* (a) static names, with T-REN and L-NAH as companions; (b) generative instances with a scope-confined `κ`, possibly a lifetime-bounded thunk (with OQ-3, OQ-28); its full construct is K-NAME's `[new]` step (02 K-NAME, *Generative instances*), collected in 03 §9.14.
> *What settles it:* the user's decision; for (b), the configuration of a stale label meeting a reused one, built at `W`.
> *Blocks:* K-NAME, L-NU, L-NAH, T-ABS, recursion through a site (SPEC §21 *Open*).
> *Default if unresolved:* (a), as R-STATIC.

<a id="oq-15"></a>

> [!IMPORTANT]
> **Open question OQ-15: The kernel reading of divergence** (SPEC entries 13, 19, 20) **[user decision]** **[settle by proof]**
> *Why open:* Div is an effect and normal programming. The kernel reads it as codata: a div function's result is `U(Loop B R)` (SPEC Entry 13, §14), with handlers per observation. `ewp` is total correctness (`∃ k', ARun …`, `Core/EffDefs.lean:36`). A handler around a div computation is not provided for any effect (SPEC §21 *Open*), which also rejects a recursion whose body loops.
> *Options:* (a) codata; a handler around a div computation is K-HDIV's `hndLoop` form, per observation or spanning observations with its state and any stored `κ` in the unfold state (03 §9.2); (b) div as a row entry, read by the partial-correctness `ewpP_W` (05 D-EWPP), a second wp family recorded as a defect in OQ-63, a handler around it the ordinary `[handle]`.
> *What settles it:* the user's decision between the readings. The handler around a div computation is in the calculus under both (K-HDIV, U5 decided); its proof obligation at the chosen reading is OQ-67 (settled by proof), and under (b) OQ-63's.
> *Blocks:* K-DIV, K-NU, K-HDIV, L-DIV, T-TOTAL's place, SPEC Entries 13, 19, 20; O-EQ, whose observation is total only under (a) (06 §1.2), and with it every law's binary form; OQ-63, OQ-67.
> *Default if unresolved:* (a). K-HDIV is specified under both readings (03 §9.2); whether its spanning form is lifted before its obligation is proved is OQ-67, whose default is R-HDIV.

<a id="oq-16"></a>

> [!IMPORTANT]
> **Open question OQ-16: Is multi-shot free?** **[settle by proof]** **[settle by literature]**
> *Why open:* Multi-shot is kept only if it costs no rule, law or seam. The kernel has `unr` (`kTy`, `Core/EffRules.lean:980`). ν/op fails at `unr` (`nu_op_fails_multishot`).
> *Options:* (a) keep `unr`, with no law or obligation depending on it; (b) drop it.
> *What settles it:* a list of every rule, law and obligation that mentions `unr`, each shown to cost nothing beyond `!`'s existing rules, or not; and a literature check against Affect (van Rooij & Krebbers, POPL 2025 [via #235]), which types one-shot and multi-shot continuations directly, for whether its typing gives `unr` at a lower cost.
> *Blocks:* K-KONT, L-P, L-ND, L-NU, T-LOWER's multi-shot class.
> *Default if unresolved:* (a); laws are stated and proved at `lin` and `aff`.

<a id="oq-17"></a>

> [!IMPORTANT]
> **Open question OQ-17: The relevant qualifier** **[user decision]**
> *Why open:* A relevant `κ` (copy, no drop) needs a modality with copy and no forget; the kernel's `!` has both (SPEC §19).
> *Options:* (a) not provided; (b) a graded `!` with grade `[1,∞]` (`experiments/Grades`), K-RELQ (03 §9.10).
> *What settles it:* the user's decision, when a program needs it.
> *Blocks:* O-QUAL, K-KONT.
> *Default if unresolved:* (a), as R-NOREL.

<a id="oq-18"></a>

> [!IMPORTANT]
> **Open question OQ-18: Sum, tensor, and threads** (critic 6 (threads)) **[user decision]** **[settle by literature]**
> *Why open:* Rows are sums (the sign-off). Disjoint capabilities should commute (tensor, Hyland, Plotkin & Power, TCS 2006 [via #235]). Ahman & Bauer's signals absorb only the kernel's state operations (`getenv(λc. kill s) = kill s`, `setenv(c, kill s) = kill s`, eq. (1)), and external operations commute with state instead; a runner's own signal skips the rest of the user code and runs the finalisation clause `kill s ↦ N_s`, and only an enveloping runner's signal bypasses the inner finalisation (arXiv 1910.11629 §3.1-3.2, Thm 7, read; 06 L-SIGNAL). Whether our cancel is such a signal is OQ-66. Threads are required eventually; the choice of combination, handler state and cancellation must not close that door. Whether a thread boundary combines two rows by a tensor has no source: operations of concurrent threads on shared state do not commute, and the standard models of concurrency (resumptions, interleavings) are not tensors [I].
> *Options:* (a) rows are sums, disjoint capabilities are tensor (the unary disjoint-capability frame fact), cancel uninterceptable and finalising; each construct records what threads would change; (b) another combination; for threads, a literature check of resumption and interleaving models against rows as sums.
> *What settles it:* the user's decision on any thread-facing choice the sections surface; the literature check for the thread-boundary reading.
> *Blocks:* K-ROW, L-SUM, L-TENSOR, L-SIGNAL, L-ASYNC, OQ-61 (fork-style operations), OQ-66.
> *Default if unresolved:* (a); no thread boundary is described as a tensor.

<a id="oq-19"></a>

> [!IMPORTANT]
> **Open question OQ-19: The meaning of "comodel" for a capability** **[user decision]**
> *Why open:* The sign-off makes capabilities comodels. The user has ruled out Ahman-Bauer runners as the user-facing effect mechanism, and keeps open the reading of a whole BoLo world as one comodel (OQ-34; 01 §4, U21: "Don't cite 'runners are a dead end' against it"). A comodel may be read as Møgelberg-Staton's state-access operation on linearly used state [via #235], with no runner construct; capability destructors and fallible co-operations (#279, external input) raise runner-like questions. Read as a coalgebra of a comonad, a capability would also owe Katsumata-Rivas-Uustalu's comonad-side conditions (counit and comultiplication, the left diagrams of arXiv 1912.13477 §3 (1)), which govern how the cell's state is threaded and which the specification does not state; KRU §4 relates monad-comonad interaction laws to `D`-coalgebraic runner specs. A fallible co-operation, one that answers or fails (the reconciler's `Kube`, 08 §9.1), is OQ-20 (c) at a row with `Fail`.
> *Options:* (a) comodel = state-access semantics only: no runner construct, no `finally`/kill; (b) runners with finalisation.
> *What settles it:* the user's decision.
> *Blocks:* OQ-34, K-COMODEL, D-COMODEL, T-COMODEL, K-HOST.
> *Default if unresolved:* (a).

<a id="oq-20"></a>

> [!IMPORTANT]
> **Open question OQ-20: A co-operation whose callee performs** (U5) **[settle by proof]** **[user decision]**
> *Why open:* `withswap`'s callback is pure. An effectful callee would hold the payload across a stop. The proposed split (#279, external input): `withswap` for an answering-only callee, and `withtake`, at any row, whose cell holds a placeholder while the payload is out (`Ref(1 ⊕ κ)` has `inl ()`).
> *Options:* (a) `withswap` only, pure callee; (b) a `withtake`-shaped candidate (03 K-SWAP), which would be a new constant beside `withswap` and so must first be justified against one borrow per printed constant (C-6) and no new mechanism (C-9): either shown an instance of K-BOR's schema or of a printed constant, or reported as a defect under 00 §0.2 item 1; (c) an effectful `withswap` under `TableOK`.
> *What settles it:* the compatibility lemma of (b) or (c) at `W`, then the user's decision.
> *Blocks:* K-SWAP, K-COMODEL, T-COMODEL, K-SWAPΣ (03 §9.11); a fallible capability, and with it the reconciler chain's `Kube` (U5, 08 §9.1), which under (a) is a handled control effect, not a capability.
> *Default if unresolved:* (a), as R-PURESWAP.

<a id="oq-21"></a>

> [!IMPORTANT]
> **Open question OQ-21: What a finaliser may perform, and the cancel error policy** **[user decision]**
> *Why open:* A finaliser performs abortive and answering operations; during a cancel the first error with a name outside the region is re-raised at the canceller and the rest are suppressed (SPEC §19 *Cancels*). No law was found for that policy (#235, L5-K). The alternative: frame destructors perform only answering operations, handler-level finalisers anything in the outer row (#245).
> *Options:* (a) as built; (b) destructors answering-only.
> *What settles it:* the user's decision.
> *Blocks:* K-THEN, K-CANCEL, D-DTOR, L-SIGNAL, L-W.
> *Default if unresolved:* (a).

<a id="oq-22"></a>

> [!IMPORTANT]
> **Open question OQ-22: Equations in a signature** **[user decision]**
> *Why open:* Every effect today is a free theory, so handler correctness is vacuous. The state laws, the choice laws and user theories need equations in `Sig`.
> *Options:* (a) `Sig` carries optional equations, and L-HCORR is an obligation of a handler of an equational theory; (b) free theories only.
> *What settles it:* the user's decision.
> *Blocks:* K-SIG, K-THEORY, L-HCORR, L-STATE, L-ND.
> *Default if unresolved:* (a) as the form; no kernel theory carries equations until one is needed.

<a id="oq-23"></a>

> [!IMPORTANT]
> **Open question OQ-23: Is lowering correctness a theorem?** (decision 48) **[user decision]**
> *Why open:* Effect handling is erased at run time; the criterion is cost parity with the hand-written program. Decision 48's acceptance (per-class laws, counts, reports) predates effects in the kernel.
> *Options:* (a) per-class laws (L-TAIL, L-ALG0) in the kernel, plus corpus counts and reports; (b) a compiler-correctness theorem for the effect lowering.
> *What settles it:* the user's decision.
> *Blocks:* T-LOWER.
> *Default if unresolved:* (a).

<a id="oq-24"></a>

> [!IMPORTANT]
> **Open question OQ-24: An abortive payload that owns a resource** (#215) **[settle by proof]** **[user decision]**
> *Why open:* An abortive operation's argument holds nothing owned (`opTable`'s `NoOwn` argument, `Core/EffDefs.lean:167`), so an error cannot hand back a buffer (#215).
> *Options:* (a) `NoOwn` payload; (b) a linear payload delivered to the handler, with the finalisers of the unwound region run first (K-OWNERR, 03 §9.9).
> *What settles it:* the compatibility of `[raise]` and `[finalise]` at (b), then the user's decision.
> *Blocks:* K-RAISE, D-OPTAB, L-EXC.
> *Default if unresolved:* (a), as R-NOOWNERR.

<a id="oq-25"></a>

> [!IMPORTANT]
> **Open question OQ-25: Handler state** **[user decision]**
> *Why open:* A resuming handler with state uses a state-passing answer type, one dispatched call per resume (SPEC §21). The alternative makes all handler state comodel state, a `Mut` cell lent to the body and owned by the clause while suspended (#245).
> *Options:* (a) state passing; (b) comodel state in a cell.
> *What settles it:* the user's decision, with OQ-1 and OQ-9.
> *Blocks:* K-HND, K-COMODEL, T-LOWER.
> *Default if unresolved:* (a).

<a id="oq-26"></a>

> [!IMPORTANT]
> **Open question OQ-26: Shallow handlers** **[user decision]**
> *Why open:* Step-wise handling is covered by `ν` codata (stored generators, SPEC §15 and §19 *Open*), not by a construct.
> *Options:* (a) `ν` only; (b) a shallow handler construct, K-SHALLOW (03 §9.7).
> *What settles it:* the user's decision, when a program needs it.
> *Blocks:* K-HND, K-NU, L-YIELD.
> *Default if unresolved:* (a), as R-DEEP.

<a id="oq-27"></a>

> [!IMPORTANT]
> **Open question OQ-27: η with cancel at an affine operation** **[settle by proof]**
> *Why open:* Forwarding a cancel is `let r = op x in resume k r` with `k` dropped on unwind, which puts a continuation inside a frame of another continuation (#279, external input). Whether SPEC §19's terms express it is not checked; the forwarding term exists in the machine and its typing is OQ-7's question (04 §7.6).
> *Options:* (a) it is a term, and L-ETA is a law to prove; (b) it is not, and the kernel lacks a form.
> *What settles it:* a typed term in `CDerives`, or a named `def ForwardCancelTerm : Prop` refuted.
> *Blocks:* L-ETA.
> *Default if unresolved:* L-ETA stated at `lin` only, as R-ETALIN.

<a id="oq-28"></a>

> [!IMPORTANT]
> **Open question OQ-28: How a stored continuation is bounded** **[settle by proof]**
> *Why open:* A continuation that captures a borrow at `'a` must not outlive `'a`. At the paper level the box is that bound: `[@c](T₁ ⊸ T₂)` outlives `@a` iff `@c ⊐ @a` (`box_lolli_outlives_iff`, `experiments/HandlersControl/HandlersControl/Outlives.lean:35`). `U(F_Σ A)` has no outlives rule (SPEC §19 *Types*). The rule `[gen]` (branch `lift-stage1`, `Core/Gen.lean`; SPEC entry E-GEN, 08 §4.2), K-GEN in 03 §4, stores `κ` at `[@c] U(Aff^c A B)`; whether `[gen]` is a rule or a derived form of K-HND and K-NU is decided here. Both options are written in full in 03 K-GEN.
> *Options:* (a) K-GEN option (a): `[gen]` a rule, a stored continuation at `[@c] U(Aff^c A B)`, the bound in the box; (b) K-GEN option (b): an outlives rule at `U C` and `K_q`, from the captures' lifetimes, so that `boxI` boxes a `κ` directly and `[gen]` is derived.
> *What settles it:* the compatibility of storing and resuming a `[@c]`-boxed `κ` at `W`.
> *Blocks:* K-KONT, K-GEN, K-FTY, OQ-14, E-GEN, OQ-67.
> *Default if unresolved:* (a).

<a id="oq-29"></a>

> [!IMPORTANT]
> **Open question OQ-29: An operation that answers a borrow into the handler's state** (#160) **[settle by proof]** **[user decision]**
> *Why open:* Operations answer owned or persistent values; a `lookup` answers a copy (#160).
> *Options:* (a) not provided; (b) K-BORANS (03 §9.4): an answer type `Imm 'h T` at the handler site's extent `'h` (with OQ-3 (a)), the handler's state frozen in the answered part while any answer is live. The part that cannot be specified yet: whether the clause may mutate the answered part between answers, which needs `[TR]` 6.150 lifted to `ewp` at a resuming table (T-FRAME).
> *What settles it:* the compatibility of K-BORANS at `W`, then the user's decision.
> *Blocks:* K-SIG (answer types), K-CAP.
> *Default if unresolved:* (a), as R-NOBORANS.

<a id="oq-30"></a>

> [!IMPORTANT]
> **Open question OQ-30: Allocation and I/O in the calculus: which presentation** (U20) **[user decision]**
> *Why open:* Allocation is an effect (U20, decided): the heap the outermost handler, arenas nested. K-ALLOC (03 §9.5) is the specified construct. SPEC §13 reads the allocator as the machine's oracle today. I/O is a bundle of per-effect linear capabilities, ambient only in `main` (SPEC §11). What is open is the presentation, which decides colouring.
> *Options:* (b) allocation as the operations of `Alloc[T]` in rows, so every function that allocates has `Alloc[T]` in its row and is coloured by it (this bears on U7); (b') allocation as a capability (a comodel over the heap, K-CAP) rather than a row entry, so that it colours no function type (with OQ-1 (b)). I/O is a comodel capability with a host carrier under both.
> *What settles it:* the user's decision between (b) and (b'). The proof obligations of K-ALLOC are OQ-68 (settled by proof).
> *Blocks:* K-HOST, K-ALLOC, T-ADEQ's statement for host programs.
> *Default if unresolved:* (b'), which keeps U7; the lift of K-ALLOC under either waits on OQ-68, whose default is R-ALLOCORACLE.

<a id="oq-31"></a>

> [!IMPORTANT]
> **Open question OQ-31: The cut-offs that keep the relation step-free** (TR §16.5) **[user decision]**
> *Why open:* The relation needs no recursive domain under five cut-offs (TR §16.5): bounded recursion, positive `μ`/`ν`, strict strata, closed operation types (which closedness is meant is part of OQ-35), and the relation never stored in the typed world. A handler that returns its own continuations is a negative recursive type and needs step-indexing.
> *Options:* (a) keep all five; (b) relax one, with step-indexing. Option (b) conflicts with the standing requirement of no step-indexing (00 §0.2 item 2) and is listed only so that the user can see it.
> *What settles it:* the user's decision.
> *Blocks:* T-DEF, K-SIG (closed operation types), K-FIX, K-NU, K-NEGREC (03 §9.15, the excluded construct stated), OQ-61 (c), L-ASYNC (OQ-60: a deep-handler scheduler stores its own continuations).
> *Default if unresolved:* (a), as R-NONEGREC: no negative recursion through a stored continuation (a handler that stores or returns its own continuations), bounded recursion, positive `μ`/`ν`. The closedness cut-off is R-CLOSEDOP's where it applies to borrow callbacks (OQ-56) and OQ-35's elsewhere.

<a id="oq-32"></a>

> [!IMPORTANT]
> **Open question OQ-32: The TR's moded calculus and the kernel** (audit M14) **[settle by proof]**
> *Why open:* The TR's rule fixes (owning lend, `Res` as an instance, scaled capture) and its resource safety are over a moded calculus; `CDerives` has no modes or instances (audit M14).
> *Options:* (a) record which kernel rule replaces each fix; (b) lift modes into the statics.
> *What settles it:* a table, per fix, of the kernel rule that refuses the TR's counterexample, each checked against a configuration.
> *Blocks:* 08; K-GRADE.
> *Default if unresolved:* (a).

<a id="oq-33"></a>

> [!IMPORTANT]
> **Open question OQ-33: How the hard-stop rule applies under this specification** (critic 2) **[user decision]**
> *Why open:* The rule of 2026-10-02 froze a finite tier-2 work list and set a halt: "if any item's run reports a new unknown, a 'reduced to lemma X', a new construct, or an open item not on the list, tier 2 halts. The language ships at tier 1" (memory record `hard-stop-on-regress`). The audit read the rule as already triggered (`docs/effects-audit.md` §1, "On tier 2"); the sign-off's correction records #285 and #287 as user-directed continuations, so tier 2 did not halt by rule (00 §0.3 item 2). This specification replaces the frozen list by D-W, D-STOP and the register of open questions, so the rule's trigger ("an open item not on the list") no longer has its list.
> *Options:* (a) the rule applies to the milestone that lifts R-T1: if the OQ-9 probe or the D-STOP work reports an unknown not in the register, that milestone halts and tier 1 ships; (b) the rule is superseded by the register: an unknown becomes a boxed question, and the user decides at each one; (c) under either, the refinement stands as a property of the specification: a result over the lend stack is proved once for every depth (01 §5.4).
> *What settles it:* the user's decision.
> *Blocks:* OQ-2's milestone structure; the issue plan's gate between the tier-1 lift and the lift of R-T1.
> *Default if unresolved:* (a) together with (c).

<a id="oq-34"></a>

> [!IMPORTANT]
> **Open question OQ-34: Is the BoLo world itself a comodel (the heap-runner architecture)?** **[user decision]** **[settle by literature]**
> *Why open:* The user called the framing "a whole BoLo world is one big comodel, a runner, inside a lawful local effect calculus" promising and "not yet decided" (2026-10-02; memory record `effects-are-core`): BoLo as the internal language of a heap runner whose state carries the global borrow invariant, local algebraic effects outside, an interaction-law or realisability boundary between them, arenas and nested allocators as nested runners. This specification takes BoLo's resource world as the carrier of one Kripke world `W` (01 §2) and does not depend on the framing; it bears on OQ-19 (what "comodel" means for a capability) and OQ-30 (allocation as an effect).
> *Options:* (a) not adopted as structure: the specification neither depends on it nor excludes it; (b) adopted as the reading of K-HOST and allocation: the heap is the outermost comodel, arenas nested ones, and `opTable`'s host entries are its co-operations.
> *What settles it:* the user's decision; for (b), a literature check of the boundary the record names (Patterson, Mushtak, Wagner & Ahmed, PLDI 2022, named in the memory record and not read for this section) and a statement of the host comodel's protocol at `W`.
> *Blocks:* K-HOST, OQ-19's framing, OQ-30.
> *Default if unresolved:* (a).

<a id="oq-35"></a>

> [!IMPORTANT]
> **Open question OQ-35: Are operation types closed in lifetimes?** (audit M13) **[settle by proof]** **[user decision]**
> *Why open:* SPEC §19 *Names* justifies re-entry of a site ("every instance of a site has one protocol") by "operation types are closed in lifetimes" (`SPEC.md:2418-2419, 2537`). No rule enforces it: `effHandle` has no such premise (`Core/Fundamental.lean:367-372`); only `Row.Unwind` asks it, of a borrow callback's row (`Core/EffBorrow.lean:133-134`); the `NuOk` leaf asks closedness in type variables only (`CTy.EffLeaf`, `Core/Types.lean:1141`); `OpSig.ent` reads operation types at the handler's `δ` (`Core/EffRules.lean:42-44`). Operations at borrowed types (`Mut @a T` of an outer lender) need lifetime-open types, and OQ-29 needs them at the handler's own extent. Every `effHandle` derivation is covered by `fundamentalC` (`Core/Fundamental.lean:434`) at `σ = []` without the premise; whether re-entry at a lifetime-open operation type stays sound at `W` is not derived. OQ-31 lists "closed operation types" among the cut-offs that keep the relation step-free; which closedness it means (type variables, lifetimes, or no self-reference of the relation through an operation type) is part of this question.
> *Options:* (a) `Closed E` (no free lifetime variable in any `A_i`, `B_i`) is a premise of `[sig]` and `[handle]`, with T-CONS checked against every existing derivation; (b) no premise: operation types may mention the lifetimes of the site's `Δ`, and the SPEC sentence is replaced by the statement proved (re-entry sound through `RowLe`'s equality of `OpSig`, T-FP at `W` and T-REN); (c) `Closed E` only below the site's own extent, or only at sites that can be re-entered (with OQ-3).
> *What settles it:* a census of `effHandle` derivations in `Core/` and the corpus whose operation types mention a lifetime (T-CONS for (a)); a re-entry configuration at a lifetime-open operation type, built in Lean at `W` with every hypothesis discharged, or `def ReentryLifetimeOpen : Prop` (re-entry preserves `𝒞⟦−⟧_W` when an operation type mentions a lifetime of `Δ`) proved or refuted; then the user's choice.
> *Blocks:* K-SIG, K-NAME (re-entry), K-HND, K-OP, K-NU (the leaf condition), OQ-29, OQ-31's statement, T-DEF, T-CONS, T-REN.
> *Default if unresolved:* (b), as built. Option (a) narrows the calculus (it excludes operations at borrowed types and OQ-29) and is not in force. This question concerns `[sig]` and `[handle]`. At a borrow callback, closedness is imposed separately by R-CLOSEDOP (OQ-56), a named restriction of K-BOR, not a premise of `[sig]`.

<a id="oq-36"></a>

> [!IMPORTANT]
> **Open question OQ-36: How the typing judgement identifies equal rows inside types** **[settle by proof]**
> *Why open:* `F_Σ A` is a chain of `CTy.eff` layers (`CTy.effOf`, `Core/Types.lean:155-157`), so `F_{Σ₁ ⊕ Σ₂} A` and `F_{Σ₂ ⊕ Σ₁} A` are different `CTy` terms. `[sub]` (`Core/Fundamental.lean:340-342`) converts them only at the top of a computation judgement, not under `U`, `⊸`, `&`, `∀` or `ν`. Their relations agree (`cC_effOf`, `Core/EffRules.lean:73-76`, reads only the table).
> *Options:* (a) a canonical row: rows normalised (keys distinct, sorted by `(n, i)`), every rule that builds a row (`Row.ofEff n E 0 ++ S` in `effHandle`, `Row.abortOnly` in `effThen`) normalises, so equal rows are equal types; (b) a type equivalence `C ≅ C'`, the congruence generated by row equality, with a conversion rule in `CDerives` and the lemma that `𝒞` respects it; (c) the row as a finite map inside the `CTy` syntax.
> *What settles it:* for the chosen option, the conservativity statement (every existing derivation maps to one at normalised or converted rows with the same meaning, via 02 K-ROW's ROW-2 and ROW-4) and, for (b), the congruence lemma through every former of O-TY, proved.
> *Blocks:* K-ROW, K-FTY, `[sub]`, T-CONS, T-REN.
> *Default if unresolved:* (a).

<a id="oq-37"></a>

> [!IMPORTANT]
> **Open question OQ-37: Handler carriers at every computation type** **[settle by proof]** **[user decision]**
> *Why open:* A model of `E` may have any computation type as carrier (Plotkin & Pretnar [via #235, L2]; phase A's handlers into any computation type, #245). `[handle]`'s carrier is `F_Σ R` (`retTy`, `clauseTy`, `kTy`, `Core/EffRules.lean:976-994`); `ewp_handle`'s clause obligation is stated at a returner's answer relation (`Core/EffRules.lean:617-627`). A carrier `S ⊸ F_Σ R` is the allocation-free state-passing handler; today the state is passed per clause (decision 59) or through a returned closure (decision 56 records the per-operation closure cost).
> *Options:* (a) K-CARRIER (03 §9.3): `[handle]` at every computation type `C`, `κ`'s types `K_q(B, C)` with `C_1` the carrier's cancel answer, defined by recursion on `C`, and T-MODEL's M1 ("every computation type is a Σ-model") used directly; `C_1` at a `νX. C` carrier is not yet specified and is part of this question; (b) carrier `F_Σ R` only, every other carrier by encoding.
> *What settles it:* `ewp_handle` and `handle_compatC` at a carrier `S ⊸ F_Σ R` and at `C & D` at `σ = []`, or a separating configuration; then the user's decision with OQ-25.
> *Blocks:* K-MODEL, K-HND, K-KONT, T-MODEL, OQ-25, T-LOWER (state-passing class).
> *Default if unresolved:* (b), as R-RETCARRIER (00 §7.2).

<a id="oq-38"></a>

> [!IMPORTANT]
> **Open question OQ-38: Is site freshness a premise of `[handle]`?** (decision 57) **[settle by proof]** **[user decision]**
> *Why open:* `effHandle` makes the handler's name fresh for the outer row (`hnS`, `Core/Fundamental.lean:370`) but not for the context `Γ₂` of the body. A thunk in `Γ₂` whose row holds `n` is caught by an inner `handle_n` of the same `E`: typed, sound, and accidental handling (02 §4, case 2). Decision 57 checks site freshness (R3) in the elaborator only and says it "may move into `[handle]` later as a pure restriction".
> *Options:* (a) add `n ∉ names(Γ₂) ∪ names(A)` to `[handle]`, so the kernel's binder is respected and T-NAH holds of every kernel derivation; (b) keep R3 in the elaborator, and state T-NAH relative to it.
> *What settles it:* first, the configuration of 02 §4 case 2 built in Lean (`def AccidentalHandlingTyped : Prop`, a typed derivation and a run in which the inner handler catches the outer thunk's operation); then T-REN's cost with and without the premise; then the user's decision.
> *Blocks:* K-NAME, K-REN, T-NAH, T-ABS, L-NAH.
> *Default if unresolved:* (b), as decided in decision 57.

<a id="oq-39"></a>

> [!IMPORTANT]
> **Open question OQ-39: Qualifier subsumption in `[sub]`** **[settle by proof]** **[user decision]**
> *Why open:* A computation whose captured contexts tolerate a dropped continuation also tolerates one resumed exactly once, so `F_{n:{op : A ↠^{aff} B}} C ≤ F_{n:{op : A ↠^{lin} B}} C` (and `unr` below `aff`) is the grade order of 02 §3 read contravariantly [I]. `RowLe` requires the same `OpSig` (`Core/EffRules.lean:699`), so the kernel has no such subsumption. Graded calculi normally subsume along the grade order.
> *Options:* (a) `[sub]` admits a row whose operations' qualifiers are pointwise below in the grade order; (b) exact qualifiers only.
> *What settles it:* the compatibility of (a) at `σ = []`: `opTable` at the smaller qualifier implies `opTable` at the larger one's protocol, through `contShare` (`Core/EffDefs.lean:144-150`), proved or refuted; then the user's decision.
> *Blocks:* K-ROW, `[sub]` (03), L-ALG's statement at mixed qualifiers.
> *Default if unresolved:* (b), as built, as R-EXACTQ.

<a id="oq-40"></a>

> [!IMPORTANT]
> **Open question OQ-40: The syntactic row class of a borrow callback** (audit C4) **[settle by proof]**
> *Why open:* K-BOR is generic over every callback row with `TableOK ⟦Σ⟧δ` (O-BOR, D-TABLEOK), but `TableOK` is a semantic predicate on tables and a typing rule needs a syntactic premise on `Σ`. 00-structure names no syntactic counterpart of D-TABLEOK. Today's classes are pairwise exclusive (`Row.Unwind`, `Core/EffBorrow.lean:133`; `LinResume`, `experiments/GhostEnd/GhostEnd/Body.lean:141`), so a `Fail ⊕ Yield` callback fits none (audit C4).
> *Options:* (a) one class `BorOK_x Σ ≜ Σ.NZ`, the full class; the conjunct `Closed ∧ Data_x` is R-CLOSEDOP (OQ-56) and "every operation abortive" is R-T1, each a named restriction added to it; (b) a class per qualifier with closure under `⊕` proved by T-SUMOK; (c) the typing rule takes a derivation of `TableOK` as an external premise (rejected by default: it puts a semantic proof in a typing derivation).
> *What settles it:* `theorem borOK_tableOK : BorOK_x Σ → ∀ δ, TableOK (⟦Σ⟧δ)` at the chosen class, proved at R-T1 (from `Row.Unwind.abort`, `Row.Unwind.tab_extend`, `Row.Unwind.out`, `Core/EffBorrow.lean:143-172`) and, without R-T1, after OQ-9's probe.
> *Blocks:* K-BOR, K-CAP (an answering handler's body row), L-BOR, T-SUMOK, OQ-2.
> *Default if unresolved:* (a). With R-T1 and R-CLOSEDOP both imposed, as they are by default, the class is today's `Row.Unwind x`.

<a id="oq-41"></a>

> [!IMPORTANT]
> **Open question OQ-41: A continuation captured inside a cancel run** **[settle by proof]** (related to OQ-7)
> *Why open:* P-CANCEL and P-ABORT (04 §7.1, §7.2) assume the captured `K` contains no `ccatch` or `cfin` frame. Such a frame enters a captured context only if an operation is performed and captured while a cancel is running: a finaliser (running under `cfin`, inside the region's `ccatch`) performs a non-abortive operation handled outside the canceller. Under R-FINAB that cannot happen, because a finaliser is typed at `S.abortOnly` (`Core/Fundamental.lean:364`). Under OQ-7's option (a) it can. Then cancelling that inner continuation sends its `⊥(N', none)` to the *nearest* `ccatch` (`Catches ⊥`, `Paper/S3_Dynamics/Definitions.lean:400-406`), which may be the outer cancel's delimiter. Alternatively it reaches the outer cancel's `cfin` first, where `[cfin-raise]` at `m = ⊥` stores the inner cancel state as the kept error whenever `0 ∉ N` (`errNext`, `:378-382`).
> *Options:* (a) keep R-FINAB, and prove the invariant "every captured `K` of a typed run is free of `ccatch` and `cfin`" from T-FP; (b) key `ccatch` to its region, so that `[cancel]` fires only at a state whose `N` equals the delimiter's, a machine change; (c) give `[cfin-raise]` the side condition `m ≠ ⊥` and let a cancel pass through `cfin`, a machine change.
> *What settles it:* a closed configuration typed under OQ-7 (a), in which a finaliser performs a resuming operation handled outside the canceller and that continuation is then cancelled, run in Lean to its end. Either the run reaches the intended delimiter, or `def NestedCancelDelimits : Prop` is stated and refuted.
> *Blocks:* K-CANCEL (P-CANCEL, P-ABORT in general form), D-OWED, L-W, T-FIN, OQ-7.
> *Default if unresolved:* (a). P-CANCEL and P-ABORT are stated with the `ccatch`/`cfin`-free hypothesis, and OQ-7 (a) is not adopted until this is settled.

<a id="oq-42"></a>

> [!IMPORTANT]
> **Open question OQ-42: The constructs the lowering rejects** (U6) **[user decision]** **[settle by proof]**
> *Why open:* The compiler is never stale: every construct lands with its lowering. The lowering rejects three things (SPEC §19 *Lowering*, "Not lowered"): a name with both control and abortive operations; a cancel whose finalisers may raise under a handler site reached again from its own body, because there the static mask is not the region's `N(n, K)` (`masks`, `Backend/Clos/Capture.lean:984-996`); and a handler named `64` or more, because the mask is a `UInt64`. The machine has none of these limits. T-LOWER.machine (04 §6.3) holds only up to them.
> *Options:* (a) extend the lowering: carry the region's names at run time where the static mask is inexact, and give a mixed name both conventions; (b) record each as a restriction of the lowering, stated in 08, which never narrows the calculus.
> *What settles it:* the user's decision. For (a), T-LOWER.machine's cancel clause proved with a run-time mask.
> *Blocks:* T-LOWER, 08's lowering table.
> *Default if unresolved:* (b). The calculus keeps every construct, and 08 lists the three as lowering gaps with corpus programs that exercise them rejected. This default restricts two decided positions: "compiler never stale" (every construct lands with its lowering) and "effect handling is erased" (U6), since three constructs of the calculus then have no lowering; it is recorded as such, as R-ALLOCORACLE is for U20.

<a id="oq-43"></a>

> [!IMPORTANT]
> **Open question OQ-43: Determinism up to renaming at every step, and two-run facts with array steps** (critic 6 (TwoRun)) **[settle by proof]**
> *Why open:* T-2RUN, OQ-4's option (b), T-SOUND's every-allocator observation, and the laws whose two sides allocate in different orders (L-NU's ν/ν, L-STATE with a cell allocated on one side only) need determinism up to renaming for every run of the calculus. Two pieces are missing. (1) `head_rename` (`experiments/TwoRun/TwoRun/Rename.lean:359-394`) has cases for the pure, memory, host and array steps only; the capture steps, `count`, `countTry` and `boundedFix` have none (04 §8). (2) `freshRun_det`, `fresh_run_image` and `run_sim` hold only for runs with no array step, because `tab`, `idx` and `drop` compute `ℓ + i`, which a permutation of `Loc` does not preserve; their source says the extension "under a renaming of blocks rather than of single locations" is not derived (`experiments/TwoRun/README.md`, *Step 1*).
> *Options:* (a) extend `head_rename` to every `Head` constructor, and state the two-run facts for runs with no array step, the binary halves at programs with arrays marked not proved; (b) also prove them for array steps under block renamings (permutations of blocks that preserve each block's consecutive cells); (c) laws over programs with arrays go through T-BINFP only (OQ-4 (a)).
> *What settles it:* `head_rename` built at every constructor of today's `Head`; for (b), `def BlockRenameRun : Prop` (runs with array steps are invariant under a block permutation) proved, or a configuration with an array step at which two fresh runs are related by no block renaming, every hypothesis discharged.
> *Blocks:* T-2RUN, T-DET's renaming form, T-SOUND, T-NAH's T-REN route at programs with arrays, L-REN's run half, L-NU (ν/ν), the allocating forms of L-STATE, OQ-4 (b).
> *Default if unresolved:* (a). Every law is stated for every program; (a) limits the route of the binary halves, not the calculus.

<a id="oq-44"></a>

> [!IMPORTANT]
> **Open question OQ-44: What the open-lend component `σ` holds** **[settle by proof]**
> *Why open:* O-W says `σ` is `TW`'s own `ps`/`rs`. Three facts do not fit. (1) `ps` records 6.64 frames only; 6.65 and 6.66 leave it unchanged (`TW.mutFold`, `TW.mutUnfold`, `Core/World.lean:135-144`), so a 6.65 lend open across a stop has no `ps` entry. (2) The records of open 6.64 frames are already in `ls` (`TW fρ ps (rsOf ls)`, `Tagged`, `Core/EffDefs.lean:29`), so what `σ` adds for them is a selection, not data. (3) Under OQ-9 (b) the stop is unchanged and `σ` is the stack of lends to re-lend (GhostEnd's `LStack` with `ReLend`, `Stacked.lean:93-107, 158`), which is not a set of open frames at all. Separately, the relation reads `σ` as the lends a term sits under (lifetimes, `TabAt`), while `wpG` needs the frames a run must close (D-WPG's `τ`); these are the same lends seen from the borrower and from the lender's continuation, and D-W carries both by keeping `τ` a parameter of `wpG_W`.
> *Options:* (a) `σ` = GhostEnd-form entries `⟨ℓ, x, T, k, R, α⟩`, with `imm` entries linked to `ps` records and `mut` entries resource-only (D-W as written); (b) a `TW` constructor recording 6.65 frames, so that `σ` is literally a selection of `ps` (a kernel definition change to `TW`); (c) `σ` as two lists, `σ_close ++ σ_under`, split at the handler (audit M8's remedy).
> *What settles it:* its own probe, after OQ-9's: `def OpenMutFrameCancel : Prop` (05 §12.2), a 6.65 lend by `withbor2U` open at an affine stop whose continuation is cancelled. Under (a) and (c) it fixes what a stop must record of a 6.65 lend; `def MutLendRecorded : Prop` (every 6.65 lend a resuming stop leaves open is recorded in the `τ'` the table receives, as a `mut` entry) is proved or refuted at that configuration. A statement that 6.65 lends appear in `ps' ∖ ps` cannot hold without (b), since 6.65 leaves `ps` unchanged.
> *Blocks:* D-W, D-ORD, D-STOP, D-ARISE, T-ARISE, T-FRAME.
> *Default if unresolved:* (a).

<a id="oq-45"></a>

> [!IMPORTANT]
> **Open question OQ-45: Does the arising guard stay in the clauses?** **[settle by proof]**
> *Why open:* D-ARISE makes `TabAt_W` a `TW` invariant (T-ARISE). The relation's `⊸`, `∀` and `U` clauses still quantify over argument resources that need not arise; #285 restricted them by a guard (`guardS`, `Arising.lean:169`) because without it GFP fails at `[x]` (`not_gfpAt_below`, `gfp:experiments/GhostEnd/GhostEnd/Below.lean:196`). With the guard, a callback read at `σ` is obliged on no argument below the stack (`below_excluded`, `Arising.lean:446`), which is why the `withbor` row reads it at `σ·y`.
> *Options:* (a) keep `guard_W` at `U`, `⊸`, `∀`, discharged at every elimination by T-ARISE; (b) drop it, with every clause's quantifier restricted to worlds at which the composite arises.
> *What settles it:* first, whether the invariant is achievable: `theorem tabAt_of_TW` (05 T-ARISE.0: every `TW` world, with `σ` consistent with its `ps`, has `TabAt_W` at every part a term holds) proved by induction on `TW`'s constructors, or refuted by a configuration that arises. Until it is proved, D-ARISE's claim that `TabAt` is a `TW` invariant is not in force, and the guard is a guard. A free-standing premise `HeldUnder ρ σ` (the part's borrow cells are views the stack's lends handed it, or lie away from the stack's places) that neither `TW` nor `Tagged` carries (`TW`, `Core/World.lean:110`, has no stack index): stated so, it would relocate the guard into a premise rather than deriving it. The `TW`-derived fact that would replace it is a constraint on which `ps` records a part holds: every borrow cell of the part is either inside a frame record of `ps` whose lend is an entry of `σ` (a view handed by the stack) or at a location no entry of `σ` lends; 05 states T-ARISE.0 with that constraint, `HeldUnderTW ρ ps σ`, defined from `ps` and `σ` alone; whether the lemma holds with it is what this question's first step settles. Then `def GuardFreeAgrees : Prop` (the guarded and guard-free relations agree on every resource with `TabAt_W`), proved or refuted; and the configuration of `not_gfpAt_below` checked at (b).
> *Blocks:* D-ARISE, D-REL, D-SEM, T-FP (07).
> *Default if unresolved:* (a).

<a id="oq-46"></a>

> [!IMPORTANT]
> **Open question OQ-46: The world a stored payload is read at** **[settle by proof]**
> *Why open:* `ptoMutS` and `ptoImmS` store the payload's predicate at `ls₀`, the members of `ls` strictly longer-lived than the cell (`Core/Relation.lean:43-54`), which makes them monotone along `Ext` (T-MONO). The relation families beside the kernel read a `Mut`/`Imm` payload at the kernel's `vC` with no stack (audit M1), so a `U` inside a `Mut` payload, a stored generator, `Aff` or a `ν` cell, where lend-spanning callbacks get stored, is read at the wrong relation. At `W`, the payload must be read at some `σ₀`.
> *Options:* (a) `σ₀` = the entries of `σ` strictly longer-lived than the cell, as `ls₀`; (b) `σ₀ = []`, payloads stack-free.
> *What settles it:* T-MONO at the `Mut` clause and `wpG_M_frameX` at `W`, at each option; a stored callback (`Ref(U C)` holding a callback lent across a stop) built at `W` with every hypothesis discharged.
> *Blocks:* D-REL (`Imm`, `Mut`), T-MONO, K-NU (stored generators), OQ-28.
> *Default if unresolved:* (a).

<a id="oq-47"></a>

> [!IMPORTANT]
> **Open question OQ-47: Is reduction in every context contained in `≡`?** **[settle by proof]**
> *Why open:* Every reduction-shaped law (06 §1.3) gets its binary form from a join, if the replacement relation "equal up to instances of `M` replaced by instances of `N`", closed under the law's `D`, is a stuttering simulation of the machine under a fixed allocator (06 §1.5, T-SI2). No such relation is built over the kernel. Two cases are not checked: an instance substituted into a thunk later copied under `!` at `unr`, and an instance captured into `κ` by an outer `[op]` and then resumed or cancelled. TwoRun's `run_sim` (`experiments/TwoRun/TwoRun/Sim.lean:253`) is a simulation of this kind for location renaming, with no logical relation.
> *Options:* (a) T-SI2 holds for every `D` named in 06 §1.3, and OQ-4 (b) carries every reduction-shaped law; (b) it holds for `D` = equality only, and the capture-relating laws (L-ALG, L-HFWD, L-NAH) need `≈`; (c) it fails, and every binary form needs `≈`.
> *What settles it:* `def StepInclusion (D : Expr → Expr → Prop) : Prop` (for `D` closed under substitution and plugging, and `M ↦ N` allocation-free, `M ≡ N`), proved per `D`, or a configuration at which joinable sides give different observations, every hypothesis discharged.
> *Blocks:* the binary forms of L-ALG, L-ALG0, L-GEN, L-HRET, L-HOP, L-HFWD, L-EXC, L-YIELD, L-DIV, L-FIX, L-SUM (4), L-SIGNAL, L-W, L-BETA, L-NAH, L-REN, L-BOR, L-TAIL; OQ-4's option (b); T-2RUN (07).
> *Default if unresolved:* every binary form is stated and marked not proved; the unary halves stand.

<a id="oq-48"></a>

> [!IMPORTANT]
> **Open question OQ-48: Answering/control commutation at an affine operation, on the kernel** (audit m2) **[settle by proof]**
> *Why open:* L-INTER holds in TR T13.13's special case. P13.14 shows it failing at an affine operation whose clause cancels, but P13.14 was computed by hand in the sibling calculus (audit m2), and a blocker must be machine-checked (00 §0.2 item 6).
> *Options:* (a) build P13.14's two programs in `CDerives` and show their observations differ (`adequacyD_obs`, `Core/EffPrograms.lean:41`), so that L-INTER is stated at linear operations only; (b) withdraw P13.14 and state L-INTER at `aff`.
> *What settles it:* two closed `CDerives` programs at `F 1 ⊕ …` whose `Obs_A` differ under every allocator, every hypothesis discharged, or a proof of the law at `aff`.
> *Blocks:* L-INTER, T-COMODEL's "one protocol" (05), the capability-with-control row of 06 §5's table.
> *Default if unresolved:* L-INTER stated under T13.13's hypotheses only, with linear `o`, as R-INTERLIN.

<a id="oq-49"></a>

> [!IMPORTANT]
> **Open question OQ-49: The composite handler as a kernel term** **[settle by proof]**
> *Why open:* L-HFUSE needs `H₂ ∘ H₁`. Two mismatches. (1) Its clause must pass `c₁_i` a continuation landing in `F_{n₂:E₂⊕Σ} R₁`, while the composite's `κ` lands in `F_Σ R₂`; `κ_n(H, K)` is built by the machine (`kappa`, `Paper/S3_Dynamics/Definitions.lean:438`), and it is not known whether a continuation of the needed type can be written in the kernel's terms with its cancel entry and typed at `kTy` (`Core/EffRules.lean:976`). (2) A body that performs `n₂` itself has those operations handled by `H₂` on the left of the law and forwarded unhandled by a one-name `hnd_{n₁}` on the right, so the two sides are not at the same type unless the body's row excludes `n₂`, or the composite handles both names (a two-name handler, which the kernel does not have).
> *Options:* (a) the needed continuation is a term, and `H₂ ∘ H₁` types by `[handle]` for bodies whose row excludes `n₂`; (b) it is not, and L-HFUSE is stated only for clauses that resume in tail position (where no continuation needs re-typing) and `n₂`-free bodies; (c) a two-name handler `hnd_{n₁,n₂}`, a new construct, which must be justified against C-9.
> *What settles it:* a `CDerives` derivation of `H₂ ∘ H₁` at `retTy`/`clausesTy`, or `def CompositeClauseTerm : Prop` refuted.
> *Blocks:* L-HFUSE; fusion in the lowering (08).
> *Default if unresolved:* (b), as R-FUSETAIL.

<a id="oq-50"></a>

> [!IMPORTANT]
> **Open question OQ-50: How the linear use of a continuation is observed** **[settle by proof]** **[user decision]**
> *Why open:* T-LIN and T-FIN (1) say a `κ` is used exactly once at `lin` and at most once at `aff`. The unary relation sees only resources. A `κ` that captures nothing owned can be dropped or used twice without any effect on `NoOwn` (`Core/EffDefs.lean:38`) or on safety, so T-FP alone does not state it. Today it holds only by typing (`kTy`, `Core/EffRules.lean:976`). No syntactic preservation theorem exists to carry typing along a run (07 §6, T-PRES).
> *Options:* (a) a syntactic invariant along runs: subject reduction over `CDerives` extended to configurations holding `κ` values (with OQ-52); (b) the TR's technique: a one-shot continuation is a heap cell freed by its use, so "used twice" is a use after free and "dropped" is a leak (`docs/effects-tr/12-sources.md` §12.3 item 4, D3.2/D4.4, T5.2.3–4). This is a machine change and a kernel definition change, which needs a SPEC entry; (c) state only the resource half: no leak and no double release through a `κ`, from T-LEAK and T-ADEQ.
> *What settles it:* for (b), a Lean configuration in which the cell form's `[op]` and `resume` steps keep `head_det_eff` (`Core/Steps.lean:596`) and every effect row of T-COMPAT; for (a), the user's decision whether a syntactic preservation theorem is wanted; for (c), nothing beyond T-LEAK.
> *Blocks:* T-LIN, T-FIN (1), L-C, L-P, T-LOWER's "resume once" class.
> *Default if unresolved:* (c), with T-LIN and T-FIN (1) stated in their resource form and marked, as R-LINRES.

<a id="oq-51"></a>

> [!IMPORTANT]
> **Open question OQ-51: Adequacy observed at a row** **[settle by proof]**
> *Why open:* T-ADEQ is stated at `F 1` with the empty row. A closed program whose row holds only host-handled or abortive operations (a `main` that may `raise`) has no adequacy statement except through an outermost handler. T-SAFE's open form gives the stops, but nothing names the observation: which stops a closed program may end at, and what the outside sees there.
> *Options:* (a) adequacy only at `F 1`; every program is closed by explicit handlers (and host handlers, OQ-30); (b) adequacy at `F_Σ 1` for a designated `Σ` of observable operations, the final configuration being a value or an allowed stop with a `NoOwn` leftover.
> *What settles it:* (b)'s statement proved from T-SAFE's open form and `reclaim` (`Core/Fundamental.lean:534`), or a configuration where an allowed stop at `W₀` has an owned leftover.
> *Blocks:* T-ADEQ's statement for host programs (with OQ-30), T-LEAK at a stop of a closed program.
> *Default if unresolved:* (a), as R-ADEQF1.

<a id="oq-52"></a>

> [!IMPORTANT]
> **Open question OQ-52: Is a syntactic subject-reduction theorem part of the calculus?** **[user decision]**
> *Why open:* Type soundness here is semantic: T-FP and T-ADEQ, with preservation of the typed world (T-PRES). No declaration states subject reduction for `CDerives`. The elaborator, the lowering (T-LOWER) or OQ-50 (a) may want one, and it is a large induction over every rule and every step of 04.
> *Options:* (a) not part of the calculus; (b) part of it, over configurations including `κ` values and cancel states.
> *What settles it:* the user's decision, informed by OQ-50 and OQ-23.
> *Blocks:* OQ-50 (a); T-LOWER if a lowering proof needs it.
> *Default if unresolved:* (a).

<a id="oq-53"></a>

> [!IMPORTANT]
> **Open question OQ-53: Is the elaborator proved, or each program checked?** **[user decision]**
> *Why open:* T-ELAB.typed holds today per program: the certifying checker types each elaborated program (SPEC §18 *Baseline*, `SPEC.md:2246`). T-ELAB.model and T-ELAB.comodel are about what an elaborated handler means, and can be checked only as theorems about each schema's emitted term. A proved elaborator (every accepted source program elaborates to a derivable term) is a different, larger theorem over `Frontend/`.
> *Options:* (a) per-program certifying check for typing, plus T-ELAB.model/comodel proved per schema over the schema's term shape; (b) an elaborator-correctness theorem over the frontend.
> *What settles it:* the user's decision.
> *Blocks:* T-ELAB; the surface work of #188.
> *Default if unresolved:* (a).

<a id="oq-54"></a>

> [!IMPORTANT]
> **Open question OQ-54: The lend stack `σ` under a fork** (critic 6 (threads)) **[settle by proof]**
> *Why open:* D-W makes `σ` one LIFO stack of open 6.64 frames (O-W). A fork splits `ρ` by `⋆`. Open frames have a lineage (`TW`'s `rs`, `Core/World.lean:110`), and LIFO closing is what T-LEAK and T-FIN rest on. Nothing in the calculus says whether two threads may each hold frames opened before the fork, or whether `σ` becomes a forest.
> *Options:* (a) `σ` stays a stack, and a fork takes no open frame (a thread starts at `σ = []` relative to its parent's top); (b) `σ` a forest, with a frame owned by exactly one branch.
> *What settles it:* a Lean configuration at `W` of a fork under an open 6.65 frame, at (a) and at (b).
> *Blocks:* nothing now. D-W must not be stated in a way that excludes (b): stated over a list, (b) is a change of D-W.
> *Default if unresolved:* (a); recorded so that D-W's statement is checked against it.

<a id="oq-55"></a>

> [!IMPORTANT]
> **Open question OQ-55: The declaration kind at the surface** (decision 55) **[user decision]**
> *Why open:* Decision 55 fixes the kind per effect, `fn` (answering) or `ctl` (control), "an effect has one kind of operation" (`docs/decisions.md:686`; `EffSig.answering`, `Frontend/Elab/Effects.lean:63`). In the calculus one signature has two implementations, a model and a comodel (O-MODEL, O-COMODEL); whether an operation is answered by a capability or by a handler is a property of the handler, not of the declaration. PP08's constraint still applies: a theory with an abortive operation has only the empty comodel [via 12-sources], so such an effect has only handlers. Surface syntax is a one-way door.
> *Options:* (a) keep the kind on the declaration, the comodel/model choice following from it; (b) declarations carry the signature only, and the handler declares which it is; (c) (b), with the kind inferred from the clauses.
> *What settles it:* the user's decision, after OQ-1.
> *Blocks:* T-ELAB; checklist item C-7 (08 §8); the surface of #188.
> *Default if unresolved:* (a).

<a id="oq-56"></a>

> [!IMPORTANT]
> **Open question OQ-56: Operation types that mention the lend's variable or the site's lifetimes, at a borrow callback** (finding on K-BOR's row class) **[settle by proof]** **[user decision]**
> *Why open:* The full class of rows a borrow callback may perform is `BorOK_x Σ ≜ Σ.NZ` (03 K-BOR). Today's `Row.Unwind x` adds, besides the abortive conjunct R-T1, that every operation's argument type is free of `'x` and outlives every lifetime (`Core/EffBorrow.lean:133-134`), and D-TABLEOK's conjuncts (3)-(4) carry the same. Those conjuncts exclude the programs that motivate tier 2 (01 §5.3): an asynchronous read into a local buffer passes the lent `Mut 'x Buf` to the operation, and a generator yielding views of its borrowed buffer answers `Imm 'x T`. An operation type cannot simply mention `'x`: the callback's row is the borrow's result row (`F_Σ(res_k)`), which lies outside `'x`'s scope (K-BOR's premise `x ∉ fv(A, B)`).
> *Options:* (a) R-CLOSEDOP: operation types at a borrow callback are closed and free of `'x` (today's conjuncts), a named restriction; (b) lifetime-polymorphic operations: an operation `op : ∀'y ⊏ c. A['y] ↠^q B['y]` (03 §6, *The full class*), instantiated at the lend's `'x` at the perform, whose clause is parametric in `'y`, so that the view it receives cannot outlive the stop; its continuation, which holds the lend, is bounded as OQ-28 bounds a stored continuation; (c) operation types that mention only lifetimes outside the borrow (the site's `Δ`), i.e. `Data_x` without "outlives every lifetime".
> *What settles it:* `def LifetimePolyOpTableOK : Prop` (03 §6: `opTable` at a row with a lifetime-polymorphic entry satisfies D-TABLEOK at every instantiation below the lend), proved or refuted by a configuration that arises; the async-read program of 01 §5.3 typed at (b); then the user's decision.
> *Blocks:* K-BOR, D-TABLEOK (3)-(4), OQ-40, the tier-2 programs of 01 §5.3.
> *Default if unresolved:* (a), as R-CLOSEDOP.

<a id="oq-57"></a>

> [!IMPORTANT]
> **Open question OQ-57: The closing-obligation list `τ` as an index beside `W`** (00 §0.2 item 1) **[settle by proof]**
> *Why open:* A run that resumes a continuation holding open 6.64 frames must close them (D-STOP's value clause). The frames a run holds the closing obligation for, `τ`, are not the stack `σ` a term sits under: a suspended run passes `τ'` to its table and a resumed run receives it. 05 states `τ` as an explicit index of `wpG_W(τ)`, `ewp_W(τ)` and the table (D-WPG, D-EWP, D-TABLE). That is an index beside `W = (ρ, ls, σ)`, which 00 §0.2 item 1 says is a defect to report, not a design.
> *Options:* (a) `τ` stays an explicit index, as 05 writes it, recorded here as a defect against 00 §0.2 item 1; (b) the obligation as a field of each `σ` entry, `closer ∈ {outer, this-run}`, so that `τ = σ.filter (·.closer = this-run)` and `W` carries it; (c) `σ` as two lists, `σ_close ++ σ_under`, split at the handler (OQ-44 (c), audit M8).
> *What settles it:* `def ClosingInW : Prop` (05 §4): `ewp_W(τ)` at `W = (ρ, ls, σ)` equals the τ-free `ewp` at the world whose entries carry `closer` as (b) defines, at every `τ` and `W`; proved, or refuted by a configuration where the two disagree.
> *Blocks:* D-WPG, D-STOP, D-TABLE, D-EWP, D-SHARE, D-OWED, D-OPTAB, D-CANCELTAB, T-FRAME, OQ-44.
> *Default if unresolved:* (a), with the defect recorded.

<a id="oq-58"></a>

> [!IMPORTANT]
> **Open question OQ-58: Is Core the `σ = []` instance at `U` (and at `share`, `KapRel`)?** (finding on T-NIL) **[settle by proof]**
> *Why open:* At `σ = []` the new `U` clause quantifies over every `W' ⊒ W`, which ranges over non-empty stacks `τ` (05 T-NIL). So the new clause is today's `vCE` thunk clause (`Core/Relation.lean:127-128`) conjoined with obligations at every non-empty extension, under both OQ-8 candidates; the same holds of `share` and `KapRel`. `new ⊆ old` is immediate (instantiate `τ = []`). `old ⊆ new` is an obligation at every rule that introduces a `U` value, a `share` or a `KapRel`, and it is not derived. If it fails, the kernel's `vCE` thunk clause is strictly strengthened: Core's relation changes meaning, `fundamentalC` and every Core theorem do not transfer by definition, and they must be re-proved through T-FP at `W` under E-W.
> *Options:* (a) `old ⊆ new` holds at every introduction row, and T-NIL makes Core the `σ = []` instance; (b) it fails, and Core's `vCE` is redefined as the new clause, with every Core theorem re-proved through T-FP at `W` (a kernel definition change under E-W).
> *What settles it:* the first probe `def NilAgreesU : Prop` (05 T-NIL): a thunk value in today's `vC (.thunk C)` at `ls` is in `𝒱⟦U C⟧` at `(ρ, ls, [])`, i.e. forced at every one-entry extension `[e]`; proved at the `thunk`, `fixSelf`, `κ` and handler-clause rows, or refuted by a configuration that arises, every hypothesis discharged. It is run next to OQ-9's probe.
> *Blocks:* T-NIL, T-CONS.2-3, T-FP's corollaries as stated, OQ-8's criterion (i), every claim that Core is the `σ = []` instance.
> *Default if unresolved:* none: no section claims that `vC`/`cC` are the `σ = []` instance "by definition"; each claims "equal by T-NIL, proved per introduction row, unknown at `U`".

<a id="oq-59"></a>

> [!IMPORTANT]
> **Open question OQ-59: How a handler reaches into the scope of a scoped operation** (OQ-12) **[settle by literature]** **[user decision]**
> *Why open:* K-SCOPE (03 §9.1, not adopted) gives a scoped operation its signature form, its term, its typing, its machine reading (the scope runs as an ordinary thunk) and the law that replaces algebraicity (L-SCOPE: algebraic in the continuation, not in the scope). What it does not give is whether the handler of `n` handles the operations of `n` performed inside the scope, and how: a deep scoped handler must reinstall itself inside the scope and thread its carrier through the scope's result, which in the literature takes a distributive law or a weaving function. Which of these fits a linear calculus with `κ` qualifiers is not known.
> *Options:* (a) the clause receives the scope unhandled and may handle it itself (the scope stays in `n`'s row); (b) the scope is handled before the clause receives it, the clause seeing `U(F_{Σ} S_C)` at its own carrier; (c) scoped operations elaborate into algebraic ones (hefty algebras), leaving no scoped construct in the kernel.
> *What settles it:* a literature check of the sources OQ-12 names, then the user's decision.
> *Blocks:* K-SCOPE's clause type and step, L-SCOPE.
> *Default if unresolved:* none: K-SCOPE's handling of the scope is unspecified until settled, and R-FO holds.

<a id="oq-60"></a>

> [!IMPORTANT]
> **Open question OQ-60: The asynchronous scheduler against the negative-recursion cut-off** (U7, U16) **[settle by proof]** **[user decision]**
> *Why open:* Async is in the lead axis (01 §4, U7). L-ASYNC (06 §4) specifies its signature and its laws. A scheduler written as a deep handler of `Async` keeps a run queue of the continuations it captured; its carrier is then `S ⊸ F_Σ R` with `S` a queue of `K_aff(1, S ⊸ F_Σ R)`, a negative recursive type, which R-NONEGREC (OQ-31) excludes. A scheduler over codata keeps a queue of threads as `U(Loop_Σ 1 1)` values (K-NU), each observation one step up to its next suspend; `ν` is positive, and the queue is an ordinary value or a lent cell. The two differ in what a thread may hold across a suspend: under the codata form a thread's lends across a suspend are those of a stored `Loop_Σ` (OQ-28, OQ-46).
> *Options:* (a) the deep-handler scheduler, which needs OQ-31 (b), conflicting with no step-indexing; (b) the scheduler over `Loop_Σ` codata, with `spawn` and `suspend` as observation boundaries; (c) the scheduler as a comodel whose state is a run queue in a lent cell, threads as codata, operations as calls.
> *What settles it:* `def DeepSchedulerCarrier : Prop` (the deep scheduler's carrier is definable at T-DEF's structural recursion), refuted or proved; the async program of 08 §9 typed at (b); then the user's decision.
> *Blocks:* L-ASYNC, the async program of 08 §9, OQ-31's statement, OQ-28, OQ-46. L-ASYNC also depends on OQ-61 (`spawn`'s parameter names the `Async` row) and OQ-7 (finalising a parked queue).
> *Default if unresolved:* (b); the deep-handler scheduler is excluded by R-NONEGREC.

<a id="oq-61"></a>

> [!IMPORTANT]
> **Open question OQ-61: Operation types that perform their own effect (effect-recursive signatures)** (finding on L-ASYNC against K-SIG) **[settle by proof]** **[user decision]**
> *Why open:* An operation whose parameter or answer performs the effect that declares it names its own row inside its own operation type: `spawn : U(F_{n:Async ⊕ Σ} 1) ↠^{lin} 1`, a `fork`, an `ask` that answers a computation of the same effect. As built a row inside a type is a finite `CTy.effOf` chain (`Core/Types.lean:155-157`), so such a signature would be an infinite type term, and `⟦Σ⟧`'s entry would read `𝒞⟦F_{n:E ⊕ Σ} …⟧` at the table being defined, which T-DEF's structural recursion does not reach. 02 K-SIG excludes it ("a signature cannot contain its own row in an operation type"). The asynchronous program (06 L-ASYNC, 08 §9.2), fork-style threads (U16) and the higher-order algebraic effects of OQ-12's literature need it. The occurrence is positive in a parameter (`P_A` enters `opTable`'s stop allowance positively, D-OPTAB) and negative in an answer (`P_B` is assumed by the continuation obligation, D-SHARE).
> *Options:* (a) not provided: no operation type mentions its own signature's row; an effect that needs it takes the thread at a row given from outside (`spawn_Σ : U(F_Σ 1) ↠ 1` with `n ∉ Σ`), so a spawned thread cannot itself spawn through the same name; (b) a recursive signature binder in parameters only, `E = μe. {op_i : A_i[e] ↠ B_i}` with `e` occurring only positively in parameters, `⟦μe. E⟧` the least fixed point of the table functional (K-SELFROW, 03 §9.12); (c) as (b) with occurrences in answers too, which is negative and needs OQ-31 (b), conflicting with no step-indexing; (d) reference by name: an operation type mentions `self`, interpreted as the row at which the operation is performed, the row a meta-index of the perform (with OQ-13).
> *What settles it:* `def SelfRowPositiveLFP : Prop` (03 §9.12: the table functional of a signature whose self-reference occurs only positively is monotone, by `ewp_mono` in the table, `Core/EffWp.lean:795`, and `opTable_mono`, `:951`; its least fixed point satisfies D-TABLEOK and the relation stays defined without a step index), proved or refuted by a configuration that arises; for (d), the `[perform]` rule at `self` typed and its compatibility at `W`; then the user's choice.
> *Blocks:* K-SIG, K-ROW, K-INT, T-DEF, OQ-31's statement, L-ASYNC, the async program of 08 §9.2, OQ-60, threads (OQ-18).
> *Default if unresolved:* (a), as R-NOSELFROW. Under it L-ASYNC's `spawn` takes its thread at an outer row, and a spawned thread spawns only through an enclosing scheduler's name.

<a id="oq-62"></a>

> [!IMPORTANT]
> **Open question OQ-62: Folds and counted loops at a row** (finding on 03 §2) **[settle by proof]** **[user decision]**
> *Why open:* The kernel's structural recursion schemes have pure algebras: `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ …`, `foldOwn`, `foldReuse` at `F R` (`Core/Fundamental.lean:311-327`), `countFold`, `countTry` with pure steps (`:183-191`). A raise inside a fold (SPEC §18 *Not provided*, K4), a yield from a tree traversal, or a loop over finite data whose body resumes an operation is therefore outside every kernel rule; today such a loop is a div loop (SPEC §16 *Effectful bodies*) or rejected (a `for` over data whose body resumes). Typing these constants at `F_Σ R` is a change to kernel rules. `foldImm`'s algebra runs under an `Imm 'y` lend, so an effectful algebra is a borrow callback that performs and inherits R-T1, OQ-9 and OQ-56.
> *Options:* (a) not provided: algebras and steps pure; (b) K-FOLDΣ (03 §9.13): each constant at a callback row `Σ`, `foldImm[Σ]` under `BorOK_y Σ` as K-BOR's schema, `foldOwn[Σ]`, `foldReuse[Σ]`, `countFold[Σ]`, `countTry[Σ]` at any row, each step's run an `ewp_W` at `opTable ⟦Σ⟧`; (c) (b) at abortive rows only first (`Row.Unwind`), resuming rows after OQ-9.
> *What settles it:* the compatibility of each constant at a row at `σ = []` (by induction on the structure for folds and on the count for loops, each step at `ewp`), `foldImm[Σ]`'s at a resuming row after OQ-9's probe, then the user's choice.
> *Blocks:* K-FOLDΣ, total iteration from finite data with effects (SPEC §16, §18 K4), L-FOLD, 08 §6's fold row, 01 §3.2's iteration row.
> *Default if unresolved:* (a), as R-PUREFOLD.

<a id="oq-63"></a>

> [!IMPORTANT]
> **Open question OQ-63: A partial-correctness `wp` beside `ewp_W`** (00 §0.2 item 1; finding on OQ-15 (b)) **[settle by proof]**
> *Why open:* OQ-15's option (b) reads div as a row entry and needs a relation that does not demand termination: `wpG` asks `∃ k'. ARun A k μ e k' μ' t` (`Core/EffDefs.lean:36`). 05 D-EWPP defines that relation in full at `W`: `wpGP_W`, which takes `wpTSD`'s every-run quantifier (`Core/Demonic.lean:223`) and replaces its conclusion ("every run continues to a value", total correctness) by safety at every reachable configuration and the post at every final one (partial correctness), and `ewpP_W`, its greatest fixed point into "value in `Q`, or a stop `Tb` allows". That is a second wp family beside `ewp_W`, which 00 §0.2 item 1 makes a defect to report.
> *Options:* (a) `ewpP_W` as written in D-EWPP, recorded here as a defect, used only at rows holding `div`; (b) one definition with a mode: `ewpMode m` for `m ∈ {total, partial}`, the least fixed point over `wpG_W` or the greatest over `wpGP_W` of one step functional, every lemma of D-EWP and T-FRAME proved once for both modes; (c) no partial-correctness relation: div is codata only (OQ-15 (a)).
> *What settles it:* `def EwpModeUniform : Prop` (05 D-EWPP: every fact D-EWP carries and every frame of T-FRAME holds at both modes by one proof), proved or refuted; with it, T-STOP at `ewpP_W` and `ewp_W ⊨ ewpP_W`.
> *Blocks:* OQ-15 (b), K-HDIV under (b), L-DIV (b), D-EWPP, T-FRAME at a `div` row.
> *Default if unresolved:* (a), with the defect recorded; it is in force only under OQ-15 (b).

<a id="oq-64"></a>

> [!IMPORTANT]
> **Open question OQ-64: The effect-dependent laws of rows** (finding on 06) **[settle by literature]** **[settle by proof]**
> *Why open:* A row type justifies equations by itself: discarding a computation whose row neither diverges nor raises and whose result drops, duplicating one whose row is idempotent, and swapping two whose rows commute. 06 L-DISCARD, L-COPY and L-COMMUTE state them graded by row and qualifier. Their standard source, Kammar & Plotkin, *Algebraic foundations for effect-dependent optimisations* (POPL 2012), is named in #235's bibliography and was not read for this specification: the copy at the author's page was not retrievable when fetched. The exact side conditions in a linear calculus with finalisers and borrows (which operations count as read-only, whether a capability call is discardable, how finalisers interact with discard) are not settled.
> *Options:* (a) the three laws as 06 states them, with the side conditions derived from `opTable`'s entries and the grade; (b) as (a) with the side conditions transcribed from Kammar-Plotkin's effect-dependent theory once read; (c) only L-DISCARD, the others left to OQ-4.
> *What settles it:* reading the primary source, upgrading the [R] marks in 06; then each law's unary half proved at `W` (an `ewp_W` interchange at the row's table).
> *Blocks:* L-DISCARD, L-COPY, L-COMMUTE; dead-call elimination and reordering in the lowering (T-LOWER, 08 §6); the equational content of rows.
> *Default if unresolved:* (a), with the citation marked [R].

<a id="oq-65"></a>

> [!IMPORTANT]
> **Open question OQ-65: An operation form with an explicit cancel continuation** (finding on L-ALG) **[settle by proof]** **[user decision]**
> *Why open:* L-ALG's binary form `K[op(V; y.M)] ≡ op(V; y.K[M])` holds at plain frames. At a finaliser frame `ubind(N, D)` the left side's `κ` runs `D` on cancel, and no term `op(V; y. K[M])` carries `D`, because the kernel has no operation form with an explicit cancel continuation (06 L-ALG, *At a non-plain frame*). Handler frames of other names are L-HFWD and borrow frames are L-BOR's resuming half; finaliser frames are the remaining case.
> *Options:* (a) algebraicity's binary form is stated at plain frames, handler frames of other names and borrow frames only; (b) a derived form `op(V; y.M | D) ≜ (perform_{n,i} V) then y. M unwind D`, with L-ALG at a finaliser frame stated as `K°[op(V; y.M)] ≡ op(V; y. K°[M] | D_K)`, which needs a finaliser at the operation's row (OQ-7 (a)).
> *What settles it:* the `[then]` derivation of (b)'s form at a resuming row, which needs OQ-7 (a); then the user's decision.
> *Blocks:* L-ALG's binary form at finaliser frames.
> *Default if unresolved:* (a), as R-ALGPLAIN.

<a id="oq-66"></a>

> [!IMPORTANT]
> **Open question OQ-66: Is cancel an instance of Ahman & Bauer's signal?** (finding on L-SIGNAL) **[settle by literature]**
> *Why open:* Read in Ahman & Bauer, arXiv 1910.11629, §3.2, the text after eq. (3): when a co-operation sends a signal, "the rest of the user code M is skipped and the control proceeds directly to the corresponding case of the finalisation part F", the clause `kill s ↦ N_s`; Thm 7's finalisation map has the case `φ_γ(ι₂ s) = ⟦N_s⟧`. Only a signal of an *enveloping* runner bypasses the inner `F` ("unless some enveloping runner sends a signal"). So a runner's own signal discards the remaining continuation and runs finalisation, which is the shape of our cancel. The differences found: a signal discards the kernel state (eq. (1), `getenv(λc. kill s) = kill s`, `setenv(c, kill s) = kill s`), and `N_s` does not receive the final state `c`, whereas our cancel runs `D_K`, the finalisers of the frames the continuation holds, each on its own resources; and A-B's finalisation is one clause per `run`, ours one per frame, LIFO.
> *Options:* (a) cancel is read as a signal of the handler's own region (tensor-with-kill), with `D_K` the finalisation and the kernel state empty; (b) cancel is not classified as a signal; L-SIGNAL stands on its own free-theory derivation (L-HOP then L-W).
> *What settles it:* a reading of A-B §4 (λcoop's typing and semantics of `kill`) against K-CANCEL's steps, and of whether per-frame finalisation is a nesting of runners (A-B §6, Ex. 8, nesting); the literature check of OQ-18 for threads.
> *Blocks:* the classification in L-SIGNAL, 02 §11, 07 T-FIN, 08 §7 item 3, OQ-18.
> *Default if unresolved:* (b): no law depends on the classification.

<a id="oq-67"></a>

> [!IMPORTANT]
> **Open question OQ-67: The proof obligation of a handler that spans observations of a div computation** (U5) **[settle by proof]**
> *Why open:* The user decided that several effects at once "need to work, full stop" (U5), and a timeout or retry around the whole reconcile loop is such a case. K-HDIV (03 §9.2) specifies the handler around a div computation in both readings of OQ-15: under (a) as a `hndLoop` whose unfold state carries the handler's state and any continuation captured in one observation and resumed in the next; under (b) as the ordinary `[handle]` at a `div` row, read by `ewpP_W` (D-EWPP, OQ-63). What is not proved is its compatibility: under (a), a `κ` stored in the loop's state across an observation is read at the world OQ-46 fixes and bounded as OQ-28 bounds a stored continuation; under (b), `handle_compatC` at `ewpP_W`.
> *Options:* none of design: the construct is K-HDIV. The question is whether its obligation holds at the reading OQ-15 chooses.
> *What settles it:* `def HndLoopSpanCompat : Prop` (03 §9.2: K-HDIV's spanning form under (a) is in `𝒱⟦U(Loop_Σ A_H B_H)⟧_W` whenever its handler is `IsModel` at the observation carrier and its state is in the relation), proved, or refuted by a configuration that arises; under (b), `handle_compatC` at `ewpP_W` proved. The spanning form threads its state through the observation's answer, so its pending type `P = μP. U(Loop…) ⊕ K_q(B, Σ, A_H ⊕ (S ⊗ P))` is positive; threading it through a state-passing carrier `S ⊸ F_Σ R` with `S` holding `κ` would be the negative recursion of R-NONEGREC (03 §9.2, §9.15).
> *Blocks:* K-HDIV's lift, the reconciler chain's whole-loop timeout and retry (U5, 08 §9.1), L-DIV's handler law.
> *Default if unresolved:* the construct is specified; the kernel lift does not implement a handler that spans observations until its obligation is proved. This is R-HDIV, a restriction of the decided position U5, recorded as such.

<a id="oq-68"></a>

> [!IMPORTANT]
> **Open question OQ-68: The proof obligations of allocation as an effect** (U20) **[settle by proof]**
> *Why open:* The user decided that allocation is an effect (U20). K-ALLOC (03 §9.5) specifies it: `Alloc[T]` with a host-provided outermost handler whose clauses are BoLo's `alloc` and `free` resuming in tail position, arenas as nested handlers. Which presentation colours function types, a row entry (OQ-30 (b)) or a capability (OQ-30 (b')), is the user's choice under OQ-30. What is not proved: the host handler as a model (mechanical from `[TR]` 6.165-6.166), an arena handler's frame of a lent block across `new` (T-FRAME at a resuming table), and T-ADEQ's every-allocator statement restated with the allocator as the host handler.
> *Options:* none of design: the construct is K-ALLOC.
> *What settles it:* the host handler's `IsModel` at `opTable ⟦Alloc[T]⟧` proved; an arena configuration (a lent block, two `new`s, a `free` of the block) at `W` with every hypothesis discharged; T-ADEQ at a host allocator handler.
> *Blocks:* K-ALLOC's lift, K-HOST, T-ADEQ for host programs, per-thread arenas (08 §7 item 9).
> *Default if unresolved:* the construct is specified; the kernel lift keeps allocation as the machine's oracle until its obligations are proved. This is R-ALLOCORACLE, a restriction of the decided position U20, recorded as such.


---

## 3. Indexes

**Questions that need the user** (the *user decision?* column is "yes"): [OQ-1](#oq-1), [OQ-2](#oq-2), [OQ-3](#oq-3), [OQ-4](#oq-4), [OQ-5](#oq-5), [OQ-6](#oq-6), [OQ-7](#oq-7), [OQ-12](#oq-12), [OQ-13](#oq-13), [OQ-14](#oq-14), [OQ-15](#oq-15), [OQ-17](#oq-17), [OQ-18](#oq-18), [OQ-19](#oq-19), [OQ-20](#oq-20), [OQ-21](#oq-21), [OQ-22](#oq-22), [OQ-23](#oq-23), [OQ-24](#oq-24), [OQ-25](#oq-25), [OQ-26](#oq-26), [OQ-29](#oq-29), [OQ-30](#oq-30), [OQ-31](#oq-31), [OQ-33](#oq-33), [OQ-34](#oq-34), [OQ-35](#oq-35), [OQ-37](#oq-37), [OQ-38](#oq-38), [OQ-39](#oq-39), [OQ-42](#oq-42), [OQ-50](#oq-50), [OQ-52](#oq-52), [OQ-53](#oq-53), [OQ-55](#oq-55), [OQ-56](#oq-56), [OQ-59](#oq-59), [OQ-60](#oq-60), [OQ-61](#oq-61), [OQ-62](#oq-62), [OQ-65](#oq-65). Of these, the ones
settled by the user alone, with no proof or source read first: [OQ-2](#oq-2), [OQ-5](#oq-5), [OQ-6](#oq-6), [OQ-13](#oq-13), [OQ-17](#oq-17), [OQ-19](#oq-19), [OQ-21](#oq-21), [OQ-22](#oq-22), [OQ-23](#oq-23), [OQ-25](#oq-25), [OQ-26](#oq-26), [OQ-30](#oq-30), [OQ-31](#oq-31), [OQ-33](#oq-33), [OQ-52](#oq-52), [OQ-53](#oq-53), [OQ-55](#oq-55). The rest need a Lean statement,
a configuration or a source read before the user decides, in the order each *What settles it*
gives.

**Questions settled by a Lean statement or configuration** (**[settle by proof]**): [OQ-1](#oq-1), [OQ-3](#oq-3), [OQ-4](#oq-4), [OQ-7](#oq-7), [OQ-8](#oq-8), [OQ-9](#oq-9), [OQ-10](#oq-10), [OQ-11](#oq-11), [OQ-14](#oq-14), [OQ-15](#oq-15) (the obligation of its construct, with OQ-67), [OQ-16](#oq-16), [OQ-20](#oq-20), [OQ-24](#oq-24), [OQ-27](#oq-27), [OQ-28](#oq-28), [OQ-29](#oq-29), [OQ-32](#oq-32), [OQ-35](#oq-35), [OQ-36](#oq-36), [OQ-37](#oq-37), [OQ-38](#oq-38), [OQ-39](#oq-39), [OQ-40](#oq-40), [OQ-41](#oq-41), [OQ-42](#oq-42), [OQ-43](#oq-43), [OQ-44](#oq-44), [OQ-45](#oq-45), [OQ-46](#oq-46), [OQ-47](#oq-47), [OQ-48](#oq-48), [OQ-49](#oq-49), [OQ-50](#oq-50), [OQ-51](#oq-51), [OQ-54](#oq-54), [OQ-56](#oq-56), [OQ-57](#oq-57), [OQ-58](#oq-58), [OQ-60](#oq-60), [OQ-61](#oq-61), [OQ-62](#oq-62), [OQ-63](#oq-63), [OQ-64](#oq-64), [OQ-65](#oq-65), [OQ-67](#oq-67), [OQ-68](#oq-68).

**Questions settled by reading a primary source** (**[settle by literature]**): [OQ-12](#oq-12), [OQ-16](#oq-16), [OQ-18](#oq-18), [OQ-34](#oq-34), [OQ-59](#oq-59), [OQ-64](#oq-64), [OQ-66](#oq-66).

**Questions with no default** (the work they block does not start until they are settled): [OQ-8](#oq-8), [OQ-58](#oq-58), [OQ-59](#oq-59).

**The audit's questions.**

| audit | question | OQ |
|---|---|---|
| Q1 | answering and control handlers | [OQ-1](#oq-1) |
| Q2 | tier 1 or tier 2 | [OQ-2](#oq-2) |
| Q3 | handler extent | [OQ-3](#oq-3) |
| Q4 | a binary relation | [OQ-4](#oq-4) |
| Q5 | EffModelRel | [OQ-5](#oq-5) |
| Q6 | role declarations | [OQ-6](#oq-6) |
| Q7 | finalisers at a non-abortive table | [OQ-7](#oq-7) |

The critic's corrections that are open questions: correction 1 asks whether a control handler is a
borrow as an answering handler is ([OQ-3](#oq-3), with [OQ-1](#oq-1)); 2 is [OQ-2](#oq-2) and
[OQ-33](#oq-33); 3 is [OQ-8](#oq-8); 4 is [OQ-9](#oq-9) with [OQ-10](#oq-10); 5 is
[OQ-11](#oq-11); 6 bears on [OQ-18](#oq-18), [OQ-43](#oq-43) and [OQ-54](#oq-54).
