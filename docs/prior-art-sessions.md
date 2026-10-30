# Prior art: session types, par, and modes

This is a literature survey for issue #68 ("session types as the unifying abstraction") and its
two scope additions: par (`⅋`) and modes. It records what other work establishes, then reads it
against this project in §6. It does not change the spec. It does not repeat
`docs/prior-art-optics.md` §6.3–§6.5 (residuation, acquire/release, the session reading of a
lens) or `docs/prior-art-borrow-splitting.md` §2.6 (OCaml modes as a borrow-splitting
precedent). Where this survey reads the same source more deeply, it says so.

**The hypotheses under test.**

| Row | Claim |
|---|---|
| S1 one mechanism | Borrows, iterators, handlers and futures are instances of one session mechanism in the sequential setting, with one soundness argument |
| S2 polarity is direction | CBPV polarity decides who speaks: a positive type sends, a negative type receives |
| S3 sequential par | `⅋` at computation type has a sound, deterministic, interleaving (coroutine) reading |
| S4 par unlocks | Adding `⅋` as a former or a derived form passes at least one of the unlock tests U1–U4 of #68 |
| S5 one lattice | Our `!`/linear split, OxCaml-style locality and portability, and Granule grades fit one adjoint mode lattice |
| S6 concurrency | Tree-shaped composition gives deadlock freedom for the async runtime (#52) at a cost we can state |

The unlock tests are the issue's: (U1) a protocol we could not express before, (U2) a law proved
once for all instances, (U3) an optimization, (U4) fewer mechanisms.

**Citation conventions.** Each source carries how it was read:

- *(full)*: the full text, or every section cited, was read from the PDF;
- *(sections)*: the named sections, theorems or passages were read, and the rest skimmed;
- *(abstract)*: only the abstract or a publisher/conference page was read;
- *(secondhand)*: known only from another paper's text or bibliography, which is named.

Remarks marked *(ours)* are this survey's reading, not something a source prints. Section and
theorem numbers are those of the version read, which is listed in Sources; a conference and a
journal version may number differently. `[CONF]`/`[TR]` are Wagner et al. (2025) and its
technical report, as elsewhere in `docs/`.

---

## 0. Summary

- **S2 is printed.** Pfenning–Griffith (FoSSaCS 2015) polarize session types: positive
  propositions send, negative ones receive, and a shift `↑`/`↓` is the one message that reverses
  direction. Paykin–Zdancewic show that linear λμ, a *sequential* calculus, equationally
  corresponds to a polarized CP (CP±), in which "the scheduling is statically decided". CBPV's
  value/computation split is the intuitionistic fragment of this polarity (Zeilberger, LICS
  2010). So "polarity decides who speaks" has a printed basis, and so does "a polarized session
  calculus can be run deterministically".
- **S1 holds for three of the four and only rhymes for the fourth.** *(ours)* Iterators,
  futures and loops are already one mechanism here: the `ν` former (decision 28). Read through
  Pfenning–Griffith, an `Iter A R R'` is literally a polarized session type: an external choice
  `&{next, close}` whose branches send. Handlers join them if `ν` admits one position it
  excludes today: an observation that takes an input (a "sink", SPEC §7 *Open*). Pfenning–Griffith's
  own running example, a queue `&{enq : A ⊸ queue A, deq : …}`, sits in exactly that position.
  Borrows are different. The session reading of `withbor` is "call, then return", which every
  function has (Caires–Pfenning's `⊸`). None of what makes a borrow sound (the frozen lender, the
  lifetime, outlives) is in the session type. This agrees with `docs/prior-art-optics.md` §6.4.
- **S3: a sequential `⅋` exists in print, but as classical control, not as a new CBPV
  connective.** Its sequential readings are multiple conclusions and continuations: linear λμ
  (Paykin–Zdancewic), linear continuation-passing (Berdine et al.), and delimited control
  (Zeilberger; Lolliproc). Zeilberger states that CBPV's type structure coincides with the
  "immaculate" polarized fragment, which `⅋` is not in, and that `⅋` is "essentially the Church
  encoding of disjunction". No source was found that adds `⅋` to CBPV computation types with a
  logical relation, or that calls an iterator plugged into its consumer a `⅋`.
- **S4: `⅋` as a former fails the unlock tests in the sequential setting.** *(ours)* The
  sequential work `⅋` would do, a producer and a consumer interleaved deterministically, is what
  `U(ν…)` plus application already does, with the consumer as the scheduler. The one missing
  protocol shape is the sink position of `ν`, which is a relaxation of `NuOk`, not `⅋`. `⅋`
  earns its place with real concurrency, where Wadler's CP makes tree-shaped cut the
  deadlock-freedom argument.
- **S5: the usage modes line up with adjoint logic, but the rest is a product of axes, not one
  lattice.** *(ours)* The five interval grades of `experiments/Grades` are Pruiksma–Pfenning's
  four modes (linear `[1,1]`, affine `[0,1]`, strict `[1,∞]`, unrestricted `[0,∞]`) plus an erased
  grade `[0,0]`. Jang et al. (FSCD 2024) give those four modes a sequential call-by-value
  semantics with garbage-freedom and erasure theorems. OxCaml is itself the counterexample to "one
  lattice". Its documentation lists nine axes, its papers order modes pointwise as a product, and
  each paper proves its own axes sound by its own model. Locality looks like sugar over lifetimes
  plus a lowering. Portability becomes necessary only with threads *and* interior mutability.
  Security levels are a different semiring whose soundness theorem (noninterference) is binary.
  Our relation is unary.
- **S6 is well supported, and the price is known.** Caires–Pfenning Thm 5.8, Wadler Thm 2 and
  Jacobs–Balzer–Krebbers Thm 3.2 derive deadlock freedom from tree or acyclic topology. The last
  gives deadlock *and leak* freedom as one "final state" theorem, which has the shape of our
  adequacy. Sharing (Balzer–Pfenning) gives deadlock freedom up. It is recovered by an order on
  acquisitions (worlds, priorities).

---

## 1. Propositions as sessions

### 1.1 Caires & Pfenning, *Session Types as Intuitionistic Linear Propositions* (CONCUR 2010) *(sections)*

- **Def 3.1 (types).** `1 | !A | A ⊗ B | A ⊸ B | A ⊕ B | A & B`. The paper states:
  - "`A ⊗ B` is the type of a session channel that first performs an output (sending a session
    channel of type `A`) to its partner before proceeding as specified by `B`";
  - `A ⊸ B` "first performs an input (receiving a session channel of type `A`)";
  - `1` "means that the session terminated";
  - `A ⊕ B` selects left or right; `A & B` "offers its partner a choice";
  - `!A` types "a non-session (non-linearized, shared) channel … to be used by a server for
    spawning an arbitrary number of new sessions (possibly none)".
- **Two zones (dual intuitionistic linear logic).** The judgment `Γ; Δ ⊢ P :: z:C` has an
  unrestricted `Γ` and a linear `Δ`. A process *provides* one channel `z`. This is why the system
  has `⊸` and no `⅋`: an intuitionistic sequent has one conclusion.
- **Thm 5.6 (subject reduction)** gives session fidelity. **Lemma 5.7 and Thm 5.8 (progress)**:
  a closed live process typed at `x:1` reduces. The paper attributes this to the logical
  composition rules `cut` and `cut!`: "typing intrinsically enforces global progress, unlike
  with traditional session type systems" (§6).
- **§6.** Independent parallel composition is derivable from `cut` at type `1` (rule `comp`).

### 1.2 Wadler, *Propositions as Sessions* (ICFP 2012; JFP 2014) *(full, ICFP version)*

- **CP.** CP is classical linear logic with one-sided sequents. There is a single output
  connective and a single input connective: "`A ⊗ B` 'times', output `A` then behave as `B`";
  "`A ⅋ B` 'par', input `A` then behave as `B`" (§2, Fig. 1). `⊸` is not primitive:
  `A ⊸ B = A^⊥ ⅋ B`.
- **Cut is composition along one channel (§2.1).** Cut is interpreted "as a symmetric operation
  combining parallel composition with name restriction". It shares exactly one channel: "If
  communication could occur along two channels rather than one, then one could form a loop of
  communications between P and Q that leads to deadlock."
- **Output disentangles (§2.2).** In `x[y].(P | Q)` the processes `P` and `Q` are disjoint, and
  "Disjointness of P and Q ensures there is no further entangling between x and y, which
  guarantees freedom from deadlock." Input keeps both channels in one process `R`. That is safe
  because output has already disentangled them.
- **Thm 2 (top-level cut elimination).** A process can reduce until it is not a cut. "Top-level
  cut elimination corresponds to lack of deadlock."
- **GV (§3).** GV is a linear functional language with session-typed channels, translated into
  CP. It differs from Gay–Vasconcelos so as to be deadlock-free: `end` is split into `end!` and
  `end?`. The translation *inverts* the reading: GV's send `!T.S` becomes CP's `⅋`, because "Send
  and Receive in GV take channels as arguments, whereas the interpretation of the connectives in
  CP is for channels as results".
- **§5 (conclusion), two extensions.**
  - Mix (`P | Q` with no shared channel) is "equivalent to provability of `A ⊗ B ⊸ A ⅋ B`" and
    still does not deadlock.
  - Binary Cut (two shared channels) is equivalent to `A ⅋ B ⊸ A ⊗ B` and "allows one to express
    systems where communications form a loop and may deadlock".
  - With both, the system is compact, and `⊗` and `⅋` coincide.
  - **This is the printed boundary between deadlock-free and cyclic topologies.**
- **§4.** Wadler compares DILL (Caires–Pfenning) with CLL. He records Pfenning's preference for
  DILL for locality and for dependent types.

### 1.3 The GV line

- **Gay & Vasconcelos**, *Linear Type Theory for Asynchronous Session Types* (JFP 20(1), 2010)
  *(secondhand: Wadler §3; Pfenning–Griffith bibliography)*. A linear functional language with
  buffered asynchronous channels. It is not deadlock-free (Wadler §3).
- **Lindley & Morris**, *A Semantics for Propositions as Sessions* (ESOP 2015) *(abstract)*. They
  relate CP's cut-elimination semantics to an operational semantics for a session-typed
  functional language.
- **Lindley & Morris**, *Talking Bananas: Structural Recursion for Session Types* (ICFP 2016)
  *(abstract)*. They extend GV "with recursive types and catamorphisms, following the initial
  algebra semantics of recursion". *(ours)* This is the session-side counterpart of our folds
  over `μ` (SPEC §6).
- **Fowler, Lindley, Morris & Decova**, *Exceptional Asynchronous Session Types: Session Types
  without Tiers* (POPL 2019) *(abstract)*. Affine sessions with exceptions (EGV). Kokke's Rust
  library `sesh` embeds EGV (Ferrite §8, §5.2 below).

### 1.4 The connectives as protocols

Read from the provider's side. The CP column is Wadler's, the DILL column Caires–Pfenning's, and
the polarity column Pfenning–Griffith's (§2.3 below).

| connective | CP (classical) | DILL (intuitionistic) | polarity | nearest thing here *(ours)* |
|---|---|---|---|---|
| `A ⊗ B` | send `A`, continue as `B` | send `A`, continue as `B` | positive | a value pair inside `F(A ⊗ B)` |
| `A ⅋ B` | receive `A`, continue as `B` | (absent) | negative | none; `A ⊸ C` is the special case `A^⊥ ⅋ C` |
| `A ⊸ B` | defined, `A^⊥ ⅋ B` | receive `A`, continue as `B` | negative | `A ⊸ C` (computation type) |
| `A ⊕ B` | select | select | positive | `F(A ⊕ B)` returning a tag |
| `A & B` | offer a choice | offer a choice | negative | `C & C'` (codata observations) |
| `1` / `⊥` | end (send / receive) | `1` only | pos / neg | `F 1` |
| `!A` / `?A` | replicable server / client | `!A`, unrestricted zone | positive `!` | `!T` (SPEC §2) |
| `↓A⁻` / `↑A⁺` | (none in CP) | Pfenning–Griffith shifts | pos / neg | `U C` / `F A` |

### 1.5 Deadlock freedom and its limits

**Tree topology.** Deadlock freedom comes from cut sharing one channel (Wadler §2.1, quoted
above; Caires–Pfenning Thm 5.8). Composition therefore builds a tree of processes. This is what
excludes cycles, and it also excludes some useful programs.

**Cyclic topologies.**

- **Kobayashi**, *A New Type System for Deadlock-Free Processes* (CONCUR 2006) *(abstract)*.
  Types with usages and priorities, which admit type inference. Wadler §4 describes the older
  line (Sumii–Kobayashi 1998) as "a separate partial order on time tags".
- **Dardha & Gay**, *A New Linear Logic for Deadlock-Free Session-Typed Processes* (FoSSaCS
  2018) *(abstract)*. Priority-based linear logic (PLL) and its term assignment PCP. A **Cycle**
  rule admits cyclic process structures that respect priority orderings. The paper combines
  Caires–Pfenning with Kobayashi.
- **Dardha & Pérez**, *Comparing Type Systems for Deadlock Freedom* (arXiv 1810.00635, v4 2021)
  *(abstract)*. The class `L` of processes typed by the Curry–Howard (CLL) systems is *strictly
  included* in the class `K` typed through Kobayashi's usages. The paper gives the conditions
  under which they coincide, and translations from `K` into `L`. This is the printed measure of
  what tree topology costs.
- **Kokke & Dardha**, *Deadlock-Free Session Types in Linear Haskell* (Haskell 2021)
  *(abstract)*. Priority Sesh offers both disciplines as a library: trees and forests ("simple
  and composable, but rules out cyclic structures") and priorities ("allows the programmer to
  safely use cyclic structures").
- **Carbone & Debois** (2010) *(secondhand: Wadler §4; Jacobs et al. §1)*. Acyclicity of a
  dependency graph.

**Mechanised deadlock and leak freedom.**

- **Jacobs, Balzer & Krebbers**, *Connectivity Graphs* (POPL 2022) *(abstract, §1, §3.1
  statements)*.
  - The method is parametric in vertices (threads, channels) and labelled edges (references with
    protocols).
  - Preservation is proved locally by rules that keep the graph acyclic. Progress uses a
    "waiting induction principle for acyclic connectivity graphs".
  - **Thm 3.2** (generalized type safety): from `init(e)`, either `final(ρ)` or `ρ` can step.
    "By defining final this way, the type safety theorem expresses deadlock and memory leak
    freedom." The whole development is in Coq.
- **Jacobs, Hinrichsen & Krebbers**, *Deadlock-Free Separation Logic* (POPL 2024) *(abstract)*.
  LinearActris gets deadlock and leak freedom "for free" from linearity. Its model is a
  step-indexed separation logic over connectivity graphs. A GV-style type system is proved sound
  in it by logical relations.
- `docs/prior-art-optics.md` §6.4 already records Jacobs & Balzer, *Higher-Order Leak and
  Deadlock Free Locks* (POPL 2023).

**Sharing gives it up.** Balzer & Pfenning, *Manifest Sharing with Session Types* (ICFP 2017,
TR CMU-CS-17-106R) *(sections)*. The language "retains session fidelity but not the absence of
deadlocks, which can arise from contention for shared processes" (abstract). Progress is
weakened to allow blocked processes (TR Thm 2). Balzer, Toninho & Pfenning (ESOP 2019)
restore deadlock freedom with *worlds*, a partial order on acquisitions (optics doc §6.4).

---

## 2. Par (`⅋`)

### 2.1 Computational readings

| reading | where printed | sequential? |
|---|---|---|
| input on a channel | Wadler CP §2.2 | no: a process calculus |
| parallel composition and communication | Aschieri & Genco, *⅋ Means Parallel* (POPL 2020) | no |
| multiple conclusions / several continuations | Paykin & Zdancewic, *Linear λμ is CP (more or less)* | **yes**: linear λμ |
| classical and delimited control | Mazurak & Zdancewic, *Lolliproc* (ICFP 2010); Zeilberger (LICS 2010) | yes (control operators) |
| coroutines as linear use of continuations | Berdine, O'Hearn, Reddy & Thielecke, *Linear Continuation-Passing* (HOSC) | yes |

- **Aschieri & Genco** (POPL 2020; arXiv 1907.03631) *(abstract, §1)*. A linear
  multiple-conclusion natural deduction for MLL is isomorphic to λ`⅋`, "a simple and natural
  extension of λ-calculus with parallelism and communication primitives". The paper proves
  subject reduction, progress, strong normalization and confluence. §1 quotes Girard: the
  multiplicative fragment "can be seen as a system of communication without problems of
  synchronization". The paper criticises CP for implementing only top-level cut elimination.
- **Paykin & Zdancewic**, *Linear λμ is CP (more or less)* (in *A List of Successes That Can
  Change the World*, LNCS 9600, 2016) *(§1–§3, §6)*.
  - Linear λμ has a term context `Γ` and a *continuation* context `Π`. A term has at most one
    type and may send to several continuation variables. This is the sequential,
    multiple-conclusion reading of `⅋`.
  - `A ⊸ B` is encoded as `¬(A ⊗ ¬B)` (§3.1).
  - **Thm 4** (and §1): linear λμ equationally corresponds with CP±, a polarized CP.
    "Operationally, polarization reduces the amount of nondeterminism, statically making more
    choices about how processes synchronize … CP± is thus 'more or less' CP, where the
    scheduling is statically decided."
  - §6.5: "CP± has the ability to set a particular reduction strategy such as CBV, CBN, or
    something in between. Once an evaluation strategy is fixed, the types dictate the evaluation
    of any particular process."
  - **This is the strongest printed support for S3**: a polarized session calculus is
    equationally a deterministic sequential calculus with control.
- **Mazurak & Zdancewic**, *Lolliproc* (ICFP 2010) *(abstract; Wadler §4)*. Lolliproc relates
  double-negation elimination in classical linear logic to delimited control, and gives
  concurrency primitives "that combine to provide the functionality of session types".
- **Berdine, O'Hearn, Reddy & Thielecke** (HOSC; doi:10.1023/A:1020891112409) *(abstract)*. Calls
  and returns, exceptions, jumps and "process switching (coroutines)" all use their continuations
  linearly; backtracking is the exception. The paper formalises this with a CPS target that has
  both intuitionistic and linear function types.

### 2.2 How intuitionistic systems replace `⅋` by `⊸`

In DILL a sequent has one conclusion, so the negative multiplicative is available only in the
form `A ⊸ B` (Caires–Pfenning Def 3.1). In CLL it is `A^⊥ ⅋ B` (Wadler §2). Wadler §4 records
Caires et al.'s reasons to prefer DILL:

- a locality property for replicated input;
- Pfenning's view that DILL, unlike CLL, is amenable to dependent types.

*(ours)*: our computation-type `⊸` is DILL's. What the core lacks is not the negative
multiplicative as such, but a computation with *two open continuations*: `C ⅋ C'` with neither
side an input.

### 2.3 Polarized and focused linear logic, where `⅋` is negative

- **Pfenning & Griffith**, *Polarized Substructural Session Types* (FoSSaCS 2015) *(full)*.
  - Positive propositions `1, A⁺ ⊗ B⁺, A⁺ ⊕ B⁺, τ ∧ B⁺, ↓A⁻` are "send". Negative propositions
    `A⁺ ⊸ B⁻, A⁻ & B⁻, τ ⊃ B⁻, ↑A⁺` are "receive". The reason: "the right rules for negative
    connectives are invertible and therefore carry no information: any information has to come
    from the outside".
  - A process that sends "will continue to do so until it sends a shift and then it starts
    receiving". A queue therefore always has a definite direction.
  - The same shifts serve as adjoint-logic modalities between modes (§3.3 below).
  - The running example is a session-typed queue,
    `queue A = &{enq : A ⊸ queue A, deq : ⊕{none : 1, some : A ⊗ queue A}}`.
  - Pfenning–Griffith cite Laurent for polarization. They do not cite Levy or CBPV.
- **Zeilberger**, *Polarity and the Logic of Delimited Continuations* (LICS 2010) *(abstract,
  §I, the passage on immaculate polarizations, conclusion)*.
  - "Polarized logic is the logic of values and continuations … The main limitations of this
    logic are the limitations of CPS: that continuations cannot be composed, and that programs
    are fully sequentialized."
  - "The immaculate fragment coincides precisely with the standard definition of polarized
    intuitionistic logic …, as well as with the type structure of Call-By-Push-Value."
  - `⅋` lies outside that fragment. It is "perfectly constructive", "essentially the Church
    encoding of disjunction", and `(P → ⊥) ⅋ ↑P` "is isomorphic to `P → ↑P`".
  - The paper explains CBPV-style "intuitionistic polarity" as a restriction on the use of the
    classical polarized connectives, over delimited continuations whose answer types are
    positive.
- **Zeilberger**, *The Logical Basis of Evaluation Order and Pattern-Matching* (PhD, CMU 2009)
  *(abstract)*. A polarized type theory from focusing, where "evaluation order is explicitly
  reflected at the level of types".
- **Laurent**, *Polarized proof-nets and λμ-calculus* (TCS 290, 2003); *Étude de la polarisation
  en logique* (PhD 2002) *(abstract; secondhand via Paykin–Zdancewic, Pfenning–Griffith)*.
  Polarized linear logic (LLP), with structural rules on negative formulas and λμ encoded in
  polarized proof-nets.
- **Munch-Maccagnoni**, *Focalisation and Classical Realisability* (CSL 2009) *(abstract)*.
  System L, a polarised λμμ̃ for focalising sequent calculi, with Krivine realisability extended
  to call-by-value.
- **Curien, Fiore & Munch-Maccagnoni**, *A Theory of Effects and Resources: Adjunction Models
  and Polarised Calculi* (POPL 2016) *(abstract; talk slides)*. Effects and resources are to be
  treated orthogonally. The models are "a linearisation of CBPV adjunction models" and an
  extension of linear/non-linear models "with an adjoint resolution of computational effects".
  *(Not read: whether its calculus includes `⅋` at negative types.)*
- **Ehrhard**, *Call-By-Push-Value from a Linear Logic Point of View* (ESOP 2016) *(abstract)*.
  CBPV with fixpoints and recursive types, interpreted in models of linear logic.

### 2.4 Sequential or coroutine readings: what exists

- **Paykin–Zdancewic.** A polarized CP is equationally linear λμ, and polarization fixes the
  schedule (above).
- **Pruiksma & Pfenning**, *Back to Futures* (JFP 32, 2022; arXiv 2002.04607) *(§1, §4)*.
  - The base language Seax is concurrent, a write-once shared-memory reading of adjoint logic.
  - §4 adds sequentiality, defined as "only one thread (the active thread) is able to take a step
    at a time". The mechanism is a *sequential cut* `x ⇐ P ; Q`, defined through "a shift from a
    mode m to itself [which] does not affect provability, but does force synchronization".
  - Futures, fork/join and a SILL-style concurrency monad are then encodings in one framework,
    including linear futures.
  - *(ours)*: this is the printed pattern of "same logic, sequential schedule by a shift". It is
    the adjoint-logic counterpart of Paykin–Zdancewic's polarization.
- **Anton & Thiemann**, *Typing Coroutines* (TFP 2010) *(abstract, §1)*. The first type system
  with dedicated support for coroutines. It is simply typed λ with an *effect* system for control
  transfers, not a session type system.
- **Not found.** Nothing was found that:
  - is titled or framed as "call-by-push-value and session types";
  - adds `⅋` to CBPV computation types with a (unary or binary) logical relation;
  - reads an iterator plugged into its consumer, or a handler plugged into its computation, as a
    `⅋`-cut.

  Pfenning–Griffith is the nearest: polarized sessions with shifts, not CBPV. Zeilberger comes
  next: CBPV as a fragment, with `⅋` needing control.

---

## 3. Adjoint logic as a mode system

### 3.1 Origins

- **Benton**, *A Mixed Linear and Non-Linear Logic* (CSL 1994) *(secondhand: OxCaml ICFP 2024
  and Pfenning–Griffith bibliographies)*. LNL: two layers joined by an adjunction.
- **Reed**, *A Judgmental Deconstruction of Modal Logic* (manuscript 2009) *(secondhand:
  Pfenning–Griffith [18], Pruiksma–Pfenning [24])*.
- **Pruiksma, Chargin, Pfenning & Reed**, *Adjoint Logic* (manuscript 2018) *(secondhand;
  optics doc §6.4)*.

### 3.2 Pruiksma & Pfenning, *A Message-Passing Interpretation of Adjoint Logic* (PLACES 2019, EPTCS 291; JLAMP 120, 2021) *(sections, PLACES version)*

- **Modes.** Each mode `m` has a set of structural properties `σ(m)`. There are four named modes:
  - *linear*: a unique client that must communicate;
  - *affine*: a unique client that may communicate or cancel;
  - *strict*: several clients, each of which must communicate;
  - *unrestricted*: several clients, each of which may communicate, which covers replicable
    services and multicast.
- **Preorder.** `m ≥ k` requires `σ(m) ⊇ σ(k)`. This embodies "the declaration of independence":
  a proposition at mode `m` may depend only on hypotheses at modes `≥ m`.
- **Theorems.** Thm 1 is session fidelity and Thm 2 is deadlock freedom. §4 derives that a
  terminated network "leaves no garbage": weakening is cancellation, contraction is multicast.
  Thm 3 is identity expansion and Thm 4 is cut elimination, both for the logic.

### 3.3 Shifts between modes

**Pfenning–Griffith** (FoSSaCS 2015) *(full)*, the adjoint logic section.

- There are three layers, `U > F > L` (unrestricted, affine, linear). `↑ᵐₖ` goes up from `k` to
  `m` and `↓ᵐₖ` goes down.
- "the familiar exponential of linear logic `!A` is decomposed into two shifting modalities, one
  going from A (which is linear) into the unrestricted layer, and one going from the
  unrestricted layer back to the linear one".
- `↑` is negative and `↓` positive. The same `↑`/`↓` therefore serve as polarity shifts and as
  mode shifts.

### 3.4 Jang, Roshal, Pfenning & Pientka, *Adjoint Natural Deduction* (FSCD 2024; arXiv 2402.01428) *(abstract, §1, the statement list)*

- A natural deduction form of adjoint logic, related to the sequent calculus by Thms 12 and 13.
- "a computational interpretation of adjoint logic in the form of a functional language". It
  has "a sequential call-by-value semantics similar to the K machine".
- The paper proves "freedom from garbage (for modes without weakening and contraction),
  strictness (for modes disallowing weakening), and erasure (based on a preorder between
  modes)".
- *(ours)*: this is the closest published object to our setting: a *sequential* functional
  adjoint language with a leak-freedom-shaped theorem and an erasure theorem. It has no borrows
  and no lifetimes.
- A follow-up, *Ordered Adjoint Logic* (arXiv 2605.19112, 2026), exists. Only its title was
  seen.

### 3.5 Sharing by acquire/release

- **Balzer & Pfenning** (ICFP 2017) *(sections; optics doc §6.4)*. `↑ˢₗ` (acquire) and `↓ˢₗ`
  (release) are adjoint shifts between a shared and a linear layer. Equi-synchronizing: "any
  release restores the session to the same type at which a preceding acquire occurred".
  Deadlock freedom is lost (§1.5).
- **Balzer, Toninho & Pfenning** (ESOP 2019) *(optics doc)*. Worlds restore it.
- **Sano, Balzer & Pfenning**, *Manifestly Phased Communication via Shared Session Types*
  (COORDINATION 2021) *(title only)*.

### 3.6 Mode theories

- **Licata & Shulman**, *Adjoint Logic with a 2-Category of Modes* (LFCS 2016) *(abstract)*.
  They allow several different adjunctions between the same pair of modes.
- **Licata, Shulman & Riley**, *A Fibrational Framework for Substructural and Modal Logics*
  (FSCD 2017) *(abstract, §1)*.
  - A sequent calculus is parametrised by a *mode theory*, whose terms say how the context may
    be used.
  - One positive and one negative connective yield "non-associative, ordered, linear, affine,
    relevant, and cartesian products and implications; … (co)monads and adjunctions; n-linear
    variables; and bunched implications".
  - Cut admissibility is proved once, independently of the mode theory.
  - *(ours)*: it is the formal home for "several mode axes in one framework". It is a logic with
    an equational theory. It has no operational semantics, memory, or leak freedom, so it would
    organise a presentation and would not save a soundness proof.

### 3.7 What this repository already has

- `experiments/ModesLabels` checks that `lin` (`Ref`, `⊸`, `∀`), the mode with weakening only (`Mut`) and `unr` (`Imm`,
  `!T`, `1`, `Unk`) satisfy their structural properties *semantically* at every type
  (`weaken_sound`, `contract_sound`). It finds that the only formers that break the declaration
  of independence are the two labelled borrows. Its reading is that a lifetime label is a licence
  to break independence for a scope.
- `experiments/Shifts` shows that the four label-introducing borrow axioms are instances of one
  "labelled shift" schema `src ⊸ (∀'x ⊏ bnd. view 'x ⊸ ['x] T) ⊸ …`. It notes that the schema
  predicts a shift from adjoint logic's affine mode to its unrestricted one (lending a `Mut` as
  an `Imm`) with no axiom behind it.
- `experiments/Grades` provides interval grades over `{0, 1, ∞}` with endpoint type conditions.
  It shows `GDerives ⇔ CDerives` under the Core profile, and proves erasure at grade `0`.

---

## 4. Modes in practice

### 4.1 OxCaml

**Lorenzen, White, Dolan, Eisenberg & Lindley**, *Oxidizing OCaml with Modal Memory Management*
(ICFP 2024) *(§1–§4, parts of §5 and §8)*.

- **Axes (§3).**
  - affinity `many < once`, uniqueness `unique < aliased`, locality `global < local`;
  - "Modes are ordered pointwise … Modes form a lattice".
- **Modalities.** A modality maps a mode triple to a mode triple, and "If a record r has mode m
  and field f has modality n, then r.f has mode n(m)". Some modes have no modality: a `local`
  field inside a `global` value would let the heap point into the stack (the same point is made
  in DRFCaml §4.3).
- **Borrowing (§2.6).** `val borrow : 'a @ unique -> ('a @ local -> 'b) -> ('a * 'b aliased) @
  unique`.
  - "The reason this is sound is that the argument type of f is local, so there can be no other
    reference to v once f has returned."
  - The `global` modality must also imply `aliased`, "to soundly support borrowing".
  - *(ours)*: this is `withbor`'s shape, with locality standing in for the lifetime.
- **Regions.** Regions "are lexical": a function body is one. `exclave e` "ends the current
  region and then executes e in the outer region", and only in tail position.
- **Soundness (§4).** A *usage-aware store semantics*: each store binding carries a mode, or is
  marked consumed, and a stack-frame index.
  - "If an aliased value in the store is accessed as unique, our semantics is stuck."
  - At the end of a region every `local` binding of that frame is deleted.
  - Soundness of reuse, stack allocation and borrowing is progress over this instrumented
    semantics.
- **§5 (graded reading).** The system relates to a graded modal calculus. Applying functions
  that are aliased but were closed over unique values needs an element "that acts as a right
  residual to A … then A⊸1 would be a right adjoint to A, and A∘A⊸1 would be a comonad".
- **§8.4.** Adjoint approaches are cited (Benton; Licata–Shulman; Pruiksma et al.; Jang et al.).
  Generic multimodal type theories "could in principle model our system, although they do not
  yet support substructural type systems or side-effects".
- **§9.** Future work names thread-sharing modes, modes for user-defined effects, and mode
  polymorphism.

**Georges, Peters, Elbeheiry, White, Dolan, Eisenberg, Casinghino, Pottier & Dreyer**, *Data
Race Freedom à la Mode* (POPL 2025) *(abstract, §2.4, §4.3, §5–§6 statements)*.

- **Contention and portability.**
  - Contention: `uncontended ≤ shared ≤ contended`. "A reference can be written only if it is
    uncontended, and can be read only if it is shared or uncontended".
  - Portability: `portable ≤ nonportable`. "if a closure captures an uncontended or shared value,
    then this closure must be nonportable".
  - Together they enforce "a variant of Rust's AXM discipline".
- **Past and future.**
  - Uniqueness and contention describe the past: whether a value has been duplicated or shared.
  - The future axes restrict what may happen next.
  - "G, M, and P" are "quasi-comonadic" and "A, C, and S … quasi-monadic". The paper says this is
    not precise.
- **Interior mutability by API.** Capsules (a unique ghost key guards a region) and
  reader-writer locks.
- **Soundness.** An Iris semantic model in Rocq:
  - Thm 5.1 (compatibility) and Thm 5.2 (fundamental theorem);
  - Thm 5.3: semantically typed expressions are data-race free.
  - The capsule API is implemented with `Obj.magic`. It is proved separately (Thm 6.1) by giving
    its types bespoke semantic interpretations. The paper credits "the semantic approach".
  - *(ours)*: this is the same route as our decision 27 (an unchecked body with a semantic-type
    contract).

**The OxCaml documentation** (oxcaml.org, *Modes: Intro*) *(fetched summary)*.

- Nine axes: locality, contention, portability, forkable, uniqueness, linearity, yielding,
  visibility and statefulness.
- Each axis is either:
  - "a *future* mode, which tracks whether the operation is allowed to happen to this value in
    the future", or
  - "a *past* mode, which tracks whether the operation has happened to this value in the past".
- *Yielding* "tracks whether a function is permitted to perform effects that will be handled in
  its parent stack". Local values default to yielding.
- **Mode crossing**: "some types don't have interesting interactions with some modes. Such types
  are said to mode cross on those axes, which means values of these types may freely move in
  either direction on the axis."
- The fetch summary orders locality opposite to the ICFP paper. The paper's orientation is used
  here.

**Other OxCaml sources.**

- **Peters, Jacobs, Kalinichenko, Stevenson, Smith, Dreyer & Eisenberg**, *Mode Crossing* (ICFP
  2026) *(Zenodo artifact page; search summary)*. It introduces *modal kinds*, interpreted "as
  monotone functions on a lattice of modes", to support mode crossing through abstract types.
- **Jane Street blog**: *Oxidizing OCaml: Locality* (M. Slater, 26 May 2023) *(fetched
  summary)*, *Rust-Style Ownership* and *Data Race Freedom* *(titles only)*. Per the locality
  post, "OCaml's modes do not affect type inference"; it presents them as lighter than lifetime
  variables.
- **Tang, White, Dolan, Hillerström, Lindley & Lorenzen**, *Modal Effect Types* (OOPSLA 2025)
  *(abstract)*. Effect handlers typed by modalities, which avoids explicit effect polymorphism.

**Soundness story and what it would cost here** *(ours)*. OxCaml proves each extension against
its own model:

- ICFP 2024: an instrumented store semantics, progress only.
- POPL 2025: an Iris logical relation.

Our relation is already a semantic model with a Fundamental Property, so the POPL 2025 route is
the one that transfers. A new axis is a new coordinate in `vC`/`cC` with a compatibility lemma
per rule. Decision 19 says such a coordinate goes in a type former or the model, never as a
defaulted judgment index.

### 4.2 Granule and graded types

- **Orchard, Liepelt & Eades**, *Quantitative Program Reasoning with Graded Modal Types* (ICFP
  2019) *(sections)*.
  - Semiring-graded necessity `□ᵣA`, written `A [r]`.
  - **Def 4.2 (security levels).** `Level` is "a three-point lattice of security levels
    {Irrelevant ⊑ Private ⊑ Public} with 0 = Irrelevant, 1 = Private, + = ⊔", intended for
    "enforcing noninterference".
  - Grades combine as products of coeffects.
  - **Thm 7.1** is type safety (progress and preservation). No noninterference theorem was found
    in the parts read.
- **Abel & Bernardy**, *A Unified View of Modalities in Type Systems* (ICFP 2020) *(abstract,
  Thms 7.9–7.10)*. **Thm 7.10** (irrelevance and non-interference) is a corollary of the fundamental
  lemma of a *relational* semantics, instantiated with `!₀R = ⊤`.
- **Moon, Eades & Orchard**, *Graded Modal Dependent Type Theory* (ESOP 2021) *(statement
  list)*. Thm 3 is soundness for semantic typing.
- **Marshall & Orchard**, *Replicate, Reuse, Repeat* (PLACES 2022, EPTCS 356) *(full)*.
  - Graded modal types reintroduce non-linear communication (reusable and replicated channels,
    multicast) on top of linear session types in Granule.
  - Call-by-value forces a syntactic restriction on promoting channels. Otherwise "a linear
    channel used in a shared way can easily lead to a deadlock".
  - "The next step would be to prove type safety": **no soundness proof**.
  - It contrasts itself with Pruiksma–Pfenning, which "offers non-linearity but without the
    precise quantification allowed by our grades".
- **Marshall & Orchard**, *Graded Modal Types for Integrity and Confidentiality* (arXiv
  2309.04324) *(abstract)*. Reversing the lattice for integrity is "unsatisfactory". Integrity is
  added as a second modality over which the confidentiality comonad is a relative monad.
- **Marshall, Vollmer & Orchard**, *Linearity and Uniqueness: An Entente Cordiale* (ESOP 2022)
  *(secondhand: RRR ref [14])*.

**Soundness story and what it would cost here** *(ours)*.

- *Usage grades* cost little. `experiments/Grades` already shows them equivalent to `Core`
  at the default profile and proves erasure. This is a unary property.
- *Security levels* are another matter. Noninterference compares two runs, and the printed proof
  (Abel–Bernardy Thm 7.10) is the fundamental lemma of a binary relation.
- Our relation is unary. `experiments/TwoRun` records that even the read footprint does not
  follow from `wpTS` (`not_readFootprint`), and scopes a binary relation as future work. A
  security grade therefore costs the binary relation first.

---

## 5. Session types meeting borrowing and effects

### 5.1 Ferrite: Chen, Balzer & Toninho, *Ferrite: A Judgmental Embedding of Session Types in Rust* (ECOOP 2022, LIPIcs 222:22) *(sections)*

- **Authors verified.** Ruo Fei Chen (independent researcher), Stephanie Balzer (CMU), Bernardo
  Toninho (NOVA Lisboa).
- The formal basis is the shared session calculus SILL_S (Balzer–Pfenning). Typing rules are
  Rust functions over typing judgments, so "a valid typing derivation manifest[s] as a
  well-typed Rust program".
- "Since Rust's typing discipline is essentially affine, … both shared and linear channels must
  be treated explicitly in the encoding." The linear context is a type-level structure, not Rust
  ownership.
- Shared sessions use acquire/release and must be "strictly equi-synchronizing".
- The runtime is tokio. Each cut spawns an async task, which §8 names as a performance cost.
- Shared session types reclaim expressiveness "at the cost of deadlock-freedom" (§8).
- *(ours)*: Ferrite embeds sessions *in* Rust's type system. It does not model Rust borrows as
  sessions.

### 5.2 Rust session-type libraries *(secondhand: Ferrite §8)*

- `session_types` (Jespersen, Munksgaard & Larsen, WGP 2015) was the first to use affinity.
- `sesh` (Kokke, *Rusty Variation*, ICE 2019) embeds EGV.
- `rumpsteak` (Cutner, Yoshida & Vassor) provides multiparty sessions for async Rust.
- Ferrite §8 names their shared failure: an endpoint "may be dropped by the Rust program without
  being consumed at all, thereby causing deadlock".
- *(ours)*: this failure cannot arise in a linear core with a mandatory `close` (SPEC §7) and
  implicit destructors only where a destructor exists (decision 23). Affine Rust has to catch it
  at run time.

### 5.3 Linear Haskell

Bernardy et al. (POPL 2018) is cited in `docs/prior-art-optics.md`. Priority Sesh (Kokke &
Dardha 2021, §1.5) is its session-types library. Its abstract says native linearity "lets us
avoid the complex encodings" of linearity that earlier Haskell libraries used.

### 5.4 Borrows and sessions

- **Saffrich, Spaderna, Thiemann & Vasconcelos**, *Borrowing from Session Types* (OOPSLA 2025)
  *(abstract, SPLASH page; artifact page)*.
  - BGV is "founded on ordered linear typing, for functional session types with an explicit
    operation for splitting ownership of channels".
  - Type safety and deadlock freedom come from "a type-preserving translation to PGV, a
    deadlock-free functional session type calculus". Algorithmic typing is mechanised in Agda.
  - *(ours)*: **the direction is the reverse of #68's.** Borrowing is imported *into* session
    types to make channels composable. Sessions are not used to explain borrowing.
- **Saffrich, Nishida & Thiemann**, *Law and Order for Typestate with Borrowing* (OOPSLA 2024).
  `docs/prior-art-optics.md` §6.3 reads it: the ordered product `⊙` is the one printed algebra
  where a borrow's residual carries a temporal order.
- **Jia, Liu, He, Deng, Bao & Rompf**, *Typestate via Revocable Capabilities* (PLDI 2026;
  arXiv 2510.08889) *(abstract)*. It extends "flow-insensitive capability mechanisms to a
  flow-sensitive setting", decoupling "capability lifetimes from lexical scopes", so that
  functions may "receive, revoke, or return capabilities". This is typestate over capabilities,
  not sessions.
- **Caires**, *CLASS* (PLACES 2025) *(abstract; optics doc §6.4)*. A linear session-based
  language that guarantees no leaks, no deadlocks and termination. It has mutable ADTs and
  "lazy stream programming".
- **OxCaml `borrow`** (§4.1) is the modal counterpart.
- **Not found**, as in the optics survey, is a paper that prints a lexically scoped borrow as a
  session type, or that derives a borrow's frame guarantee from session fidelity.

### 5.5 Effect handlers as sessions (request/response)

- **Orchard & Yoshida**, *Effects as Sessions, Sessions as Effects* (POPL 2016) *(§1, statement
  list)*.
  - PCF with a parameterised effect system embeds into a session π-calculus. The core idea is
    "the simulation of effectful computations using processes as effect handlers".
  - Examples: state (a "variable agent" process), sets, and resource counting (`tick`).
  - Thm 1 is operational correspondence and Thm 2 soundness w.r.t. βη.
  - The reverse embedding goes from sessions into an effect system, and yields a Haskell
    session-types library.
  - *(ours)*: the handler here is a concurrent *process* on a channel. A sequential handler is
    the special case in which the computation and its handler alternate, which is the
    Paykin–Zdancewic/Back-to-Futures move again.
- **Mathiasen, Timany & Birkedal**, *Yarrow* (arXiv 2607.15876, 2026) *(abstract)*. "the
  non-local control flow of algebraic effects break[s] the stack discipline … that region-based
  memory management relies on, and multi-shot effect handlers break the invariant that regions
  can be exited at most once." The program logic is in Iris.
  - *(ours)*: this is the printed form of why our continuations are one-shot (SPEC §14,
    surface-cbpv §2.11) and why a handler holding a borrow must be well-bracketed.
- **Tang et al.**, *Modal Effect Types* (OOPSLA 2025), and OxCaml's *yielding* axis (§4.1):
  effects tracked as modes.

### 5.6 Iterators and coroutines as sessions

- **Toninho, Caires & Pfenning**, *Corecursion and Non-Divergence in Session-Typed Processes* (TGC
  2014, LNCS 8902) and *Corecursion in Session-Typed Processes* (CMU-hosted manuscript)
  *(abstracts)*. Linear logic with coinductive types gives a session π-calculus with corecursion.
  A *logical relations* argument shows every well-typed composition non-divergent. *(ours)*: this
  parallels our `ν` with coiteration sound by a greatest fixed point (SPEC §7) and totality
  (`total_no_infinite_run`).
- **Lindley–Morris, *Talking Bananas*** (§1.3): catamorphisms for recursive sessions.
- **Pfenning–Griffith's queue** (§2.3) is a session-typed object with an input observation:
  `enq : A ⊸ queue A`.
- **Anton–Thiemann** (§2.4) type coroutines by effects. **Berdine et al.** (§2.1) put coroutines
  among the linear uses of continuations.

### 5.7 Futures and async as sessions

- **Pruiksma–Pfenning, *Back to Futures*** (§2.4). Futures, linear futures and fork/join are
  encodings in one adjoint session framework, with a sequential mode by self-shift.
- **Ferrite** runs sessions on tokio (§5.1). **rumpsteak** targets async Rust (§5.2).
- In this repository a future is the delay codata `D A = Loop A 1` (SPEC §7). Poll is one
  observation and cancellation is `close` (#52).

---

## 6. Analysis for us

### 6.1 The unifying claim (S1, S2)

Each artifact below is written in our types (SPEC §3, §7, §14) and in Pfenning–Griffith's
polarized session notation. *(ours throughout)*

| artifact | our type | session reading (provider side) | in `NuOk`? |
|---|---|---|---|
| iterator | `Iter A R R' = νX. F((A ⊗ U X) ⊕ R) & F R'` | offer `&{next : ↑⊕{yield : A ⊗ X, done : R}, close : ↑R'}` | yes |
| future / delay | `D A = νX. F(A ⊕ U X) & F 1` | offer `&{poll : ↑⊕{ready : A, pending : X}, cancel : ↑1}` | yes |
| loop (div) | `Loop A B` | as the future, with residual `B` | yes |
| stream | `νX. F(A ⊗ U X) & F 1` | offer `&{next : ↑(A ⊗ X), close : ↑1}` | yes |
| generator receiving on resume; a handled computation | `νX. (Resp ⊸ F((Req ⊗ U X) ⊕ R)) & F R'` | offer `&{resume : Resp ⊸ ↑⊕{request : Req ⊗ X, done : R}, close : …}` | **no**: an observation with an input |
| queue object | `νX. (A ⊸ F(U X)) & F(… )` | Pfenning–Griffith's `&{enq : A ⊸ queue A, deq : …}` | **no**, same reason |
| borrow (schematic, after `experiments/Shifts`) | `Ref A ⊸ U(∀'x ⊏ @b. Mut 'x A ⊸ F(['x] T)) ⊸ F(Ref A ⊗ T)` | receive a callback, send it a view, receive `T` back, send the owner back | not codata |

**What supports S1.**

- *Polarity is direction.* CBPV computation types are negative (they receive: `⊸` and `&`) and
  value types are positive (they send: `⊗` and `⊕`). This is Pfenning–Griffith's polarization,
  with `F`/`U` as their shifts `↑`/`↓`. Zeilberger places CBPV's type structure inside classical
  polarity. So S2 holds as printed, and every CBPV computation type is a protocol read from its
  provider.
- *The codata are already one mechanism.* Iterators, futures, loops and streams are one former,
  `ν`, with one soundness argument: coiteration by a greatest fixed point (decision 28, SPEC
  §7). Under the session reading, `ν` is a recursive session type offered by one party and
  driven by the other.
- The sequential reading is sound because the consumer is the scheduler: it chooses each
  observation, so there is no nondeterminism to rule out. Paykin–Zdancewic (polarization fixes
  the schedule) and Back to Futures §4 (sequentiality by a self-shift) are the printed forms of
  that argument.
- The soundness argument that would cover all the codata instances already exists and is
  proved. Session types rename it; they do not add a proof.
- *Handlers are one relaxation away.* A shallow handler is one observation of a suspended
  computation (decision 15). A handled computation that *receives* the handler's answer on
  resumption has an observation with an input. `NuOk` excludes that position (SPEC §7 *Open*:
  "the argument of an observation (`A ⊸ …`, a sink)"). The session literature treats it as
  ordinary: Pfenning–Griffith's queue, and Orchard–Yoshida's handler processes that answer
  requests. **This is the one concrete thing the session reading predicts that we do not have.**

**What undercuts S1.**

- *Borrows are only a rhyme.*
  - The session type of `withbor` is a call followed by a return. That is the `⊸` every function
    has, not something peculiar to borrowing.
  - What makes a borrow a borrow is absent from the session type: the frozen lender, the
    lifetime `'x`, the `['x]` box on the result, and the outlives side condition.
  - The borrow's soundness comes from the frame rules (`[TR]` 6.64–6.66), not from coiteration.
    So "one soundness argument for all four" fails at the borrow.
  - Acquire/release (Balzer–Pfenning) is the nearest session phenomenon, and the optics survey
    (§6.4) already lists five mismatches: dynamic versus static exclusion, lack of lexical
    scope, read sharing as a mode rather than a shift, deadlock versus validity ordering, and
    process versus sequential setting.
  - The one session paper that joins the two, BGV (Saffrich et al. 2025), borrows *channels*.
    It does not derive borrowing from sessions.
- *The literature does the sequential case by restriction, not by design.* Every printed
  sequential session system starts concurrent and then fixes a schedule: polarization in CP±,
  the sequential cut in Seax. None starts from a sequential CBPV with memory and lifetimes, and
  none has our leak-freedom adequacy for a borrowing language.

**Verdict.**

- **Iterators, futures and loops**, and handlers once the sink position lands: one mechanism.
  The evidence is moderate to strong. The pieces are printed (polarized sessions, coinductive
  sessions with logical relations, sequential scheduling by polarity), and the mechanism is
  already built here as `ν`. The session framing adds a vocabulary and one prediction (the
  sink). It does not add a new soundness argument.
- **Borrows:** a rhyme. The evidence is weak: nothing printed, and the structural mismatches
  are recorded in two surveys. The unifying abstraction for borrows remains where decision 22
  left it, at the frame guarantee.

### 6.2 Par here (S3, S4)

**Three ways to have `⅋`.**

1. **A computation-type former `C ⅋ C'`.**
   - Sequentially this is a computation with two continuations. The printed sequential readings
     are all control: λμ's continuation context, and Zeilberger's answer-typed delimited
     continuations.
   - Our machine has no control operator. `cC` interprets a computation by `wpTS` with one
     result.
   - Giving `⅋` a clause means either an answer-type (biorthogonal or realisability)
     interpretation of computations, in the style of Munch-Maccagnoni, or a judgment with
     several conclusions. Either changes every compatibility lemma: the "tax on every rule" that
     decision 19 forbids for an index.
   - It would also reopen what adequacy means: "`F 1` runs to `()` with empty memory" presumes
     one return.
   - **Proof cost: high. Unlock: none sequentially.**
2. **`⅋` as a derived form (the sequential coroutine).**
   - A producer and its consumer interleaved deterministically is `U(ν…)` handed to the
     consumer. The cut is application; the schedule is the consumer's choice of observation.
   - This exists today for one-way protocols. Two-way coroutines need the sink position (§6.1).
   - **Proof cost:** coiteration's map at a `⊸` position, which is post-composition under the
     argument. The relation is already monotone there wherever `X` avoids `Mut` payloads (SPEC
     §7 *Open*).
   - **Unlock:** U1 for bidirectional protocols and U4 for handlers, below.
3. **`⅋` with real concurrency (CP-style).**
   - This is where `⅋` does work that nothing else does: two processes that both run, with
     deadlock freedom by tree-shaped cut (Wadler §2.1; Jacobs et al. Thm 3.2).
   - It belongs to #52's threads phase, not to the sequential core.

**Against U1–U4** *(ours)*:

| test | former `⅋` | derived (`ν` + sink) | concurrent `⅋` (later) |
|---|---|---|---|
| U1 new protocol | none beyond control effects we route through codata | bidirectional coroutines, request/response objects, Pfenning–Griffith's queue | channels between tasks |
| U2 law once | a cut-associativity law, not a property we need | coiteration's soundness at the new position, once for every instance | deadlock + leak freedom as one "final" theorem |
| U3 optimization | none new; state machines are decided by shifts already (#18) | none new | none sequentially |
| U4 fewer mechanisms | adds one | handlers become `ν` instances, not a separate former | replaces ad hoc channel APIs |

The sequential `⅋` question reduces to the sink position of `ν`, and the conclusion is to not
add `⅋`.

### 6.3 One lattice? (S5)

| candidate | where it lands *(ours)* | why |
|---|---|---|
| usage: linear / affine / strict / unrestricted / erased | **an adjoint mode preorder**, already in `experiments/Grades` | The five grades `[1,1]`, `[0,1]`, `[1,∞]`, `[0,∞]`, `[0,0]` are Pruiksma–Pfenning's four modes plus an erased grade. Jang et al. give the four modes a sequential CBV semantics with garbage freedom and an erasure theorem based on the mode preorder (whether their erasure matches our grade `0` was not checked). `ModesLabels` checks `σ` semantically. |
| `Imm` / `Mut` | a mode for the payload plus a labelled shift | `ModesLabels`/`Shifts`: `Imm` is `unr`, `Mut` is at the mode with weakening only. The borrow axioms are shifts that break independence under a lifetime label. The adjoint frame classifies them; the label is not a mode. |
| locality (`local`/`global`) | **sugar over lifetimes, plus a lowering** | OxCaml's `borrow` is `withbor` with `local` for the lifetime. For owned data, "does not escape the region" is already forced by linearity (every cell is freed), so stack placement is a LIFO property of the lowering (dream C4), not a mode in the relation. OxCaml needs it as a mode because OCaml has a GC and free aliasing. |
| portability / contention | **a separate axis, needed only with threads and interior mutability** | Closures are `!T` and hold no resource (decision 3), so persistent closures cross threads trivially. The unsound case is an `Imm` borrow of data with interior mutability shared across threads (DRFCaml's `shared` versus `contended`). That arrives with interior mutability (being explored in another experiment, not on `main`) and threads, not before. |
| security levels | **a second semiring, as a product; a binary theorem** | Granule combines grades as products (ICFP 2019). The soundness theorem is noninterference, a two-run property (Abel–Bernardy Thm 7.10), which needs a binary relation we do not have (`experiments/TwoRun`). |

**Verdict.**

- **One adjoint mode lattice covers usage and adjoint logic's `!`/linear/affine split.** The evidence is
  strong: it is printed (Pruiksma–Pfenning; Jang et al.) and partly built (`Grades`,
  `ModesLabels`).
- **It does not absorb the rest.** OxCaml, the most developed modal system, is a product of axes
  (nine in its documentation) ordered pointwise, and each axis is justified by its own model (ICFP
  2024, POPL 2025, ICFP 2026 for crossing).
- Licata–Shulman–Riley could present such a product as one mode theory, but that is
  presentation, not a saved proof.
- The honest design is therefore a product of independent axes with one mode preorder inside
  the usage axis. Each new axis should arrive with the feature that needs it (threads,
  secrets), as decision 19 requires.

### 6.4 The north star (#67)

- **Typestate on an HTTP connection (U1).**
  - A protocol is a computation type, so a connection handle can be `U(Proto)` for a linear
    `Proto`. For example, `Req ⊸ F(Resp ⊗ U(Iter Chunk Conn Conn))`: send a request, receive a
    response head, then stream the body as an iterator whose residual hands the connection back.
  - A Kubernetes *watch* is `Iter Event Conn Conn`, which exists today.
  - An extern's contract is a semantic type at any value type (SPEC §11), and `U C` is a value
    type. So the kernel admits a host-implemented protocol handle with no new former. Whether the
    frontend accepts such a declaration is unchecked.
  - Leak freedom then says every connection reaches `close` on every run. That is the
    protocol-completion guarantee Rust session libraries cannot give (§5.2).
  - What needs the sink position is a handle whose *next step takes an argument chosen per
    step*: `send_header : Header ⊸ X` repeatedly, before `body`.
- **Deadlock-free channels for the async runtime (#52).**
  - In a single-threaded cooperative scheduler, deadlock means every task is blocked on a
    channel.
  - Tree-shaped channel creation (each channel's two ends go to exactly two tasks that share no
    other channel) rules it out by the CP argument, mechanised by Jacobs et al. with the same
    final-state shape as our adequacy.
  - The cost is a model of tasks and channels plus an acyclicity invariant in `wpTS`. That is a
    model change; our model is not step-indexed, where LinearActris's is.
  - An operator's fan-out (watch → work queue → reconcilers) is a tree. A cycle (a reconciler
    reporting back to the watcher) needs priorities (Kobayashi; Dardha–Gay; Priority Sesh).
- **Secrets (the service-account token).**
  - The cheap, unary version fits what exists: an opaque type `Secret` (decision 31) with no
    eliminator except externs that consume it at a trusted sink, such as attaching it as an
    `Authorization` header inside the TLS/HTTP extern.
  - By the frame result (`wpTSD_frame_own`), code not given the secret cannot observe it. That is
    confinement, not noninterference.
  - Security *grades* (computing on secrets while keeping outputs public) need the binary
    relation. The operator does not appear to need that.

### 6.5 Next experiments, ranked

1. **`ν` with a sink position: sessions as codata** (highest value, bounded).
   - *Do.* Extend `NuOk` so that an observation may take an argument, `A ⊸ (observation
     tree)`, with `A` closed (no `X`). Define coiteration's map there as post-composition. Prove
     `unfold` sound at the extended class, reusing the greatest-fixed-point candidate.
   - *Derive, with no new former:*
     - a coroutine whose `resume` takes a value;
     - Pfenning–Griffith's queue object;
     - a shallow handler for a request/response effect as a `ν` instance.
   - *Proves:* S1 for handlers (U4: handlers need no separate former) and U1 (bidirectional
     protocols).
   - *Evidence:* `fundamentalC` covering the relaxed `nuIn`/`nuOut`/`unfold`; each example a
     closed `CDerives` derivation run by adequacy with no cell left; the existing `Iter`/`D`
     instances unchanged.
   - *Falsifier:* coiteration at the input position fails monotonicity or needs a step index.
2. **A protocol-typed capability at the extern boundary** (U1, north star).
   - *Do.* Declare a model HTTP-like connection extern at a `U(Proto)` type, with the model as a
     Lean term meeting the contract, where `Proto` is a request, a response head, then an
     `Iter` body with the connection as residual. Write a corpus program that performs two
     requests and a watch-style stream.
   - *Proves:* typestate needs no kernel change, and leak freedom is protocol completion. It
     also checks whether the frontend accepts externs at `U C` types.
   - *Evidence:* the corpus program compiles and runs with `live 0`, and the use of a closed
     connection is rejected as a `bc,reject` example.
   - *Falsifier:* the extern contract at a computation type cannot be met by a model, or the
     elaborator needs a rule.
3. **Modes as a product, measured** (S5, bounded, no model change).
   - *Do.* In `experiments/Grades`, state the five grades as Pruiksma–Pfenning modes with
     `σ`, and check the preorder and the declaration of independence against `ModesLabels`
     (`decide` where finite).
   - *Do.* Add a two-point `Level` as a second axis of the context coordinate. Prove its
     *unary* consequence (confinement: a function whose context holds a `Secret` only at an
     erased or sink position cannot return it) from the existing frame result.
   - *Do.* State, but do not build, the binary statement noninterference would need.
   - *Proves:* the usage axis is an adjoint mode system, and what a second axis costs when its
     theorem is unary versus binary.
   - *Evidence:* laws by `decide`, one confinement theorem, and a written `def … : Prop` for
     noninterference with its missing ingredient named.

**Not recommended now.**

- A `⅋` former (§6.2): high cost, no sequential unlock.
- Concurrent channels before #52 has threads: the model change is real and nothing sequential
  needs it.
- Security grades before a binary relation exists.

---

## 7. Not read, or not verified

- **Abstract, publisher page or search summary only**:
  - Kobayashi (CONCUR 2006); Dardha & Gay (FoSSaCS 2018); Dardha & Pérez (arXiv); Kokke &
    Dardha (Haskell 2021);
  - Lindley & Morris (ESOP 2015; ICFP 2016); Fowler et al. (POPL 2019);
  - Lolliproc; Berdine et al.; Laurent; Munch-Maccagnoni (CSL 2009);
  - Curien–Fiore–Munch-Maccagnoni (the HAL PDF did not download; slides were read); Ehrhard
    (ESOP 2016);
  - Licata–Shulman; Toninho–Caires–Pfenning (both corecursion papers); LinearActris;
  - *Borrowing from Session Types* (the ACM PDF was refused; SPLASH abstract and artifact page
    read); *Typestate via Revocable Capabilities*;
  - *Mode Crossing* (artifact page and a search summary only); *Modal Effect Types*; Yarrow;
    Marshall–Orchard (arXiv 2309.04324); CLASS.
- **Secondhand**: Gay & Vasconcelos (JFP 2010); Benton (CSL 1994); Reed (2009); Pruiksma et al.
  (2018); Carbone & Debois (2010); `session_types`, `sesh`, `rumpsteak` (via Ferrite §8);
  Marshall–Vollmer–Orchard (ESOP 2022).
- **Fetched through a summarising tool, not read verbatim**: the OxCaml modes documentation and
  the Jane Street locality post. The two disagree on the orientation of the locality order; the
  ICFP 2024 paper's is used.
- **Numbering**: Wadler was read in the ICFP 2012 version; Pruiksma–Pfenning in the PLACES 2019
  version; Back to Futures in arXiv v2. Journal versions may number differently.
  Pfenning–Griffith's sections are cited by name, because the extracted text did not preserve
  their numbers.
- **Not found**, after searching:
  - a paper on "call-by-push-value and session types" as such;
  - `⅋` added to CBPV computation types with a logical relation;
  - a lexically scoped borrow printed as a session type;
  - a sequential, memory-carrying session calculus with a leak-freedom adequacy theorem.
- **Not built or typed**: every *(ours)* type in §6 (the sink-position `ν`, the protocol
  handles, the `Secret` confinement statement).

---

## Sources

- Caires, Pfenning. *Session Types as Intuitionistic Linear Propositions*. CONCUR 2010.
  https://www.cs.cmu.edu/~fp/papers/concur10.pdf
- Wadler. *Propositions as Sessions*. ICFP 2012; JFP 24(2–3), 2014.
  https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf
- Gay, Vasconcelos. *Linear Type Theory for Asynchronous Session Types*. JFP 20(1), 2010.
- Lindley, Morris. *A Semantics for Propositions as Sessions*. ESOP 2015, LNCS 9032.
  doi:10.1007/978-3-662-46669-8_23
- Lindley, Morris. *Talking Bananas: Structural Recursion for Session Types*. ICFP 2016.
  doi:10.1145/2951913.2951921
- Fowler, Lindley, Morris, Decova. *Exceptional Asynchronous Session Types: Session Types without
  Tiers*. POPL 2019. doi:10.1145/3290341
- Kobayashi. *A New Type System for Deadlock-Free Processes*. CONCUR 2006, LNCS 4137.
  doi:10.1007/11817949_16
- Dardha, Gay. *A New Linear Logic for Deadlock-Free Session-Typed Processes*. FoSSaCS 2018.
  doi:10.1007/978-3-319-89366-2_5
- Dardha, Pérez. *Comparing Type Systems for Deadlock Freedom*. arXiv:1810.00635.
- Kokke, Dardha. *Deadlock-Free Session Types in Linear Haskell*. Haskell 2021.
  https://arxiv.org/abs/2103.14481
- Jacobs, Balzer, Krebbers. *Connectivity Graphs: A Method for Proving Deadlock Freedom Based on
  Separation Logic*. POPL 2022. https://iris-project.org/pdfs/2022-popl-connectivity-graphs.pdf
- Jacobs, Hinrichsen, Krebbers. *Deadlock-Free Separation Logic: Linearity Yields Progress for
  Dependent Higher-Order Message Passing*. POPL 2024.
  https://iris-project.org/pdfs/2024-popl-dlfactris.pdf
- Aschieri, Genco. *⅋ Means Parallel: Multiplicative Linear Logic Proofs as Concurrent
  Functional Programs*. POPL 2020. https://arxiv.org/abs/1907.03631
- Paykin, Zdancewic. *Linear λμ is CP (more or less)*. In *A List of Successes That Can Change
  the World*, LNCS 9600, 2016. https://www.cis.upenn.edu/~stevez/papers/PZ16.pdf
- Mazurak, Zdancewic. *Lolliproc: to Concurrency from Classical Linear Logic via Curry-Howard and
  Control*. ICFP 2010. doi:10.1145/1863543.1863551
- Berdine, O'Hearn, Reddy, Thielecke. *Linear Continuation-Passing*. Higher-Order and Symbolic
  Computation. doi:10.1023/A:1020891112409 (year not checked).
  http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/LinCP.pdf
- Pfenning, Griffith. *Polarized Substructural Session Types*. FoSSaCS 2015, LNCS 9034.
  https://www.cs.cmu.edu/~fp/papers/fossacs15.pdf
- Zeilberger. *Polarity and the Logic of Delimited Continuations*. LICS 2010.
  https://www.lix.polytechnique.fr/~zeilberger/papers/polpol.pdf
- Zeilberger. *The Logical Basis of Evaluation Order and Pattern-Matching*. PhD thesis, CMU, 2009.
  https://noamz.org/thesis.pdf
- Laurent. *Polarized Proof-Nets and λμ-Calculus*. TCS 290(1), 2003.
- Munch-Maccagnoni. *Focalisation and Classical Realisability*. CSL 2009, LNCS 5771.
- Curien, Fiore, Munch-Maccagnoni. *A Theory of Effects and Resources: Adjunction Models and
  Polarised Calculi*. POPL 2016. https://hal.science/hal-01256092
- Ehrhard. *Call-By-Push-Value from a Linear Logic Point of View*. ESOP 2016.
  https://www.irif.fr/~ehrhard/pub/llcbpv.pdf
- Pruiksma, Pfenning. *A Message-Passing Interpretation of Adjoint Logic*. PLACES 2019, EPTCS 291;
  JLAMP 120, 2021. https://arxiv.org/abs/1904.01290
- Pruiksma, Pfenning. *Back to Futures*. JFP 32, 2022. https://arxiv.org/abs/2002.04607
- Jang, Roshal, Pfenning, Pientka. *Adjoint Natural Deduction*. FSCD 2024, LIPIcs, article 15.
  https://arxiv.org/abs/2402.01428
- *Ordered Adjoint Logic* (extended version). arXiv:2605.19112, 2026 (title only).
- Benton. *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models*. CSL 1994.
- Reed. *A Judgmental Deconstruction of Modal Logic*. Manuscript, 2009.
- Pruiksma, Chargin, Pfenning, Reed. *Adjoint Logic*. Manuscript, 2018.
  https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf
- Balzer, Pfenning. *Manifest Sharing with Session Types*. ICFP 2017; TR CMU-CS-17-106R.
  https://www.cs.cmu.edu/~fp/papers/CMU-CS-17-106R.pdf
- Balzer, Toninho, Pfenning. *Manifest Deadlock-Freedom for Shared Session Types*. ESOP 2019.
- Sano, Balzer, Pfenning. *Manifestly Phased Communication via Shared Session Types*.
  COORDINATION 2021. https://arxiv.org/abs/2101.06249
- Licata, Shulman. *Adjoint Logic with a 2-Category of Modes*. LFCS 2016, LNCS 9537.
  doi:10.1007/978-3-319-27683-0_16
- Licata, Shulman, Riley. *A Fibrational Framework for Substructural and Modal Logics*. FSCD 2017.
  https://drops.dagstuhl.de/opus/volltexte/2017/7740/pdf/LIPIcs-FSCD-2017-25.pdf
- Lorenzen, White, Dolan, Eisenberg, Lindley. *Oxidizing OCaml with Modal Memory Management*.
  ICFP 2024. https://homepages.inf.ed.ac.uk/slindley/papers/mode-inference.pdf
- Georges, Peters, Elbeheiry, White, Dolan, Eisenberg, Casinghino, Pottier, Dreyer. *Data Race
  Freedom à la Mode*. POPL 2025. https://iris-project.org/pdfs/2025-popl-drfcaml.pdf
- Peters, Jacobs, Kalinichenko, Stevenson, Smith, Dreyer, Eisenberg. *Mode Crossing*. ICFP 2026.
  Artifact: https://zenodo.org/records/20436924
- OxCaml documentation, *Modes: Intro*. https://oxcaml.org/documentation/modes/intro/
- Slater. *Oxidizing OCaml: Locality*. Jane Street blog, 2023.
  https://blog.janestreet.com/oxidizing-ocaml-locality/ ; *Rust-Style Ownership*:
  https://blog.janestreet.com/oxidizing-ocaml-ownership/ ; *Data Race Freedom*:
  https://blog.janestreet.com/oxidizing-ocaml-parallelism/
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen. *Modal Effect Types*. OOPSLA 2025.
  https://arxiv.org/abs/2407.11816
- Orchard, Liepelt, Eades. *Quantitative Program Reasoning with Graded Modal Types*. ICFP 2019.
  https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- Abel, Bernardy. *A Unified View of Modalities in Type Systems*. ICFP 2020.
  https://www.cse.chalmers.se/~abela/icfp20.pdf
- Moon, Eades, Orchard. *Graded Modal Dependent Type Theory*. ESOP 2021.
  https://arxiv.org/abs/2010.13163
- Marshall, Orchard. *Replicate, Reuse, Repeat: Capturing Non-Linear Communication via Session
  Types and Graded Modal Types*. PLACES 2022, EPTCS 356. https://arxiv.org/abs/2203.12875
- Marshall, Orchard. *Graded Modal Types for Integrity and Confidentiality*. arXiv:2309.04324.
- Marshall, Vollmer, Orchard. *Linearity and Uniqueness: An Entente Cordiale*. ESOP 2022.
- Chen, Balzer, Toninho. *Ferrite: A Judgmental Embedding of Session Types in Rust*. ECOOP 2022,
  LIPIcs 222:22. https://arxiv.org/abs/2205.06921
- Jespersen, Munksgaard, Larsen. *Session Types for Rust*. WGP 2015.
- Kokke. *Rusty Variation: Deadlock-Free Sessions with Failure in Rust*. ICE 2019.
- Cutner, Yoshida, Vassor. *Deadlock-Free Asynchronous Message Reordering in Rust with
  Multiparty Session Types*. arXiv:2112.12693 (as cited by Ferrite; later venue not checked).
- Bernardy, Boespflug, Newton, Peyton Jones, Spiwack. *Linear Haskell*. POPL 2018.
  https://arxiv.org/abs/1710.09756
- Saffrich, Spaderna, Thiemann, Vasconcelos. *Borrowing from Session Types*. OOPSLA 2025.
  doi:10.1145/3763173 ; https://2025.splashcon.org/details/OOPSLA/199/Borrowing-From-Session-Types
- Saffrich, Nishida, Thiemann. *Law and Order for Typestate with Borrowing*. OOPSLA 2024.
  https://arxiv.org/abs/2408.14031
- Jia, Liu, He, Deng, Bao, Rompf. *Typestate via Revocable Capabilities*. PLDI 2026.
  https://arxiv.org/abs/2510.08889
- Caires. *Thread and Memory-Safe Programming with CLASS*. PLACES 2025.
  https://arxiv.org/abs/2505.20848
- Orchard, Yoshida. *Effects as Sessions, Sessions as Effects*. POPL 2016.
  https://www.doc.ic.ac.uk/~dorchard/publ/popl16-orchard-yoshida.pdf
- Mathiasen, Timany, Birkedal. *Yarrow: Reconciling Effect Handlers and Region-Based Memory
  Management*. arXiv:2607.15876, 2026.
- Toninho, Caires, Pfenning. *Corecursion and Non-Divergence in Session-Typed Processes*. TGC
  2014, LNCS 8902; *Corecursion in Session-Typed Processes* (CMU-hosted manuscript, 2014; venue
  not checked). https://www.cs.cmu.edu/~fp/papers/coind14.pdf
- Anton, Thiemann. *Typing Coroutines*. TFP 2010.
  https://proglang.informatik.uni-freiburg.de/projects/coroutines/TFP2010-ext.pdf
