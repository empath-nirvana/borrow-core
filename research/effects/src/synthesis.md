# Synthesis: coherent whole-system designs

This chapter reads the nine prior-art menus together with the targets (`experiments/Targets`), the shared brief and today's kernel. From them it derives a small set of whole-system designs, each consistent with every decided constraint and with every relation the menus state. Where a design meets a menu edge only by a reading of this chapter's, §1.4 records the edge and the reading. Each design is given as a change to today's kernel: what it adds, what it gives up, where the two systems meet in it, and how System A and System B fare in it. The chapter names the design closest to today and a probe that would show whether that design is tractable. It does not recommend a design. The user chooses.

**Marks.** As in the menus:
- **[read]**: read for this chapter in the named source (a menu, a target file, the kernel, the brief).
- **[synthesis]**: my reading across sources. No single source states it.
- **[local]**: read off this repository's Lean or documents.

No Lean was built for this chapter. Every "open" means that I have not derived it and have not verified that any obstruction is real. Nothing here is a claimed obstruction.

**Worlds.** These are the notebook's tags: Core σ=[], W, GE (GhostEnd), SIB (EffModelRel), PAPER, probe.

**Option codes.** The menus' codes collide. X.1 appears in two menus, F.1 in two, and B1–B7 is both I4's option list and B's guarantees. So every option is written with its menu as a prefix:

| prefix | menu | its codes |
|---|---|---|
| `p2:` | [P2 effect safety](prior-art/p2-effect-safety.md) | R1–R6 (representation), S-a … S-g (statement and route) |
| `p8:` | [P8/P5 linearity, drop](prior-art/p8-p5-linearity-drop.md) | 8.1–8.6, 5.1–5.6, X.1–X.3 (interception), F.1–F.3 (finaliser rows) |
| `i2:` | [I2 capture and resume](prior-art/i2-capture-resume.md) | M0–M3, T1–T4 |
| `p10:` | [P10/P9 exclusivity, lifetimes](prior-art/p10-p9-exclusivity-lifetimes.md) | X.1–X.7, L.1–L.7 (L.4a/b/c, L.6a/b/c) |
| `rc:` | [rows vs capabilities](prior-art/rows-vs-capabilities.md) | O1–O4 and variants (O1-a, O1-c, O1-ε, O2-pure, O2-C, O2-lt, O2-g, O3-surface) |
| `p11:` | [P11/I5 laws](prior-art/p11-i5-laws.md) | H.1–H.4, F.1–F.4 (forms), K.1–K.6, Z.1–Z.3 |
| `p12:` | [P12 abstraction](prior-art/p12-abstraction.md) | AS0–AS5, N1–N8, PR-a … PR-d |
| `p13:` | [P13 zero cost](prior-art/p13-zero-cost.md) | Z0–Z5, C1–C5, P0–P4 |
| `p14:` | [P14, I1, I4 interaction](prior-art/p14-i1-i4-interaction.md) | W0–W6, V1–V7, B1–B7 |

The targets' own names are RESTRUCTURE's and are written bare: S0–S6, E1–E10, B0–B7, I1–I5, `Tier2Programs`, `Combined`. This chapter's own items are numbered by design: D1.a (A's side), D1.i (the interaction), D1.h (the hard test, beyond done), D2.c, D2b.o and D3.k. The design D1+B4 takes two of D2's items (D2.c4, D2.c11) and has no items of its own.

---

## 0. Summary

- **The map.** The options of the nine menus and the relations they state form one map (§1). Three chains run through it:
  - every design in which a lend spans a stop needs a handler extent (`p10:L.4a`) and static nesting order (D-ORD);
  - every design that makes capabilities values (`rc:O2`) needs boxes or an outlives rule at `U C` (`p10:L.3`) for stored callbacks. By rc §3.7, rows of lends (`rc:O3`) need the same at Core. This chapter reads D2.c9, the extent bound in callback types, as removing that need for rows of lends; the reading is unchecked (§1.4 item 13);
  - hiding at W (`p11:K.5`) is needed exactly when handler state is lent across a stop (`p10:X.2`).
- **Inconsistencies.** §1.4 flags fourteen inconsistencies between the menus.
  - Three change a cost:
    - under ghost end, neither K.2 nor L.5 needs the freeze binder;
    - Z4b holds under the as-built placement (`p13:P1`);
    - AT17 needs no location symmetry in the relation, by a reading of Core's machine that is not checked (item 11).
  - One changes a target: `reconB`, as RESTRUCTURE §3.4 writes it, puts both of its handlers inside the borrow, so by reading it is typable at tier 1.
  - One records how ghost end meets the menus' "tier-2 stop change" with conjuncts 37 and 40 unchanged (item 12).
  - One may add OQ-28's rule to D2a: rc §3.7 says that rows of lends need everything capabilities need at Core, the outlives rule at `U C` among them (item 13).
  - One records how D1's `p10:L.4` (a) meets `p14:B1`'s requirement of (c) (item 14).
- **What decides A, and which designs change it** (§2.5).
  - A's statements read no resource, but their proofs at our instance do. S2 and S3 come through B's `Sound` and FL (`p2:S-e`), the only route built at W. So at `J₂` they ride on FL at W, which is Law 2 and GFP, and the tier-2 choice decides them in every tier-2 design.
  - `p2:S-f` would free S3 from B, at the cost of A-level typing rules and a syntactic subject reduction that Core lacks. No menu frees S2.
  - D0, D1 and D1+B4 leave A's object as it is today: `orowRF`, with operation types closed in lifetimes.
  - D2 puts the site's extent into row entries and callback types.
  - D3 puts lifetime-quantified operations into signatures, and needs scoped rows for their masking.
- **Where the two systems meet** (§2.5, §4.2).
  - D0 meets "two algebras with interactions only at cuts".
  - D1 and D1+B4 meet it only if Law 2 is placed at the resume cut: proved as naturality, or with the future-world quantifier at `U`, `contShare` and `KapRel` (OQ-8's options 1 and 2). The evidence so far points to the binder clauses (option 3), which would put a resume obligation into every `⊸` and `∀` clause of the relation. §11's statement 0 settles the placement in Lean.
  - D2 and D3 each put a lifetime inside the effect algebra, away from the cuts.

  In today's kernel the relation reads effects through `opTable` and the stop conjuncts of `wpG`. The typing reads them in `effLet`'s capturing condition and in the six `*U` constants, which every design replaces (§3.1, §3.3).
- **The hard test, at done** (§4.3).
  - **Laws of handling.** Done holds S4's reductions. `TailLaw`, `AlgLaw` and `EtaHold` are laws of the handling construct, stated beside done, not in it.
  - **Handlers as models.** Signatures carry no equations, so every handler is a model (Plotkin–Pretnar Def. 4.5), and models and comodels (`p14:B3`) are vacuous. A model obligation needs equations in signatures.
  - **The answering class.** The surface's answering handlers, which §18 elaborates to `withbor`/`withswap`, are A's handlers only with `I4Typing` and a run correspondence, or natively under D1+B4. Done's `Pins` holds `I4a` alone.

  The completion is D1.h1–h4:
  - h1, `A.UnaryLaws`, the laws of handling;
  - h2, `I4Typing` with a unary run correspondence;
  - h3, models and comodels (`p14:B3`, the signed-off item 2);
  - h4, the theory side: equations writable in signatures (OQ-22 (a)), with a model obligation per handler.

  Decided items require all four in every design: "Laws first", "the actual calculus … no effect-ish encoding" and "effects are core" (§2.1). They cost about the same in every design. Under D3's scoped rows `TailLaw`'s hygiene premise changes (§6.3).
- **The signed-off structure** (BRIEF §5, 2026-10-03; §2.1).
  - D1 meets items 1, 3 and 5.
  - It meets item 4's one world W with the stop instantiated at `held = ([],[])`, which is today's stop. Whether that is the relativised stop item 4 names, or a departure from it, is for the user. Item 4's placement of the future-world quantifier is open, and the cuts depend on it (above).
  - Item 2 (`p14:B3`) is stated nowhere in the targets. Every design can take it (D1.h3). It is non-vacuous only with D1.h4.
- **A capability kernel is not excluded; it is costed** (§2.3). A capability kernel (`rc:O2`) costs:
  - an elaborating instance for A's label-based terms;
  - System Ξ's rule Def, for E2c, E2d and E10;
  - boxes or `p10:L.3`, for E1′, E2b and E9;
  - `rc:O2-g`, for the lowering's class.

  By reading, E2b also needs a quantifier over what a stored callback asks of the context it later meets, which is `rc:O3`'s row on stored callbacks. So D2 has two variants: D2a (rows of lends, `rc:O3`) and D2b (capabilities as values, `rc:O2`). D2b's delta is D2a's plus those costs (§5.7).
- **The designs** (§2.4):
  - **D0**, tier 1 with the row `∀`: a stage of D1;
  - **D1**, rows and ghost end;
  - **D1+B4**, D1 with one install mechanism. Answering handlers are native `hnd`, and an answering site lends its state, in the borrow form. Rows stay rows of labels, and no type names an extent;
  - **D2a / D2b**, capabilities as borrows with extents in types and answers borrowed from handler state: rows of lends, or capabilities as values;
  - **D3**, rows and carried lends.
- **D1's target is done**, `Combined orowRF J₂ W admClosedOp .any`, and it keeps today's stop condition. It is the coherent design closest to today. None of it is built. Two of its claims rest on readings I have not checked:
  - AT17 without a location symmetry (§1.4 item 11);
  - that item 4's relativised stop admits `held = ([],[])`.
- **"You're just missing …" (D1, §10).** Two laws stand between today and done:
  - Law 1: the row `∀` is the intersection of its instances;
  - Law 2: a lend ended at a stop is re-lent at a fresh lifetime at resume.

  Beyond them stand S6's proof route, wiring that is named lemma by lemma, and two lemmas on B's side that every design shares. The wiring includes [TR] 6.150 lifted to resuming tables. `withload`'s spanning rule needs that lift whatever OQ-29 decides, and six reports have carried it forward unbuilt (BRIEF §8 pattern 7). Meeting the user's hard test adds four items: the laws of handling (h1), the answering class (h2), models and comodels (h3), and theories with their model obligations (h4).
- **The next cheapest sacrifice after multi-shot** (§9). It depends on the measure.
  - **By value lost**, it is OQ-29, answers borrowed from handler state. No target in done needs it. As D2 would take it (Ante's coarse rule, A5(b)), it covers handlers with one live answer at a time. Arenas with many live allocations need a finer rule, which no design here takes, so every design loses them.
  - **By proof saved**, it is OQ-56's borrow form, that is, keeping R-CLOSEDOP. It is what saves the stop change, scoped rows for masking, and `p10:X.5`. It costs one program shape: `read(&mut buf)` passes the buffer by ownership.
  - D1 makes both sacrifices, and done already makes them.
  - **Free theories only** is not available as a sacrifice: "Laws first" is decided, and OQ-22 is constrained toward equations in signatures (§2.1).
  - **The step from D3 to D1** gives up two features. One is OQ-56's borrow form. The other is OQ-28's rule, which D3 must take and D1 may leave open. OQ-28's program cost is that no closure or continuation that owns a resource is returned out of a borrow callback. Its saving (T2, #173) does not depend on the stop.
  - Placement parity is paid by every tier-2 design, D3 included, so it is not part of that step.
- **Capabilities as borrows, at its marginal cost over D1** (§5.1). It comes in three tiers. Each tier can be taken without the ones after it:
  - **(i) Install and the answering class (D1+B4): small.**
    - Answering handlers become native `hnd`, an answering site lends its state in the borrow form (`p14:B4`), and rows stay rows of labels.
    - Over D1 it costs D2.c4 (§18 emits `hnd`, and `ewp_handle`'s answering case is discharged by 6.65 through the borrow form and the correspondence) and D2.c11 (an `answering` class in W1's guard). D1.h2 and D1.h3 are shared, since the hard test needs them in D1 too.
    - Its cuts are D1's, with the answering lend at the install cut. No type names an extent, so D2.c8 and D2.c9 do not arise.
  - **(ii) Extents in types: moderate, and open.**
    - Row entries carry the site's extent (D2.c1–c3), Law 2 re-reads types at extents (D2.c8), and callbacks bind extents (D2.c9). By rc §3.7 it may also need OQ-28's rule (§1.4 item 13).
    - It buys AS1 and a second route to S3, both by 6.60 (B7).
    - It puts a lifetime into the row algebra and into callback types. That is away from the cuts unless extents are read only at install, transit and resume.
  - **(iii) Answers borrowed from handler state (OQ-29): large, and open.**
    - It needs tier (ii), `AntiFrameW` at W, the handler-state instance of 6.150's lift, and decision 59's state passing shown to be X.2's round trip (D2.c5, D2.c10). The lift itself is D1's (D1.i5), so it is not a cost of this tier.
    - It buys Ante's rule (b) as B6. No target in done asks for it.
  - **Shared by every tier:** the handler extent, which D1 needs too, and the control-class carrier for the lowering, which costs the same under every design.
  - **No gain in reuse at tier (i).** The borrow facts about answering handlers concern the borrow encoding that D1's surface already emits: `handle_is_shift`, `effect_safety`, `op_tail`, `op_answer`, `handle_fold` and the escape check. They reach native `hnd` only through `I4Typing` and a run correspondence, which is D1.h2. Tier (i) does remove the answering encoding's cell (`log-outside` 1 → 0), and S4 and h1 then cover the language's answering handlers directly.
- **Ranking.**
  - **The cuts criterion** ranks D0 > D1 = D1+B4 > D2a > D3, with D2b last: D2b types effects by borrows throughout, so there is no separate effect algebra for the cuts to bound. D1's place assumes Law 2 at the resume cut. Under OQ-8's option 3, D1 still ranks ahead of D2a, which inherits Law 2 and adds extents in types, and of D3; but only D0 then meets "only at the cuts" (§8).
  - **Expressiveness** runs the other way. D3 alone carries the async read in its borrow form, and D2 alone carries OQ-29. D1+B4 carries what D1 carries.
  - **By concrete reuse** D1 and D1+B4 rank first. Under ghost end every borrow guarantee is reused at Core's stop, and tier 2 is the printed 6.64 and 6.65 proofs applied once per resumption. D2a reuses three more borrow facts: B7 for AS1 and for a second route to S3, and B6 for the exclusivity of answers borrowed from handler state. It pays for them with D2.c3, c8, c9 and c10, all open, and the third fact arises only with OQ-29. D3 re-proves every consumer of the run-end relation off the nil slice, and reopens S1.
  - **The dependency of A's proofs on B** (S2 and S3 through FL) is shared by every tier-2 design, so it does not reorder them. It does mean that the probe's failure costs A's S2 and S3 at `J₂` (§11).
- **The one-shot cell (`p8:8.3`)** is the variant under which continuation linearity is not built twice. S6 would then follow from B's adequacy: a second use is stuck, and a forgotten continuation leaves a cell. It needs S4 restated, and the user's call (AGREE Q9). See §7.1.
- **The probe (§11).** It asks whether FL at W holds for exactly the rules `genSelf` and `reconB′` use. It is the same probe for D1 and D1+B4. Its statements, in order:
  0. W's `U`, `⊸` and `∀` clauses fixed together in Lean, with the guard read from `TW`, and the `U`-clause thaw proved there rather than assumed to transport from the unguarded stacked relation. This settles where the future-world quantifier sits, and with it the cuts criterion;
  1. the arising guard read from `TW` (OQ-45);
  2. the borrow-constant row read at σ·y (#275), with Core as W's σ=[] instance (OQ-58);
  3. `[handle]` with a lend open, and a stop handled inside the borrower (#278, `AllCross` relaxed);
  4. `[allR-E]` at W.

  A sample of GFP's remaining rows, `effThen` at a frozen frame's cancel, tests whether the pattern extends. The rest of GFP's induction stays open whatever the probe shows. Success records which placement the proofs used. The fallback is D3, then D0.

---

## 1. The compatibility map

### 1.1 The nodes

"Today" says where the kernel or the targets sit. "—" means not built.

**P2 effect safety**

| node | option | today |
|---|---|---|
| `p2:R1` | simple rows over static per-site names, no masking | `orowRF`, SPEC §19 |
| `p2:R2` | R1 with Yoshioka's conditions (3)/(4) as checked conjuncts (`NoLift`, `OneSigPerName`) | prose only (RESTRUCTURE §1.5) |
| `p2:R3` | Rémy rows with lacks constraints | `RowCon.adm` could carry it |
| `p2:R4` | scoped rows with mask/lift (Koka); erasable variant `EA_EScpR` | — |
| `p2:R5` | capabilities: (a) a proof route for S3, (b) a replacement for rows | HandlersAsBorrows (PAPER) |
| `p2:R6` | modal effects, Met(X) | — |
| `p2:S-a` | progress at ε over reachable configurations | S3 `EffSafe` |
| `p2:S-b` | terminating-only | — |
| `p2:S-c` | faulty terms untypable | — |
| `p2:S-d` | capability form ("no undelimited label") | — |
| `p2:S-e` | a corollary of the fundamental lemma and adequacy | `effSafe_tier1` (Core σ=[]) |
| `p2:S-f` | a generic A-level theorem, `RowAlgebra ∧ TypingRules ⇒ EffSafe` | — |
| `p2:S-g` | trace over-approximation under every runner | — |

**P8/P5 linearity and drop**

| node | option | today |
|---|---|---|
| `p8:8.1` | capture lemma, typing side | in the rules, no lemma |
| `p8:8.2` | tagged conservation (Tang Thm 3.6) | — |
| `p8:8.3` | one-shot cell in the machine | excluded by S4 (AGREE Q9) |
| `p8:8.4` | ghost obligation in the relation | named as a route to `ContUse` |
| `p8:8.5` | observational use counts on runs | S6 `ContUse` (stated, open) |
| `p8:8.6` | resource half only | B4, B5 |
| `p8:5.1` | event traces of cancel and unwind | S5 (stated, open; `noInterception_tier1` at Core σ=[]) |
| `p8:5.2` | denotational factoring (Ahman–Bauer Thm 7) | — |
| `p8:5.3` | instrumented invariant (Voigt Thm 3.6) | — |
| `p8:5.4` | exactly once via empty memory | B2, B4, B5 |
| `p8:5.5` | tagged finaliser frames, global exactly-once | — |
| `p8:5.6` | lends ended by the cancel | `ShareCancel` (σ=[]); `CancelCloses` named only |
| `p8:X.1` | catchable, must re-raise | §19's finaliser frames |
| `p8:X.2` | uncatchable forced unwind | §19's handlers |
| `p8:X.3` | interceptable, re-linearised (OCaml) | rejected by §19 |
| `p8:F.1` | finalisers abortive-only | as built |
| `p8:F.2` | resuming finalisers to outer handlers | OQ-7 (a), open |
| `p8:F.3` | finalisers that must not fail | §19 *Open* |

**I2 capture and resume**

| node | option | today |
|---|---|---|
| `i2:M0` | keep T1 and `↭` (tier 1 only) | today's kernel |
| `i2:M1` | ghost end: end internal lends at the stop, re-lend fresh at resume | GhostEnd instances (Core σ=[], GE) |
| `i2:M2` | carry lends open across the stop | WorldW (probe) |
| `i2:M3` | unfold at the stop, refold at the same lifetime | refuted (`refoldKripke_false`) |
| `i2:T1` | Ante-style restrictions as a tier-2 typing (H1/H2) | — |
| `i2:T2` | second-class resume; a boxed κ with a lifetime bound | `ewp_gen` (`lift-stage1`, stopped) |
| `i2:T3` | freeze-as-binder equivariance as the proof route | `FreezeBinder` stated, open |
| `i2:T4` | immovable placement (Pin) | — |

**P10/P9 exclusivity and lifetimes**

| node | option | today |
|---|---|---|
| `p10:X.1` | reborrow encoding, answering handlers | PAPER; `i4a_tier1` (abortive rows) |
| `p10:X.2` | reborrow encoding, control handlers (6.66 across stops) | `AntiFrameW` stated, open at W |
| `p10:X.3` | count suspended loans in the world (≡ `i2:M2`) | `exclusive_core` (nothing held) |
| `p10:X.4` | ghost end, nothing held (≡ `i2:M1`) | GhostEnd instances |
| `p10:X.5` | a borrow passed up ends at `resume` (Ante H2) | — (R-CLOSEDOP) |
| `p10:X.6` | the clause cannot touch the body's places | enforced by `!U` clauses |
| `p10:X.7` | dynamic enforcement | out |
| `p10:L.1` | second-class `resume` and capabilities as frame-pinned borrows | capabilities at PAPER |
| `p10:L.2` | boxed continuation, a `[gen]` rule (OQ-28 (a)) | stopped |
| `p10:L.3` | outlives rule at `U C` (OQ-28 (b), #173) | none: Core's `VOutlivesR` has no `U C` constructor (`thunk_not_outlives`, CoeffectsStrict) |
| `p10:L.4a/b/c` | a handler site opens a lifetime: (a) every site, (b) a named restriction, (c) answering sites only | (c) at PAPER; `effHandle` opens none |
| `p10:L.5` | resumption under a different handler: D-ORD | `AllCross` at constant `true` only |
| `p10:L.6a/b/c` | operation types at a borrow callback: (a) R-CLOSEDOP, (b) `∀`-operations masked at the lend's end, (c) only outer lifetimes | done at (a) |
| `p10:L.7` | lifetime tokens owned by κ | — |

**Rows vs capabilities**

| node | option | today |
|---|---|---|
| `rc:O1` (`O1-a`, `O1-c`, `O1-ε`) | rows of labels (simple, scoped, with a class bound on row variables) | layers, no row `∀` in `CDerives`; `RowCon.cls` in the targets |
| `rc:O2` (`O2-pure`, `O2-C`, `O2-lt`, `O2-g`) | capabilities as borrows (System Ξ, System C, lifetime bounds, with a class grade) | answering effects at the surface (§18) |
| `rc:O3` (`O3-surface`) | rows of lends `(instance, lifetime)` (capabilities at the surface) | EffModelRel `Rw` (SIB) |
| `rc:O4` | modal effects as the common encoding | — |

**P11/I5 laws**

| node | option | today |
|---|---|---|
| `p11:H.1` | reduction equations, empty theory | S4 (open at our instance) |
| `p11:H.2` | the model rule in the program logic | `ewp_handle`, `p11_core` (σ=[]) |
| `p11:H.3` | the uniqueness half | `handle_unique` (one signature) |
| `p11:H.4` | denotational initiality via a sibling model | EffModelRel (SIB) |
| `p11:F.1` | unary reductions (`PureJoin`) | S4 |
| `p11:F.2` | unary laws in the world | `I5beta`, `RedLaws`, `AntiFrameW` |
| `p11:F.3` | run-level, closed | `A.UnaryLaws` (stated, beside done) |
| `p11:F.4` | contextual equivalence (binary) | A₂, `Laws` (stated, out of the first pass) |
| `p11:K.1` | β, unary | `I5beta` (every world) |
| `p11:K.2` | β up to fresh internal lifetimes | — |
| `p11:K.3` | η, renaming form (binary) | `CapEta` stated |
| `p11:K.4` | η with a frame holding the continuation | `EtaHold` stated |
| `p11:K.5` | hiding, unary (6.66 at W) | `antiFrameW_core` (σ=[]) |
| `p11:K.6` | hiding, binary | `Hiding` stated |
| `p11:Z.1` | per-class laws plus corpus counts | — |
| `p11:Z.2` | compiler correctness by forward simulation | A₃ `LoweringCorrect` (stated) |
| `p11:Z.3` | laws as source rewrites | — |

**P12 abstraction**

| node | option | today |
|---|---|---|
| `p12:AS0` | E6 `Tunnel` (unary) | in done |
| `p12:AS1` | scope (escape) | `[handle]`'s `n ∉ Σ` |
| `p12:AS2` | resolution, on runs | — |
| `p12:AS3` | tunnelling, binary | stated, open |
| `p12:AS4` | instance parametricity | SIB |
| `p12:AS5` | representation independence | stated, open |
| `p12:N1` | static per-site names, site freshness (SF), recursion through a site rejected | decision 57 (SF not built) |
| `p12:N2` | N1 with lacks constraints | — |
| `p12:N3` | mask, lift, adaptors | — |
| `p12:N4` | tunnelling with handler variables | — |
| `p12:N5` | generative instances (ν) | — |
| `p12:N6` | lexical capabilities as borrows | PAPER |
| `p12:N7` | parametrized or existential handlers | — |
| `p12:N8` | named handlers with rank-2 scope variables | — |
| `p12:PR-a…d` | by construction / binary over Core / binary in SIB / an elaborator check | PR-d (decided, not built) |

**P13 zero-cost lowering**

| node | option | today |
|---|---|---|
| `p13:Z0` | counts and reports | operating |
| `p13:Z1` | per-class laws at the source | `op_tail`, `op_answer` (`withswap` only) |
| `p13:Z2` | whole-pipeline preservation on complete runs | stated (A₃) |
| `p13:Z2⁺` | Z2 with diverging and reacting runs | — |
| `p13:Z3` | validated passes | — |
| `p13:Z4a` | cost parity on a fixed corpus | stated (`refCost` unchecked) |
| `p13:Z4b` | "a handler adds no cost of its own", as a refinement | — |
| `p13:Z5` | erasure by the target's shape | stated (A₃) |
| `p13:C1` | key: the instantiated row's profile | as built (finer) |
| `p13:C1b` | key: a class bound on row variables | `RowCon.cls`, unconsumed |
| `p13:C2` | key: the callback value | — |
| `p13:C3` | key: a class grade on blocks and boxes | — |
| `p13:C4` | the class read off the handler | as built for tail clauses |
| `p13:C5` | fallback: (a) worst class, (b) two versions plus a run-time bit, (c) tag dispatch | (c) for closures |
| `p13:P0` | no lend spans a suspension | as built (typing) |
| `p13:P1` | spanned places stay heap cells; the state moves freely | the representation as built |
| `p13:P2` | spanned places inline in a pinned state | — |
| `p13:P3` | inline places, relocated on move | excluded in practice |
| `p13:P4` | stackful, non-moving | excluded as the semantics |

**P14, I1, I4 interaction**

| node | option | today |
|---|---|---|
| `p14:W0` | tier 1 by construction | `wbCore` |
| `p14:W1` | class-restricted embedding (`ConservativeWB`) | trivially at σ=[] |
| `p14:W2` | every-type embedding (`Conservative`) | trivially at σ=[] |
| `p14:W3` | well-bracketing as a type-level bound (`RowCon.cls`) | — |
| `p14:W4` | a context-local or ghost-stack wp | — |
| `p14:W5` | the leak and abort half from linearity and §19 | built |
| `p14:W6` | the re-entry half from exclusivity | — |
| `p14:V1` | second-class κ only | — |
| `p14:V2` | first-class linear κ with two observations | today (`kTy`, `KapRel`) |
| `p14:V3` | boxed κ, a `[gen]` rule | stopped |
| `p14:V4` | an outlives rule at `U C` | — |
| `p14:V5` | κ with a one-shot cell (≡ `p8:8.3`) | excluded |
| `p14:V6` | κ's type closed over internal names (≡ `i2:T3`) | stated |
| `p14:V7` | κ's type records its loan set | — |
| `p14:B1` | the borrow form pinned, with no relation to `hnd` | `i4a_tier1` (restricted) |
| `p14:B2` | one mechanism: an answering handler is a tail-resumptive `[handle]` | `I4Typing`, `I4c` stated |
| `p14:B3` | models and comodels of one signature | signed off (BRIEF §5 item 2); not stated in the targets |
| `p14:B4` | answering is a borrow in the relation (`hnd` opens a lifetime and lends its state) | `handle_is_shift` (PAPER) |
| `p14:B5` | runner architecture | — |
| `p14:B6` | capability transport: (a) rows and evidence, (b) second-class arguments, (c) moded arguments | (a) |
| `p14:B7` | capability mode `Mut`, `Imm`, `!` | `Mut` only |

### 1.2 The edges

Each edge is stated in its menu. The relation is **R** (requires), **X** (excludes), **F** (favours), **≡** (the same option seen from another menu) or **~** (in tension: the menu states a cost, not an exclusion).

**From P2** ([p2](prior-art/p2-effect-safety.md))

| from | rel | to | where |
|---|---|---|---|
| `p2:R1` | X | `p12:N3` (mask, lift) | §0.1, §5.1 R1: "R1 cannot take a mask/lift without changing ∼" |
| `p2:R1` | R | `p12:N1`'s SF, for E6 | §5.1 R1 *Interactions* |
| `p2:R1` | R | effect polymorphism (`rc:O1`'s tail variable), for E1/E2 | §5.1 R1 *Interactions* |
| `p2:R1` | F | `p13:C1`/`C4`: static dispatch | §5.1 R1 *Interactions* |
| `p2:R2` | F | `p13:Z2` (`OneSigPerName` is a P13 obligation) | §5.1 R2 |
| `p2:R3` | F | `p12:AS0` (`PolyUseLacks` is a lacks quantifier) | §5.1 R3 |
| `p2:R3` | X | masking (needs R4) | §5.1 R3 |
| `p2:R4` | R | Yoshioka Def. 7.1 proof; the erasable variant if dispatch erases arguments | §5.1 R4 |
| `p2:R4` | F | `p12:N5` (generative or nested same-site instances) | §5.1 R4 |
| `p2:R5` | R | `p14:V3`/`V4` (OQ-28), to store effectful values | §5.1 R5 |
| `p2:R5` | R | the tier-2 stop change for control operations | §5.1 R5: "Control operations are not lends today … (a) covers answering effects (I4) before control ones" |
| `p2:R5` | F | `p12:AS0` by construction; `p10:L.1` | §5.1 R5 *Buys* |
| `p2:R5`(b) | X | decision 62 | §0.1, §5.1 R5 (see §1.4 item 1) |
| `p2:R6` | R | a modal kernel (the user) | §5.1 R6 |
| `p2:S-e` | R | `p11:H.2` (FL at W) | §5.2: "It reaches W when FL does" |
| `p2:S-f` | ~ | A's minimal formers | §5.2 S-f |
| `p2:S-g` | F | `p13:Z2` | §0.2, §5.2 S-g |
| `p2:S-g` | R | runner answers preserve typing (`Respects`) | §5.2 S-g |

**From P8/P5** ([p8](prior-art/p8-p5-linearity-drop.md))

| from | rel | to | where |
|---|---|---|---|
| `p8:8.1` | ~ | decision 63 (meaningful only at `unr`) | §5.1 8.1 |
| `p8:8.2` | F | `p8:5.5` | §5.1 8.2 |
| `p8:8.2` | R | OQ-50 (a) subject reduction (D21 cost) | §5.1 8.2 |
| `p8:8.3` | X | `p11:H.1` (S4 as stated) | §5.1 8.3; p11 §5.5 |
| `p8:8.3` | R | B1–B5 re-run at the new machine; `BumpSim` with κ cells; an erasure simulation | §5.1 8.3 |
| `p8:8.3` | F | S6 from B2 and B4 | §5.1 8.3 *Buys* |
| `p8:8.4` | R | OQ-8's placement | §5.1 8.4 |
| `p8:8.4` | X | a ghost index beside W (ONEW) | §5.1 8.4 |
| `p8:8.5` | ≡/R | proved through `8.2` or `8.4`; `8.3` needs S4 relaxed | §5.1 8.5 |
| `p8:5.2` | X | control handlers (runners use κ at most once, in tail position) | §5.2 5.2 |
| `p8:5.6` | R | OQ-57 (b) or (c); (a) is a defect under ONEW | §5.2 5.6 |
| `p8:X.3` | X | SPEC §19 (decided) | §5.3 |
| `p8:F.2` | R | dying handlers that forward, or region-bounded finaliser rows | §5.4 F.2 |
| `p8:F.1` | ~ | the async design (threads; OQ-56, 60, 61) | §5.4 F.1 |

**From I2** ([i2](prior-art/i2-capture-resume.md))

| from | rel | to | where |
|---|---|---|---|
| `i2:M0` | ≡ | `p14:W0`, `p13:P0` | §5 M0; p14 §0.4; p13 §6 |
| `i2:M0` | X | `Tier2Programs` | §5 M0 |
| `i2:M1` | R | `p10:L.4a` (OQ-3 (a)) | §5 M1 |
| `i2:M1` | R | D-ORD (`p10:L.5`) | §5 M1 |
| `i2:M1` | R | an OQ-8 decision (the stacked line puts it at the binder clauses) | §5 M1 |
| `i2:M1` | F | `p14:W1` ("P14 is cheapest here") | §5 M1; p14 W1 |
| `i2:M1` | R | `i2:T3` or `i2:T4`, for AT17 with self-references | §5 M1 *Does not buy alone* (see §1.4 item 11) |
| `i2:M2` | R | D-ORD, OQ-44, OQ-57, replacements for 6.50 and 6.27 | §5 M2 |
| `i2:M2` | ~ | `p14:W1`/`W2` (P14 harder) | §5 M2; p14 W2 |
| `i2:M3` | X | (refuted at Core's `Ext`) | §5 M3 |
| `i2:T1` | R | `i2:M1` ∨ `i2:M2` | §5 T1 |
| `i2:T1` | X | a κ stored past the clause (so, the async read) | §5 T1 |
| `i2:T2` | R | `p10:L.2` ∨ `p10:L.3`; ~ colouring (H4) | §5 T2 |
| `i2:T3` | R | `NotVDenNaturalArises` first | §5 T3 |
| `i2:T3` | F | AT17, TwoRun, D-ORD | §5 T3 |
| `i2:T4` | F | `p13:P2` | §5 T4; p13 §6 P2 |
| `i2:T4` | X | migration after placement (threads) | §5 T4 |
| device `FramesW` (single-α form) | ~ | `i2:M1` (needs the `Relend` form) | §6.2 item 1 |

**From P10/P9** ([p10](prior-art/p10-p9-exclusivity-lifetimes.md))

| from | rel | to | where |
|---|---|---|---|
| `p10:X.1` | ≡ | `p10:L.4c`; F OQ-29 (b) | §5.1 X.1 |
| `p10:X.2` | R | `p11:K.5`; `p10:L.4a` ∨ `L.4c`; decision 59's passing shown to be its round trip | §5.1 X.2; p11 §5.5 |
| `p10:X.3` | ≡ | `i2:M2`; R `FreezeBinder`'s location half if κ moves (AT17) | §5.1 X.3 |
| `p10:X.4` | ≡ | `i2:M1`; R `p10:L.4a` | §5.1 X.4 |
| `p10:X.5` | R | an `Adm` beyond `admClosedOp` (arguments) | §5.1 X.5 |
| `p10:X.5` | X | a stored κ, unless `p10:L.2`/`L.3` "carry 'x" | §5.1 X.5 |
| `p10:X.6` | ≡ | `[handle]`'s `!U` clauses; at tier 2 it moves into X.2/X.3 | §5.1 X.6 |
| `p10:X.7` | X | the assurance goal | §5.1 X.7 |
| `p10:L.1` | X | E9 alone (needs L.2/L.3); ~ H4 | §5.2 L.1; p14 V1 |
| `p10:L.2` | ⊕ | `p10:L.3` (either/or); both R: AT07 stays rejected | §5.2 L.2, L.3 |
| `p10:L.3` | R | OQ-58 (the `U` clause at every extension) | §5.2 L.3 |
| `p10:L.4a` | R | a change to `handle_compatC`; D-ORD to tell it from (b) | §5.2 L.4 |
| `rc:O2` | R | `p10:L.4a` ("Under capabilities (a) is forced") | §5.2 L.4 |
| `p10:L.5` | R | `p10:L.4a` and the binder's lifetime half (see §1.4 item 3) | §5.2 L.5 |
| `p10:L.6b` | R | Yoshioka's conditions (`p2:R2`/`R4`), `p10:X.5`, `p10:L.4` | §5.2 L.6; §5.3 |
| `p10:L.6c` | ≡ | a sub-case of `RowSpan`'s `Adm`, no new construct | §5.2 L.6 |
| `p10:L.7` | R | the stop change (conjuncts 37 and 40) | §5.2 L.7 |
| `p10:X.3` ∨ `X.4` | R | `p10:L.4a` (between lenders), then L.5 | §5.3 |
| `p10:X.2` & `X.5` | ≡? | "two directions of one reborrow"; under capabilities possibly one statement | §5.3 |

**From rows vs capabilities** ([rc](prior-art/rows-vs-capabilities.md))

| from | rel | to | where |
|---|---|---|---|
| `rc:O1` | R | an abstraction mechanism beside rows (`p12:N1`–`N4`) | §3.2 |
| `rc:O1` + handler-state borrows | R | `p10:L.4`, which turns it into `rc:O3` | §3.3 |
| `rc:O1` | ~ | tier 2: the spans are invisible to the type | §3.4 |
| `rc:O1` | F | `p13:C1`/`C1b` | §2.3 |
| `rc:O2` | R | `p10:L.3` (stored callbacks), `p10:L.4a`, the tier-2 stop change | §1.2, §5 |
| `rc:O2` | X | `p14:W3` (a bound on parameters), unless `rc:O2-g` | §3.5, §5 |
| `rc:O2` | F | `p13:C2`; loses the class in a lifetime-bounded box (needs `p13:C3`) | §2.3 |
| `rc:O2` | ≡ | `p10:X.1` (handler-state exclusivity as B6), `p12:AS0` by construction | §3.2, §3.3 |
| `rc:O2` | ~ | aliased stateful capabilities (`twoBlocks_refused`) | §3.3 |
| `rc:O3` | R | a row algebra and outlives, both proved; a SIB bridge | §5 |
| `rc:O3` | R | "everything O2 needs at Core": the CBPV form of HandlersAsBorrows; control operations as lends ("exactly tier 2's stop change"); block parameters (FnMut-shaped); "the box/outlives rule at `U C` (T2, OQ-28)"; an aliasing decision; the class grade if O2-g. Then "the row algebra over instances; the bridge from SIB to Core, which does not exist" (see §1.4 item 13) | §3.7, proof-burden table |
| `rc:O2`, `rc:O3` | F | `i2:T3` (lifetimes in the suspension's type) | §3.4 |
| `rc:O4` | R | a modal kernel | §5 |

**From P11/I5** ([p11](prior-art/p11-i5-laws.md) §5.5, and the entries)

| from | rel | to | where |
|---|---|---|---|
| `p11:H.1` | X | `p8:8.3` | §5.5 |
| `p11:H.1` | ~ | equations in signatures (OQ-22 (a)): with them, "correctness becomes undecidable in general … and becomes a proof obligation per handler" | §3 pitfall 9 |
| `p11:H.2` | R | the I2 world; it is required by B1 at W | §5.5 |
| `p11:H.3` | F | `p11:K.3` | §5.5 |
| `p11:K.2` | R | `i2:M1` and `i2:T3` (see §1.4 item 2) | §5.5 |
| `p11:K.2` | ≡ | `p11:K.1` at W with `held`, under `i2:M2`; K.1 under `i2:M0` | §5.3 K.2 |
| `p11:K.5` | ← R | `p10:X.2` | §5.5 |
| `p11:K.4` | F | `p8:5.5` | §5.5 |
| `p11:K.3` | ~ | `p8:X.2` (an uncatchable cancel), unless `p11:K.4` | §5.5 |
| `p11:K.6` | F | P12 (AS5) | §5.5 |
| `p11:Z.2` | F | `p2:S-g`, `i2:T4`; R the tail hygiene that `p2:R1`/`R3` give | §5.5 |
| `p11:Z.1` | ~ | `rc:O2` (class lookup easier under O1); `rc:O2-g` restores it | §5.5 |
| `p11:Z.3` | R | `p11:F.4` | §5.5 |
| `p11:F.3` | F | determinism up to renaming (`i2:T3`'s location half) | §5.2 F.3 |

**From P12** ([p12](prior-art/p12-abstraction.md) §5)

| from | rel | to | where |
|---|---|---|---|
| `p12:N1` | R | `p2:R1` ∨ `p2:R3`; ≡ `rc:O1-a`; F `i2:T3` without an instance half | §5 table |
| `p12:N2` | R | `p2:R3`; F `p12:AS0` | §5 table |
| `p12:N3` | R | `p2:R4`; X `p2:R1`'s ∼ | §5 table |
| `p10:L.6b` | R | condition (3), as `p12:N3` does: "L.6 (b)'s masking needs the same condition (3)" | §5, mechanisms table, N3 row |
| `p12:N4` | ≈ | `rc:O3`; F `p10:L.4` | §5 table |
| `p12:N5` | R | `i2:T3` with an instance half, `p10:L.5`; a machine step (changes S0/S4); F `p2:R4`/`R6` | §5 table |
| `p12:N6` | ≡ | `p2:R5`, `rc:O2`; R `p10:L.1`, `p10:L.4`; gives `p10:X.1` | §5 table |
| `p12:N7` | ⟂ | everything (orthogonal) | §5 table |
| `p12:N8` | ≈ | `rc:O3`; R `i2:T3` instance half; F `p10:L.4a`, `L.6b` | §5 table |
| `p12:AS1` | ≡ | B7 under `p12:N6`; R T2's confinement former under `p12:N5` | §5 AS1 |
| `p12:AS2` | F | P13 (static dispatch) | §5 AS2 |
| `p12:AS3`, `AS5` | R | `p12:PR-b` (a binary BoLo relation) | §5 *Proof routes* |
| `p12:AS4` | R | `p12:N5` | §5 AS4 |

**From P13** ([p13](prior-art/p13-zero-cost.md) §0 table, §6)

| from | rel | to | where |
|---|---|---|---|
| `p13:Z1` | F | p11's laws (A₂); R "binary laws optional" lifted for it | §0 |
| `p13:Z2` | R | `p2:S-g` (io); `p8:5.1` observable (the cancel entry) | §0, §6 Z2 |
| `p13:Z2⁺` | ← R | E10 (if A₃ covers it) | §0 |
| `p13:Z4a` | F | `p13:P2` | §0 |
| `p13:Z5` | R | Z4 (to exclude a heap runtime); X `p13:P4` as the semantics | §0, §6 Z5 |
| `p13:C1` | ≡ | `rc:O1`/`O4`; with `p2:R1`, static routing | §0, §6 |
| `p13:C1b` | ≡ | `rc:O1-ε` | §0 |
| `p13:C2` | ≡ | `rc:O2`/`O3-surface`; F `p10:L.1` | §0 |
| `p13:C3` | ≡ | `rc:O2-g`, `rc:O3` | §0 |
| `p13:C4` | R | a static handler (`p2:R1` or `rc:O2`'s lexical binding); combines with C1–C3 | §0, §6 C4 |
| `p13:C5`(b) | X | "no effect information at run time" | §0 |
| `p13:P1` | R | `i2:M1` ∨ `i2:M2`; `i2:T2` or `p10:L.2`/`L.3` for a stored κ | §6 P1 (see §1.4 item 11) |
| `p13:P2` | R | `i2:T4`; F `p10:L.1`, `L.2` | §6 P2 |
| `p13:P3`, `P4` | X | L3 (in practice), L2 (as the semantics) | §6 |
| `p8:8.3` | ~ | Z4 ("a store per resume unless ghost"); `p8:8.4` F | §6 interactions |
| `p10:L.5` | ← R | erasure (the dynamic guard is excluded) | §6 interactions |
| `i2:M1` | ≡ | `i2:M2` in the lowering ("identical code") | §5 item 1, §6 |

**From P14, I1, I4** ([p14](prior-art/p14-i1-i4-interaction.md) §0.4, copied)

| from | requires | excludes | favours |
|---|---|---|---|
| `p14:W0` | `i2:M0` | `i2:M1`/`M2`/`M3` as tier 2; `Tier2Programs` | `p10:L.1`, `p8:F.1` |
| `p14:W1` | `Mono` at W; OQ-8's clause set checked | — | `i2:M1` over `M2`; `p2:R1`/`R3` with a class bound; `p14:B1`/`B2` |
| `p14:W2` | W at every type; `FramesW` at resuming types | — | `i2:M1` + `T3`; hardest under `i2:M2` |
| `p14:W3` | `rc:O1-ε` or `rc:O2-g` | — | `p2:R3`, `p10:L.6a` |
| `p14:W4` | a definition over `ewpW` | a parallel wp | `i2:M1` |
| `p14:W5` | `p8:8.5` or `8.4`; `p8:5.1`; `p8:X.1` ∩ `X.2` | `p8:X.3` | `p8:F.1` |
| `p14:W6` | `p10:X.6`; B6; no shared interior mutability | unrestricted interior mutability | `p10:X.4` |
| `p14:V1` | `p10:L.1`; `i2:T2`'s second-class half | E9 and `I1Prog` in done | `rc:O2-pure` |
| `p14:V2` | `contShare`/`KapRel` (8.4's wand) | `p14:V5` | `p8:8.5`; `i2:T2`'s first-class half |
| `p14:V3` | `p10:L.2`; T14.4 | `p14:V4` as primary | `i2:M1` |
| `p14:V4` | `p10:L.3`; OQ-58 | `p14:V3` as primary | O1 and O2 alike; HandlersAsBorrows precondition 2 |
| `p14:V5` | `p8:8.3`; S4 relaxed | `p14:V2`'s machine | `p14:W5` for free |
| `p14:V6` | `i2:T3`; `i2:M1` | — | `i2:T4` if the location half is not built |
| `p14:V7` | `p14:V3` or `V4` with a loan-set bound | — | threads; `p10:X.3` |
| `p14:B1` | `p10:X.1`; `p10:L.4c` | — | `p2:R5` as a route for answering operations; P13 (call) |
| `p14:B2` | `p14:B1`; `capPass`'s spine; S4's deep handler | — | `p14:W1`; P13 |
| `p14:B3` | one `Sig`; P11's initiality | OQ-1 (c) | `p14:B5` |
| `p14:B4` | `p10:L.4a` or `L.4c` at Core; 6.65 at answering tables | — | `p2:R5` (S-d); `p10:X.1` at `hnd` |
| `p14:B5` | `p14:B3` | — | `p8:5.2`; P13 |
| `p14:B6`(a) / (b) | `rc:O1` / `rc:O2` and `p10:L.1` | — | `p2:R1`–`R4` / `p2:R5` |
| `p14:B7` `Imm`/`!` | 6.64 for `Imm` | — | System C's aliasing |

The P14 menu also records three couplings (§0.4):
1. E9 forces a first-class κ.
2. Our well-bracketing condition is lend-bracketing, not control-bracketing.
3. Answering operations are inside the well-bracketed class by construction, because they are `Mut` arguments, not row layers.

### 1.3 What the edges force [synthesis]

- **Any tier 2.** The chain is: `Tier2Programs` ⇒ not `i2:M0` ⇒ `i2:M1` or `i2:M2` (`i2:M3` is refuted). Both need:
  - `p10:L.4a` for the case of a handler between two lenders (p10 §5.3);
  - D-ORD, which must also be static, because erasure excludes the dynamic guard (p13 §6).
- **Capabilities as values** (`rc:O2`). They need:
  - `p10:L.4a`, which is forced;
  - `p10:L.3`, or boxes, for stored callbacks. Three edges say so: rc §5; P2's R5 ("storing an effectful value needs a box with a lifetime bound"); and `p12:N6` R `p10:L.1`, with `p10:L.1` X E9 alone;
  - control operations as lends that may span a stop: "the tier-2 stop change" (rc §5). Under `i2:M1` such a lend spans a stop by being ended at it and re-lent at resume, with conjuncts 37 and 40 unchanged (§1.4 item 12).

  A's (E) programs are label-based A-terms (RESTRUCTURE §1.6), so a capability kernel meets A through an elaborating instance (§2.3).
- **Rows of lends** (`rc:O3`). They need a row algebra and outlives, both proved, and a SIB bridge (rc §5). rc §3.7 adds everything capabilities need at Core, and the outlives rule at `U C` (OQ-28) is among those needs. By this chapter's reading, where `rc:O2` boxes a stored callback, `rc:O3` binds the extent in the callback's type instead. A callback written before its handler exists, or passed into a function that installs the handler itself, cannot name the extent (D2.c9). §1.4 item 13 records the disagreement.
- **Handler state without extents in types.** An answering site may lend its state (`p14:B4`) under rows of labels, provided no answer is borrowed from that state. rc §3.3's edge concerns answers borrowed at `'h`: "answers are borrows at it. At that point the row element is effectively a lend, which is O3." With answers closed in lifetimes (`p10:L.6a`) no type names `'h`, so the row stays `rc:O1` [synthesis]. That is D1+B4 (§5.2).
- **Handler state across a stop.** `p10:X.2` ⇒ `p11:K.5` (`AntiFrameW` at resuming tables) ⇒ a W in which handler-state lends span stops. X.2 also owes that decision 59's state passing is its round trip, "not a second mechanism" (p10 §5.1 X.2).
- **The async read in its borrow form.**
  - `asyncRead` ⇒ `p10:L.6b` ⇒ `p10:X.5` for arguments, and Yoshioka's conditions for the masking.
  - The masking needs condition (3). P12 states it as an edge: "L.6 (b)'s masking needs the same condition (3)" (p12 §5, N3 row). R1 "cannot take a mask/lift without changing ∼" (p2 §5.1 R1), and R3's masking "still needs R4" (p2 §5.1 R3).
  - With a lifetime as the operation's argument, dispatch by name also meets condition (4): one name, two lifetime instantiations, which is "Def. 7.6's shape, with lifetimes as the type arguments" (p2 §4). Only `EA_EScpR` meets (1)–(4) (Yoshioka §7.3).
  - So the borrow form needs `p2:R4` in its erasable variant.
  - A stored κ then needs `p10:X.5` with `p10:L.2`/`L.3` "carrying 'x".
  - The view in transit leaves `[α]`, which ghost end's admissibility excludes. OQ-56's text: "A stop that hands the lent view to an outside handler moves it out of `[α]`. GhostEnd's admissibility condition states the same thing." So that lend must be carried: `i2:M2`, for lends in transit.
- **S6 at our instance.** S6 is stated as `p8:8.5`. Its proof is `p8:8.2` (subject reduction, D21 cost) or `p8:8.4` (the coupling is open). `p8:8.3` is excluded by `p11:H.1` unless the user relaxes S4 (AGREE Q9).
- **The lowering's class carrier.**
  - `p13:C1`/`C1b` under `rc:O1`;
  - `p13:C2` (plus C3 for stored callbacks) under `rc:O2`;
  - `p13:C3` under `rc:O3`.

  Under every option the carrier is one annotation that no lowering statement consumes today: `RowCon.cls`, a grade, or an element bound.
- **Abstraction.** `p12:N1` ⇒ `p2:R1`/`R3` and SF (decided, not built). `p12:N3` ⇒ `p2:R4`, which excludes `p2:R1`. `p12:N5` ⇒ `i2:T3` with an instance half, which `FreezeBinder` lacks.
- **Conservativity.** `p14:W1` is cheapest under `i2:M1` and hardest (as W2) under `i2:M2`.

### 1.4 Inconsistencies between the menus

1. **Decision 62 as a reason.**
   - P2's R5 (b) "conflicts with decision 62" (p2 §0.1, §5.1 R5). The rows-vs-capabilities menu (§0) records the user's 2026-10-06 reading: decision 62 is "an implementation choice to reach a goal", and the P10/P9 menu repeats it.
   - So P2's stated reason is superseded. What remains for capabilities as a *replacement* is a cost, not an exclusion: an elaborating instance for A's label-based terms, and the storage edges (§2.3). That A's terms are label-based is a reading of RESTRUCTURE §1.6, not a decision.
2. **K.2's requirements.**
   - P11 says K.2 "requires I2 M1 + T3" (p11 §5.3, §5.5).
   - I2 says M1's re-lend is proved without naturality, and that T3 only explains ghost end as instantiation (i2 §5 T3: "GhostEnd step 4 shows it never needs naturality at a Mut cell").
   - GhostEnd's README step 2 proves `ewpTS_M_frameR` by 6.65's printed proof once per resumption.
   - So K.2 in form F.2 (the `Relend` form) needs M1 only. K.2 stated as a binder law (`FreezeBinderLife`) needs T3.
3. **L.5's requirements.** P10 lists "the freeze binder's lifetime half" as L.5's cost (p10 §5.2 L.5). GhostEnd proves `relend_respects_nesting` with no binder. This is the same split as item 2.
4. **Z4b under P1 (inside P13).**
   - P13's table row P1 and §5 item 3 say that genSelf and AT17 under P1 "fail Z4a and Z4b".
   - P13's §6 Z4b says: "Under P1, a spanned place's cell is charged at its `alloc`, so Z4b holds where Z4a-against-Rust fails."
   - By Z4b's definition (a source cost that charges `alloc`), §6 is right. "Fails" holds only against a pinned Rust reference, which is Z4a.
5. **M0 and OQ-28.** I2's M0 says "OQ-28 is still needed for a stored κ that holds no lend" (i2 §5 M0). But a κ that holds no lend is stored at tier 1 with no outlives rule (E9, `storeCancel`; p14 V2). OQ-28 matters only for a `U C` value that must cross a borrow scope or enter a lifetime box. The sentence most likely means "no *internal* lend".
6. **`held` and 6.65 lends.**
   - I2's M2 says that `held` records the entries: 6.64 frames, 6.65 lends, 6.66 anti-frames and 6.150 records (i2 §5 M2).
   - `SemWorld.held`'s docstring says that a 6.65 lend adds no 6.64 frame or record, so `held` does not see it. A world that carries one open accounts for it through `Upd` and the index (p10 §2.1, §6).
   - P10's `Exclusive` therefore sees only 6.64 frames in `held` under M2.
7. **B2 and W1's guard (inside P14).**
   - Coupling 2 and W1 count answering operations as well-bracketed because they are `Mut` arguments, so `AbortRows` admits them.
   - P14 B2, and `rc:O1` with answering operations in rows, put them in rows as tail-resumptive layers. `AbortRows` then excludes them (p14 §6 observation 2).
   - So B2 with answering operations in rows needs an `answering` class in W1's guard. D2.c11 carries it.
8. **P14's statement and P14's menu.**
   - The property chapter states P14 as "Proofs that assume well-bracketed control" ([conservativity](properties/conservativity.md)).
   - The menu's coupling 1 and pitfall 1 show that E9, which is in done, already breaks control-bracketing at tier 1, and that our condition is lend-bracketing.
   - Read as control-bracketing, done contradicts itself. The chapter needs the menu's reading.
9. **The device's `FramesW`.**
   - RESTRUCTURE §3.6 picks no OQ-9 option for done, and the device may fix options. But the device's `MutFrameW`/`ImmFrameW` quantify the lend once, at the callback's start: "the lend quantified at the callback's start" (`Targets/I/Interface.lean`). That is the shape of `i2:M2`/`M3` (i2 §6.2 item 1).
   - Under M1 the device would need restating in the `Relend` form.
10. **`reconB`'s shape (RESTRUCTURE §3.4 against its own claim).** The term is:

    `r₁ ← borrow imm cfg (λb. resumer wait (retry (…)))`; `r₂ ← borrow imm cfg (λb. timeout (…))`

    It installs both handlers inside the borrow's callback, so the callback performs nothing outside it. By reading, its row is empty and today's pure `withbor1` types it with no spanning rule. Yet RESTRUCTURE §3.4 says that "Tier 1 rejects each of the six", and §6.1 lists `not_tier2_tier1` for `reconB`. The operator's shape, a scheduler at `main` outside the borrow, needs the scheduler outside. §11 uses that form and calls it `reconB′`. Not checked in Lean.
11. **AT17 and placement (I2 and P10 against P13)** [synthesis, unchecked].
    - I2's M1 says that AT17's move of κ, "if the frozen frame holds self-references", needs T3's location half or T4 (i2 §5 M1; §0 table; combinations table; pitfall 1). P10's X.3 says the same for carry: "`FreezeBinder`'s location half if κ moves (AT17)" (p10 §5.1 X.3).
    - P13 says that under P1 "T3's location half is trivial at run time" (p13 §0 P1, §5 item 2). That sentence is about the lowering, not about the proof obligation in the relation.
    - **From the relation:**
      - In Core's machine every place is a heap cell made by `alloc`, and κ (`kappa n H K`) is a value whose frames hold locations.
      - Storing κ in a cell and loading it back copies that value, so no location changes. A self-reference, meaning a lend of a cell allocated inside the frozen segment, stays at its cell.
      - Under M1 the lend is ended at the stop and κ's share holds the owner. So AT17 is `storeCancel`'s mechanism (κ stored in a cell and taken back, checked at tier 1), followed by Law 2's re-lend at the same location.
      - The relation never needs a location symmetry for it. The same reading holds under M2 (D3).
    - **Where T3 and T4 are needed.** T3's location half and T4 are needed when a design places spanned places inline in the frozen state (`p13:P2`, `P3`). Every design here leaves that to the variant §7.3.
    - **P13's stored-κ requirement.** P13 also lists "T2 or L.2/L.3 for stored κ" as a requirement of P1 (p13 §6). Under D1 and D1+B4, and under D2a if §5.3's reading holds (item 13), a stored κ needs no bound for soundness: no `U C` value has an outlives judgement (`thunk_not_outlives`), so κ never leaves a borrow scope. That meets the requirement on the conservative side of OQ-28, at the program cost OQ-28 names (§9).
    - **No proof exists.** No AT17 proof at W exists; `at17_eval` is an interpreter run. If the reading fails, D1 and D3 need T3's location half or T4, and T4 forbids moving κ after placement, which bears on threads (i2 §5 T4).
12. **"The tier-2 stop change" (P2 and rows-vs-capabilities against I2).**
    - P2's R5 and the rc menu's O2 require "the tier-2 stop change" for control operations (p2 §5.1 R5; rc §5: "control operations must become lends, which is the tier-2 stop change itself").
    - I2's M1 changes no stop conjunct: "the stop condition is unchanged, so no kernel definition change is needed for the stop" (i2 §5 M1).
    - By reading, the requirement is that a lend may span a stop. M1 meets it with conjuncts 37 and 40 unchanged. A lend inside the frozen segment ends at the stop and is re-lent at resume, and a catching control handler's extent lends nothing. So D1, D1+B4 and D2 meet the edge through M1, and D3 meets it through M2's relativised stop.
13. **What rows of lends require (rows vs capabilities §3.7 against its §5, and D2a)** [synthesis, unchecked].
    - The rc menu's §5 lists O3's costs as "both a row algebra and outlives must be proved" and "the SIB proofs have no bridge to Core". Its §3.7 proof-burden table says more: O3 needs "everything O2 needs at Core, plus the row algebra over instances; the bridge from SIB to Core, which does not exist".
    - O2's Core needs in that table are: "the CBPV form of HandlersAsBorrows"; "control operations as lends (exactly tier 2's stop change, OQ-8/9)"; "block parameters (FnMut-shaped)"; "the box/outlives rule at `U C` (T2, OQ-28)"; "aliasing (accept the refusal, or state behind control)"; "the class grade if O2-g".
    - **How D2a meets each, by reading:**
      - the CBPV form of HandlersAsBorrows: D2.c4 with D1.h2, at Core (`I4Typing` and a run correspondence);
      - control operations as lends: M1, with conjuncts 37 and 40 unchanged (item 12);
      - block parameters: not needed while operations go by label (§5.6, risks);
      - aliasing: D2a accepts the refusal (`twoBlocks_refused`; §5.6, risks);
      - the class grade: under O3 the carrier is the entry's bound (`p13:C3`), not a grade;
      - the row algebra over instances: D2.c1–c3;
      - the SIB bridge: it is the route by which EffModelRel's proofs (`safety`, its laws) would be reused. D2a states and proves its results at Core (D2.c1–c12, D1.h1–h4) and reuses nothing from SIB, so it does not need the bridge. It pays for S1 at extents at Core instead (D2.c3).
    - **The outlives rule at `U C` is where they disagree.** §5.3's "OQ-28 under D2a" argues that D2a needs no more of OQ-28 than D1, because O3 binds a stored callback's extent in its type (D2.c9) where O2 boxes it. That argument is this chapter's reading, and it is unchecked. If it fails, D2a takes OQ-28's rule (T2, #173), as D2b does (D2.c12).
    - D1 and D1+B4 are not affected: they take `rc:O1`, and no type in them names an extent.
14. **B1's L.4 (c) and D1's L.4 (a) (P14 against P10).**
    - `p14:B1` requires `p10:L.4` (c), that answering sites open a lifetime (p14 §0.4). D1 and D1+B4 take `p10:L.4` (a), that every site opens one.
    - (a) is (c) widened to every site, so it meets B1's requirement [synthesis]. Under D1 an answering handler is §18's `withbor` (2), which opens its own lifetime as any borrow constant does; that is (c) as PAPER has it (`handle_is_shift`). `[handle]`'s extent (D1.i1) covers the control sites. Under D1+B4 an answering site is a `[handle]`, and opens its extent under (a).

None of these changes which designs are coherent. Items 2, 3, 4 and 11 lower a cost; item 11 is unchecked. Item 10 changes a probe program. Items 12 and 14 record how designs meet an edge. Item 13 may add OQ-28's rule to D2a's delta, depending on a reading that is unchecked.

---

## 2. From the map to designs

### 2.1 What the decided constraints and the signed-off structure fix

**Decided constraints.**

| decided constraint (at the user's strength) | what it fixes on the map |
|---|---|
| Nothing breaks the borrow calculus | `B.Guarantees` at W in every design; `p11:H.2` is required (B1 at W) |
| The core is linear; discard is an explicit cancel | `p14:V2` (first-class linear κ); `p8:8.5` as the statement; no forget (AT13); `p14:W5` |
| Cancellation is what SPEC §19 builds | `p8:X.1` ∩ `p8:X.2` (X.3 excluded); `p8:5.1` (S5) |
| Handlers are deep | `p11:K.1`; S4's deep resume |
| Multi-shot is ignored | `J₂` is unr-free; `p8:8.1` is moot |
| Errors are `raise` | the abortive class; compatible with `p8:F.1` |
| Divergence is codata | `Loop`; `p13:Z2⁺` if A₃ is to cover E10 |
| Handling is erased, with no colouring | `p13:Z5`; X `p13:P4`, `p13:C5`(b), `p10:X.7`, dynamic resumption guards; effect polymorphism is required (E1, E2, E6, E10) |
| No step-indexing | `audit_W`; OQ-60 (a) is out |
| Threads are kept open | prefer `p13:P1` (κ may migrate) to `i2:T4`; keep `p14:V7` available |
| Row variables in the kernel (decision 62) | not binding: "It's not a core goal it was an implementation choice to reach a goal" (2026-10-06). Effect polymorphism is binding |
| Effects are core (K1): "we aren't going to be able to implement them correctly with sugar, and we need to build them on a mathematical foundation backed by the literature" | `hnd` is the kernel's handler. An answering handler that exists only as §18's encoding over borrow constants is A's handler only through D1.h2, or natively under D1+B4 |
| Laws first (P2): "find the laws that we have to implement instead of trying to wing it" | the laws are required, not optional: D1.h1 (laws of handling) and D1.h4 (theories, with OQ-22 below), in every design. What stays open on axis 9 is the laws' form, not whether they are in |
| The actual calculus (K8): "building the actual effects calculus not an approximation of it"; one real mechanism (K15: "declared operations, handlers as folds of the free model, and a proved typing discipline") | the language's handlers, answering ones included, are A's handlers (D1.h2, or D1+B4), and "handlers as models" is not vacuous (D1.h3 with D1.h4). Done as RESTRUCTURE states it falls short of this (§4.3), so D1.h1–h4 are required in every design |
| Spec first (P1, K12) | every kernel change a design makes (D1.i1's extent, D1.a8's checked `ClosedLife`, D3.k1's stop) is specified, with its open questions boxed, before it is built. The probe (§11) is an experiment, not kernel work |
| Handler state is passed to each clause and at each resume (decision 59) | control-handler state is passed, not lent. Under OQ-29, X.2 must show that this passing is its round trip (D2.c10) |
| Allocation is an effect (A1, 04-decisions §5): "`box` is the operation, the heap is the outermost linear State handler, and arenas are nested handlers" | the host handler's `IsModel` and an arena's frame across `new` are unproved (OQ-68). An arena that hands out borrows into its state is OQ-29's family (§5.1, §9) |

**OQ-22, constrained by Laws first.** OQ-22 asks whether signatures carry optional equations, with handler correctness an obligation (a), or free theories only (b). 05a classes it "CONSTRAINED, toward (a) as the form". Laws first asks for "theory-specific laws (exceptions, state and linearly used state, nondeterminism, generators)", and "that needs equations to be writable, which excludes (b)". Binary proofs of those laws stay optional (U22). The draft's default, "the form; no kernel theory carries equations until needed", meets both. Every design takes (a) as the form; that is D1.h4.

**The structure the user signed off** (BRIEF §5, 2026-10-03). It is the audit's structure with the critic's corrections, and the brief calls it the target. The one open part is marked.

| item (BRIEF §5) | strength | where it lands |
|---|---|---|
| 1. One signature object: rows are sums, and `opTable` is the interpretation | signed off | A's S1 `RowSig` at our instance (the bridge `rowAlgebra_ourInst`). The kernel's rows stay first-match lists of layers keyed by `(n, i)` (BRIEF §3 item 6), with `opTable` interpreting them |
| 2. Models and comodels: handlers are models and capabilities are comodels of one signature; `withswap` is the co-operation carrier; one `IsModel` lemma, with `ewp_handle` as initiality | signed off | `p14:B3`. Not stated in the targets (p14 §6 table); `I4a`'s `ImplTyped` is a dead hypothesis (AGREE §5). D1.h3, which has content only with D1.h4's equations |
| 3. Handler laws over the kernel relation | signed off | S4's reductions, in done; P11 and I5 at W, in the device beside done; `A.UnaryLaws`, beside done until D1.h1 |
| 4. One Kripke world W = (ρ, ls, σ). The stop condition is relativised. `vC`/`cC` are the σ=[] instance, and the five `vRL*` families are retired into it | signed off | `SemWorld`'s `held`, `Stop` and `Upd` fields (RESTRUCTURE §3.1); OQ-44, OQ-57, OQ-58 |
| 4, continued. Where the future-world quantifier goes (the binder clauses, or `U`/`contShare`/`KapRel`) | OPEN: "A Lean statement settles it, not prose" | OQ-8 (§4.2) |
| 5. One borrow per printed constant over any well-formed row; the frame lemmas lifted once; the `*U` twins become abbreviations | signed off | the spanning rules at `RowSpan Adm` (`SpanRule1` …); the device's `SpanBorrows` |
| The critic's corrections: build on HandlersAsBorrows; probe the unknowns first; a change to the stop condition is a kernel definition change and needs a SPEC entry; state laws at W, or show they survive the re-index | with the structure | D3.k1 carries the SPEC entry for the stop; D1 changes no stop conjunct, and its rule changes (D1.i1, D1.a8) carry their own |

**Defaults and open questions every design assumes.** These are not decisions (BRIEF §6, "Defaults and deferrals (not prohibitions)"). Each design takes the as-built side, and none excludes the other.

| item | strength (source) | what every design assumes |
|---|---|---|
| binary laws | default: "optional and don't get pursued unless they become necessary for safety" (2026-10-02) | `p11:F.4`, `K.3`, `K.6`, `Z.3` and `p12:AS3`–`AS5`, `PR-b` stay out of the first pass |
| higher-order operations | "out of scope" in decision 57 (2026-10-01), read as not now (BRIEF §6) | operations take values only |
| rank n | OQ-13's question (RESTRUCTURE §7 Q2) | done needs rank 1 |
| effects in finalisers (`p8:F.2`) | OQ-7 (a), open | `p8:F.1`, as built |
| generative instances | static per-site names as built (decision 57; SPEC §19); generative names a named follow-up (#173) | recursion through a site rejected |
| runners | not user-facing; BoLo-as-runner "not yet decided" | `p14:B5` as a proof architecture only |

### 2.2 The axes that remain

| axis | options left | menus |
|---|---|---|
| 1. representation and polymorphism | `rc:O1` (+`p2:R3` lacks, +`p2:R2` guards, +`O1-ε`); `rc:O1-c` (`p2:R4` erasable), which L.6b's masking needs; `rc:O3` (rows of lifetime-indexed static names); `rc:O2` (+`O2-g`) through an elaborating instance | p2, rc |
| 2. answering and control | `p14:B1`; `B2` (`I4Typing` with a run correspondence); `B4` (one install mechanism), under rows of labels with `B6`(a) or with extents in types; `B3` (models and comodels, signed off) | p14 |
| 3. handler extent | `p10:L.4a` (forced by any tier 2); `L.4c` (tier 1 only) | p10, i2 |
| 4. lends across a stop | `i2:M0`; `i2:M1`; `i2:M2` | i2, p10 |
| 5. transit (what operation types may mention) | `p10:L.6a` (R-CLOSEDOP); `L.6c`; `L.6b` with `p10:X.5` | p10 |
| 6. a stored κ's bound | none (OQ-28 open); `p14:V3`; `V4`; `V7` | p14, p10 |
| 7. placement | `p13:P1`; `p13:P2` with `i2:T4` | p13, i2 |
| 8. S6's proof route | `p8:8.4`; `8.2`; `8.3` (the user's Q9) | p8 |
| 9. laws in done | not whether, but in what form. The hard test and Laws first require S4 plus non-vacuous laws: the laws of handling (`A.UnaryLaws`, F.3, or an equivalent) and theories with a model obligation per handler (D1.h4). The form is the user's: axes H, F and K | p11 |
| 10. lowering theorem | `p13:Z0`; `Z2` with `Z4b` (OQ-23, the user's) | p13, p11 |
| 11. abstraction | `p12:AS0` + `AS1` (+`AS2`) | p12 |

Axes 7 to 11 do not depend on the design: each design can take any of their options. There are two notes:
- if §1.4 item 11's reading fails, AT17 makes axis 7 matter (T3 or T4);
- under D3's scoped rows `TailLaw`'s hygiene premise changes (axis 9, §6.3).

The designs differ on axes 1 to 6.

### 2.3 Excluded combinations, and one that is only costed

- **A capability kernel is not excluded; it is costed** (`rc:O2`; `p2:R5`(b); `p12:N6` alone). A's programs are A-terms over labels (RESTRUCTURE §1.6). That is a reading of how the targets are written, not a decision. A capability kernel meets them through an elaborating instance, and the menus' edges price it [synthesis]:
  - **E2c, E2d and E10** (`retryP`, `sumGen`, `retryR`, `timeoutR`): the higher-order function installs the handler of its callback's label inside itself. System Ξ types exactly this shape. Under its rule Def "programmers can control which effects are handled at the call-site (i.e., ε′)" (rc §1.2), so the callback takes the capability as a parameter. The cost is the elaboration and its typing lemma.
  - **E1′, E2b and E9**: a callback or κ is returned or stored and used later. Second-class κ alone fails E9 (`p14:V1`), so this needs System C's boxes, or `p10:L.3` with a lifetime bound (`rc:O2-lt`). That is OQ-28 and T2 (#173), a cost, not an exclusion.
  - **E2b, further** (unchecked).
    - `asyncCb lw` is written outside the `wait` handler that the composed closure is later called under. Under capability passing, the stored closure's code takes `lw`'s capability as a parameter, and `compose`'s one typing must serve it and the pure callback alike.
    - Met says effect variables "are only necessary for use-cases such as higher-order effects in which a computation needs to be stored for use in an effect context different from the ambient one" (rc §1.4).
    - In a capability kernel that is a quantifier over what a stored callback asks of its later context: a row on stored callbacks. That is the rc menu's O3, "contextual polymorphism for called-only callbacks with rows only on stored ones" (rc §0.1).
  - **The lowering's class.** Under O2 the class is in no type, so the un-specialised fallback is the worst class unless a grade is added (`rc:O2-g`, `p13:C3`).

  Effekt's route, which elaborates implicit capabilities into System Ξ with explicit capability parameters, is an O2 kernel (`rc:O2-pure`; p14 V1). D2b (§5.7) is this variant, with its delta. D2a keeps labels in the kernel with extents attached (`rc:O3`). §5.7 states why D2a ranks ahead on cost.
- **A modal kernel** (`rc:O4`, `p2:R6`).
  - It is a different kernel.
  - E2b still needs effect variables in Met: they are "only necessary for … a computation [that] needs to be stored for use in an effect context different from the ambient one" (rc §1.4).
  - The borrow interaction is unaddressed in the literature, and no target is gained.
  - It stays available as a *proof architecture* for A (Met(X)'s encodings), not as a design.
- **Second-class κ only** (`p14:V1`). It fails E9 and `I1Prog` (p14 §5.2).
- **The one-shot cell as the default** (`p8:8.3`, `p14:V5`). It is excluded by S4 as stated (`p11:H.1`). It is kept as a variant that composes with every design (§7.1); the user's call is AGREE Q9.
- **Refold at the same lifetime** (`i2:M3`). Refuted at Core's `Ext` (`refoldKripke_false`, at a list that arises).
- **Stackful semantics, run-time class tests, dynamic enforcement, dynamic resumption guards** (`p13:P4`, `p13:C5`(b), `p10:X.7`). Excluded by erasure.
- **Binary-first designs** (`p11:F.4` with `Z.3`; `p12:PR-b`). Optional unless safety needs them, and nothing in safety does (p12 §0.4).
- **The runner architecture** (`p14:B5`). It covers the answering class only (p14 pitfall 10: runners exclude control). It is a proof architecture for that class, compatible with every design, not a design.

### 2.4 The designs

| axis | D0 (stage) | D1 rows + ghost end | D1+B4 one install mechanism | D2a rows of lends | D2b capabilities as values | D3 rows + carried lends |
|---|---|---|---|---|---|---|
| A's object | today's: `orowRF`, operation types closed in lifetimes | as D0 | as D0 | extents in row entries and in callback types | capability sets, read through an elaborating instance | lifetime-quantified operations; scoped rows |
| 1. representation | `rc:O1-a`, `p2:R1`→`R3`, `R2` guards, row `∀` (`J₁`) | as D0 | as D0; answering operations become row layers (`p14:B6`(a)) | `rc:O3` / `O3-surface`: row entries carry the site's extent | `rc:O2-lt` with `O2-g`; labels elaborated away | `rc:O1-c`: `p2:R4` erasable (`EA_EScpR`), row `∀` |
| 2. answering and control | `p14:B1` | `p14:B1`; for the hard test `B2` and `B3` (D1.h2, h3) | `p14:B4` + `B2` + `B3`: one install mechanism; §18 emits `hnd` (D2.c4) | `p14:B4` + `B2` + `B3`: one install mechanism | as D2a | as D1 |
| 3. handler extent | `p10:L.4c` (PAPER only) | `p10:L.4a`, extent only | `p10:L.4a`; an answering site also lends its state, in the borrow form | `p10:L.4a`, extent in the row entry | `p10:L.4a` (forced) | `p10:L.4a` |
| 4. lends across a stop | `i2:M0` | `i2:M1` (`p10:X.4`), D-ORD | as D1 | `i2:M1`, D-ORD | `i2:M1`, D-ORD | `i2:M2` (`p10:X.3`), D-ORD |
| 5. transit | `p10:L.6a` | `p10:L.6a` | `p10:L.6a` | `p10:L.6a` + answers at the site's extent (`p10:X.2`, OQ-29 (b)) | as D2a | `p10:L.6b` + `p10:X.5` |
| 6. stored κ | `p14:V2`, OQ-28 open | as D0 | as D0 | as D0 if §5.3's reading holds (D2.c9); otherwise `p14:V4` (§1.4 item 13) | `p14:V2` + `V3` or `V4` (forced) | `p14:V7` or `V4` for κ holding carried lends |
| 7. placement | — | `p13:P1` | `p13:P1` | `p13:P1` | `p13:P1` | `p13:P1` |
| its target | tier 1 (`I.Tier1 J₁`) | done | done, with the language's answering handlers native `hnd` | done, plus OQ-29 for handlers with one live answer | done through the elaboration, plus OQ-29 as D2a | done at a wider `Adm` and row form, plus `asyncRead` |

D0 is listed because it is the first stage of D1 and the floor of the sacrifices (§9). It is not a candidate for done. D1+B4 is D1 plus D2.c4 and D2.c11: the first of the three tiers of capabilities as borrows (§5.1, §5.2). D2a adds the other two tiers. D2a and D2b differ on axes 1 and 6; §5.7 gives D2b as a delta from D2a.

### 2.5 What decides A, and which designs change it [synthesis]

A's statements involve no borrow. Their proofs at our instance do. They are decided by four items:
- the row `∀` (`J₁`), for E1, E2, E6 and E10;
- the bridges from Core's head steps and statements to A's laws (RESTRUCTURE §4.1), for S0–S5;
- for S2 and S3, the B statements those bridges take as hypotheses. `safety_of_sound` takes `Sound ⟦J⟧`, which `soundnessOfFL` gives. `effSafe_of_core` takes `EffSafe ⟦J⟧` and `EffSafeDrive ⟦J⟧`, which come from `effSafeOfFL` and `effSafeDriveOfFL : FL M J → FamEmpty M → AdequateEvery M → EffSafeDrive J` (RESTRUCTURE §4.1). So both rest on B's FL at the design's world. This is `p2:S-e`. At W it is the only route: "at W it is the only route available, since there is no syntactic preservation" (p2 §5.2);
- S6's proof route.

**So the tier-2 choice decides part of A.** At `J₁`, S2 and S3 ride on FL at `coreW`: `fundamentalC` and Law 1's `FLOpen`. At `J₂` they ride on FL at W, which is Law 2 and GFP, tier 2's unknown. That holds in every tier-2 design. It is a dependency of A's proofs on B, not an interaction of the two algebras, since no statement of A reads a resource. The user: "There might be a way to get some effect properties we want by leaning on borrow properties but it's not necessary" (system-a.md). At W the borrow route is the only one built.

**The route that would free S3 from B** is `p2:S-f`: `RowAlgebra ∧ TypingRules ⇒ EffSafe`, proved once over every `EffectSystem`, Yoshioka's Lemma 5.7 abstractly. Its cost (p2 §5.2):
- typing rules for `perform`, `handle`, `[sub]` and `[let]` in A, against A's design of minimal formers;
- an A-level subject reduction or relation, which A lacks. At our instance that is a syntactic typing of configurations, which Core lacks because it types locations semantically (RESTRUCTURE §1.5). It is the same cost as `p8:8.2`'s subject reduction (OQ-50 (a)).

No menu offers a route to S2 at our instance that avoids B. Whether S-f at `J₂` is cheaper than FL at W is not known: its subject reduction would have to type configurations that hold suspended lends.

**Whether A's object itself changes** is decided elsewhere:
- **D0, D1 and D1+B4** keep it as today's: the row form `orowRF`, and `AdmEff`'s `ClosedLife` (operation types closed in lifetimes). D1.a8 makes `ClosedLife` a checked rule. Under D1+B4 the answering effects' operations also appear in rows, as layers (D2.c11); the row form does not change.
- **D2a** changes it in three places. Row entries carry extents, so S1 meets Yoshioka's condition (4) at extents (D2.c3). Callback types bind extents (D2.c9). `AdmEff`'s `ClosedLife` gives way to "own extent only" (D2.c2).
- **D2b** replaces rows in the kernel by capability values, so A's S1 holds at our instance only through the elaboration (D2b.o6).
- **D3** changes it twice. Signatures carry lifetime-quantified operations, so `AdmEff` loses `ClosedLife` for them (D3.k8). The row algebra becomes scoped rows in the erasable variant, for the masking (D3.k12): S1 adds conditions (3) and (4), `∼` changes, and `[handle]`'s `n ∉ Σ` goes.

**Where the two systems meet.** The shape the user asked for is "two algebras with interactions only at cuts".
- D0 has it.
- D1 and D1+B4 have it only if Law 2 is placed at the resume cut: proved as naturality, or with the future-world quantifier at `U`, `contShare` and `KapRel` (OQ-8's options 1 and 2, §4.2).
- The evidence so far points to the binder clauses (option 3). With the guard at `⊸`, #275's borrow-constant row must read its callback at σ·y (02-experiments §1.3), and §11's statement 2 adopts that shape. Naturality is under `mut_not_natural`, and whether its witness arises is not checked. Under option 3 every `⊸` and `∀` clause of the relation carries a resume obligation, away from the cut.
- D2 and D3 each put a lifetime inside the effect algebra, which is interaction away from the cuts whatever OQ-8 decides.

---

## 3. The cuts

### 3.1 Where the two systems meet today [read]

In today's kernel the borrow relation and the typing see effects in four places:

| place | Lean | what crosses |
|---|---|---|
| the protocol table | `opTable` (`Core/EffDefs.lean`) | `en.PA` (the argument, in transit up); `en.PB` (the answer, in transit down); `contShare` (κ's share: resumed at every `Ext`-future, cancelled through `cancelOwed`) |
| the stop | `wpG`'s final conjuncts | `ResU.UpdV ρ π` (`↭`, conjunct 37); `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)` (T1, conjunct 40) |
| capture typing | `effLet` (`Core/Fundamental.lean`) | `S.Weak → Γ₂.Drops`; `S.Unr → Persistent Γ₂` (the capturing condition) |
| borrow callbacks | `Row.Unwind`, the six `*U` constants (`Core/EffBorrow.lean`) | abortive rows only; argument types free of the lend and outliving every lifetime |

`effHandle` adds two hygiene facts: `n ∉ Σ`, and clauses at `!U`. Everything else belongs to one system:
- The effect laws (S4, S5) are machine steps that change no store.
- The row algebra mentions no resource.
- The borrow laws (6.64–6.66, 6.150, 6.60) "never inspect the term the run ends at" (`Core/EffWp.lean` heading; `wpG_reborrow`'s docstring). That is why the `wpG` frame lemmas are textual copies of the `wpTS` ones.

### 3.2 The cut vocabulary

| cut | effect side | borrow side: the question | today's answer |
|---|---|---|---|
| **install** | a handler (a model) is put around a body | does the handler open a lifetime or lend anything? | no (`effHandle` opens none); the answering class at the surface is a `withbor` lend (§18) |
| **stop** (capture) | `perform` caught; κ is the frozen context | what may be open at the stop, and what κ's share holds | nothing internal (T1, `↭`); κ's share is whatever the frames hold |
| **transit** | the operation's argument goes up; the answer comes down | may a borrow travel with them? | no (R-CLOSEDOP at borrow callbacks; `AdmEff.ClosedLife`) |
| **resume** | deep resume reinstalls the handler | at what world and lifetimes does κ continue? | every `Ext`-future of the stop's list (`contShare`, `KapRel`) |
| **cancel** | κ's finalisers fire, innermost first | do κ's lends end, and is its memory released? | the unwinding constants end lends at abortive rows; B4 releases memory |
| **placement** | κ (or a thunk) is stored or moved | may it leave a lender's scope; do addresses move? | no outlives rule at `U C`; cells are heap objects (`p13:P1`) |

### 3.3 Today's interaction away from the cuts

These are the places where today's kernel smells by the user's criterion:
- **The six `*U` twins.** A borrow constant is restated per effect class (BRIEF §2), so the stop cut's law is spread over six constants. Every design replaces them by the printed constants at a row predicate: the sign-off's "one borrow per printed constant over any well-formed row". `SpanRule1`–`SpanRuleSliceI` already reuse the `*U` terms and type formers at `RowSpan` (`Targets/I/Interface.lean`).
- **`Row.Unwind`'s outlives conjunct.** This is transit hygiene stored in a borrow constant's row predicate. It belongs to the transit cut, as a rule of the effect typing that `AdmEff` and `RowSpan Adm` then read (D1.a8). SPEC §19 says operation types are closed in lifetimes, but neither `effPerform` nor `effHandle` checks it (BRIEF §3 item 8).
- **Two handler mechanisms with no relation.** `withswap` (answering) and `hnd` (control) are unrelated (BRIEF §3.5). Relating them is the install cut's law for the answering class (I4).

### 3.4 The borrow–handler dictionary: what BoLo already discharges

This is the concrete form of "a clean mapping between borrowing and lending and some handler laws". Each row is an effect-side obligation, the borrow-side fact that discharges it, and the world.

| effect-side obligation | borrow-side fact | world |
|---|---|---|
| install an answering handler, at the encoding §18 emits | 6.65 through `withbor` (2)'s compatibility in `fundamentalC`. `handle_is_shift` says only that `withbor` (2)'s type is Shifts' schema (`axWithbor2Ty = shiftTy`, a type identity) | Core σ=[]; PAPER |
| install an answering handler as native `hnd` (D1+B4, D2): `ewp_handle`'s answering case | the same 6.65, reached through the borrow form and D1.h2's run correspondence (`p14:B4`; D2.c4) | open (the correspondence) |
| an answering operation; the tail-resumptive law at the encoding | `withswap` (6.66): `op_tail`, `op_answer`, at `withswap`, not at `hnd` | Core run facts |
| an answering handler is the fold of its clauses | `handle_fold`, at the encoding | Core run facts |
| effect safety for answering operations | for §18's encoding, FL and adequacy at Core (`fundamentalC`, `adequacyD`). For System Ξ's fragment, `effect_safety`: adequacy of the translated program at the paper's `DerivesWf`, angelic (some run). Its composition with `embed` into `CDerives` is not written: `translate_typed` is in no Core or CBPVWorld file | Core σ=[]; PAPER |
| no capability escapes its handler (`p12:AS1`) | `[]I`'s premise at `withbor` (2) (6.60: `Mut 'x S ⊐ 'x` fails); stated for the fragment as `capability_not_outlives`, `escape_refused` | PAPER; at Core by the same rule, not stated as a lemma |
| two answers from one handler rejected (AT05) | `Mut` has no copy: `twoBlocks_refused` | PAPER; at Core an inversion to build |
| the clause cannot touch the body's places (AT06, `p10:X.6`) | clauses at `!U` capture only persistent values | Core typing |
| κ not duplicated, not forgotten (AT08, AT13; S6's resource half) | `kTy` is a linear thunk; no weakening; `NoOwn`/`reclaim` (B4), B5 | Core σ=[] |
| κ used exactly once on complete runs (S6's counts) | only under `p8:8.3`: B3 (a second use is stuck) and B4 (an unused κ leaves a cell). Otherwise it is new proof | — |
| finalisation exactly once, memory half | B4 + B5 (`p8:5.4`) | Core σ=[] (+`BumpSim`) |
| finaliser order, no interception (S5) | none: machine facts (`CancelRun`, `noInterception_tier1`) | Core σ=[] |
| an abortive operation crossing a borrow ends the lend | 6.64–6.66 at abortive tables: `ewp_unwind`, `ewp_box_end`, `withborUE` | Core σ=[] |
| capture with a lend inside (ghost end) | the 6.65/6.64 exits at a stop (`wpG_M_frameX`, `wpG_I_frameX`); `freeze_at` | Core σ=[], GE |
| resume re-lends (β up to fresh lifetimes, K.2 in form F.2) | the 6.65/6.64 entries with И freshness (6.108–6.112, H4): `ewpTS_M_frameR`, `ewpTS_I_frameR`; at every stack, `stack_step_*` | GE |
| hiding (handler state invisible to the body, K.5) | 6.66: `wpG_M_antiFrameX`; at resuming tables `ewpTS_M_antiFrameR` | Core σ=[], GE |
| a reborrow open across a stop: `withload` spanning a stop, which D1.i5's `SpanWithload` needs whatever OQ-29 decides | 6.150: `wpG_reborrow` ("a reborrow ends at a stopped operation as at a return"). Its lift to resuming tables is not written; its added step, `ptoImm_dup`, is proved (GhostEnd step 3c; step 3g's "What is work"; the report lists for steps 3f–3i) | Core σ=[] (lift open) |
| an answer borrowed from handler state (OQ-29) | the same 6.150 lift at the handler's state cell, with 6.66 at W (`AntiFrameW`) and decision 59's passing as X.2's round trip | open |
| the handler extent (no use after the handler) | 6.147 at `wpG`: `wpG_box`, `frozen_above_extent` | GE |
| exclusivity across the handler (P10) | `TW.valid`, `TW.inv` (with nothing held at a stop) | Core σ=[] |
| a stored κ respects lifetimes (P9) | 6.60 at `U C`: no rule. Core's `VOutlivesR` has no `U C` constructor (`Core/Types.lean:1730`); `thunk_not_outlives` (CoeffectsStrict) is that fact as a lemma | open |
| conservativity for `{fn, abort}` callbacks (`p14:W1`) | `vC_local` and Core's `↭` at every index (`updRefl_of_core` …) | Core σ=[] |
| deep resume (K.1) | `I5beta`, `ewp_kappa_resume` | every world |
| cancel of κ | `ewp_kappa_cancel`, `ewp_ccatch`, `cancelOwed` | Core σ=[] |
| a handler as a model of the free theory (the existence half of initiality, H.2) | `ewp_handle`, by the inner least fixed point | Core σ=[] |
| a handler as a model of a theory with equations (D1.h4) | none: a fact about the clauses against the equations, and for an answering handler about its co-operations on the carrier `S` | — |
| the row algebra (S1) | none: `rowAlgSafe_orowRF` is effect-only | algebra |

**Whose reuse these are.**
- **The first six rows concern the borrow encoding.** They are facts about `withbor` (2) and `withswap`, which §18 emits today. They are D1's reuse, since D1 keeps that surface.
- **HandlersAsBorrows' fragment is narrower than §18's** (README §1, §6). It has first-order data, with value variables used linearly. Its blocks have one value parameter, no block parameter and no captured value variable. Its clauses are pure and tail-resumptive. It has no effectful clause and no control effect.
- **Under D1+B4 and D2, §18 emits native `hnd`** (D2.c4). These facts then say something about `hnd` only through `I4Typing` and a run correspondence between `ctlForm` and `ansRun` (§5.6).

**Exclusivity is built once:** in `TW`, and through `Mut`'s missing copy rule. **Linearity is built once:** κ is a linear BoLo value, and B4/B5 release what it holds. `kTy` is `U((B ⊸ F_Σ R) & ⊤)` at `lin` and `U((B ⊸ F_Σ R) & F_Σ 1)` at `aff` (`Core/EffRules.lean:976`). The one place where linearity would be built twice is S6's use count for a κ that holds nothing. There `NoOwn` "cannot see a dropped or duplicated κ that holds nothing owned" (OQ-50), and `p8:8.4`'s ghost obligation is a second, logical copy of linearity. `p8:8.3` would remove the second copy (§7.1).

---

## 4. D1 — rows and ghost end (the minimal perturbation)

**Choices.**
- Rows of static per-site names, with lacks constraints and R2's guards, and a rank-1 row `∀`.
- Answering effects stay the borrow encoding at the surface: §18's `withbor` (2) and `withswap`.
- Every handler site opens an extent and lends nothing.
- Internal lends end at each stop and are re-lent at a fresh lifetime at each resume.
- Operation types stay closed in lifetimes.
- Cells stay heap objects, and κ moves as a value (§1.4 item 11).

Done does not hold everything the user's hard test asks for. D1.h1–h4 (§4.1) are what D1 adds for it, and decided items require them (§2.1).

**Stage D0.** D0 is D1 without the interaction additions D1.i1–i8: `I.Tier1 J₁` = `Combined orowRF J₁ coreW admClosedOp .abortive`.

### 4.1 The delta from today

**Additions, A's side** (the same in D0 and D1; D2 and D3 change some, §5.3, §6.1):

| id | addition | where specified | what exists | status |
|---|---|---|---|---|
| D1.a1 | `[allR-I]`, `[allR-E]` at `U` and `!U`: a Curry-style row `∀` with a value restriction | RESTRUCTURE §4.2 | — | to build |
| D1.a2 | the relation at `U(∀ρ:k. C)` is the intersection over admissible instances on the same erased term (`I.ovalW`); `I.FLOpen`; `fl_of_flOpen` | RESTRUCTURE §4.2 | `SemW` already reads a row context as the family of its instances; `tier1`/`tier1NU` hold at every admissible instance | to build |
| D1.a3 | lacks-kinded row variables: `RowCon.adm` carries `n ∉ ρ` for `[handle]`'s `n ∉ Σ` (`p2:R3` as a specialisation) | p2 §5.1 R3 | `RowCon.adm` | to build |
| D1.a4 | `NoLift` and `OneSigPerName` as conjuncts of S1 (`p2:R2`). D3 makes both false and replaces them (D3.k12) | p2 §5.1 R2 | prose in RESTRUCTURE §1.5 | to build (cheap) |
| D1.a5 | the bridges: `machShape_ourInst`, `letLaw_ourInst`, `rowAlgebra_ourInst`, `safety_of_sound` (with `platformOf`, `runs_platformOf`, `runs_platformOf_drive` and the stuttering simulation), `effSafe_of_core` (with `effSafeDriveOfFL`), `handlerSem_ourInst`, `noIntercept_of_core`, `unwindOrder_of_core`, `det_ourInst` | RESTRUCTURE §4.1, U.3 | `ConfLaws`, `KontLaws`, `NoIO`, `DataInj`, `LiftExt` proved | to build (mechanical) |
| D1.a6 | S6's proof route: `p8:8.4` (κ's share owns an obligation consumed at its resume or cancel, coupled to the step) or `p8:8.2` | RESTRUCTURE §1.5, §7 Q9 | `contShare`'s non-persistent wand | **open** (the coupling) |
| D1.a7 | the positive (E) runs at `tier1Open` (an interpreter proved to agree with `Step1`, or runs written out); the elaborator's SF check | RESTRUCTURE §6.1; p12 §6.2 | the `*_eval` checks (evidence) | to build |
| D1.a8 | **the transit law as a checked rule of the effect typing.** Operation types closed in lifetimes become a premise of `[perform]` and `[handle]`, or of forming a `CTy.eff` layer, so that `AdmEff`'s `ClosedLife` is a checked fact and `RowSpan admClosedOp` reads it rather than enforcing it. Today SPEC §19 says operation types are closed in lifetimes, "but neither `effPerform` nor `effHandle` requires it. Only `Row.Unwind` and `EffLeaf` do" (BRIEF §3 item 8). So the transit law (T-a) is enforced only inside borrow constants' row predicates and as `AdmEff`'s range: a borrow rule policing an effect-side fact (§3.3). A rule change, with a SPEC entry | BRIEF §3 item 8; `AdmEff`, `ClosedLife` (`Targets/Instance/Core.lean`) | `ClosedLife` as a hypothesis on `Ξ`; `admClosedOp` | to build |

**Additions, at the interaction** (D1 only):

| id | addition | where specified | what exists | status |
|---|---|---|---|---|
| D1.i1 | `[handle]` takes an extent `∀'h`, and `handle_compatC` starts the body in `Res_h` (`p10:L.4a`). A rule change, with a SPEC entry | GhostEnd README step 1 | `wpG_box`, `frozen_above_extent` (GE) | to build |
| D1.i2 | **the re-lend law at resume** (Law 2, §10): a lend ended at a stop is re-lent at a fresh lifetime beneath the resumer's list, and what κ holds is related at the fresh lifetime | GhostEnd steps 2, 3a, 3h, 3i | `ewpTS_M_frameR`, `ewpTS_I_frameR`, `RBodyT`, `RBodyC`, `tv_thaw`; the stacked relation `vRLs` with `force_RLs`, `thunkF_RLs` and `stack_step_*` (GE); `lam_RLa`, `allI_RLa` (PR #285, unmerged). Open: GFP's induction, #275, #276, #278, and 6.150 at a resuming table (D1.i5) | **open** |
| D1.i3 | W: one world `(ρ, ls, σ)`. σ is GhostEnd's lend stack (OQ-44 (a)), `held = ([],[])`, `Upd` is `↭` at every index, the arising guard is read from `TW`, and `audit_W` passes. **The logical relation is re-indexed by the lend stack**, with Core's `vC`/`cC` as its σ=[] instance (OQ-58 (a)). GhostEnd step 3f prices this: "every compatibility lemma of `fundamentalC` restated at the generalised relation", and "every consumer of `vC`/`cC` in `Core/` (adequacy, every run, totality, the embedding, the programs) re-pointed at the empty-stack instance; mechanical if the instance is definitional". If OQ-58 (a) fails, Core is redefined (OQ-58 (b)), a kernel change with a SPEC entry | BRIEF §5 item 4; RESTRUCTURE §3.6; GhostEnd step 3f | `vRLs_nil`, `gfpAt_nil` (GE); `vRLa_nil` (PR #285, unmerged); `updRefl_of_core` … `updLendBack_of_core` (generic) | to build |
| D1.i4 | D-ORD: fresh lifetimes respect the nesting | i2 §5 M1; p10 L.5 | `relend_respects_nesting` (GE); `AllCross` only at constant `true` | open in general |
| D1.i5 | the spanning rules: the six constants at `RowSpan admClosedOp` (`SpanRule1` … `SpanRuleSliceI`), with their compatibility at W (`SpanWithbor1` …, `SpanWithload`) from D1.i2. **`SpanWithload` needs [TR] 6.150 lifted to resuming tables**: a `withload` spanning a stop. Its exit, 6.52's subtraction at a stop, is proved inside `wpG_reborrow`, and its added step `ptoImm_dup` is proved; "the lift re-instantiates the chooser `rebChooseTW_top` at each resumption's list", and is not written. It is the untranscribed printed lemma in the run-up of the borrow-constant rows (GhostEnd's report lists for steps 3f, 3g, 3h and 3i; i2 §5 M1 *Cost*). It is needed whatever OQ-29 decides, and six reports have carried it forward (BRIEF §8 pattern 7). The cancel path is proved for 6.65 (`withborR_compat`) and not built over a 6.64 frame (p10 §5.1 X.4) | `Targets/I/Interface.lean`; GhostEnd steps 3c, 3f, 3g | `withbor_spans_yields_cC`, `imm_spans_yield`, `withborR_compat` (instances, Core σ=[]); `ptoImm_dup`, `wpG_reborrow` | to build; 6.150's lift **open** |
| D1.i6 | the device restated in M1's shape: `FramesW` in the `Relend` form | i2 §6.2 item 1 | — | to restate |
| D1.i7 | `CancelCloses` for re-lent lends: the cancel ends the frozen owner frames by their unwinding finalisers. **OQ-57 under M1:** `p8:5.6` requires OQ-57's closing list τ in form (b) or (c), (a) being a defect under ONEW. i2 §5 M1 reads τ as `OpenS`'s stack parameter, which is W's σ (D1.i3). So τ is σ's stack index, a component of W and not an index beside it, and (a)'s defect does not arise. Nor does the cancel need τ to close anything in the world: under ghost end nothing is held at a stop, and every lend κ froze was ended there, so the cancel only runs the frozen owner frames' finalisers (C-b). So (b) and (c) are not needed [synthesis, unchecked: no `ClosingInW` is stated] | p8 5.6; i2 §5 M1; OQ-57 (05b) | `spans_two_affine_yields`, `withborR_compat` (GE); `OpenS` carries σ as a parameter | open in general |
| D1.i8 | AT17 at W: κ, whose share holds the owner of an ended internal lend, is stored in a cell and taken back, and no location changes (§1.4 item 11) | i2 §5 M1; p13 §6 P1 | `storeCancel` (tier 1, checked); `at17_eval` (interpreter) | open; that it needs no location symmetry is [synthesis] |

**Additions for the hard test, beyond done.** Done does not hold these, and decided items require them in every design (§2.1). Without them the laws are S4's reductions only, every handler is a model only because signatures carry no equations, and the language's answering handlers are not A's handlers (§4.3).

| id | addition | why | what exists | status |
|---|---|---|---|---|
| D1.h1 | `A.UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`) at our instance, and in done | S4's reductions (F.1) cannot state the tail-resumptive law with an effectful clause, η or hiding (p11 §5.2 F.1). These are **laws of the handling construct**: they relate `handle`, `perform` and `bind` forms, whatever the handler. They do not make any handler a model of a theory; that is D1.h4 | stated beside done (`Targets/A/UnaryLaws.lean`); `etaLin_of_etaHold`; the four non-vacuity lemmas | open. Run-level (F.3): at a machine deterministic up to fresh locations (`head_det_eff`), each is a join of traces |
| D1.h2 | `I4Typing` and a run correspondence between `ctlForm` and `ansRun`, in every evaluation context of a reached configuration (the F.3 form `A.UnaryLaws` uses) | so that S4's and D1.h1's laws about `hnd` hold of the language's answering handlers, which §18 elaborates to the borrow form. Under D1+B4 they are `hnd`, and D1.h2 is still needed: B4's discharge and the encoding's borrow facts reach `hnd` through it (§5.2) | `I4Typing` stated beside done; `handle_fold`, `op_tail`, `op_answer` (encoding) and `ewp_handle` (`hnd`) unrelated; the correspondence is not stated (p11 §5.2 F.3: "the A-level form of I4c restricted to closed programs") | open. `I4c` (binary) is needed only to substitute one form for the other inside open programs [synthesis] |
| D1.h3 | `p14:B3`: `IsModel` for `hnd`'s clauses (`ewp_handle` as the existence half of initiality) and `IsComodel` for the co-operations `co_j : !U(S ⊗ A_j ⊸ F(S ⊗ B_j))`, over one `opTable`. With D1.h2 the two forms are provably one | BRIEF §5 item 2, signed off | `ImplTyped`'s `co` type (dead in `I4a`, AGREE §5); `ewp_handle` | not stated; "the two structure lemmas" (p14 §5.3 B3). Under the free theory both are vacuous: every handler is a model and every family of co-operations a comodel. They gain content only with D1.h4 |
| D1.h4 | **the theory side.** <br>• (a) Equations writable in a signature: `OpSig` gains equations between terms over the signature's operations (OQ-22 (a), the form). <br>• (b) Handler correctness as a model obligation per handler: a handler of `l` is correct when, for each equation of `l`, the two sides handled by it run alike. That is Plotkin–Pretnar Def. 4.5 read at F.3's `RunsAlike` [synthesis]. <br>• (c) For a tail-resumptive handler the obligation falls on its co-operations. Such a handler is determined by them (Ahman–Bauer Prop 3; p11 §1.8), so (b) reduces to the co-operations validating the equations on the carrier `S`. That is D1.h3's `IsComodel` with content [synthesis]. <br>• (d) A row is a sum of signatures (BRIEF §5 item 1), so its theory is the sum of its labels' theories. A tensor, under which operations of different labels commute, is valid only at linear operations: an answering operation and an affine control operation do not commute when the control clause cancels (p11 pitfall 5; TR P13.14). As an equation it is binary, so optional | Laws first (decided) and OQ-22 (constrained toward (a)): "theory-specific laws (exceptions, state and linearly used state, nondeterminism, generators)" need equations to be writable. Without them "handlers as models" is met only vacuously (Plotkin–Pretnar: "If the effect theory is empty, then any handler is correct") | `OpSig` has `arg`, `ans` and `cls`, and no equations (`Targets/A/System.lean`). S4's docstring: "With no equations in signatures (OQ-22) … handler correctness is exactly these equations". A₂'s `EffDepLaws` states Discard at the pure row only, since with no equations "'op(x, …, x) = x' holds of no operation" | not stated anywhere. Correctness is undecidable in general (Π₂-complete, p11 §1.2), so each handler that claims a theory carries its own proof. Under OQ-22's default no kernel theory carries an equation until one is needed. The hard test needs at least one theory declared and its handlers proved models; the cheapest is state for the answering class, through (c) |

**Additions that every design shares (B's side):**
- adequacy at platforms with operations and for the drive (`Adequate coreB`, `AdequateOfLaws`);
- `BumpSim` (OQ-43);
- `Rejects`' inversions and `rejects_at07_of_sound`.

**Sacrifices.** D1's target is done. Its sacrifices are done's, and none goes beyond done:

| sacrifice | what it costs | already in done? |
|---|---|---|
| OQ-56: operation types stay closed in lifetimes (`admClosedOp`) | `asyncRead` in its borrow form (`read(&mut buf)`). The workarounds are OQ-56's: pass the buffer by ownership, hoist the owner, or re-borrow after each resume. `at04` stands in | yes |
| OQ-28: no outlives rule at `U C` | no `U C` value, κ included, has an outlives judgement (`thunk_not_outlives`), so none is returned out of a borrow callback or boxed at a lifetime, even one that holds none of the lend. Only `!U C` crosses (`VOutlives.bang`). So a borrow callback cannot return a closure or a suspended computation that owns a resource it made. A κ whose frozen segment holds the lend itself is not affected: ghost end stores and resumes it (§4.5) | yes: done reads `J.out`, with OQ-28 open |
| OQ-29: no answers borrowed from handler state | Ante's rule (b): handlers that hand out one borrow into their state at a time. Arenas with many live allocations need a finer rule, which no design takes (§5.1), so D1 does not lose them relative to D2 | yes |
| placement parity (`p13:P2`) | one heap cell per spanned place. Z4a against a pinned Rust frame fails on tier-2 programs; Z4b holds. Every tier-2 design pays it | yes (A₃'s corpus omits tier 2) |
| multi-shot | `unr` is outside `J₂`; it still works at tier 1 | decided |
| binary laws and AS3–AS5 | A₂ | a default, not a decision (§2.1) |

If §1.4 item 11's reading fails, AT17 also needs T3's location half or T4, and T4 forbids moving a placed κ (threads).

D0 also sacrifices **self-referential suspension**: `Tier2Programs` (`at02`, `at04`, `at12`, `at17`, `genSelf`) and `reconB′`.

### 4.2 Cuts and their laws

| cut | interaction law | Lean |
|---|---|---|
| install | (I-a) the handled body runs from `Res_h`, and every end of it, value or stop, has its share in `Res_h` (6.147 at `wpG`) | `wpG_box`, `frozen_above_extent` (GE); D1.i1 |
| install, answering class | (I-b) a typed control form with tail-resumptive clauses has a typed borrow form, `withbor` (2) and `withswap`, with the same runs (D1.h2) | `I4Typing` (open, beside done); a run correspondence (not stated) |
| stop | (S-a) the stop condition is unchanged: conjuncts 37 and 40 | `Core/EffDefs.lean` |
| stop | (S-b) ghost end: each lend opened inside the frozen segment ends by its printed exit at the stop. This is admissible when the frozen share, less the views, lies in `[α]` | `wpG_M_frameX`, `wpG_I_frameX`, `wpG_reborrow`; `freeze_at` (GE) |
| transit | (T-a) operation arguments and answers are closed in lifetimes, so no borrow crosses with an operation | `admClosedOp`, `Row.Unwind.out`. Today these are borrow constants' row predicates, and `AdmEff`'s `ClosedLife` is a hypothesis: neither `effPerform` nor `effHandle` checks it (BRIEF §3 item 8, SPEC §19 drift). D1.a8 makes it a rule of the effect typing |
| capture typing | (S-c) `[let]`'s capturing condition | `effLet` |
| resume | (R-a) deep resume reinstalls the handler | `ewp_kappa_resume`, `I5beta` |
| resume | (R-b) re-lend: each ended lend is re-lent at a fresh lifetime beneath the resumer's list, and κ's frames are related at it (**Law 2**) | `ewpTS_M_frameR`, `ewpTS_I_frameR`, `stack_step_*` (GE); open in general |
| resume | (R-c) D-ORD | `relend_respects_nesting` (GE) |
| cancel | (C-a) κ's finalisers fire innermost first; the error policy is §19's | `ewp_kappa_cancel`, `ewp_ccatch`, S5 |
| cancel | (C-b) the frozen owner frames' unwinding finalisers end the lends (`withborUE`'s `ubind`) | `withborR_compat`, `spans_two_affine_yields` (GE), for 6.65; not built over a 6.64 frame (p10 §5.1 X.4) |
| cancel | (C-c) the memory κ held is released | `reclaim`, `NoOwn` (B4), B5 |
| placement | (P-a) κ is a linear value, stored and moved as one. Every place is a heap cell, so a move copies κ's value and changes no location (§1.4 item 11, [synthesis]). P13 says the same of the lowering under `p13:P1` (p13 §5 item 2) | `kTy`; `storeCancel` |
| placement | (P-b) with no outlives rule at `U C`, a κ holding an external lend stays inside that lend's scope | Core's `VOutlivesR` has no `U C` constructor (`Core/Types.lean:1730`); `thunk_not_outlives` (CoeffectsStrict, `Context.lean:111`) is that fact as a lemma, by case analysis on Core's `VOutlives` |

**Independence away from the cuts.**
- On A's side:
  - S1's algebra reads no resource;
  - S4 and S5 are joins of steps that change no store;
  - the row `∀`'s relation clause is an intersection over rows on one erased term, so it reads no resource either;
  - A's statements read no resource. Their proofs at our instance do: S2 and S3 come through B's FL (`p2:S-e`), at W the only route built (§2.5). That is a dependency of proofs, not an interaction of the algebras.
- On B's side:
  - the frame lemmas at `wpG` read no term;
  - 6.60 reads values only;
  - `TW` and `TI` mention no effect.
- The relation reads effects only through `opTable` and the stop conjuncts, which are the transit, resume, cancel and stop cuts. The typing reads them in `effLet`'s capturing condition, the capture cut, and in the six `*U` constants, which D1.i5 replaces by the printed constants at a row predicate. With D1.a8 it also reads them in `ClosedLife`'s premise at `[perform]` and `[handle]`, which is the transit cut.

**Where a smell could enter (Law 2's placement)** [synthesis]. A closure in κ's frames that holds the lend must be related at the fresh lifetime. GhostEnd's README step 3a, item 2: "Each needs a relation for U, → and ∀ values read with the lend re-lendable". This is OQ-8's question, and there are three places for the answer:
1. **Naturality.** A lemma about the borrow relation alone (`FreezeBinderLife` at the configurations a freeze leaves), used only at the resume cut.
2. **A quantifier at `U`, `contShare` and `KapRel`.** This is the audit's placement (BRIEF §5 item 4). The stacked relation does it at `U`: its clause is `RelendableS`, so a thunk thaws at a fresh lend by construction (`force_RLs`, `thunkF_RLs`).
3. **A quantifier in the binder clauses** (`∀`, `⊸`). This is #287's placement (`vRLk`, `callback_ext`). It puts a resume obligation into value clauses, away from the cut. The borrow-constant row reaches it: with the arising guard at `⊸`, the row must read its callback at σ·y (#275; 02-experiments §1.3).

The cuts criterion orders them 1, 2, 3. This orders an open question; it does not recommend a design.

**The evidence so far points to option 3.**
- 02-experiments §1.3 records that with the guard at `⊸`, #275's borrow-constant row "must read its callback at σ·y", which is `vRLk`'s shape. §11's statement 2 adopts that shape.
- Option 1 is under `mut_not_natural`, and whether its witness arises has not been checked (§4.8).
- Option 2 is what the stacked relation does at `U`. But the guarded relation `vRLa` guards `U`, `⊸` and `∀` together, and 02-experiments §1.3 lists "whether `U` and `⊸` take the same quantifier" as open.

**What option 3 would cost the cuts criterion.** D1 would then carry a resume obligation in every `⊸` and `∀` clause of the relation: an interaction away from the cuts. D1 would no longer meet "two algebras with interactions only at cuts", though it would still rank ahead of D2a, which inherits Law 2 and adds extents in types (§8). BRIEF §5 item 4 says "A Lean statement settles it, not prose". §11's statement 0 is that statement.

### 4.3 Hard tests

**A as an effect algebra** at `ourInst orowRF Ξ J`, at every `AdmEff Ξ`:

| A property | what discharges it | D1 (and D0) |
|---|---|---|
| S0 `MachShape`, `LetLaw` | `ConfLaws`, `KontLaws`, `NoIO`, `DataInj` proved; `AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`, `LetLaw` from Core's steps | open (mechanical) |
| S1 `RowAlgebra` | `rowAlgSafe_orowRF`, `rowLink_orowRF`; `SubClosed` with the row `∀` | open (bridge) |
| S2 `Safety` | `Sound` through `safety_of_sound`; `Adequate` at every platform and the drive | open (shared B lemma). D0: from FL at `coreW`. D1: rides on FL at W, through `soundnessOfFL` |
| S3 `EffSafe` | `effSafe_tier1` + `EffSafeDrive` (`p2:S-e`) | D0: from FL at `coreW` (`fundamentalC` and `FLOpen`), once bridged. D1: rides on FL at W (`effSafeDriveOfFL`). `p2:S-f` would free it from B (§2.5) |
| S4 `HandlerSem` | Core's `hret`, `hop`, `hunwind`, `uthen`, `ufin`, `seq` and `kappa`'s administrative steps | open (mechanical) |
| S5 `Cancellation` | `noInterception_tier1` (σ=[]), `CancelRun`, `UnwindRun`; `FinaliserOrder` (`two_frame` proved) | open (bridge + `FinaliserOrder`) |
| S6 `ContUse` | D1.a6 | **open (route)** |
| `TailLaw` (beside done; D1.h1) | a run-level fact about `hnd` (F.3), with the hygiene that `[handle]`'s `n ∉ S` appears to supply (not checked). `op_tail`/`op_answer` are the same fact at the borrow encoding, related by D1.h2 | open; not in done |
| `AlgLaw`, `EtaHold`/`EtaLin` (beside done; D1.h1) | S3's `StopsIn` under bind frames and determinism; K.4's frame through `thenT` | open; not in done |
| E1, E1′, E2a–d, E6, E10 | `J₁`'s row `∀` and the positive runs; non-vacuity proved at every instance (`not_noColouring_of_monoCallback` …) | open (needs `J₁`) |
| E3, E4, E5, E7, E8, E9 | positive lemmas at `tier1Open` from Core's encodings (`nLogOutside`, `nFailOutside` checked; `takeProg`, `storeCancel`, `prog`, `prog₃`, `two_frame` shapes) | open (no missing feature) |

**The hard test, property by property.** What done realises, and what it does not:
- **Signatures and operations: realised, without equations.** `Ξ n` is one signature object per name (`RowSig`, S1), with the classes abortive, linear and affine. `AdmEff` keeps operation types closed in lifetimes, as a hypothesis on `Ξ` that D1.a8 makes a checked rule. Signatures carry no equations until D1.h4.
- **Laws of handling: the reductions only.**
  - S4 states the induced homomorphism's reductions in every context, up to store-free steps (`p11:H.1`): return, the resuming and abortive catch, deep resume, cancel, and both finaliser laws.
  - The device adds `ewp_handle` at W, the existence half of initiality (`p11:H.2`), beside done.
  - Done states no law beyond the reductions: no `TailLaw`; no algebraicity beyond its reduction form (S3's `StopsIn` under bind frames); no η; no uniqueness half. A's equational laws are the binary ones, outside the first pass (system-a.md).
  - D1.h1 adds `TailLaw`, `AlgLaw` and `EtaHold`. These are laws of the handling construct, true or false of the machine's `handle`, whatever handler is installed. They say nothing about whether a particular handler validates a theory.
- **Handlers as models: vacuous at done.**
  - Signatures carry no equations (`OpSig` is `arg`, `ans`, `cls`), so every handler is a model: "If the effect theory is empty, then any handler is correct" (Plotkin–Pretnar, after Def. 4.5).
  - D1.h3 states `IsModel` and `IsComodel`, which are vacuous under the free theory.
  - D1.h4 makes them obligations: equations writable in signatures (OQ-22 (a)), and a model obligation per handler, which for an answering handler falls on its co-operations.
- **Control with real continuations: stated in done; S6's route open.** `kappa` is a captured value with deep `resume`, §19's `cancel` and `raise` unwinding. Linear use is stated as S6, and its proof route is open (D1.a6).
- **Composition: realised.** Nesting works in both orders (E5). Forwarding is the structural fact that a handler frame of `l` catches only `l` (`KontLaws`).
- **Effect polymorphism: realised** by the row `∀` (Law 1).
- **The language's answering handlers: not realised at done.**
  - §18 elaborates them to `withbor`/`withswap`. A's properties cover those programs as programs (S2, S3, S5, S6).
  - S4 and the laws are about `hnd`. So, as handlers, these are the borrow calculus with an effect-like surface.
  - They become A's handlers with `I4Typing` and a run correspondence (D1.h2), or natively under D1+B4 (§5.2). `I4Typing` alone is the typing half, and done's `Pins` holds `I4a` only.
  - A's own E5 uses the native `hnd`, so A holds either way.
- **Models and comodels** (the signed-off item 2): not stated at done (D1.h3), and vacuous until D1.h4 puts equations in signatures.

**B in the composite, at W:**

| B | D0 (`coreW`) | D1 (W, Core's stop) |
|---|---|---|
| B0 `ExtendsB` | proved (`extendsB_tier1`) | a pin |
| B1 FL | `fundamentalC` + `FLOpen` for `J₁` | FL at W: `GFPA` / Law 2 (**open**), at the relation re-indexed by the lend stack (D1.i3), with 6.150's lift for `withload` (D1.i5) |
| B2 `Adequate` | at a restriction; platforms and the drive open | `AdequateOfLaws`, with `UpdSeq`/`UpdReclaim` from Core's `Upd` (`updSeq_of_core`, `updReclaim_of_core`) |
| B3, B4 `Sound` | `soundnessOfFL` (generic) | the same |
| B4′, B5 | `soundContractsOfFL`; `releasedOnceReuse_of_bumpSim` + `BumpSim` (open) | the same |
| B6 `ExclusiveB` | `exclusiveB_core` | `TW.valid` at every stop (nothing held): reused |
| B7 `LifetimeSound` | `lifetimeSound_core` | 6.60 at W; κ's bound holds external lends only |
| run-end laws for FL's printed route | `updRefl_core` … | `updRefl_of_core` … (generic, because `Upd` is Core's) |

**I:**

| I | D0 | D1 |
|---|---|---|
| `Bounds` | proved at σ=[] | at W, with `Upd` Core's everywhere |
| `Interface` (`Arises`, `Exclusive`) | proved at σ=[] | nothing held: `TW` over the visible frames (reused) |
| `Pins` (`I4a`) | at `.abortive` (`i4a_tier1`) | at `.any`: an answering lend spanning a control stop is an internal lend under ghost end, so it rides on Law 2 |
| `Accepts`: `CompositeT1` | `acceptedT1_*`; NU derivations to build | the same |
| `Accepts`: `Tier2Programs` | fails (sacrificed by design) | `J₂` + Law 2 (open); `at17` by D1.i8 |
| `Rejects` | inversions to build; AT07 from `Sound` | the same |

### 4.4 Concrete reuse

Reused directly:
- every row of §3.4 at Core σ=[];
- the borrow encoding's facts, because D1 keeps §18's surface:
  - `op_tail`, `op_answer` and `handle_fold` (Core run facts);
  - the escape check at `withbor` (2)'s `[]I` premise;
  - AT05 by `Mut`'s missing copy;
  - for System Ξ's fragment at PAPER, `translate_typed` and `effect_safety`. Their composition with `embed` is not written;
- the frame proofs at a stop and at resume (`wpG_M_frameX`, `wpG_I_frameX`, И freshness), once per resumption, and the stacked steps (`stack_step_*`);
- the run-end laws, every consumer of `↭`, `TW.valid` and `TW.inv`, because the stop is unchanged;
- conservativity (`p14:W1`): `↭` keeps its printed meaning at every stop, and answering operations stay `Mut` arguments, inside `AbortRows` (p14 coupling 2).

New proof:
- the row `∀` clause and `FLOpen`;
- the relation re-indexed by the lend stack, with every compatibility lemma of `fundamentalC` restated at it and every consumer of `vC`/`cC` re-pointed (D1.i3);
- FL at W at the rows §11 names, then GFP's induction over the rest. The rows are: W's `U`, `⊸` and `∀` clauses fixed together; the guard read from `TW`; the borrow-constant row at σ·y; `[handle]` with a lend open; and `[allR-E]` at W;
- [TR] 6.150 lifted to resuming tables, for `withload`'s spanning rule (D1.i5);
- the cancel path over a 6.64 frame (D1.i5, C-b);
- D-ORD in general;
- the extent in `handle_compatC`, and `ClosedLife` as a rule (D1.a8);
- S6's route;
- for the hard test, D1.h1–h4.

### 4.5 Tier 2

| program shape | D0 | D1 |
|---|---|---|
| an unstored κ holding an internal lend (`at02`, `at04`, `genSelf`) | rejected | ghost end |
| a κ cancelled while holding a lend (`at12`; `thread::scope` with κ dropped) | rejected | the cancel path (C-b) |
| a κ moved into a cell and back within the handler (`at17`) | rejected | yes, by a reading that needs no location symmetry (§1.4 item 11, unchecked); otherwise T3's location half or T4 |
| a κ stored past its handler, holding internal lends | rejected | re-lent beneath the resumer (D-ORD) |
| a closure holding an internal lend across a stop, inside a row-polymorphic HOF (`reconB′`) | rejected | Law 2 at the rows §11 targets: the probe |
| a κ or thunk that owns a resource, returned out of a borrow callback | no | no (OQ-28) |
| the async read, borrow form (`read(&mut buf)`) | no | no: a view in transit leaves `[α]` (OQ-56's text) |
| the async read, ownership form | yes | yes |
| a generator borrowing its own state (`genSelf`) | rejected | yes |
| resuming inside a younger lend (between lenders) | n/a | D-ORD; no program pins it (p10 pitfall 6) |

### 4.6 Lowering and zero cost

- Lowering stays at `p13:Z0` now. If OQ-23 is answered "a theorem", it becomes `p13:Z2`, with `Z4b` and `Z2⁺` for E10.
- The class key is `p13:C1`, plus `C4` for tail clauses, as built. `C1b` (`RowCon.cls`) is optional, for shared un-specialised bodies.
- Ghost end and carry lower to the same code (p13 §5 item 1). A lend is an address word, and a spanned place is a heap cell that keeps its address when the state moves (`p13:P1`). The cost is one allocation per spanned place, against a pinned Rust frame.
- The answering encoding costs one cell (`log-outside` 1 against 0 for the native form). That is the cell-placement question, not a handler cost.

### 4.7 Novelty against the literature

- Re-lend at a fresh lifetime per resumption: none published. The nearest is Yarrow's temporary revocation, which has no lifetimes (i2 §4 (ii)).
- Preserving a lifetime-indexed exclusivity invariant across capture and resume: none found (i2 §4 (i); p10 §4).
- A relation-level conservativity statement for a lifetime calculus with one-shot handlers (p14 §4).
- A mechanised calculus with lifetime-indexed `&`/`&mut` and handlers (survey §6 item 1).
- A Lean `LoweringCorrect` for a handler lowering, if Z2 is taken (p13 §1.3).

### 4.8 Open risks, with the evidence

| risk | evidence |
|---|---|
| Law 2 for a closure holding the lend (O15.2) needs a relation family beside W (BRIEF §8 pattern 4) | GhostEnd step 3f: "where the single-lend relation stops: a closure under an inner borrow" (`thunkF_RL_fails_below`), fixed at GE by `vRLg` and by the stacked `vRLs` |
| GFP fails at W | GFP refuted as first stated (`not_gfp`) by a witness that does not arise (`wpG_below_not_arises`); `GFPA` open beyond the `lam` and `allI` rows; its guard `TabAtS` is not related to `TW` (OQ-45) |
| the borrow-constant row at σ·y (#275) | with the guard at `⊸`, the row reads its callback at σ·y, which is `vRLk`'s shape; `vRLk` has no σ=[] lemma (OQ-58) |
| `[handle]` inside the borrower (#278) | `effHandle`'s inner-stop clause, and a handler frame that passes the lender's stops, are not built (GhostEnd step 3f); `AllCross` is discharged only at constant `true` |
| naturality is not available for live lends | `mut_not_natural`; `NotVDenNaturalArises` unchecked. GhostEnd step 4: the freeze ends the witness's cell, and "the route never asks naturality at such a cell" |
| D-ORD in general | `relend_respects_nesting` for one lender frame per segment; the between-lenders case is not built |
| S6's coupling | p8 §5.1 8.4: "the coupling step is the unknown" |
| the device's shape | §1.4 item 9 |
| AT17 | §1.4 item 11: a reading of the relation, unchecked |
| item 4's relativised stop at `held = ([],[])` | a reading of BRIEF §5 item 4 for the user to approve (§2.1) |
| [TR] 6.150 at a resuming table stays unbuilt | its added step (`ptoImm_dup`) and its exit at a stop (inside `wpG_reborrow`) are proved; the lift is not written. It is the untranscribed printed lemma in the run-up of the borrow-constant rows in GhostEnd's report lists for steps 3f–3i, and i2 §5 M1 lists it as M1's cost. BRIEF §8 pattern 7: "The 6.150 lift to resuming tables appears in six reports". `SpanWithload` needs it whatever OQ-29 decides (D1.i5) |
| the cancel path over a 6.64 frame | proved for 6.65 (`withborR_compat`, `spans_two_affine_yields`); "cancel over a 6.64 frame is not built" (p10 §5.1 X.4). `reconB′`'s `Imm` lend under `timeout`'s cancel needs it (§11, statement 2) |
| Law 2 lands in the binder clauses (OQ-8's option 3) | the evidence of §4.2. D1 would then have an interaction away from the cuts in every `⊸` and `∀` clause (§8) |
| A's S2 and S3 at `J₂` | they ride on FL at W (`p2:S-e`, the only route at W; §2.5), so any failure of Law 2 or GFP at a rule costs A's safety and effect safety for the programs that need that rule, not only `Tier2Programs` |

---

## 5. Capabilities as borrows: D1+B4, D2a and D2b

The user: "I actually think capabilities as borrows is kind of a small change tbh."

Capabilities as borrows comes in three tiers. Each tier can be taken without the ones after it [synthesis]:
- **(i) Install and the answering class.** Answering handlers are native `hnd`, and an answering site lends its state, in the borrow form (`p14:B4`). Rows stay rows of labels, the capability reaches the operation by row and evidence (`p14:B6`(a)), and no type names an extent. Taken alone, this is **D1+B4** (§5.2).
- **(ii) Extents in types.** Row entries carry the site's extent, and callbacks bind it (`rc:O3`).
- **(iii) Answers borrowed from handler state** (OQ-29 (b), `p10:X.2`). It needs tier (ii), since an answer of type `Mut 'h T` names the extent.

**D2a** takes all three tiers and keeps static per-site names in the kernel (`rc:O3`, with `O3-surface` at the surface). **D2b** replaces rows by capability values (`rc:O2`), and reaches A's label-based programs through an elaborating instance.

§5.1 prices the user's claim, tier by tier. §5.2 is D1+B4. §5.3–§5.6 are D2a. §5.7 gives D2b as a delta from D2a.

### 5.1 The marginal cost, claim by claim

| claim | reading | evidence |
|---|---|---|
| answering effects and I/O are already capability-passing in Core | **True in Core, for the elaborated encoding.** §18 elaborates `with h(e) { M }` to `borrow mut (alloc(e)) { 'l, c -> M' }` and an operation to `withswap`, so the capability passing is in Core's own terms, `withbor` (2) and `withswap`. I/O is capability-passing (decision 30; CoeffectsStrict §8). What Core lacks is a `hnd` form for answering handlers, and any relation between the two mechanisms (BRIEF §3.5) | SPEC §18 *Elaboration*; `Core/Handlers.lean` |
| HandlersAsBorrows exists at the paper layer | **True at PAPER, for a fragment, and not lifted.** <br>• `translate_typed` is at the paper's `DerivesWf`, over a fragment of Ξ's answering handlers: first-order data, value variables used linearly, one-parameter blocks with no block parameter and no captured value variable, and pure tail-resumptive clauses; no effectful clause and no control effect (README §1, §6). <br>• `embed` sends `DerivesWf` to `CDerives`, so the composition type-checks in principle. It is not written: `translate_typed` is in no Core or CBPVWorld file. <br>• These facts concern the borrow encoding, which D1's surface already emits (§3.4). They are not a gain of any tier | HandlersAsBorrows README §1, §3, §6; `Core/Embedding.lean` |
| control effects as borrows share cost with the tier-2 stop change and OQ-28 | **True for the extent:** D1 needs it (GhostEnd step 1). <br>**True for the stop:** a lend that spans a stop under M1 changes no stop conjunct (§1.4 item 12). <br>**Shared at resume for tier (i); not shared for tier (ii)**, by reading. Under D1 and D1+B4 no type mentions an extent, and `admClosedOp` keeps operation types closed in lifetimes, which OQ-56's text ties to ghost end's admissibility. In the borrow form, an answering site's state lend frozen in κ is then an internal lend like any other, re-lent by Law 2. Under tier (ii) row entries and answers mention `'h`, so re-lending an inner answering handler's state re-reads types in κ's frames (D2.c8). <br>**OQ-28:** D1+B4 needs no more of it than D1. For D2a, rc §3.7 says rows of lends need the outlives rule at `U C`, and §5.3's reading (D2.c9) says they do not; that reading is unchecked (§1.4 item 13). D2b needs it (§5.7). <br>**Caveat:** if control-handler *state* became a lent cell, rather than decision 59's state passing, every stateful control program would depend on Law 2, not only `Tier2Programs`. S4's store-free laws would also fail at install and return, because the cell is allocated and freed (S4 is `PureJoin`, RESTRUCTURE §1.5) | GhostEnd step 1; RESTRUCTURE §1.5; decision 59; OQ-56; rc §3.7 |
| the control-class carrier for the lowering is new under any option | **True.** `RowCon.cls` exists in the targets and no lowering statement consumes it. Under `rc:O3` the carrier is the entry's bound; under `rc:O2` it is a grade (`O2-g`). The cost is the same | rc §0.2, §6; p13 C1b, C3 |
| what the claim leaves out | (1) A capability kernel that drops labels needs an elaborating instance, boxes, and by reading a row on stored callbacks (§2.3, §5.7). <br>(2) Extents enter the row algebra (D2.c3) and callback types (D2.c9): tier (ii). <br>(3) Re-lending at extents (D2.c8): tier (ii). <br>(4) Borrowing *from* handler state across a suspension (OQ-29) needs X.2's round trip at W and the handler-state instance of 6.150's lift: tier (iii). Both are open (§4.8, D2.c5) | §2.3; p2 §4; p10 X.2; OQ-29 |

**Verdict, by tier** [synthesis]:

| tier | what it adds over D1 | cost | cuts | what it buys |
|---|---|---|---|---|
| (i) install and the answering class: D1+B4 | D2.c4: §18 emits `hnd` for answering handlers, and `ewp_handle`'s answering case is discharged by 6.65 through the borrow form and the correspondence. D2.c11: an `answering` class in W1's guard | **small.** D1.h2 and D1.h3 are shared, since the hard test needs them under D1 too. The rest is an elaboration change (the backend's C4 already lowers `hnd` with tail clauses to a call), B4's discharge lemma, which composes 6.65 at the borrow form with D1.h2's correspondence, and a device change | D1's. The install cut carries the answering site's state lend, in the borrow form. No type names an extent, so D2.c8 and D2.c9 do not arise | one install mechanism, so OQ-1 is settled by construction; S4 and D1.h1 cover the language's answering handlers directly; the answering cell is gone (`log-outside` 1 → 0) |
| (ii) extents in types | D2.c1–c3 (row entries carry `'h`; "own extent only"; condition (4) at extents), D2.c6, D2.c7, D2.c8 (Law 2 at extents), D2.c9 (extent binders in callback types); by rc §3.7, perhaps OQ-28's rule (D2.c12) | **moderate, and open.** D2.c3, D2.c8 and D2.c9 have no Lean, and D2.c9 is not in Law 1 | adds resume at extents (R-d). Puts a lifetime inside the row algebra and callback types, which is away from the cuts unless extents are read only at install, transit and resume (§5.4) | AS1 by 6.60 at row entries (B7); a second route to S3, by outlives (D2.c6); the extent in the type, which tier (iii) needs |
| (iii) answers borrowed from handler state | D2.c5 (answers at `'h`, A5(b)), D2.c10 (decision 59's passing as X.2's round trip), with `AntiFrameW` at W and 6.150's lift at the handler's state cell | **large, and open** | adds the transit of an answer borrowed at `'h` (T-b), and X.2's round trip at the stop | Ante's rule (b) as B6: handlers that hand out one borrow into their state at a time. No target in done asks for it |

So the user's "kind of a small change" holds for tier (i). Capabilities as borrows at install and for the answering class, with rows of labels, costs about D2.c4 and D2.c11 over D1, once the hard test's h2 and h3 are in. By reading it does not hold for tiers (ii) and (iii), which hold the open items. None of this is checked.

**The program family that motivates tier (iii)** is handlers that hand out borrows into their state, and arenas as nested handlers belong to it.
- Allocation as an effect is decided: "`box` is the operation, the heap is the outermost linear State handler, and arenas are nested handlers" (04-decisions §5 A1). OQ-68 classes the construct as decided and its obligations as open: "the arena frame at a resuming table is a real unknown that depends on OQ-9/T-FRAME".
- D2's OQ-29 (b) takes A5(b)'s coarse rule, which ends each answer before the next operation at the same handler. That is Ante's H3: "one borrow per handler with no per-call disjointness". It covers handlers with one live answer at a time.
- An arena with many live allocations needs disjoint lends per operation, the finer rule that H3 defers ("Finer per-operation disjointness can come later"). No design here takes that rule. So tier (iii), as costed here, does not deliver arenas with many live allocations either.

### 5.2 D1+B4 — capabilities as borrows at install, with rows of labels

**Choices.** As D1, except:
- `p14:B4` with `B2` and `B3`: answering handlers are `[handle]` with tail-resumptive clauses, and an answering site lends its state, in the borrow form (D2.c4);
- `p14:B6`(a): an operation reaches its handler by row and evidence, so answering operations become row layers (D2.c11);
- operation types stay closed in lifetimes (`p10:L.6a`), so no answer is borrowed from handler state, and no type names an extent;
- control handlers open an extent that lends nothing, as in D1.i1;
- control-handler state stays decision 59's state passing.

**Consistency with the edges** [synthesis].
- `p14:B4` requires `p10:L.4` (a) or (c) at Core, and "6.65 at answering tables" (p14 §0.4). D1.i1 gives (a). 6.65 is met through the borrow form: there an answering operation is a `withswap` call, not a stop, and `withbor` (2)'s compatibility is 6.65 at Core (D2.c4).
- `p14:B2` requires B1, `capPass`'s spine and S4's deep handler: `I4a` and D1.h2.
- `p14:B6`(a) requires `rc:O1`, rows of labels.
- rc §3.3's edge, "`rc:O1` + handler-state borrows R `p10:L.4`, which turns it into `rc:O3`", concerns answers borrowed at `'h` (§1.3). D1+B4 borrows none, so it stays `rc:O1`.
- `p14:B1` requires `p10:L.4` (c), which (a) meets (§1.4 item 14).

**The delta from D1.**
- D2.c4: §18 emits `hnd` for answering handlers. `ewp_handle`'s answering case is discharged by 6.65 through the borrow form and D1.h2's correspondence. The backend's C4 already lowers `hnd` with tail clauses to a call.
- D2.c11: an `answering` class in `ConservativeWB`'s guard. Answering operations become row layers, which `AbortRows` excludes (§1.4 item 7).
- Nothing else. D1.h2 and D1.h3, which tier (i) leans on, are already in D1's completion for the hard test. No kernel definition changes beyond D1's.

**Resume.** The native form passes the state as a value (decision 59), so the lend is the borrow form's. There, an answering handler frozen inside κ, whose body was caught by an outer control handler, holds its state lend as an internal lend of the frozen segment. Ghost end ends it at the stop and re-lends it at resume. That is Law 2, as for any other internal lend (`I4a` at `.any`, §4.3). No type names that lend's lifetime, so no type in κ's frames is re-read, and D2.c8 does not arise [synthesis].

**Cuts.** D1's. The install cut gains the answering site's lend (6.65 on the state cell, in the borrow form). The law relating the two forms (I-b) becomes the justification of what §18 emits. §3.3's smell, "two handler mechanisms with no relation", is gone: there is one mechanism, and the borrow form is its proof device.

**Hard tests.** As D1 (§4.3), with one change: S4 and D1.h1's laws cover the language's answering handlers directly, since they are `hnd`. D1.h4's model obligation for an answering handler falls on its co-operations (D1.h4 (c)).

**Reuse.** As D1. The borrow facts about answering handlers reach native `hnd` through D1.h2's correspondence (§5.6): `op_tail`, `op_answer`, `handle_fold`, the escape check, and AT05 by `Mut`'s missing copy. AS1 stays `[handle]`'s `n ∉ Σ`, as under D1.

**Lowering.** Answering handlers are native `hnd`, lowered by C4 to a call with no allocation (the `*-native` programs). The class key is D1's (`p13:C1`, `C4`).

**Sacrifices.** D1's. D1+B4 carries the same programs as D1.

**What "effects are core" says about it** [synthesis]. Read with the hard test, K1 ("we aren't going to be able to implement them correctly with sugar") and K15 ("handlers as folds of the free model") favour one install mechanism. Under D1 the language's answering handlers are borrow constants, related to `hnd` by D1.h2. Under D1+B4 they are `hnd`. Whether D1 with D1.h2 meets K1 and K15, or only D1+B4 does, is for the user.

**The probe** (§11) is the same for D1 and D1+B4: by reading their definitions, neither `genSelf` nor `reconB′` installs an answering handler.

### 5.3 The delta from D1 (D2a)

D2a is D1+B4 plus tiers (ii) and (iii). In the table, D2.c4 and D2.c11 are tier (i), which D1+B4 already takes.

**Choices (D2a).** As D1+B4, plus:
- `rc:O3` (`O3-surface` at the surface): row entries carry the site's extent `'h`;
- `p10:X.2`: answers borrowed from handler state at `'h`;
- `p2:R5`(a): a second proof of S3 by outlives;
- `p12:N6`'s escape check for AS1.

Control-handler state stays decision 59's state passing. D2.c10 says what X.2 then owes.

| id | tier | addition | status |
|---|---|---|---|
| D2.c1 | (ii) | row entries carry the site's extent `(n, 'h_n)`: a change to `CTy.eff`'s layers | to build |
| D2.c2 | (ii) | `AdmEff`'s `ClosedLife` replaced by "own extent only": an operation type may mention its own site's extent and no other lifetime. This is what ghost end's admissibility asks (§5.4). It must be a checked conjunct, not prose (D1.a8, widened) | to change |
| D2.c3 | (ii) | Yoshioka's condition (4) at extents. R2's `OneSigPerName` holds if the extent is the instance's, fixed by dynamic nesting and kept out of `∼`. Otherwise erasable scoped rows (`p2:R4`, `EA_EScpR`) are needed | **open** (p2 §4: "I have not built such a configuration") |
| D2.c4 | (i) | one install mechanism: answering handlers are `hnd` with tail-resumptive clauses. Their borrow form is `withbor` (2) and `withswap`, related by `I4Typing` and a run correspondence (D1.h2). `p14:B4` discharges `ewp_handle`'s answering case by `wpG_M_frameX` on a state cell. With decision 59's state passed as a value (the `*-native` programs), that discharge goes through the borrow form and the correspondence. §18 emits `hnd` for answering handlers, and the backend's C4 already lowers it to a call | to build |
| D2.c5 | (iii) | answers borrowed from handler state at `'h` (OQ-29 (b)), each ended before the next stop at the same handler (A5(b)) | **open**: `AntiFrameW` at W; 6.150's lift at the handler's state cell. The lift itself is D1's (D1.i5) |
| D2.c6 | (ii) | effect safety by outlives, a second proof (`p2:R5`(a), `S-d`) | optional (`effect_safety`, PAPER) |
| D2.c7 | (ii) | surface capabilities elaborated to static names (`O3-surface`) | to build: one lemma; §18 already resolves operations lexically |
| D2.c8 | (ii) | **Law 2 at extents.** <br>• An inner answering handler frozen in κ lends its state at its extent (6.65, D2.c4). That is an internal lend, ended at the stop and re-lent fresh at resume. The types in κ's frames that name that extent are then read at the fresh lifetime: row entries, and answers borrowed at it. <br>• The stacked relation's substitution acts on lend lifetimes in value types. Under D1 and D1+B4 no row mentions a lifetime, so their tables do not depend on the substitution. D2 needs operation tables read under it (`opTable` at δ, with `opTable_mono`, `opTable_shift` and `opTable_extR` re-proved), or the lifetime half of T3/V6. <br>• An inner control handler's extent lends nothing, so nothing of it ends at the stop, and types that name it keep their reading. The catching handler's own extent is not re-chosen inside `ewp_handle`'s induction, which continues the same body proof. So this arises at inner answering handlers, not at every resumption [synthesis] | **open**, no Lean |
| D2.c9 | (ii) | **Extent binders in callback types.** A callback cannot name the extent of a handler installed later, or installed inside the higher-order function it is passed to. <br>• E2c, E2d and E10 need the callback to bind it, e.g. `retryP : ∀ρ. U(∀'h. 1 → F_{(exn,'h)⊙ρ} bool) → …`. That is a lifetime `∀` around the row entry: the shape of BoLo's `withbor` callback, `∀'a ⊏ ⊓Δ. …`, and of Xie et al.'s named handlers (below). <br>• E2b and E3d build a value before its handler exists and use it under that handler. So the row variable is instantiated at a row that names a lifetime bound later. That needs either the lifetime introduced before the value is built, with the later handler's extent instantiated at it, or a row variable of kind `Life → Row`. <br>• Neither is in Law 1 as RESTRUCTURE §4.2 states it [synthesis] | **open**, not checked |
| D2.c10 | (iii) | decision 59's state passing shown to be X.2's round trip (p10 §5.1 X.2's cost: "not a second mechanism"), so that an answer borrowed from control-handler state at `'h` is a reborrow of the unfolded cell. Otherwise D2.c5 holds only for answering handlers, whose state I4 lends | **open** |
| D2.c11 | (i) | an `answering` class in `ConservativeWB`'s guard. Under D2.c4 answering operations are row layers, so `AbortRows` excludes them, and p14's coupling 2 no longer holds by construction (§1.4 item 7) | to change (device) |
| D2.c12 | (ii) | OQ-28's rule at `U C` (`p10:L.3`, T2, #173), if rc §3.7's edge holds: that is, if the reading in "OQ-28 under D2a" below fails | conditional (§1.4 item 13) |

Xie et al.'s named handlers, the precedent D2.c9 cites: `withvec : ∀α μ. (∀η. () → ⟨vec^η | μ⟩ α) → μ α` (p10 §1.11).

**Sacrifices relative to D1.** D2a gives up D1's sacrifices less OQ-29, which it takes for handlers with one live answer. OQ-28 stays among them only by the reading below (D2.c9); if that reading fails, D2a takes OQ-28's rule (D2.c12) and gives up OQ-56's borrow form and placement parity alone. D2a gives up no program D1 carries, given D2.c9. It adds risks to S1 (D2.c3), to the type language (D2.c9) and to resume (D2.c8).

**OQ-28 under D2a** [synthesis, unchecked].
- Three edges call for boxes: chain 2 (§1.3), P2's R5 edge, and `p12:N6` → `p10:L.1`. They are edges of capabilities as values.
- D2a keeps callbacks and κ as first-class thunks (`p14:V2`), and takes from N6 only its escape check (AS1).
- A thunk whose row names an extent cannot leave that extent, by that check.
- E1′'s stored closure and E9's κ are typed at the outer row, which names no extent of the catching handler.

So D2a needs no more of OQ-28 than D1, provided D2.c9 holds: where O2 boxes a stored callback, O3 binds its extent. rc §3.7 says otherwise: rows of lends need "everything O2 needs at Core", the outlives rule at `U C` among them. That is §1.4 item 13. If this reading fails, D2a takes D2.c12, and OQ-28 moves from D2a's sacrifices to its additions (§8, §9).

**The SIB bridge.** rc §5 and §3.7 list a bridge from SIB to Core among O3's needs. It is the route by which EffModelRel's proofs (`safety`, its laws) would be reused. D2a states and proves its results at Core and reuses nothing from SIB, so it does not take the bridge. It pays for S1 at extents at Core instead (D2.c3; §1.4 item 13).

**What D2 gains, by tier:**
- tier (i), as D1+B4: OQ-1 is settled by construction; S4 and D1.h1 cover the language's answering handlers directly; the answering encoding's cell is gone (`log-outside` 1 → 0, as the `*-native` programs show);
- tier (ii): AS1 is B7 at row entries; S3 gets a second route, by outlives (D2.c6);
- tier (iii): OQ-29 becomes available, for handlers with one live answer, and the exclusivity of answers borrowed from handler state is B6, for control handlers too with D2.c10.

### 5.4 Cuts

As D1+B4, plus:
- **Install** (I-c): every site opens `'h`, and its row entry carries `'h`.
- **Transit** (T-b): an answer may be a borrow at `'h`. At the next stop caught by the same handler, the frozen share less those views lies in `[α_answer]`. That is X.2's round trip: `AntiFrameW` (6.66), and 6.150's lift at the handler's state cell.
- **Resume** (R-d): Law 2 at extents (D2.c8).
- **Effect safety** (S-d): an operation of `n` reaches a live handler because `'h_n` is live (B7 at row entries).

**Admissibility at a stop** [synthesis].
- Ghost end needs, at each stop, the frozen share less the views to lie in `[α]` for each internal lend (GhostEnd step 1; OQ-56's text).
- An inner answering handler's state lend is such a lend. An operation type that named a frozen inner extent would carry a view of that state out of `[α]` when its argument goes up.
- D2.c2 restricts operation types to their own site's extent. Under static names an operation of an inner site is caught by that site, inside the segment.
- So no argument that crosses a stop names a frozen extent. That is why D2.c2 must be a checked conjunct.

**Away from the cuts.** The row algebra carries extents (D2.c3), and callback types carry extent binders (D2.c9). Both put a lifetime inside the effect algebra. They stay clean only if extents are read at install, transit and resume, and never by `∼` or `has`. If S1 has to reason about extents, the two algebras touch outside the cuts. That is the smell D2.c3 and D2.c9 guard. D2a also inherits whatever OQ-8's placement of Law 2 brings (§4.2).

### 5.5 Hard tests at extent-carrying rows

The (S) properties:
- S0, S2, S4, S5 and S6: as D1 (the bridges, S6's route). S2 and S3 ride on FL at W, as in every tier-2 design (§2.5).
- S1: open again at extents (D2.c3).
- S3: as D1, with a second route by outlives (D2.c6).
- The laws of handling: as D1.h1. As under D1+B4, they cover the language's answering handlers directly.
- Theories and models: as D1.h4.
- `I4a` at `.any`: as D1. An answering lend that spans a control stop is an internal lend, so it rides on Law 2, and at extents on D2.c8.
- OQ-29's programs: open.

The (E) programs, by reading RESTRUCTURE §1.6 [synthesis; none checked]:

| program | where its callbacks are written | what D2a needs beyond D1 |
|---|---|---|
| E1, E1′, E2a | inside the handler of every label they perform | nothing: the extent is in scope |
| E2b (`compose`) | `asyncCb lw` outside the `wait` handler that the composed closure is later called under | D2.c9, the later-bound form |
| E2c (`retryP`), E2d (`sumGen`), E10 (`retryR`, `timeoutR`) | the higher-order function installs its callback's handler inside itself | D2.c9, an extent binder around the callback's own entry |
| E3a–c, E3e–g | the platform's operations, at the top | nothing |
| E3d (`handleL logL`) | `logL` built before the per-observation handler | D2.c9, the later-bound form |
| E4, E5, E7, E8 | bodies inside their handlers | nothing |
| E6 (`fwrap`) | the callback lacks `fwrap`'s label, so `fwrap`'s extent is in no callback type | nothing |
| E9 (`stash`) | κ stored and resumed after its handler returned; its type is at the outer row | nothing beyond D1: the catching handler's extent is not re-chosen (D2.c8) |

### 5.6 Reuse, tier 2, lowering, novelty, risks

- **Reuse.**
  - **The answering-handler facts are about the borrow encoding** (§3.4), which D1's surface emits:
    - `handle_is_shift` (a type identity);
    - `translate_typed` and `effect_safety` (PAPER, System Ξ's fragment);
    - `capability_not_outlives` and `escape_refused`;
    - `twoBlocks_refused`;
    - `op_tail`, `op_answer` and `handle_fold`.

    Under D1+B4 and D2 these say something about native `hnd` only through `I4Typing` and a run correspondence. A unary correspondence, in every evaluation context of a reached configuration, suffices for A's run-level properties and D1.h1's laws. `I4c` (binary) is needed only to substitute one form for the other inside open programs [synthesis].
  - **Borrow facts that discharge effect-side obligations under D2a, and not under D1:**
    - B7 (6.60) at row entries discharges AS1. D1 discharges AS1 by `[handle]`'s `n ∉ Σ`, with the elaborator's SF check, which is decided and not built (p12's AS1 row). Whether B7 also replaces the SF check is not checked;
    - B7 gives S3 a second route, by outlives (S-d, D2.c6). D1's S3 comes through FL (S-e), so this adds a route, not a discharge that D1 lacks;
    - B6 gives the exclusivity of answers borrowed from handler state, Ante's rule (b). That obligation arises only under OQ-29, so D1 does not owe it.
  - **Against them,** D2a owes D2.c3, c8, c9 and c10, all open, and D2.c5's `AntiFrameW` at W; perhaps also D2.c12.
  - **Net** [synthesis]. Of the three facts, one (AS1) discharges an obligation D1 also has. One (S3) duplicates a route D1 has. One (answer exclusivity) discharges an obligation that only OQ-29 creates. For them D2a takes on four open items. So by concrete reuse per open item, D1 and D1+B4 still rank ahead of D2a.
- **Tier 2.** As D1, plus answers borrowed from handler state (OQ-29), for handlers with one live answer at a time.
- **Lowering.** Answering handlers become native `hnd`, lowered by C4 with no allocation. Extents are erased. The class carrier is the entry's bound (`p13:C3`).
- **Novelty.**
  - Effect safety for control operations, as outlives, in a calculus with exclusive borrows.
  - A machine-checked "one exclusive borrow per handler" (Ante's rule (b)): "would be new" (Ante deep dive, novelty item 3; p10 §1.1).
- **Risks.**
  - Condition (4) at extents (p2 §4).
  - Extent binders in callback types (D2.c9): not in Law 1.
  - Law 2 at extents (D2.c8): tables read under the substitution.
  - `AntiFrameW` at W, and the handler-state instance of 6.150's lift. D1's lift (D1.i5) comes first.
  - Decision 59's passing as X.2's round trip (D2.c10).
  - rc §3.7's edge (§1.4 item 13): if §5.3's reading fails, D2a takes OQ-28's rule (D2.c12).
  - `twoBlocks_refused`: System C's aliased stateful capability needs its state behind control (SecondClass P5).
  - HandlersAsBorrows precondition 1 (FnMut) would bite if capabilities were captured by closures called many times. It is avoided here, because operations go by label.
  - The surface elaboration is one more lemma, with two views of one thing to keep in step.

### 5.7 D2b — capabilities as values

**Choices.** As D2a, except that the kernel types effects by capability values (`rc:O2-lt`, with `O2-g`), and A's label-based programs are reached through an elaborating instance. No menu writes this kernel out; the table is my reading of the menus' O2 entries [synthesis].

| id | addition, relative to D2a | evidence | status |
|---|---|---|---|
| D2b.o1 | a handler site binds a capability value: `Mut 'h S` with its co-operations for an answering site, and a lend of the extent carrying the site's name for a control site. Computation types carry no row. Static per-site names stay as the machine's prompts (SPEC §19) | rc §1.2, §5; HandlersAsBorrows §2 | a new kernel typing; `CDerives`' effect rules restated |
| D2b.o2 | `ourInst` elaborates A's label-based terms. A callback that performs the label of a handler it is passed into takes that capability as a parameter (System Ξ's rule Def), for E2c, E2d and E10, with a typing lemma for the elaboration | rc §1.2, §3.8 | new |
| D2b.o3 | boxes (`p14:V3`, `p10:L.2`) or the outlives rule at `U C` (`V4`, `L.3`), for E1′, E2b and E9. This closes OQ-28, at T2 (#173) | chain 2; p2 §5.1 R5; `p12:N6` → `p10:L.1` | forced |
| D2b.o4 | for E2b, by reading: a quantifier over what a stored callback asks of the context it later meets. That is a row on stored callbacks, which is `rc:O3`'s other form (§2.3) | rc §0.1, §1.4 | [synthesis], unchecked |
| D2b.o5 | the class grade `rc:O2-g` (`p13:C3`); without it the un-specialised fallback is the worst class, and `p14:W3` has nothing to bound | rc §0.2, §5 | a new former |
| D2b.o6 | S1 at our instance through the elaboration: Yoshioka's (1) and (2) as facts about capability sets and lifetimes (p2 §0.1, R5 row) | p2 §5.1 R5 | a different bridge, not checked |

**Shared with D2a:**
- the extent (`p10:L.4a`, forced under capabilities);
- the relation re-indexed by the lend stack (D1.i3);
- B4 + B2 (+ B3);
- X.2 with D2.c10;
- OQ-29 (D2.c5);
- D2.c8, since capability types name the extent as D2a's row entries do;
- D2.c11.

**Gains over D2a.**
- No effect annotation on called-only callbacks (contextual polymorphism, rc §5).
- AS1 is B7 by construction.
- IO bundles are native (rc §3.8).

**Costs over D2a.**
- D2b.o2, o3, o5 and o6, and o4, which brings back a row on stored callbacks. D2b.o3 is D2.c12 made unconditional.
- Aliased stateful capabilities are refused unless their state sits behind control (`twoBlocks_refused`).
- The hard test bites hardest here. Effects are borrows throughout the typing, so A's properties hold of D2b only through the elaboration, where `ourInst` must exhibit an effect algebra and handlers as models. Otherwise D2b is the borrow calculus with an effect-like surface.

**Why D2a ranks ahead, on cost** [synthesis]. By the menus' edges, D2b needs what D2a needs for stored callbacks: D2b.o4 is O3's row on stored ones. On top of that it needs an elaborating instance, boxes or L.3, a class grade and a second S1 bridge. Nothing in the menus excludes D2b.

---

## 6. D3 — rows and carried lends

**Choices.** As D0, plus:
- `i2:M2` (`p10:X.3`): lends stay open across the stop, and the stop condition is relativised;
- `p10:L.6b` with `p10:X.5` (the async read);
- `p2:R4` in its erasable variant (`EA_EScpR`), for L.6b's masking (§1.3);
- OQ-44 (b) or (c), and OQ-57 (b) or (c);
- `p14:V7` or `V4` for a κ that holds carried lends beyond its handler;
- K.1 at W with `held`, so K.2 is not needed;
- `p13:P1`.

### 6.1 The delta from D0

| id | addition | evidence | status |
|---|---|---|---|
| D3.k1 | the relativised stop. Conjunct 40 becomes "the visible frames and records at entry, plus those handed on in `held`". `↭` is relativised off the nil slice (`carryW`'s shape: the carried cells are taken out at both ends by `ResU.delDom`, 6.56's restriction). This is a kernel definition change with a SPEC entry (BRIEF §5, critic) | `carryW` meets `UpdRefl`, `UpdOwn`, `UpdSeq`, `UpdReclaim` (`status_carryW`) | to build |
| D3.k2 | replacements for 6.50 (`UpdOutlives`) and 6.27 (`UpdLendBack`) at held entries, and every Core consumer of `↭` re-proved (FIX-RUN-END §1 table) | `not_updOutlives_carryW`, `not_updLendBack_carryW` (proved) | **open** |
| D3.k3 | 6.65 lends in `held`: `TW` gains a 6.65 record (OQ-44 (b), a kernel change), or σ splits (OQ-44 (c)) | `entryRecorded_mut` (probe): conjunct 37 forces an entry | open |
| D3.k4 | the closing list τ, as a `closer` field on σ's entries (OQ-57 (b)) or a split σ (c); (a) is a defect under ONEW | FINDING-3: τ cannot be read off the full stack | open |
| D3.k5 | exclusivity at a stop: `TI` over the visible and held frames (`HoldsChain`) | `not_holdsInjective` (at a non-arising resource) | **open** |
| D3.k6 | 6.66 at a stop (`OpenFrame66`) | `anti_handOn_needs_invariant` | open |
| D3.k7 | no copy out of κ's share in the relation (WorldW FINDING-1) | FINDING-1 | open |
| D3.k8 | `∀`-operations (`p10:L.6b`): an operation type quantified over a lifetime, instantiated at the lend and masked at its end. This changes A's signatures (S0), and `AdmEff`'s `ClosedLife` for the quantified operations | — | new construct |
| D3.k9 | `p10:X.5` at a stored κ: a passed-up view is consumed back by both of κ's entries (resume and cancel), so the lend cannot end while the view is out | — | no Lean |
| D3.k10 | a scheduler's queue holding κ at lifetimes it cannot name needs lifetime existentials in data, or loan-set types (`p14:V7`). No menu spells this out | — | I have not derived it |
| D3.k11 | the extent (`p10:L.4a`) and D-ORD (FINDING-2) | as D1 | open |
| D3.k12 | **scoped rows for the masking** (`p2:R4`, erasable). <br>• S1 adds Def. 7.1's condition (3), and Def. 7.6's condition (4) at lifetime arguments. Only `EA_EScpR` meets (1)–(4) (Yoshioka §7.3). <br>• `∼` changes from first-match lookup equality to an inductive equivalence that swaps distinct names only, so row variables no longer commute. <br>• `[handle]` removes one occurrence, and its `n ∉ Σ` premise is removed, which changes Core's rule. <br>• D1.a4's `NoLift` and `OneSigPerName` are false here; (3) and (4), as theorems, replace them. <br>• Another reading [synthesis]: L.6b's masking may generalise the label's lifetime at the lend's end, rather than lift it, as Lucassen–Gifford masking does (survey §1.4 B1: "masking an effect behaves like a lifetime ending"), and as Ante's `Mutate 'p` is discharged "once the function signature … no longer references `'p`" (p10 §5.2 L.6). Then condition (3) does not arise, but (4) still does, and an erasable simple-row algebra (Yoshioka Ex. 7.8, Thm 7.9) is the least change. `∼` still changes | p2 §5.1 R1, R3, R4; p12 §5 N3 row; p10 §5.2 L.6 | **open** |

**Sacrifices.** OQ-29 (unless combined with D2), and placement parity (`p13:P1`).

**Gains over D1.**
- `asyncRead` in its borrow form, with D3.k8–k10 and k12.
- A value whose type mentions a frozen lend's lifetime is held across stops with no re-derivation, so there is no Law 2 and no O15.2.
- OQ-28's rule, which D3 takes for carried lends (`p14:V4`, or `V7` over `V3`/`V4`).
- rustc's model, with a proof.

### 6.2 Cuts

| cut | law |
|---|---|
| install | the extent, as D1 |
| stop | hand-on: open 6.64 frames, 6.65 lends and 6.150 records are recorded in `held`; `Upd` is relativised; the nil slice stays pinned (FIX-RUN-END) |
| transit | operation types may mention the lend's lifetime (`L.6b`); a passed-up view comes back through κ's entries (`X.5`) |
| resume | refold inside the held entries at the same lifetimes (K.1 at W with `held`); D-ORD |
| cancel | each held entry is closed by its printed exit on the cancel path (τ) |
| placement | a stored κ whose held entries outlive its handler carries their loans (`V7`) or a bound (`V3`/`V4`); a move copies κ's value and changes no location (§1.4 item 11) |

**Away from the cuts.** Two places:
- `↭` changes for *every* run off the nil slice. The run-end relation is a borrow-algebra object. Under D3 it depends on whether a stop is in progress, and every consumer of it is re-proved.
- Lifetime-quantified operations and their masking enter the row algebra (D3.k8, k12). So S1 reasons about lifetimes.

These are the largest smells among the designs.

### 6.3 Hard tests, reuse, tier 2, lowering, novelty, risks

- **Hard tests.**
  - **A: not as D1.**
    - S1 is reopened at scoped rows, with conditions (3) and (4) (D3.k12).
    - S0's signatures carry lifetime-quantified operations, and `AdmEff` loses `ClosedLife` for them (D3.k8).
    - Law 1 is re-proved over the scoped rows' `∼`.
    - D1.h1's `TailLaw` loses the hygiene premise that `[handle]`'s `n ∉ S` supplied (p11 §3 item 1). Scoped rows replace it by occurrence counting [synthesis].
    - The answering class is as D1 (D1.h2). Theories and models are as D1 (D1.h3, D1.h4).
    - S2 and S3 ride on FL at the relaxed world, as in every tier-2 design (§2.5).
  - B1: FL at the relaxed world.
  - B2: `AdequateOfLaws`'s hypotheses hold in `carryW`-shaped worlds, but FL's printed route needs D3.k2.
  - B6: `HoldsChain`.
  - I: `Arises` with things held; `Tier2Programs` and `asyncRead` at the wider `Adm`; AT17 by §1.4 item 11 under M2.
- **Reuse.**
  - WorldW's resource-level hand-on and exit for 6.64, 6.65 and 6.150 (probe).
  - The printed exits on every path.
  - `ewpTS_ewpW` (Core embeds into the draft, probe).
  - D3 loses the reuse of Core's run-end laws off the nil slice, conservativity's cheap route (W1 at Core's `↭`), and the S1 proof at `orowRF` (`rowAlgSafe_orowRF`).
- **Tier 2.** Everything D1 carries, plus `asyncRead` (D3.k8–k10, k12) and closures holding a lend with no re-lend.
- **Lowering.** The same code as D1 (p13 §5). The async read hands the platform an address. Masking is static (an index shift; p13 §6 interactions).
- **Novelty.**
  - rustc's model (borrows live in a saved frame) with a soundness theorem. None exists: no mechanised `Pin` with coroutines (i2 §1.5; survey §6 item 8).
  - Ante's H2 extended to a stored κ (Ante deep dive, novelty item 1).
  - RustBelt-style tokens owned by κ (`p10:L.7`), unpublished.
- **Risks.** D3.k2, k5 and k6 are each named in a WorldW or FIX-RUN-END finding. D3.k10 is not in any menu. D3.k12 reopens S1 and changes Core's `[handle]`. P14's every-type embedding is hardest here (p14 W2).

---

## 7. Variants that cut across the designs

### 7.1 The one-shot cell: linearity not built twice

`p8:8.3` / `p14:V5`. κ carries a location allocated at the catch and freed by its resume or cancel. Then S6's two halves come from B:
- a second use meets a freed cell and is stuck, which B3 excludes;
- an unused κ leaves its cell allocated, which B4's empty memory excludes.

P8/P5's words: "In a linear core, both halves of P8 come from B2 and B4, which are already proved for today's rules" (p8 §5.1 8.3).

Its costs:
- **S4 restated.** `capture` becomes a relation on configurations, and the catch, resume and cancel laws hold up to steps that touch only the κ cell (RESTRUCTURE §1.5).
- **B re-run.** B1–B5 are re-run at the machine, and `BumpSim` must account for κ cells.
- **The lowering.** It must not allocate the cell. That needs a simulation from the machine with cells to the target without them (p13: "a store per resume unless ghost").

The variant composes with every design. The choice is the user's (AGREE Q9).

### 7.2 D2 with D3

This is the full lead-axis design. P10/P9 (p10 §5.3): "X.2 and X.5 are the two directions of one reborrow across a suspension. Under capabilities both are reborrows of one object, which may make them one statement." It buys `asyncRead` and OQ-29 together. It costs both deltas, and both changes to A's algebra (§2.5). Its cuts are D3's, plus D2's transit at `'h`.

### 7.3 Pinned placement

`p13:P2` with `i2:T4`. It gives Rust parity (Z4a against a pinned frame), at the cost of a placement rule. A κ cannot migrate after placement, which bears on threads. It is also AT17's route if §1.4 item 11's reading fails.

### 7.4 Outer lifetimes in operation types

`p10:L.6c` widens D1's `admClosedOp` with no new construct (p10 §5.2): an operation type may mention the lifetime of a lend outside the borrow. Under ghost end, admissibility still holds, because outer lends outlive the internal `α`. It does not carry `asyncRead`, whose lend is the borrow's own.

### 7.5 The laws of handling, theories, and models and comodels, in done

- **The laws of handling.** `TailLaw`, `AlgLaw` and `EtaHold` (`A.UnaryLaws`, D1.h1). Laws first and the hard test require non-vacuous laws in done (§2.1). What stays the user's, on axes H, F and K, is their form: run-level (F.3), in the world (F.2), or an equivalent. Whether they are in is not open.
  - They are run-level facts about `hnd` and Core's machine (F.3), so they cost about the same in every design. Under D3's scoped rows, `TailLaw`'s hygiene premise changes (§6.3).
  - Under D1+B4 and D2 they cover the language's answering handlers directly. Under D1 and D3 they cover them only through D1.h2.
  - They are laws of the handling construct. They make no handler a model of a theory.
- **Theories.** D1.h4: equations writable in signatures (OQ-22 (a)), and a model obligation per handler. It costs the same in every design, since it concerns signatures and clauses, not lends. It is D1.h4, not D1.h1, that makes "handlers as models" non-vacuous.
- **Models and comodels.** `p14:B3` (D1.h3) is the signed-off item 2. Every design can take it, and with `p14:B2` its two forms are provably one. Under the free theory `IsModel` and `IsComodel` are vacuous. With D1.h4 they are the per-handler obligations, and for an answering handler the comodel carries the obligation (D1.h4 (c)).

---

## 8. Comparison

| | D0 tier 1 | D1 rows + ghost end | D1+B4 one install mechanism | D2a rows of lends | D2b capabilities as values | D3 rows + carried lends |
|---|---|---|---|---|---|---|
| tiers of capabilities as borrows (§5.1) | none | none | (i) | (i), (ii), (iii) | (i), (ii), (iii), with capability values in place of rows | none |
| distance from today | one law (the row `∀`) and the bridges | D0 + the extent, Law 2, W at Core's stop | D1 + §18 emitting `hnd` for answering handlers (D2.c4) + an `answering` class in W1's guard (D2.c11) | D1+B4 + extents in rows and callback types, Law 2 at extents, OQ-29 | D2a with capability values in place of rows, an elaborating instance, boxes, a class grade | D0 + the extent, a relativised stop and `↭`, held entries, τ, `∀`-operations, scoped rows |
| kernel definitions changed | two typing rules (the row `∀`) and one relation clause; `ClosedLife` as a rule of the effect typing (D1.a8) | D0's, + `[handle]`'s extent; the spanning rules (today's constants at wider rows); **the logical relation re-indexed by the lend stack**, with Core as its σ=[] instance, every compatibility lemma of `fundamentalC` restated, and every consumer of `vC`/`cC` re-pointed (D1.i3; OQ-58). The stop is unchanged | D1's. §18's elaboration changes; the kernel does not | D1's, the re-indexed relation included, + `CTy.eff` layers with extents; `AdmEff`'s `ClosedLife` replaced by "own extent only"; + an outlives rule at `U C` if D2.c12 applies (§1.4 item 13) | D2a's, the re-indexed relation included, + capability types in place of rows; boxes or an outlives rule at `U C` | D0's, + `wpG`'s conjuncts 37 and 40; `Upd`; `TW` 6.65 records or a split σ; the relation at W with `held` (OQ-58); `∼` and `[handle]` for scoped rows |
| A's object | today's | today's | today's | extents in row entries and callback types | capability sets, through an elaboration | lifetime-quantified operations; scoped rows |
| A's (S) and (E) at done | given the bridges and S6's route; S2 and S3 from FL at `coreW` | the same; S2 and S3 ride on FL at W (§2.5) | as D1 | as D1, + S1 at extents (D2.c3); E2b–d, E3d and E10 need D2.c9 | + an S1 bridge through the elaboration; E1′, E2b and E9 need boxes | + S1 with conditions (3) and (4); Law 1 over scoped rows; S2 and S3 ride on FL at the relaxed world |
| laws of handling | S4's reductions in done; `A.UnaryLaws` with D1.h1 | the same | the same, and they cover the answering handlers directly | as D1+B4 | as D1+B4 | as D1, with `TailLaw`'s hygiene changed |
| handlers as models | vacuous: no equations in signatures. Non-vacuous with D1.h4, which costs the same in every design | the same | the same; an answering handler's obligation falls on its co-operations | as D1+B4 | as D1+B4, through the elaboration | as D1 |
| the language's answering handlers | A's only with D1.h2 | the same | A's directly (`hnd`); their borrow facts through D1.h2's correspondence | as D1+B4 | as D1+B4 | as D1 |
| B holds | at `coreW`: σ=[] proofs + adequacy + `BumpSim` | at W with Core's `↭`; FL at W rides on Law 2, with 6.150's lift for `withload` (D1.i5) | as D1 | as D1, + B7 at row entries, + `AntiFrameW` at W and 6.150's lift at the handler's state cell (D2.c5, D2.c10) | as D2a | at W with a relaxed `↭`: D3.k2, `HoldsChain` |
| concrete reuse | high | highest: every borrow guarantee at Core's stop; tier 2 is the printed 6.64/6.65 proofs per resumption; the encoding's answering facts | as D1; the encoding's facts reach native `hnd` through D1.h2 | D1's, + three borrow facts: B7 for AS1 and for a second route to S3, and B6 for answers borrowed from handler state. Against them D2.c3, c8, c9 and c10, all open (§5.6) | below D2a | medium: the printed exits at resource level; 6.50/6.27 consumers re-proved; S1 reopened |
| non-trivial cuts | resume (`Ext`), cancel | install (extent), stop (ghost end), resume (re-lend), cancel | D1's; install also carries the answering site's state lend | + transit (answers at `'h`), resume at extents | as D2a, + capability transport at every call | install, stop (hand-on), transit (lends), resume (refold), cancel (τ), placement (loans) |
| interaction away from the cuts | none known | none if Law 2 is naturality or sits at `U`/`contShare`/`KapRel` (OQ-8's options 1 and 2). Under option 3, a resume obligation in every `⊸` and `∀` clause of the relation | as D1 | D1's, + extents in the row algebra and in callback types | effects typed by borrows throughout | `↭` off the nil slice; lifetime-quantified operations in the row algebra |
| targets it meets once built | tier 1 (`I.Tier1 J₁`) | done (AT17 by §1.4 item 11) | done, as D1 | done + OQ-29 for handlers with one live answer; + OQ-28's rule if D2.c12 applies | done + OQ-29 + OQ-28's rule | done at a wider `Adm` and row form + `asyncRead` + OQ-28's rule |
| sacrifices beyond decided ones | `Tier2Programs`, `reconB′`, + D1's | OQ-56's borrow form, OQ-28, OQ-29, placement parity | as D1 | OQ-56's borrow form, placement parity; OQ-28 by §5.3's unchecked reading (§1.4 item 13) | OQ-56's borrow form, placement parity | OQ-29, placement parity |
| the hardest open item | S6's route | W's `U`, `⊸` and `∀` clauses under one quantifier (OQ-8); FL at W at the borrow-constant row read at σ·y (#275) with OQ-58, and at `[handle]` with a lend open (#278); then GFP's induction | as D1 | + D2.c8, D2.c9, OQ-29 | + the elaborating instance; D2b.o4 | `HoldsChain`, 6.66 at a stop, replacements for 6.50/6.27, scoped rows |

**If OQ-8's option 3 is forced** [synthesis]. Law 2 then puts a resume obligation into every `⊸` and `∀` clause of the relation, which is an interaction away from the cuts. D1 and D1+B4 carry it, and so do D2a and D2b, which inherit Law 2. On the cuts criterion:
- only D0 meets "two algebras with interactions only at cuts";
- D1 and D1+B4 keep their rank against D2a, which has the same binder-clause obligation plus extents in the row algebra and in callback types;
- D3 has no Law 2, but it changes `↭` for every run off the nil slice and puts lifetime-quantified operations into the row algebra. By count of places away from the cuts, one against two, D1 still ranks ahead of D3.

**A's dependency on B** [synthesis]. In every tier-2 design A's S2 and S3 at `J₂` ride on FL at the design's world (`p2:S-e`; §2.5): W for D1, D1+B4, D2a and D2b, the relaxed world for D3. So a failure of FL at a rule costs A's safety and effect safety for the programs that use that rule, as well as B's (§11, failure (a)). This is shared, so it does not reorder the tier-2 designs. It does separate them from D0, whose S2 and S3 rest on FL at `coreW` alone. `p2:S-f` would take S3 off this dependency at the cost of A-level typing rules and a syntactic subject reduction for configurations (§2.5); no menu takes S2 off it.

---

## 9. The sacrifices, feature by feature

Each row below is one feature a design may give up. The rows are independent, except where a row says otherwise, so this is not a chain. Two measures order them, and they disagree:
- what is lost: programs and targets;
- what is saved: proof.

**Decided.** Multi-shot is ignored (decision 63). It saves `unr` at W, and costs nothing the user asks for.

**Not available as a sacrifice: free theories only.** That is, signatures with no equations, so that every handler is a model. "Laws first" is decided, and OQ-22 is constrained toward equations in signatures (§2.1). Free theories would cost the theory-specific laws Laws first names ("exceptions, state and linearly used state, nondeterminism, generators"), effect-dependent laws beyond the pure row (A₂'s `EffDepLaws`), and handler correctness beyond S4's reductions. So D1.h4 is in every design. What stays open is its form, and which theories carry equations first.

**Defaults and open questions, assumed by every design** (§2.1). None of these is a decision, and none distinguishes the designs:
- binary laws and AS3–AS5 (a default): saves a binary BoLo relation;
- higher-order operations (not now): saves operations that take computations, and rank-2 row polymorphism;
- rank n (OQ-13's question): saves polymorphic arguments used at two rows;
- effects in finalisers (OQ-7 (a), open): saves a suspension inside a cancel;
- generative instances (as built under decision 57): saves confinement formers (#173).

**The features designs give up.**

| feature | programs and targets lost | proof saved | given up by | taken by |
|---|---|---|---|---|
| OQ-29: answers borrowed from handler state | Ante's rule (b): handlers that hand out one borrow into their state at a time, control handlers included. No target in done. Arenas with many live allocations ("arenas are nested handlers", 04-decisions §5 A1) need a finer rule, which Ante's H3 defers; OQ-29 (b) as D2 takes it does not deliver them, so every design loses them | the handler-state instance of 6.150's lift (the lift itself is D1's: D1.i5); `AntiFrameW` at W; decision 59 as X.2's round trip (D2.c10); the extents in types that OQ-29's answers need (tier (ii): D2.c1–c3, c8, c9) | D0, D1, D1+B4, D3 | D2a, D2b |
| placement parity (`p13:P2` with `i2:T4`) | no program. One heap allocation per spanned place, so Z4a against a pinned Rust frame fails on tier-2 programs (Z4b holds), against the zero-cost target L3 read literally | T4's placement rule; κ stays movable after placement (threads) | D1, D1+B4, D2a, D2b, D3 | the variant §7.3 |
| OQ-28: an outlives rule at `U C`, or a `[gen]` rule | a borrow callback cannot return a closure or κ that owns a resource it made; no `U C` value is boxed at a lifetime (`thunk_not_outlives`). Today's kernel already has this limitation | T2 (#173): 6.60's `U` case at every extension (OQ-58), or T14.4's coinduction | D0, D1, D1+B4; D2a by §5.3's unchecked reading (§1.4 item 13) | D2b (boxes forced); D3 (`V4`, or `V7` over `V3`/`V4`); D2a if D2.c12 applies; any design may add it |
| OQ-56's borrow form (keep R-CLOSEDOP) | `read(&mut buf)`, the lead-axis async read with the buffer lent to the operation. It is written by ownership (`read(buf) -> (n, buf)`), with the owner hoisted, or re-borrowed after each resume | the stop change (D3.k1–k7); lifetime-quantified operations and scoped rows (D3.k8, k12); `p10:X.5` at a stored κ (D3.k9) | D0, D1, D1+B4, D2a, D2b | D3 |
| self-referential suspension | `Tier2Programs` (`at02`, `at04`, `at12`, `at17`, `genSelf`) and `reconB′`, the operator's shape | W, Law 2, the extent, D-ORD, the spanning rules (6.150's lift among them), `CancelCloses` | D0 | D1, D1+B4, D2a, D2b, D3 |

OQ-29's saving does not include [TR] 6.150 lifted to resuming tables: D1 needs that lift for `withload`'s spanning rule whatever OQ-29 decides (D1.i5).

**By value lost**, the order is:
1. **OQ-29** is the next cheapest after multi-shot. No target in done needs it, and as D2 would take it, it covers only handlers with one live answer at a time.
2. **Placement parity** costs no program, but it costs the zero-cost target on tier-2 programs, and every tier-2 design pays it.
3. **OQ-28** costs a limitation today's kernel already has.
4. **OQ-56's borrow form** costs the lead-axis program shape, and that shape has workarounds.
5. **Self-referential suspension** costs the most.

**By proof saved**, OQ-56's borrow form saves the most of any single feature: with it, the stop condition never changes. Self-referential suspension saves more, but it is the floor (D0).

**The step from D3 to D1** gives up two features, each with its own program cost in the table:
- **OQ-56's borrow form.** It saves the stop change, scoped rows and X.5.
- **OQ-28's rule.** D3 must take it, because a κ holding carried lends needs a bound. D1 may leave it open. Its saving (T2) does not depend on the stop, and D1 can take OQ-28 alone at T2's cost. OQ-28 concerns a `U C` value that crosses a borrow scope or enters a lifetime box (§1.4 item 5), which arises in every design, with or without a change to the stop (§4.1's OQ-28 row).

Placement parity is not part of the step, because D3 gives it up too.

**The step from D1 to D0** gives up self-referential suspension, and saves the whole of tier 2.

**The step from D1 to D1+B4** gives up no feature. It adds tier (i) of capabilities as borrows at the cost of D2.c4 and D2.c11 (§5.2).

Done already makes the OQ-56, OQ-28 and OQ-29 sacrifices, and A₃'s corpus omits tier 2. Completion-based I/O APIs that take owned buffers are a precedent for OQ-56's workaround [unverified: from memory, not read for this chapter].

---

## 10. You're just missing …

Between today and done under D1 stand two laws, one proof route, and wiring. Between done and the user's hard test stand four more items, which decided items require (§2.1).

1. **Law 1 (A's side): the row `∀` is the intersection of its instances.**
   - The rules: `[allR-I]` and `[allR-E]` at `U` and `!U`, Curry-style, with a value restriction.
   - The relation: `I.ovalW` at `U(∀ρ:k. C)` relates a value when it is related at every admissible instance, on the same term.
   - FL at open judgements: `I.FLOpen`, and `fl_of_flOpen`.
   - Lacks kinds come from `RowCon.adm`.
   - Risk: low. The relation already reads a row context as the family of its instances, and rows are erased (RESTRUCTURE §4.2).
   - It gives E1, E2, E6 and E10.
2. **Law 2 (the resume cut): re-lend.** A lend ended at a stop is re-lent at a fresh lifetime beneath the resumer's list, and κ's frames are related at that lifetime.
   - **Proved at GE:**
     - for data and for closures the borrower builds (`RBodyT`, `RBodyC`, `tv_thaw`);
     - at the stacked relation, for the `U` clause (`force_RLs`, `thunkF_RLs`) and the stack steps at every stack (`stack_step_other`, `stack_step_reborrow`, `stack_step_imm`);
     - at the arising-guarded relation, for the `lam` and `allI` rows (`lam_RLa`, `allI_RLa`; PR #285, unmerged).
   - **Open:**
     - W's `U`, `⊸` and `∀` clauses under one future-world quantifier, with the `U`-clause thaw at the guarded relation (OQ-8; §11's statement 0);
     - GFP's induction;
     - the guard read from `TW` (OQ-45);
     - the borrow-constant row read at σ·y (#275), with Core as W's σ=[] instance (OQ-58);
     - the reborrow followed by the outer continuation (#276);
     - `[handle]` with a lend open (#278; `AllCross` at constant `true` only);
     - `effThen` at a frozen frame's cancel;
     - the cancel path over a 6.64 frame (p10 §5.1 X.4);
     - `unfoldN`;
     - [TR] 6.150 lifted to resuming tables, for a `withload` spanning a stop (D1.i5). Its added step `ptoImm_dup` is proved and the lift is not written. It is the untranscribed printed lemma in the run-up of the borrow-constant rows (GhostEnd's report lists for steps 3f–3i; i2 §5 M1 *Cost*). GhostEnd classes it as work, not an unknown.
   - Where Law 2 is placed decides whether D1 meets "two algebras with interactions only at cuts" (§4.2).
   - It gives `Tier2Programs`, and with them A's S2 and S3 at `J₂`, which ride on FL at W (§2.5).
   - It is the one genuine unknown of tier 2.
3. **The proof route: S6 (`ContUse`).** κ's use counts on runs, by `p8:8.4`'s coupled obligation, by `8.2`, or by the one-shot cell if the user admits it (§7.1). This is the one genuine unknown on A's side, and every design shares it.
4. **Wiring, each item a named lemma:**
   - the bridges D1.a5;
   - `ClosedLife` as a rule of the effect typing (D1.a8);
   - `[handle]`'s extent (D1.i1);
   - W with `held = ([],[])` and `Upd` Core's, and the relation re-indexed by the lend stack, with Core as its σ=[] instance (D1.i3);
   - D-ORD (D1.i4);
   - the spanning rules as today's constants at `RowSpan`, `SpanWithload` with 6.150's lift (D1.i5);
   - `FramesW` in the `Relend` form (D1.i6);
   - `CancelCloses`, with OQ-57's τ read as σ's stack index (D1.i7);
   - AT17's move (D1.i8);
   - SF in the elaborator;
   - `Rejects`' inversions.
5. **Shared with every design:** `Adequate` at every platform and the drive, and `BumpSim` (OQ-43).
6. **For the hard test, beyond done:**
   - the laws of handling, `TailLaw`, `AlgLaw` and `EtaHold`, at our instance (D1.h1). These are three run-level laws, each a join of traces at a deterministic machine;
   - `I4Typing` with a run correspondence (D1.h2), so that the language's answering handlers are A's handlers. Under D1+B4 they are `hnd` themselves, at the cost of D2.c4 and D2.c11 (§5.2);
   - models and comodels of one signature (D1.h3), the signed-off item 2. They are vacuous without the next item;
   - the theory side (D1.h4): equations writable in signatures (OQ-22 (a)), and a model obligation per handler that claims a theory. For an answering handler the obligation falls on its co-operations.

So "you're just missing two laws" holds for done. The hard test adds the three laws of handling, two groups of structural lemmas, and the theory side, which is equations in signatures with one model proof per handler that claims a theory.

**Sacrificed:** OQ-56's borrow form, OQ-28, OQ-29, placement parity, multi-shot and binary laws. All of these are already outside done. Free theories are not available to sacrifice (§9).

---

## 11. The tractability probe (D1)

**What it asks.** Is FL at W provable for exactly the rules `genSelf` and `reconB′` use, at one world, with `TW`'s guard, with one future-world quantifier, and with no relation family beside W? The probe is the same for D1 and D1+B4: by reading their definitions, neither program installs an answering handler.

**What is proved, and what is not assumed.**
- At the unguarded stacked relation a thunk thaws at a fresh lend by construction. The `U` clause of `vRLs` is `RelendableS`, and `force_RLs`, `thunkF_RLs` and `relendableS_thunk` are proved (GhostEnd step 3h). This is GhostEnd's O15.2 for closures, at the stacked relation.
- The guarded relation `vRLa` is "D16.1 guarded at `U`, `⊸` and `∀`" (02-experiments §0). So once the guard is read from `TW`, the thaw is not a transport, and statement 0 proves it again.
- Statement 2 puts a quantifier at `⊸`. Without statement 0, W would carry quantifiers at both `U` and `⊸`, and nothing would check that they cohere. That is the shape of BRIEF §8 pattern 4.

**The programs only D1 must carry** (against the fallback D0):
- **`genSelf`, as built** (`Targets/I/Programs.lean`).
  - Its state cell is lent `Mut`, as `withbor` (2), and read through `withswap` before each of two resumed yields.
  - Its handler is outside the borrow, and nothing is installed inside it.
  - `genSelf_eval` checks its run.
  - It needs statements 0, 1 and 2.
- **`reconB′`, to build.** It is `resumer wait (borrow imm cfg (λb. retry (λ_. *b; wait (); *b))) ; timeout (borrow imm cfg (λb. (λ_. *b; wait (); *b) ()))`, with `retryR` and `timeoutR`:
  - the scheduler (`resumer`) and `timeout` are *outside* the borrow (§1.4 item 10);
  - `retry`'s handler is installed *inside* the borrow, and `wait` passes through it to `resumer`;
  - the second wait is cancelled under `timeout`, whose cancel ends the borrow's owner frame. That borrow is `Imm`, so this is the cancel path over a 6.64 frame, which is not built (p10 §5.1 X.4).

  It is the only program here that needs Law 1 and Law 2 together, and it is the operator's shape. Its `retry` body captures the `Imm` view `b`; whether it types at `retryR`'s `!U` body is part of building it. By reading RESTRUCTURE §3.4's term, each read `*b` completes before the next `wait`, so no `withload` spans a stop, and the probe does not exercise 6.150's lift (D1.i5). It needs statements 0–4.

**The statements, in order.**

0. **W's value clauses, fixed together.**
   - One Lean definition of W's relation at `U`, `⊸` and `∀`. The arising guard is read from `TW` (statement 1's guard), and the future-world quantifier is placed once: at `U`/`contShare`/`KapRel`, or at the binder clauses (OQ-8).
   - At that guarded W, prove the `U`-clause thaw: a thunk related at W thaws at a fresh lend, the analogue of `force_RLs` and `thunkF_RLs`. Do not assume it transports from `vRLs`.
   - BRIEF §5 item 4 marks the placement "OPEN: A Lean statement settles it, not prose". 02-experiments §1.3 lists "whether `U` and `⊸` take the same quantifier" as open. This statement settles both.
1. **The guard from `TW`.** W's arising guard is read from `TW`, not from GhostEnd's `TabAtS`. That is OQ-45's first question: is the lend table a `TW` invariant at every depth (`tabAt_of_TW`, T-ARISE.0, not in Lean)? It holds for one lend (`wpG_tabAt`) and for one entry (`wpG_tabAtS_one`). Then `below_excluded` and the `lam` and `allI` rows (`lam_RLa`, `allI_RLa`) are re-proved at that guard.
2. **The borrow-constant row at σ·y, with Core as W's σ=[] instance.**
   - The statements are `SpanWithbor2 W OutJ.core admClosedOp .any` and `SpanWithbor1 W …`: the 6.65 and 6.64 constants at resuming rows.
   - With the guard at `⊸`, the row reads its callback at σ·y (#275). That is `callback_ext`'s shape (`vRLk`, PR #287).
   - Its proved pieces are:
     - the exits at a stop (`wpG_M_frameX`, `wpG_I_frameX`);
     - the entry at a fresh lifetime (`fresh_frame`, H4);
     - the stack steps (`stack_step_*`);
     - the cancel path for 6.65 (`withborR_compat`).

     `relend_of_openD` at a stack joins them.
   - The cancel path over a 6.64 frame is not built (p10 §5.1 X.4). `SpanWithbor1` at an affine row needs it, and `reconB′`'s second borrow uses it.
   - Together with it, OQ-58 (a): Core's `vCE`/`cC` is W's relation at σ=[] at every type, thunks included. `vRLk` has no σ=[] lemma.
3. **`[handle]` with a lend open** (#278). This covers two things:
   - a handler installed inside the borrower, whose frame passes the lender's stops (`reconB′`'s `retry` passes `wait` to `resumer`);
   - stops handled inside the borrower: `effHandle`'s inner-stop clause, which GhostEnd step 3f lists as not built.

   `AllCross` must be relaxed beyond constant `true`, since `retry`'s `exn` does not cross the lend.
4. **`[allR-E]` at W with a lend open.** This is Law 1's elimination inside the borrow: `retryR` is instantiated at a row inside `reconB′`'s borrow callback.
5. **The programs.**
   - `AcceptedAt J₂ genSelf Flag (inj₂ ())`, with `J₂` holding `SpanRule2`.
   - `AcceptedAt J₂ reconB′ …`, with `J₁`'s `∀` and `SpanRule1`. Its runs are exhibited, as `genSelf_eval` does.
6. **A sample of GFP's remaining rows: `effThen` at a frozen frame's cancel.**
   - The row: a finaliser frame the borrower wrote, frozen in κ with a lend open beneath it, unwinding when an outer handler cancels κ, at an inner affine row.
   - GhostEnd step 3f classes it non-routine: "a frozen frame unwinding at a cancel, at an inner affine row. Not derived; no obstruction verified". Step 3f's work list has "`[then]`'s cancel of a frozen frame".
   - Neither program uses it. Statements 0–4 meet the cancel cut only through the borrow constants' own owner frames, so this row tests whether their pattern extends to a frame the program wrote [synthesis].
7. **A cheap side check.** `Targets.NotVDenNaturalArises` (`Targets/I/Binder.lean`). It tells whether naturality is available for *live* lends. That bears on OQ-8's option 1, on K.2's binder form and on D3, not on the probe's statements.

**Success.**
- Statements 0–4 are proved at one world, with `TW`'s guard, one future-world quantifier, and no relation family beside W.
- Both programs are accepted.
- The placement the proofs used is recorded, with its consequence for the cuts criterion (§4.2, §8):
  - at `U`/`contShare`/`KapRel`, or as naturality: D1 and D1+B4 meet "two algebras with interactions only at cuts";
  - at the binder clauses: they do not, though they keep their rank against D2a and D3.
- Statement 6 is proved, or its obstruction is machine-checked as in (a).

Then the rules these two programs use have their laws at W, and Law 1 is low-risk. Statement 6 gives one sample of whether the pattern reaches a row outside the two programs. The rest of FL at W is still not shown: GFP's induction over the remaining rows stays open, and one sample does not bound them. The remaining rows are:
- `unfoldN`;
- the other `*U` constants at W, `SpanWithload` among them, which needs 6.150's lift (D1.i5);
- the reborrow followed by the outer continuation (#276).

**Failure.** Each failure must be machine-checked (method.md):
- **(a)** A statement is refuted by an elaborated `def … : Prop` at a configuration that arises in `TW`, with every hypothesis discharged. What D1 loses depends on the statement:
  - statements 0 and 1: their failures take the forms (b) and (d) below;
  - statement 2: ghost end cannot carry a borrow constant across a stop, and D1 keeps only tier 1;
  - statement 3: D1 loses handlers installed inside a borrower that suspends outward (`reconB′`'s shape);
  - statement 4: D1 loses row-polymorphic higher-order functions inside a borrower;
  - statement 6: D1 loses user finalisers frozen with a lend open beneath them, and the probe's pattern is shown not to reach every row.

  In each case A loses too, not only `Tier2Programs`. A's S2 and S3 at `J₂` ride on FL at W, by `p2:S-e`, their only route there (§2.5). So `J₂` must drop the refuted rule, and A's (S) properties hold only for what remains. At `J₁` they are unaffected.
- **(b)** A statement is provable only with a second relation family, or a guard beside `TW`. Stop and report (BRIEF §10; §8 pattern 4).
- **(c)** OQ-58 fails. Core must then be redefined (OQ-58 (b)), which is a kernel change with a SPEC entry.
- **(d)** Statement 0 holds only with different future-world quantifiers at `U` and at `⊸`, which no single definition of W reconciles. W would then carry two quantifiers, a relation family beside W in all but name. Stop and report (BRIEF §8 pattern 4).

**The fallback.**
- **D3** for tier 2. The closure keeps its lifetime across the stop, so there is no re-lend, and neither Law 2 nor O15.2 arises. The cost is the stop change (D3.k1–k7) and scoped rows (D3.k12).
- **D0** if D3's stop change also fails.

Under every outcome, D1's A-side work (Law 1, the bridges, S6, D1.a8 and the hard-test items D1.h1–h4) carries over to D0 unchanged. It carries over to D3 except where D3 changes A: S1 at scoped rows, Law 1 over their `∼`, and the signatures (§2.5).

---

## Review findings addressed

An adversarial review raised seven major findings. Each is taken up where the text stands:

1. **6.150 at a resuming table is D1's, not only OQ-29's.** D1.i5 and D1.i2 carry the lift (`withload` spanning a stop); it is in §10 Law 2's open list, §4.8, §4.4 and §8's B row. §3.4 splits the row, and §9, §5.1 and §0 keep only its handler-state instance as OQ-29's.
2. **rc §3.7's O3 edge.** §1.2 carries it in full. §1.4 item 13 records how D2a meets each of O2's Core needs, that D2a does not take the SIB bridge because it proves its results at Core, and the one disagreement, OQ-28, with D2.c9's reading marked unchecked. D2.c12 adds OQ-28's rule to D2a's delta if that reading fails; §5.3's sacrifices, §8 and §9 follow it.
3. **Three tiers of capabilities as borrows.** D1+B4 is tier (i). §0, §5.1 and §8 state the tiers and their costs alike.
4. **The theory side.** §2.1 has Laws first and OQ-22. D1.h4 (equations in signatures, a run-level model obligation per handler) is a hard-test item in every design. D1.h1 is called the laws of handling throughout, and D1.h3 vacuous without D1.h4 (§0, §4.3, §7.5, §10). Free theories are not offered as a sacrifice (§9).
5. **A's dependency on B.** §0, §2.5 and §4.2 say that S2 and S3 at `J₂` ride on FL at W. §2.5 names and costs `p2:S-f` as the route that would free S3. §0's ranking, §8 and §11's failure (a) carry the dependency.
6. **"Only at the cuts" is conditional.** §0, §2.5, §4.2, the ranking and §8 make it depend on OQ-8's placement of Law 2.
7. **The `U` clause is settled in Lean.** §11's statement 0 fixes W's `U`, `⊸` and `∀` clauses together at `TW`'s guard and proves the thaw there. Success records the placement used, and failure (d) covers different quantifiers at `U` and `⊸`.

---

## Sources

Read for this chapter:

- **The brief and the effects-state files.**
  - `docs/effects-state/BRIEF.md` (all).
  - `04-decisions.md`: §1 K1–K18, §2 C1–C10, §5 A1–A2, §6 L1–L7, §7 F1–F3, §8 T1–T4, §10 P1–P11.
  - `05a-open-questions-1-34.md`: the preamble, cross-cutting F1–F5, OQ-1, 3, 8, 9, 13, 14, 19, 20, 22, 23, 28, 29, 34, and the summary.
  - `05b-open-questions-35-68.md`: OQ-44, 45, 48–52, 56–61, 68.
  - `06-bolo-machinery.md`: Part 1.
  - `02-experiments.md`: §0, §1.1–§1.3, §4, §5.
- **The notebook.**
  - `intro.md`, `system-a.md`, `system-b.md`, `interaction.md`, `decisions.md`, `register.md`, `method.md`, `SUMMARY.md`, `literature.md`.
  - `foundations/*`, `properties/*`, `side/multi-shot.md`, `design-space/axes.md`, `tracks/log.md`, `tracks/worldw-batch1.md`.
  - The nine menus in `prior-art/`.
- **The targets** (`experiments/Targets`):
  - `AGREE.md`, `Targets/Status.lean`.
  - `RESTRUCTURE.md`: §0–§4.4 (including §1.6's (E) programs, §3.1–§3.7, §3.4's tier-2 programs and §4.1's bridges with `effSafeDriveOfFL`), §6, §7, §9.0, and §Unresolved U.1–U.4.
  - `Targets/I/Combined.lean` (`Pins`, `Combined`), `Targets/I/Interface.lean` (`I4a`, `I4Typing`, `I4c`, `admClosedOp`, the spanning rules with `SpanWithload`, `FramesW`), `Targets/I/Programs.lean` (`genSelf`, the rejections, `Tier2Programs`), `Targets/I/Binder.lean`, `Targets/Instance/Core.lean` (`AdmEff`, `ClosedLife`), `Targets/Base/Rows.lean` (declarations).
  - `Targets/A/UnaryLaws.lean` (all), `Targets/A/System.lean` (`OpSig`), `Targets/A/Soundness.lean` (heading), `Targets/A/Binary.lean` (heading, `EffDepLaws`).
- **The kernel** (`~/repos/borrow-core`):
  - `Core/EffDefs.lean` (all).
  - `Core/EffRules.lean`: rows, `ewp_kappa_resume`, `ewp_kappa_cancel`, `KapRel`, `ewp_handle`, `kTy` (line 976), the clause types.
  - `Core/EffBorrow.lean`: heading, `Row.Unwind`, the constants' types.
  - `Core/Handlers.lean` (all).
  - `Core/Fundamental.lean`: the effect constructors of `CDerives`.
  - `Core/Embedding.lean`: heading.
  - `Core/Types.lean`: `VOutlivesR`, `VOutlives`.
  - `SPEC.md` §18 and §19: *Motivation*, *Kinds of operation*, *Names*, *Lowering*, *Open*.
  - `Backend/README.md`: *Representation*.
- **Experiments.**
  - `experiments/HandlersAsBorrows/README.md` (all).
  - `experiments/GhostEnd/README.md` (all: the results table, steps 0–4, the report lists).
  - `experiments/GhostEnd/GhostEnd/Handle.lean`: heading. `experiments/GhostEnd/GhostEnd/ImmLend.lean`: declarations.
  - `experiments/CoeffectsStrict/CoeffectsStrict/Context.lean`: `thunk_not_outlives`.
- **Other research.**
  - `~/repos/borrow-core/research/effects/ante-deep-dive.md` (all).
  - `research/effects/survey.md`: TL;DR, §1.1–§1.11, §2.1 P1–P15, §4, §6.

Cited through the menus, not re-read here: the primary literature in the menus' source lists.
