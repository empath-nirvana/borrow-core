# l_lang salvage: kernel techniques, proof burden, and literature

*For borrow-core; companion to [Salvage from l_lang](l-lang-salvage.md). This report merges three read-only readers of `/Users/johnthompson/repos/l_lang` (the μ/ν kernel reader, the proof-burden reader and the bibliography readers) and checks them against borrow-core. Nothing was built, edited or run in either repo. The borrow-core checkout is on `experiment/optics` at `a572f16`, and I checked coverage against that working tree.*

**Before reading, note two things:**
- **How to read the tags.** A claim marked **[unverified]** comes from a reader or from an l_lang doc, and I did not re-check it. Line numbers into l_lang are the readers'. I checked borrow-core line references myself where I cite them.

---

## 1. Kernel proof techniques

### 1.1 What the l_lang kernel actually proved

l_lang never gave μ or ν a semantics. `LambdaLC/` proves syntactic type safety only: `Typing.safety` at `Corollaries.lean:137`, which is preservation plus progress. It has no logical relation, no fixed points over predicates and no step-indexing. `Head.cutFix` (`Semantics.lean:547`) makes divergence part of the kernel on purpose.

- **μ is iso-recursive**, a region-tagged row with an `occ` back-edge. `rollRow`/`unrollRow` are justified by preservation alone, together with one "survives unroll" lemma per type predicate (`Cart.unroll`, `DropCo.unroll`, `residentEmpty_unroll`).
- **There are three fixpoint rules**, and preservation is the only thing proved for each:

  | Rule | What it is | What is proved |
  |---|---|---|
  | `fixlam` | unrestricted recursion | preservation only |
  | `fixlam_nu` | Nakano / Simply RaTT shape: the self binder sits at delay ≥ 1, and coercion only goes upward | preservation only; productivity is not a kernel theorem |
  | `fixlam_mu` | a sized descent family plus a usage-0 base case | preservation only; termination is not a kernel theorem |

  Because unrestricted `fixlam` sits alongside the other two, the kernel cannot state what the "certified" rules guarantee.
- **There is no ν former.** `Disc.guard` plays no role in typing. The lazy ν value was marked "NOT designed". `DropCo`'s docstring says a ν former would break value-finiteness.
- **Productivity and descent-termination live only in toy spikes outside the build:**
  - `Spikes/ForkCAlgebra.lean`: contractive maps on `ℕ → A` streams have unique fixpoints, and `typing_implies_productivity`.
  - `GuardedDefAdequacy.lean`: the guard check implies contractivity.
  - `SemiContinuityMu.lean`, where `usc_closes_top` is literally `hUSC w hlim` and so discharges nothing.
  - `SExtentArithmeticMu.lean`: recursion on `n − i` cannot be typed.

  Two spikes, `DroppableCoind` and `NuValueDrop`, no longer compile at HEAD. **[unverified: reader grep only]**

### 1.2 What transfers, by borrow-core open item

**Deciding syntactic predicates at μ types, with the seen-set coinduction from `DropCo`. This is the one technique that transfers directly.**
- *The technique* (`Typing.lean:199`, `:271`, `:393`):
  - Entering a region adds its depth to `seen`.
  - `occ i` holds only if `i ∈ seen`. That is the guardedness check; the l_lang comment says leaving it out is a known soundness bug class, and cites Rust's coinductive solver.
  - There is no function arm.
  - The discharge lemma `substCap_discharge` is short and uses only induction on the derivation: if the body holds under `insert target seen` and the replacement holds under `seen`, the substitution holds under `seen`.
- *Where it fits:* deciding predicates such as `NoMut`, "holds no resource", persistence or `VOutlives` at `μX.A` by structural induction, with no fixed point needed. The nearest open issues are **#10** (`Affine` at μ), **#9** (widening promotion to persistent contexts, which needs "persistent" at μ) and **#32** (mutually recursive data).
- *Limit:* `DropCo`'s consumer (`droppable_footprint_co`) is sound only because values are finite. The technique applies to μ, and **not to ν**.

**A general `νX.C`.** l_lang has no semantic construction to copy.
- borrow-core already has the right machinery. `delayRel` is the union of post-fixed points of a monotone `delayF` (`DelayRel.lean:38`). `docs/scope-recursion.md` §3 already recommends `νX.B : CTy` with an environment and monotonicity as the positivity condition.
- The one thing l_lang offers is a **rule shape** for corecursion beyond `unfoldS`/`fixD`: `fixlam_nu`, where the self binder is at delay ≥ 1, the body is typed now, and coercion only goes upward.
  - This bears on the open item in `scope-recursion.md` ll. 314–319: a direct `fix : !U(U(D A) ⊸ D A) ⊸ D A` is "not derived, not verified", and needs either parametricity or `▷`.
  - `fixlam_nu` is the `▷` option. The guarded-recursion literature in §3 is where that route is worked out, and it re-introduces step-indexing, which decision 7 excludes.
- l_lang's own review (`PLAN-nu-touches.md` §14) warns that a type-level guard can be forged unless it is paired with a judgment-level delay column. **[unverified]** This is a design warning, not a theorem, and borrow-core has no judgment delay column (see §2, lesson L1).

**`WpChainCommutes` (whether D's greatest fixed point equals the limit of its approximations).** l_lang has **no technique** for this.
- *What l_lang has:* `ForkCAlgebra` gets "limit = fixpoint" only through contraction on total streams. `delayF` is not contractive, and getting contraction would mean step-indexing.
- *The reusable framing:* `finite_needs_no_usc` says a consumer stated observation by observation never needs the limit property. borrow-core's `D` adequacy is already stated per `n` (`scope-recursion.md` "Adequacy, restated"). So the first question is whether any consumer actually states something at the limit.
- *My own reading, not derived.*
  - `DelayApprox.lean`'s reduction is the standard Kleene-style argument: "gfp = ⋂ₙ Fⁿ(⊤)" holds when `F` preserves intersections of decreasing ω-chains (ω-cocontinuity). `WpChainCommutes` localises that condition to `wpTS`.
  - `DelayApprox.lean` already names the only non-commuting connective: the `∃` over the ghost witness `(ρ', ρp, …, ls')`. Its own `exists_forall_of_finite` / `not_exists_forall` pair frames the question as finite versus infinite witnesses.
  - The sized-types literature (Abel 2008, "semi-continuity"; Hughes–Pareto–Sabry as the failure mode) names this obligation. That literature usually avoids it by indexing approximants transfinitely, and doing so does not give the ω statement.
  - I have not derived `WpChainCommutes` and have not verified that any obstruction to it is real.

**Folds beyond `FShape`.** Nothing transfers.
- l_lang's general route was unrestricted `fixlam`, which was admissible only because its theorem ignores divergence. borrow-core proves termination and leak freedom, so that route is closed.
- `fixlam_mu` is sound only up to preservation. It needs a size known statically, since nothing converts `size none` to `some k`, and it cannot type arithmetic descent.
- `FShape` exists because `travR`/`tR` are generated per shape (`Core/FoldReuse.lean`), and l_lang has nothing that generalises that.

**Handler compilation and grades on `!`.** The kernel offers no technique here. What it offers is cost data, covered in §2 under L6 and L7.

### 1.3 Why the rest does not transfer

- **l_lang's safety was syntactic.** Everything it proved about recursion is preservation, which borrow-core's semantic fundamental property (FP) subsumes and does not need to re-derive.
- **Its semantic content was contraction on total streams**, which is step-indexing in miniature. Decision 7 rules that out.
- **Its ν was never designed**, and its drop-safety depended on values being finite.

---

## 2. Anatomy of the proof burden

**Scale.** All figures are the reader's, from grep and `git log`, and arm counts are about ±10%.
- `LambdaLC/` is about 98.8k lines in 120 files. Of that:
  - the kernel spine is about 19k;
  - the emitter and its harness are about 26k;
  - `Interp`, a second checker, is 5.9k;
  - spikes are 31.5k, in 68 files outside the build.
- `docs/` holds 153k lines of markdown.
- Git history has 621 commits over five weeks.
- The shape of the judgment: `Tm` has 20 constructors, `Typing` has 27 rules and 8 indices, `Head` has 16 arms and `ECtx` has 14 frames.

### 2.1 Lessons, with measurements, what borrow-core already does, and what is left

| # | l_lang lesson (measured) | borrow-core guard already in place | Remaining risk |
|---|---|---|---|
| L1 | **Every judgment index is a tax on every rule, even when inert.** Adding mode μ cost +1,334 / −693 over 26 commits, and it ended up "a cache, not an axis". Adding delay δ, defaulted to 0 and read by nothing, cost +887 / −705. Inversion patterns reached a median width of 15 in `Preservation`, and `app_inv` returns a 25-tuple. | `CDerives Δ Γ e j` has 4 indices, and grading lives in types and the model. | #23 (graded modalities) and #27 (temporal order) are both tempting places to add a fifth index. |
| L2 | **Syntactic preservation costs pairs of rules, not single rules.** One effect-scope former (the runner) cost 987 lines at landing, about 3.9k lines of spikes before it and about 1.2k in widenings. `plug_decomp` is 636 lines and `head_preservation` 754. | `fundamentalC` spends one line per rule. There are no inversion lemmas, no substitution lemma over derivations and no `ECtx` decomposition, and each `*_compatX` stands alone. The stream former cost 566 lines, 209 of them example programs. | Anything that *inverts* `CDerives` brings this back: checker completeness (#16), a syntactic cut or substitution lemma, or a lowering proof that inverts typing (#14, #15). |
| L3 | **Non-syntax-directed subsumption leaks into every inversion.** `Inversion.lean` has 57 `subDelay`/`subSize` arm references, and 15 call sites needed a merged `subHead` lemma. | The FP never inverts, so `immSub`/`mutSub` cost nothing today. | The same trigger as L2. |
| L4 | **One former carrying several jobs pushes distinctions into premises.** A single row former carried data, codata and context. The 27 rules have about 56 side premises, `projAt` alone has 5, and the `pos` bit was the only thing separating record from variant. | Separate formers (14 `VTy`, 7 `CTy`), with records, variants and places derived (decisions 5 and 6). | Widening folds by adding premises. `foldImm` already has 7 premises. |
| L5 | **A generalisation built alongside its instances grows the kernel.** `GenericCut` added about +1,800 lines net, and the consolidation that was supposed to follow never landed. The two changes that shrank the kernel were delete-first: RDEL (−1,837 / +95) and removing `Ty.unit` (net −171). | none specific | `delay` and `stream` mirror each other name for name (`etaD`/`etaS`, `candD`/`candS`, `DelayRel`/`StreamRel`), with 17 arms each. A third fixed ν former is about +500 lines. |
| L6 | **A grade algebra outside Mathlib becomes hand-written arithmetic in every rule.** l_lang's interval grade has no bottom and proves `¬(0 ≤ 1)`. The four proof files make 1,019 uses of 83 hand-written lemmas, plus 124 direct monotonicity calls. | Today `!` carries no grade. | **#23 is the highest-risk item.** |
| L7 | **Flags on a rule move case splits into every consumer.** `handle` is parameterised by `Depth × Bool`, is 126 lines long and routes through about 12 helpers, and `plug_decomp` splits on it three times. | Decision 15: the shallow handler is primitive and the deep handler is derived. | Adding a depth or reentry flag later for the convenience of lowering (#18). |
| L8 | **Per-type folds with no theorem saying what they guarantee.** One example: `DropCo` holds unconditionally on an opaque atom, so a compiled program can use memory after freeing it while the kernel theorem still holds (L-199). **[unverified]** | `adequacyC` states no use-after-free, no double free and no leak. | none known |
| L9 | **A second checker is a second artifact to keep in sync.** `Interp.synth` is 5.9k lines, and its gaps were catalogued by hand. | Decision 12: `checkProgram_sound`. | none known |
| L10 | **Proofs outside the build rot.** `FnRowDropSafety` rotted to `sorryAx` on 5 of 8 results. Productivity was only ever proved in a spike. μ/ν was re-architected twice. | The FP can state productivity observation by observation. | The reader measured `experiments/` at 64.8k lines against 74.1k in the library, and found a second copy of `Core` under `experiments/Core/Core/`. **[unverified by me]** |

### 2.2 Cost of a new former in borrow-core (per the reader)

| Addition | Approximate cost |
|---|---|
| New `VTy` former | 83–155 match arms across `Core/`: `int` 91, `mu` 106, `bang` 101, `tensor` 126. About half are in `Types.lean` (rename, subst, `Cl_*`, `occ_*`, `immG_*`, `noMut_*`, `VOutlives`), and there are two parallel interpretations, `vCE` and `vShapeE`, that need agreement lemmas. |
| New syntactic predicate on `VTy` | 14 arms, plus its rename and subst lemmas |
| New `CTy` former | 17–25 arms |
| New `CDerives` rule | 2 one-line arms plus one compat lemma |

### 2.3 Rules of thumb for Core's growth

1. **Never add a `CDerives` index "defaulted, for later".** Put a new coordinate in a type former or in the model. That covers grades (#23) and temporal order (#27, kept inside `LifeCtx` and the lifetime model).
2. **A generalisation lands in the same change that deletes its instances.** When general `νX.C` lands, `delay` and `stream` become abbreviations in that commit. Building the general former alongside them repeats `GenericCut`.
3. **Prefer computation-side and derived formers.** A `CTy` former costs about 20 arms and a `VTy` former about 100. Derive records, variants, places and deep handlers.
4. **Widen by adding a constructor to a grammar, never by adding a premise to a rule.** For `FShape`, extend the shape grammar so that `cases` discharges the distinctions, rather than adding premises to `foldImm`.
5. **Keep proofs semantic.** Any new proof by induction on `CDerives` must be one line per rule, like `append_dead`. A proof that needs inversion is a warning sign, so budget for it explicitly (#14, #15, #16).
6. **Grades, if added, go on a modality `!_r A`** whose carrier is a Mathlib ordered-semiring instance: one with a bottom, and where `0 ≤ 1` holds. Do not put grades on binders.
7. **No rule carries flags.** Split the rule into two, or derive one from the other.
8. **Nothing lives outside the build for long.** When an experiment graduates, either delete it or build it.
9. **Every syntactic predicate needs a stated guarantee.** A fold on types needs a theorem that consumes it (compare L8).

---

## 3. Annotated bibliography

**Column meanings**
- **l_lang used?** One of: *used* (the kernel or its design cites it and depends on it), *partly*, *unused*, or *rejected*.
- **In borrow-core?** Checked by grep over the three prior-art docs, `scope-recursion.md`, `decisions.md` and `SPEC.md`. Short surnames were checked by eye, because `Abel` and `Affe` only match inside "label" and "affected"; neither work is cited.
- **First-hand?** Whether the reader recommends that borrow-core read the primary source itself. The readers used this flag with slightly different meanings, so read it as a priority, not a record of what anyone read.

Where the source l_lang docs are unreliable, that is noted in the relevance column.

### A. Recursion, codata and approximation

| Topic | Key works | l_lang used? | Relevance to borrow-core | In borrow-core? | First-hand? |
|---|---|---|---|---|---|
| Guarded recursion and productivity | Nakano LICS 2000; Guatto LICS 2018; Krishnaswami ICFP 2013; Bahr–Graulund–Møgelberg, Simply RaTT, ICFP 2019; Atkey–McBride ICFP 2013; Clocked TT LICS 2017; Capretta LMCS 2005; Møgelberg–Paviotti (guarded recursive types) | used (`fixlam_nu`, spikes) | The `▷` route for a direct `fix` on `D` (`scope-recursion.md` ll. 314–319, #12). Guarded CBPV's lift monad `μY. X + ▷Y` is the step-indexed twin of `D`. The Leakpocalypse analogy (a type-level certificate forged in a language that allows partiality) warns about codata whose `close` is a type-level obligation. | no (only RFC 3151 is cited) | yes (Simply RaTT, Capretta) |
| Sized types, approximants, semi-continuity | Abel, Semi-continuous Sized Types, LMCS 2008; Abel–Pientka ICFP 2013 / JFP 2016; Barthe et al. MSCS 2004; Hughes–Pareto–Sabry POPL 1996; Abel MiniAgda; Agda #1946 | used (`fixlam_mu`) | The closest name for the `WpChainCommutes` obligation (the limit at ω versus the gfp). Abel–Pientka's bounded interpretation is a worked template for relating ν to its approximants. The literature treats size inference as elaboration, outside the kernel. | no | **yes** (Abel 2008 was cited by URL only in l_lang, so its content there is second-hand) |
| Copatterns and codata by observation | Abel–Pientka–Thibodeau–Setzer, Copatterns, POPL 2013; Downen et al., Codata in Action, ESOP 2019 | partly (second-hand) | The natural reference for a general `νX.C : CTy` defined by observations (audit item 8, #31). | no | yes |
| CBPV records, `&`, and linear CBPV | Levy, Jumbo λ-calculus ICALP 2006; Levy CBPV thesis/book; Egger–Møgelberg–Simpson, Enriched Effect Calculus (JLC 2014, arXiv 1209.4268); Šefl–Svoboda (additives in QTT); Levy, "Thunkable implies central" | partly | EEC is the nearest published linear-over-CBPV calculus to borrow-core's core, including an additive `&` whose components share a context. borrow-core's `D` uses `&`, and `prior-art-borrow-splitting.md` ll. 62 and 76 records that no BoCa counterpart exists for `&`. | no (Levy is the design basis but is not cited in any prior-art doc) | yes (EEC) |
| CBPV possible-world store models | Levy, Possible world semantics for general storage in CBV, CSL 2002; Levy thesis ch. 7; Curien–Fiore–Munch-Maccagnoni, adjunction models, POPL 2016 (read as abstract only) | partly | The standard reference for thunk-storing variance and world extension, relevant to experiments/CBPVWorld. CFM 2016 is the categorical account of a linear CBPV with a resource modality. The l_lang referee found that the retrieved "Levy 2006" was the Jumbo paper, so the grounding label on it is doubtful. | no | yes |
| Resource CBPV and destructors | Congard–Munch-Maccagnoni–Douence, Linear Effects, Exceptions, and Resource Safety, ESOP 2026 (arXiv 2510.23517); Munch-Maccagnoni, Resource Polymorphism | unused | **The closest formal neighbour.** It is a linear CBPV with new/delete whose headline theorem is resource safety on every exit path, including exceptions. Its authors leave deriving borrowing open, and borrow-core does derive it. It bears on handlers (#18), `close` (#31) and `!` versus a resource modality (#23). | no | **yes** |

### B. Effects, handlers and runners

| Topic | Key works | l_lang used? | Relevance to borrow-core | In borrow-core? | First-hand? |
|---|---|---|---|---|---|
| Handler theory: deep versus shallow | Plotkin–Pretnar ESOP 2009 / LMCS 2013; Hillerström–Lindley APLAS 2018; Kammar–Lindley–Oury ICFP 2013; Bauer–Pretnar JLAMP 2015; Forster et al. ICFP 2017; Lindley–McBride–McLaughlin POPL 2017 | used | Decision 15. The l_lang refereed result (Thm 3.26) says shallow handling is definable exactly for equation-free theories. borrow-core's operations have no equations, so the premise holds, but adding equations would break it. **[refereed in l_lang, not re-checked]** | no | yes (Hillerström–Lindley) |
| Combining effects: sum versus tensor | Hyland–Plotkin–Power TCS 2006; Bowler et al. 2013 | partly | What predicts whether handlers can be nested is freeness. That says when stacking shallow handlers suffices. | no | no |
| Handlers combined with linearity | Tang–Hillerström–Lindley–Morris, Soundly Handling Linearity, POPL 2024 | partly | **This is the leak-freedom hazard.** A handler that drops a continuation erases a linear debt, and one that resumes it twice duplicates it; shipped Links had exactly this bug. It applies to #18 as soon as handlers can capture a context holding linear resources. | no | **yes** |
| Runners, comodels and finalisation | Ahman–Bauer, Runners in Action, ESOP 2020 (Thm 7); Power–Shkaravska 2004; Møgelberg–Staton, Linear usage of state, LMCS 2014; Uustalu 2015; Katsumata–Rivas–Uustalu LICS 2020; Garner MSCS; Leijen MSR-TR-2018-10 (deep finalisation) | partly | The published form of a `close` that is guaranteed to run. Arrays as the state comodel bears on #8 (buffers). Møgelberg–Staton is the semantics of linear state, which is what in-place `foldReuse` relies on. l_lang flagged "duplication-freedom across resumptions" as its unproved corner. | no | yes (Ahman–Bauer) |
| Abort and cancellation | Koka cfc; WasmFX §6.2; OCaml 5 one-shot fibers; Fowler et al. POPL 2019 | partly | l_lang pinned a known hole: an abort skips the runner's finaliser. Finalisers alone do not cover abort. | no | no |
| Compiling handlers | Schuster–Brachthäuser–Ostermann ICFP 2020 (Thm 5.5); Xie–Leijen ICFP 2020/2021; Sivaramakrishnan et al. PLDI 2021; Phipps-Costin et al., WasmFX, OOPSLA 2023 | partly | Schuster's full-elimination theorem needs second-class, statically known, monomorphised handlers, which matches decision 8. WasmFX is the Wasm-level target. The survey of "typed but never lowered" features supports decision 17. | partly (Schuster 2022 regions only) | no |
| Second-class values and capture tracking | Osvald et al. OOPSLA 2016; Brachthäuser et al. OOPSLA 2020/2022 (Effekt, System C); Scala CC<:, Capless 2025, Capybara 2026 | partly | Lifetime sets on `U`/`!T` play the role of capture sets. Each capture calculus was later widened by a "box" once real programs arrived. Capybara is the capture calculus closest to `Mut` exclusivity. | partly (Effekt) | yes (Capybara) |
| Obligation effects and static leak freedom | Crary–Walker–Morrisett POPL 1999 (Thm 4); DeLine–Fähndrich, Vault; Kellogg et al. ECOOP 2022; Gordon ECOOP 2017; Orchard–Yoshida POPL 2016; Igarashi–Kobayashi | unused | `adequacyC` is essentially CWM's Thm 4 plus termination. "Balance theorems are conditional on termination" is the known caveat for stating leak freedom over `D`. | partly (CWM, Vault) | no |
| Monadic encapsulation | Launchbury–Peyton Jones PLDI 1994; Moggi–Sabry JFP 2001; Fluet–Morrisett JFP 2006; Timany et al. POPL 2018 | rejected | Rules out modelling a borrow as rank-2 encapsulation. The l_lang drafts misdescribe Timany Thm 1.1 (per the referee). | partly (Kiselyov–Shan) | no |

### C. Grades, modes and adjoint logic

| Topic | Key works | l_lang used? | Relevance to borrow-core | In borrow-core? | First-hand? |
|---|---|---|---|---|---|
| Use-count grading | Atkey QTT LICS 2018; Orchard–Liepelt–Eades, Granule, ICFP 2019; Brady, Idris 2; Bernardy et al., Linear Haskell (§6.3 tail calls, §7.2 β multiplicity) | partly (the kernel's interval grade is Granule's Interval) | #23. A grade carries use count, never extent or footprint. Granule's promotion rule requires graded, not linear, assumptions. Linear Haskell §6.3 notes that borrowing blocks tail calls, which bears on explicit tail calls. | partly (Granule in passing) | yes (Granule §4/§7, LH §6.3/§7.2) |
| Effects combined with coeffects in CBPV | Torczon–Suárez Acevedo–Agrawal–Velez-Ginorio–Weirich OOPSLA 2024 (Coq); Gaboardi et al. ICFP 2016; Petricek–Orchard–Mycroft | partly | Torczon–Weirich is the published system closest to borrow-core's shape, and it is mechanised. l_lang's Lean refuted the boundary axiom `kappa_one` at affine grades, which warns against adopting the full Gaboardi law without checking it. **[l_lang spike, unverified]** | no | yes (Torczon–Weirich) |
| Graded linear/non-linear logic | Vollmer–Marshall–Eades–Orchard CSL 2025; Eades–Orchard, Grading Adjoint Logic; Hanukaev–Eades, GRASS, MFPS 2026 | partly | #23. Vollmer et al. is a graded refinement of Benton's LNL, which is the form a graded `!` would take. GRASS makes contraction availability a property of the grade. | no | yes (Vollmer et al.) |
| Substructural metatheory frameworks | Wood–Atkey ESOP 2022; Radanne–Saffrich–Thiemann, Affe, ICFP 2020; Gratzer–Møller–Birkedal FoSSaCS 2025 | partly | Ready-made templates for subject reduction. Wood–Atkey assumes a total grade algebra, so keep fractions off any substituted grade vector. | no | no |
| Adjoint logic, and garbage-freedom from modes | Pruiksma–Chargin–Pfenning–Reed 2018; Reed 2009; Licata–Shulman–Riley FSCD 2017; Jang–Roshal–Pfenning–Pientka, Adjoint Natural Deduction, FSCD 2024 (Thm 19) | partly | Adjoint ND is a natural-deduction presentation that proves garbage-freedom from modes alone. The l_lang minimal-core result "modes cannot count" (Prop 8.12) separates what a mode `!` can express from what a grade can. **[refereed draft, sketch-level]** | partly (Pruiksma–Pfenning, LSR, Jang–Pientka metaprogramming) | yes (Adjoint ND) |
| Harmony proved once over a connective schema | minimal-core §9 (Prawitz, Dummett, Schroeder-Heister, Pfenning harmony notes) | partly | A technique for keeping per-former proof obligations from multiplying (the "few formers" item). The draft's added quotations have no retrieval record. | no | no |
| Bunched logic combined with `!` | O'Hearn, On Bunched Typing, JFP 2003 (Fact 18, §6.3); Atkey λ_sep ICALP 2004; Pym–O'Hearn–Yang TCS 2004 | unused | Fact 18: a doubly closed category carrying `!` forces distribution. §6.3 is an open problem O'Hearn posed about combining a consumption category with a sharing category, which is the question when `Imm` sharing, ownership and `!` coexist (#23, #27). | partly (BI and Pym–O'Hearn–Yang cited, not these results) | no |
| Data layout from types | DeYoung–Pfenning MFPS 2022 (SNAX); DeYoung–Pfenning–Pruiksma FSCD 2020 (SAX); Downen et al., Kinds Are Calling Conventions, ICFP 2020; Chen et al., Dargent, POPL 2023; Ng 2024 | unused | #13. Representation sits on the shifts: `↓` is a pointer, `↑` a thunk, and `|A⊗B| = |A|+|B|`. Dargent is the precedent for using ownership facts to choose layout. | partly (Back to Futures only) | no |
| Closure conversion and defunctionalisation | Minamide–Morrisett–Harper POPL 1996; Pottier–Gauthier POPL 2004; Danvy–Nielsen PPDP 2001 | partly | Lowering `U`/`!T` to Wasm is exactly the choice between a tag switch and a funcref table (#13, decision 14). | no (optics cites a different Minamide paper) | no |

### D. Memory, ownership and borrowing

| Topic | Key works | l_lang used? | Relevance to borrow-core | In borrow-core? | First-hand? |
|---|---|---|---|---|---|
| Capability and location calculi | CWM POPL 1999; Alias Types ESOP 2000; Vault PLDI 2001; L3; Linear Regions ESOP 2006; ATS; Mezzo TOPLAS 2016; **Pottier–Protzenko, SNAPL 2015 retrospective** | partly | Mostly covered already. The SNAPL retrospective is new: Mezzo designed its core without sample programs, and a Coq formalisation meant to be a kernel plus extensions became monolithic. That is l_lang's failure recorded by another project. | yes, except SNAPL | yes (SNAPL) |
| Regions | Tofte–Talpin; Cyclone PLDI 2002, ISMM 2004, SCP 2006; Grossman ESOP 2002 | partly | Memory-model Q4. Documented Cyclone failures work as forcing programs. Regions allocate while borrows lend, so region theorems are not borrow theorems. | mostly | no |
| Fractions and uniqueness | Boyland SAS 2003; Bornat et al. POPL 2005; Clean; de Vries et al. IFL 2007; Marshall–Orchard OOPSLA 2024; Marshall–Vollmer–Orchard, Entente Cordiale, ESOP 2022 | partly / rejected | Low. Decision 5 settled places by disjointness. | mostly (Entente: no) | no |
| Formal Rust | RustBelt; Oxide; Stacked Borrows; Tree Borrows | partly | Covered. | yes | no |
| The Rust frontier | NLL RFC 2094; Polonius; view types 2021/2026; Dada; Descend | partly | View types' privacy and semver objections apply to exposing block leaves in signatures. | mostly (Dada and Descend: no) | no |
| BoCa/BoLo measured against the l_lang kernel | Wagner et al. OOPSLA 2025 | used | The hand-off. The list of kernel features BoCa lacks is close to borrow-core's extension agenda. | yes (the baseline) | — |
| A categorical definition of borrow | Odersky, Observers, ESOP 1992; Choudhury–Krishnaswami ICFP 2020; Matsushita–Ishii, Pure Borrow | rejected (most of the mathematics failed refereeing) | #27. What survived refereeing: non-escape is a condition on the borrower's codomain type only, with the monad outside the modality, consistent with BoLo's `[a]T`. Do not look for an equational characterisation of non-escape. | partly (Odersky abstract only; Pure Borrow) | yes (Odersky, Choudhury–Krishnaswami) |
| Invalidation safety without ownership | Gao–Parreaux, InvalML, OOPSLA 2025; Chau–Parreaux POPL 2026; Parreaux IWACO 2024 | unused | #27. A different answer to the same safety question: region atoms as effects, plus an outer-scope device built on negated effects. The open question is whether that device can be had positively, without complement. | no | yes |
| Chu, Dialectica and lineales | de Paiva TAC 17; Capucci et al. MFPS 2024; Oliva | rejected | #27. A lineale is a residuated poset-monoid. Expect inequalities, not a self-dual model. | partly (Capucci) | no |
| Scoped references in industry and dynamic handles | Rust #24292 and RFC 3151; Swift SE-0446; C# ref struct; Pony; Verona; generational indices; Qin et al. PLDI 2020 | partly | A guard-based scope is sound only if the guard cannot be leaked, and mandatory `close` is what provides that. | partly (RFC 3151) | no |
| Continuations lack a destructor (l_lang's own rustc/Miri probes) | `docs/theory/rust-soundness-check.md` and `one-rule-mobility.md` | unused | Dropping an OCaml continuation leaks its fiber. A captured continuation holding linear resources needs a finaliser (#18, #31). **[probes not re-run]** | no | no |
| Tombstones and freshness | Krebbers CH2O JAR 2016; CompCert `Memory.v`; ISO TS 6010; VST msl | rejected | #15. Tombstone identities (CH2O) versus reused addresses (CompCert) is the framing for a relation to Wasm memory. | partly (CH2O's shape, not tombstones) | no |
| Places ontology and the 317 forcing programs | `docs/theory/places-*` | unused | Low for theory. The catalogue of programs that must be admitted or refused could seed #5 and #6. | partly | no |
| Mathematics of places | nominal sets, contact algebras, Simpson independence, optics and containers | unused | Low. These are reading lists, not findings (a second-order adjudication of subagent surveys). | partly | no |
| Sequent calculus, polarity and state | Curien–Herbelin; Downen–Ariola; Sequent Core ICFP 2016; Miquey–Herbelin | partly | Low. A sequent presentation buys nothing for state. | no | no |
| FILL dependency as grade support | Bräuner–de Paiva; Clouston et al.; Choudhury arXiv 2304.03175 | partly | Low. Relevant only for multi-conclusion judgments. | no | no |
| Droppability and promotion under call-by-value | Hughes–Vollmer–Orchard §7.1; Granule issue #225; Lorenzen–Leijen ICFP 2022 §5.3 | used | Supports decisions 3 and 11: excluding closures from structural drop is what the field converged on. The owed "graded Bekić" item bears on mutual ν (#32). | partly | no |
| Numerics and data refinement | Cryptol; LLVM poison; Wasm traps; Hoare, data representations, 1972 | partly | Decision 10. Hoare 1972 is the frame for fast buffers against a list reference model (#8). | no | no |

### Leads borrow-core has not followed

Each lead below meets all three criteria: l_lang did not use it, or used it only partly; none of the prior-art docs or `scope-recursion.md` cite it; and it bears on an open item. Issue numbers come from `gh issue list` (32 issues; #26–#29 are not listed except #27).

1. **Abel, Semi-continuous Sized Types (LMCS 2008), and Abel–Pientka (JFP 2016).** These name and handle the approximant-limit obligation behind `WpChainCommutes`. There is **no issue** for it; the nearest homes are audit item 8 and `Core/DelayApprox.lean`. l_lang used the idea, but only in a spike that discharges nothing.
2. **Congard–Munch-Maccagnoni–Douence, ESOP 2026.** It proves resource safety of a linear CBPV under exceptions → **#18**, **#31**. It is also a candidate comparison point for a paper, because its authors leave borrowing open.
3. **Tang–Hillerström–Lindley–Morris, POPL 2024.** Soundness of handlers over linear resources → **#18**.
4. **Ahman–Bauer, ESOP 2020; Leijen, deep finalisation; Møgelberg–Staton, LMCS 2014; Power–Shkaravska 2004.** Guaranteed finalisation, and linear or array state as a comodel → **#18**, **#31**, **#8**.
5. **Hillerström–Lindley, APLAS 2018, and Hyland–Plotkin–Power.** The primary sources for decision 15 and for when stacking shallow handlers suffices → **#18**.
6. **Copatterns (Abel et al., POPL 2013), the Enriched Effect Calculus, and Levy's Jumbo λ-calculus.** The observation-based `νX.C` and a linear-CBPV `&` → **#31**. There is no issue for a general ν; audit item 8 covers it.
7. **Guarded recursion (Nakano; Simply RaTT; Capretta).** The `▷` alternative for a direct `fix`, and its cost of reintroducing step-indexing → **#12**.
8. **Torczon–Weirich, OOPSLA 2024; Vollmer–Marshall–Eades–Orchard, CSL 2025; GRASS; Wood–Atkey, ESOP 2022; O'Hearn 2003 Fact 18.** Grading `!` in a CBPV/LNL core → **#23**.
9. **Levy, CSL 2002 (possible worlds for general storage).** The reference for world-indexed CBPV store models; it has no issue. It bears on the CBPVWorld experiment and possibly **#15**.
10. **Gao–Parreaux, InvalML (OOPSLA 2025), and Choudhury–Krishnaswami (ICFP 2020).** Alternative accounts of non-escape and footprint → **#27**.
11. **Schuster et al., ICFP 2020 (capability-passing compilation), and WasmFX.** Handler lowering to Wasm → **#18**, **#13**.
12. **Minamide–Morrisett–Harper; Pottier–Gauthier; DeYoung–Pfenning, MFPS 2022; Dargent.** Closure and layout lowering → **#13**.
13. **Pottier–Protzenko, SNAPL 2015.** A project comparable to l_lang, on what sank Mezzo. It maps to no issue and applies to the "few formers" discipline.
14. **Linear Haskell §6.3 (borrowing blocks tail calls).** No issue. Check it before explicit tail calls meet `withbor`.

**Caveats on this list:**
- Coverage was checked by grep, and a work cited under a different name would be missed.
- The reliability of the l_lang docs varies. The handler grounding was the most carefully checked (quotations verified verbatim by a referee). `places-mathematics.md` and the `compiler-theory/raw/` workflow reports are the weakest; the l_lang `MANIFEST` says `raw/` holds eight statements later refuted.
- I read none of the primary sources myself.
