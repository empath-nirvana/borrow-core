# Coeffects: borrows, capabilities and handlers

**Question.** Andrew Wagner suggested that borrowing and effect handling are deeply related,
and pointed at coeffects. The hypothesis tested here is hers: a borrow block (`withbor`)
*provides* a coeffect (access to a resource at `'a`) for its scope, the way a handler
*discharges* an effect for its scope. The user sharpened it three ways:

- the 2×2 of data/codata/effects/coeffects;
- the claim that every handled effect carries a coeffect;
- the claim that tail-resumptive effects need only the coeffect interface.

Adopting coeffects could mean rewriting the typing judgment, so the question is whether that is
worth doing.

**Build.** `lake build Coeffects`. The library imports `Core` and `Optics` and nothing imports
it. `Paper/`, `Support/`, `Core/`, `Frontend/`, `Backend/`, `SPEC.md`, the corpus and `CDerives`
are unchanged. There are 42 theorems and definitions. Every one has `#print axioms` within
`[propext, Classical.choice, Quot.sound]`, and none uses `sorry`.

| file | contents |
|---|---|
| `Demand.lean` | the demand type `Dem U T = ∀'x ⊏ ⊓Δ. Mut 'x U ⊸ ['x] T`; weakening (`d_weakenD`); one reborrow (`d_rebAt`); **contraction by reborrowing** (`d_seqD`) |
| `Imm.lean` | the `Imm` demand; **parallel contraction by `copy`** (`d_parI`) |
| `Judgment.lean` | `KDem`, a `needs Mut U` layer; `KDem.elab` into `CDerives`; `KDem.sem` by `fundamentalC`; the providers `provide_wf` (from `Ref U`, `withbor` form 2) and `reprovide_wf` (from `Mut @a U`, form 3) |
| `Programs.lean` | a helper that needs `stdout` and never names it; `main` provides it; typed (`d_main`), every run safe and leak-free (`main_every_run`), and run (`main_eval`) |

## 1. Literature

Each source is tagged with how much of it was read, as in `docs/prior-art-sessions.md`:

- *(full)*: the whole text;
- *(sections)*: the named sections, with the rest skimmed;
- *(abstract)*: the abstract only;
- *(secondhand)*: known only through another source.

PDFs were read from the URLs listed under Sources.

- **Petricek, Orchard, Mycroft**, *Coeffects: a calculus of context-dependent computation*,
  ICFP 2014 *(sections: §1–3.5, Thm 8, Thm 27, §6)*.
  - Def. 1 is the coeffect scalar `(C, ⊛, ⊕, use, ign, ≤)`: `⊛` is sequential composition,
    `⊕` is contraction, and `⊛` distributes over `⊕`.
  - Flat systems add `∧` for λ. A body's demand "[is] split between immediate (declaration-site)
    and latent (call-site) coeffects" (§3.1).
  - The instances are bounded reuse, dataflow, liveness and implicit parameters.
  - §2.1: "coeffect systems are not trivially dual to effect systems."
  - The theorems are subject reduction and equational soundness.
  - The ICALP 2013 version *(sections)* puts the difference from effects "mainly in the (abs)
    rule".
- **Implicit parameters**, via Petricek's thesis, UCAM-CL-TR-906 *(sections: §3.2.1, Figs. 9–10,
  Thm 34)*.
  - The provider rule is `Γ@r ⊢ e₁ : τ₁`, `Γ@s ⊢ e₂ : τ₂` ⟹
    `Γ @ r ∪ (s \ {?p:τ₁}) ⊢ letdyn ?p = e₁ in e₂ : τ₂`. It "removes the bound parameter from
    the set of requirements."
  - Lewis, Launchbury, Meijer, Shields (POPL 2000) is *(secondhand)*; its PDF was not
    retrieved.
- **Brunel, Gaboardi, Mazza, Zdancewic**, *A core quantitative coeffect calculus*, ESOP 2014
  *(sections: §1–3, Thm 10)*.
  - `!ᵣA` is graded by a semiring, and promotion scales the context by `r`.
  - Its "co-handlers" are context *operations* (e.g. `next`), not scoped providers.
  - Soundness is by a realizability model with no heap.
- **Ghica, Smith**, *Bounded linear types in a resource semiring*, ESOP 2014 *(sections: §1–3.1,
  §4)*.
  - It takes the comonadic view of reusable resources, "the typical example of which is memory".
  - The scoped variable `new` is an ordinary higher-order constant of type
    `(J·exp ⊸ acc ⊸ σ) ⊸ σ`. That is `withbor`'s continuation shape, typed without any coeffect
    discharge rule.
- **Gaboardi, Katsumata, Orchard, Breuvart, Uustalu**, *Combining effects and coeffects via
  grading*, ICFP 2016 *(sections: §2.3, §3, §5 Defs 5–6 and Thm 1, §6)*.
  - Combining the two needs a graded distributive law
    `σ : Dʳ(Tᵉ A) → T^{κ(r,e)}(D^{ι(r,e)} A)` over an "R,E-matched pair" `(ι, κ)` (Def. 2). It
    must satisfy four equational axioms, and it exists only for some pairs.
  - Coeffects form a semiring; effects form only a monoid.
  - The coeffect discharge `letD` and the effect bind `letT` are separate. No construct
    discharges both, and there are no handlers.
- **Orchard, Liepelt, Eades**, *Granule*, ICFP 2019 *(sections: §2, §4.2, Thm 7.1)*.
  - It has graded necessity (Nat, Level, Interval and their products) and graded possibility
    for I/O.
  - It has no handlers: "exceptions … cannot be caught".
  - Thm 7.1 is progress and preservation.
- **Marshall, Vollmer, Orchard**, *Linearity and Uniqueness*, ESOP 2022 *(sections: §3, Thms
  4–6)*. `&t : !A` from a unique `*A` forgets uniqueness. It has no scope and no lifetime.
- **Marshall, Orchard**, *Functional Ownership through Fractional Uniqueness*, OOPSLA 2024
  *(sections: §5, §6)*.
  - `withBorrow : *A → (&₁A ⊸ &₁B) → *B` is continuation-scoped, with fractional `split`/`join`.
  - Lifetimes are "only … lexical"; there are no lifetime variables.
  - The heap model admits garbage collection, so there is no leak freedom.
  - It is not phrased as a coeffect.
- **Abel, Bernardy**, *A Unified View of Modalities*, ICFP 2020 *(sections: Def 2.1, §7.2, Thm
  7.8)*. It is a modality ringoid with a fundamental lemma of a relational, store-free model.
- **Brachthäuser, Schuster, Ostermann**, *Effects as Capabilities* (Effekt), OOPSLA 2020, TR
  *(sections: §1, [Try], System Ξ, Thms 4–5, §7.3)*.
  - `[Try]` has type `τ | (ε \ {F}) ∪ ε′`, the same shape as `letdyn`.
  - "the handler … creates a capability and binds it".
  - §7.3: effects "can also be handled either at the call-site or the definition-site. Petricek
    et al. refer to those requirements as latent or immediate". Effekt is "a combination of
    coeffects, second-class values, and delimited control", and the authors "hope to formally
    establish the relation to coeffects."
- **Brachthäuser et al.**, *Effects, Capabilities, and Boxes* (System C), OOPSLA 2022, TR
  *(sections: §1–3.2, [Try], [Region], Thms 3 and 5, §6.5, §6.8)*.
  - `[Region]`: `Γ, f :* Reg ⊢ s : τ | C ∪ {f}` ⟹ `Γ ⊢ region {f ⇒ s} : τ | C`.
  - "Handlers introduce capabilities."
  - §6.5: the capture set "roughly corresponds to a flat coeffect … the precise connection is
    unclear."
  - Soundness is progress and preservation, in Coq.
- **Odersky et al.**, *Scoped Capabilities for Polymorphic Effects* (CC<:) *(sections: §1,
  Thms 4.6, 4.8)*. A `CanThrow` capability "generated by a try expression … valid only as long
  as the try is executing"; its scope is kept by avoidance.
- **Plotkin, Pretnar**, *Handlers of algebraic effects*, ESOP 2009, and *Handling algebraic
  effects*, LMCS 2013 *(sections: introductions, §2)*.
  - Handling is by "unique homomorphisms … induced by the universal property of the free model".
  - Operations and handlers are dual as effect *constructors* and *deconstructors*.
  - The word "fold" does not occur.
- **Ahman, Bauer**, *Runners in action*, ESOP 2020 *(sections: §2, §3.2, Fig. 3, Thm 7)*.
  - Runners are comodels.
  - The rule `using V @ W run M finally F` provides a resource for a scope and finalises it, but
    "the user code does not have direct access to the file handle".
  - "runners are simply a restricted form of handlers, which apply the continuation at most once
    in a tail call position."
- **Katsumata, Rivas, Uustalu**, *Interaction laws of monads and comonads*, LICS 2020
  *(sections: §1, §3, §4.1)*.
  - The free monad `μZ. X + FZ` interacts with the cofree comonad `νW. Y × GW`.
  - A runner is a coalgebra.
  - The comonad is the *machine* that runs the effects.
- **Uustalu, Vene**, *The Essence of Dataflow Programming*, APLAS 2005 *(sections: §5.1, §6)*.
  - It lists comonads (the cofree comonad among them) and a distributive law `DT → TD`.
  - It has no provider construct, and neither "unfold" nor "coalgebra" occurs in it.
  - *Comonadic notions of computation* (CMCS 2008) was read *(abstract)* only.
- **Torczon, Suárez Acevedo, Agrawal, Velez-Ginorio, Weirich**, *Effects and Coeffects in
  Call-By-Push-Value*, OOPSLA 2024 *(sections: §1, Thms 2.1, 3.1, 3.4)*.
  - "U(F A) forms a monad and the combination F(U B) forms a comonad [Levy]". They grade `U`
    for effects and `F` for coeffects.
  - Soundness of effects and of coeffects is by mirrored logical relations, with no heap and no
    handlers.
  - This is the only "dual argument" found.
- **Not read**: Uustalu's *Stateful runners*; Plotkin–Power comodels; Katsumata's graded
  monads; Orchard's thesis; Levy, Zeilberger and Curien–Fiore–Munch-Maccagnoni on polarity;
  Scala's *Simplicitly* and *Capturing types*; Tofte–Talpin; Tang et al. *Modal effect types*
  *(abstract)*.

What the literature settles:

- **No source prints "handler discharges an effect / provider discharges a coeffect" as a
  duality.** What is printed is an identity of rule *shape*:
  - Effekt's `[Try]`, System C's `[Region]` and the implicit-parameter binder `letdyn` all
    remove one requirement from the body's set for the scope of a binder.
  - Two papers note the resemblance, and both leave it unformalized (Effekt §7.3, System C §6.5).
- **No coeffect paper has named lifetimes or an outlives relation.**
- **No coeffect paper proves leak freedom or every-run safety over a heap.** The results are
  syntactic type safety or equational soundness.

## 2. Our core read as a coeffect system

Structural coeffects in Petricek's sense annotate each variable. Flat coeffects annotate the
whole context. Here is the core, mapped:

| part of `CDerives` | coeffect reading | kind | where it lives |
|---|---|---|---|
| liveness bit of a slot | the `{0,1}` usage coeffect | structural | `Ctx` slots. `Ctx.SplitP` is `+`, `Ctx.DeadP` is `0`, `Ctx.SoloP` is `1` (`experiments/Grades`: `splitP_iff`, `deadP_iff`, `soloP_iff`) |
| persistence (§10) | the `ω` grade. `SplitP.dup` is `ω = ω + ω`, `DeadP.drop` is `0 ≤ ω` | structural | by type (`VTy.persistent`) |
| promotion `!Γ` | scaling `ω · Γ` (Brunel et al.'s promotion) | structural | `bangThunkF`/`bangThunkV`'s `Persistent Γ` |
| `[]I`'s `CtxOutlives Δ Γ a` | a lifetime-indexed necessity. Its intro rule *filters* the context (every live slot outlives `@a`); it does not scale it | flat, lattice-indexed | `boxI` |
| `Δ` and the outlives premises | scope labels ordered by `⊏`. `withbor`'s fresh `'x ⊏ ⊓Δ` is the provider's scope | not a semiring grade | `allI`, the borrow axioms |
| a borrow `Mut 'x U` / `Imm 'x U` held in a body | a **demand** on the context, discharged by the enclosing `withbor` | flat, one per borrow | the callback's binder (`Dem U T`, `Demand.lean`) |
| a capability `ref output` (§11) | an owned resource; the demand is its borrow, `Mut 'a Output`, which `read_byte`/`write_byte` take | flat | a context slot of `main`; passed explicitly |

What this shows:

- **The usage coeffect is already in the kernel.** Liveness and persistence are the `{0, 1, ω}`
  grades, and `SplitP`/`DeadP`/`SoloP` are the semiring's `+`, `0` and `1`, as the Grades
  experiment proved.
- **The borrow demand is a context slot at a scope label.** `KDem.elab` elaborates the `needs`
  layer into `CDerives` with no new rule. So "a borrow is a coeffect demand" is true, and it is
  already what `withbor`'s callback binder *is*: the callback's `Mut 'x U` parameter is the
  demanded context, and `withbor` supplies it.
- **Contraction lives in terms, not in the context algebra.** A structural coeffect needs two
  operations, `⊕` (contraction) and `⊛` (sequential composition). The kernel's context algebra
  has one, `SplitP`, used at every binary rule, CBPV `bind` included. So a `Mut` demand shared
  by `M to x. N` cannot be split by `SplitP`: that would be `1 + 1` at a non-persistent slot. It
  is contracted by a *term*, the reborrow, which `d_seqD` proves. The same holds for `Imm`, whose
  `⊕` is the `copy` constant (`d_parI`), because `Imm` is not persistent.

| demand | `⊛` (sequential) | `⊕` (parallel) | weakening |
|---|---|---|---|
| persistent `A` | `SplitP.dup` | `SplitP.dup` | `DeadP.drop` |
| `Imm 'x U` | `copy` at `'x` (`d_parI`) | `copy` at `'x` (`d_parI`) | `forget` |
| `Mut 'x U` | reborrow at `'y ⊏ 'x`, handed back (`d_seqD`) | none | `forget` (`d_weakenD`) |
| owned `Ref U` | none (used once) | none | the destructor (§12), which is an action |

  The `Mut` row's missing `⊕` is `Mut 'x U ⊸ Mut 'x U ⊗ Mut 'x U`. It is not a `CDerives` rule.
  This spike neither derives it nor verifies an obstruction to it.

## 3. The duality verdict

**Wagner's hypothesis holds as an identity of scope shape. As a duality it only rhymes.**

**What is real (printed, and built here).**
- In capability-passing style, a handler is a binder that introduces a capability for its scope
  (Effekt, System C, CC<:). That rule has the implicit-parameter provider's shape.
- `withbor`'s type is that shape exactly: `Ref U ⊸ (∀'x ⊏ ⊓Δ. Mut 'x U ⊸ ['x] T) ⊸ Ref U ⊗ T`.
  - The fresh `'x` plays the part of System C's fresh capability or region.
  - `['x] T` is its escape check, the job System C's boxes and CC<:'s avoidance do.
- `provide_wf` is the discharge rule, and `KDem` is the requirement set. Evidence: strong (two
  printed rule shapes, plus a Lean elaboration with a running program).

**What only rhymes.**
- **The fold/unfold duality.** Handlers are homomorphisms out of the free model, which is a fold
  (Plotkin–Pretnar). The "co" side printed opposite them is the runner: a comodel, or a
  coalgebra of the cofree comonad (Ahman–Bauer; Katsumata–Rivas–Uustalu). A runner is the
  *machine that runs effects*, and it **hides** the resource from the client. A borrow **hands**
  the resource to the client.
- **A provider is a special case of a handler, not its dual.** Ahman–Bauer state that runners
  are "a restricted form of handlers" that resume at most once, in tail position. `withbor` is
  that restricted handler with no operations at all: it lends, runs the scope once, and takes
  the cell back.
- **Soundness.** Nothing about why a borrow is safe comes from comonadic structure: not the
  frozen lender, not outlives, not the frame result. It is all in the typed world (`Core/`), and
  the `needs` layer inherits it from `fundamentalC` (`KDem.sem`). The only printed mirrored
  soundness argument (Torczon et al.) has no heap and no handlers. This is where the #68 survey
  also found only a rhyme, and decision 22 says the same of optics.

**Wagner's "deeply related", made precise.** A borrow block is a handler that has no operations
and resumes once in tail position. Equivalently, it is a scoped capability provider. Handlers
that capture a continuation are a different interface.

## 4. The 2×2, the capability claim, and polarity

| | built by | consumed by | verdict |
|---|---|---|---|
| data `μ` | constructors | `foldImm`/`foldOwn`/`foldReuse` | real (initial algebra, SPEC §6) |
| codata `ν` | `unfold` | `next`/`close` observations | real (final coalgebra, SPEC §7) |
| effects | operations | handlers | printed: handler = homomorphism out of the free model. **In this core, control effects are codata** (decision 15: a suspended computation is `ν`, and a shallow handler is one observation). `div` is `F(U(Loop B R))`, and `div_fuel` observes it. |
| coeffects | providers | demands | **not a dual of the effects row.** A provider is a tail-resumptive handler without operations (above), and a demand is a function argument (`Dem U T`). No source phrases a provider as an unfold. |

**Verdict on the 2×2.** Real on the data/codata row. Partial on the effects row: its printed
structure is the free monad, but here it is codata. A rhyme on the coeffects row.

**Polarity.**
- In CBPV the monad is `UF` and the comonad is `FU` (Levy, via Torczon et al., who grade `U` for
  effects and `F` for coeffects).
- In this core the demand sits on the context/`⊸` side: `Dem U T` takes `Mut 'x U` as an
  argument. Effects appear under `F` as codata (`F(U(Loop …))`).
- So "coeffect demands on the context side" holds. "Effects are data (a free monad)" does not:
  our effects are `ν`. The table's alignment of effects with `μ` and coeffects with `ν` is
  inverted here.

**"Every handled effect carries a coeffect" (the refined claim).**
1. **Supported by the literature.** "Handlers introduce capabilities" (System C). The capability
   generated by a `try` is "valid only as long as the try is executing" (CC<:).
2. **Our kernel already has it.** A capability is a linear cell, the operations take a `Mut`
   borrow of it (§11), and the provider is `withbor`. `Programs.lean` runs I/O through exactly
   this, with nothing monadic in the types.
   - *Caveat:* the state threading is still there, inside the reborrow. `withbor` form 3 hands
     the `Mut` back, and `d_seqD` threads it. "Coeffect interface only" means the reborrow does
     the state passing.
3. **Tail-resumptive versus control.** Ahman–Bauer's runner restriction draws exactly this line.
   In this core:
   - stdio, state through `Mut`, and logging are availability plus ordinary calls (`needs`);
   - divergence, async and generators need the rest of the run, and that is codata with
     observers (SPEC §14, #52, #18).
   - So there are two interfaces, as the refined hypothesis says, not one.
4. **Fewer mechanisms (U4).** At the surface, yes: the `main`-only ambient capabilities, the
   `&mut c` lend and borrow blocks become one `needs`/`provides` form. In the kernel, no: the
   kernel already has one mechanism, `withbor` plus capabilities as cells, and there is nothing
   to delete.

**Allocation.** Under the tail-resumptive split, allocation is a need. `alloc` and `free` resume
at once, and `provide arena { … }` is a provider with finalisation, the shape of Ahman–Bauer's
`using … finally`.
- In the kernel today `alloc` is an untracked constant at any dead context, and the allocator is
  §13's oracle. So `needs alloc` against the global heap would be a checker discipline with no
  semantic content, like `total`. There is no "no allocator, no allocation" theorem to match
  `wpTSD_frame_own`, because nothing requires a capability to allocate.
- To give it content, `alloc`/`free`/`tab` would have to take a capability. That is a kernel
  change: three constants' types, their compatibility lemmas, and §13's oracle becoming the
  provider's model.
- An arena provider over arrays is library code, with no kernel change.
- **Recommendation:** model allocation as a need (a coeffect) at the surface, and leave the
  kernel's `alloc` untracked until a program needs the theorem.

## 5. What a coeffect formulation would unlock

The unlock tests are #68's: U1 a new program, U2 a law proved once, U3 an optimization, U4 fewer
mechanisms.

| candidate | U1 | U2 | U3 | U4 | verdict |
|---|---|---|---|---|---|
| capabilities as implicit demands (`needs stdout`) in every function, tracked in its type | surface only: every elaborated program is an explicit-passing program `CDerives` already has (`KDem.elab`) | contraction by reborrow proved once for every `Mut` payload (`d_seqD`), provision once (`KDem.sem`) | none | surface: ambient `main`, `&mut c` and borrow blocks become one form | **yes, as elaboration** |
| lifetimes and outlives as a coeffect semiring, with inference | none: lifetimes are scope labels in a meet-semilattice, and `[]I` filters, it does not scale | none | none | none | no. Lifetime inference is a surface problem, and no coeffect system in the literature has named lifetimes |
| grade-0 erasure | already built (`Grades`, `prog_runs_any`) | — | lowering may drop the argument (not done) | — | nothing new from the coeffect framing |
| data-flow and security levels | needs noninterference, a two-run theorem over a binary relation we lack (`TwoRun`) | — | — | — | no, not before a binary relation |
| one effect-and-coeffect grading for div, alloc, IO and borrows | none | none | none | no | no. `div` is control (codata), IO and borrows are scoped provision, and alloc is untracked. Combining would need Gaboardi et al.'s distributive law, which exists only for matched pairs, and none of our encodings needs it |

## 6. The prototype

The fragment is a flat `needs Mut U` demand, one capability, and its providers.

**The demand type.** A computation of `T` that needs `Mut U` is a value of

    Dem U T = ∀'x ⊏ ⊓Δ. Mut 'x U ⊸ ['x] T          (Optics' `cbTy` at `Mut`)

This is `withbor`'s callback type. Needing `Mut U` and being a borrow callback are the same
thing.

**Structural rules**, each a closed `CDerives` derivation, generic in the payload `U` (any
`Payload`: plain types, integers, opaque host types) and in plain results:

- `d_weakenD`: a value that needs nothing needs `Mut U` and drops it (`forget`).
- `d_rebAt`: one reborrow. At `Δ, 'x`, the demand `m : Mut 'x U` serves a demanding `g` by
  `withbor m (Λ. λv. g () v)` at a fresh `'y ⊏ ⊓(Δ, 'x)`, and comes back.
- `d_seqD`: **contraction.** `seqD : Dem U T₁ ⊸ Dem U T₂ ⊸ Dem U (T₁ ⊗ T₂)`. The reborrow axiom
  is the demand's sequential contraction.
- `d_parI`: the `Imm` demand's **parallel** contraction,
  `parI : DemI U T₁ ⊸ DemI U T₂ ⊸ DemI U (T₁ ⊗ T₂)`. It works by `copy` at the same `'x`, with
  no reborrow.

**The layer.** `KDem U x Δ Γ e T` has three rules:

- `need`: any core term at `Dem U T`, which includes a call `f a` of a function whose result
  needs `Mut U`: the latent demand in a function type;
- `weaken`;
- `seq`: elaborated `seqD e₁ e₂`.

It has two providers:

- `provide_wf`: from `c : Ref U`, by `withbor` form 2;
- `reprovide_wf`: from `m : Mut @a U`, by form 3. A function that needs `stdout`, called from
  another that needs it, is served this way.

`KDem.elab` gives a `CDerives` derivation of every elaborated term, and `KDem.sem` is
`fundamentalC` at it. There is no new rule, no new index on `CDerives`, and no new semantic
case.

**The worked program** (`Programs.lean`):

    fn greet() needs stdout = { put(72); put(105) }        -- "Hi"
    main(inp) = { let c = mk_output(1);
                  let (c, _) = provide c { greet(); greet() };
                  take_output(c) }

- `put b` is `Λ. λm. forget (write_byte () (m, b)); ()`, through §11's `write_byte` extern
  (`d_putD`).
- `greet` and the pair of calls are `KDem.seq`, and `main` provides the demand with `withbor`.
  The capability is never named inside `greet`.
- `d_main` types `main : Bytes ⊸ F (I32 ⊗ Bytes)` at the three externs' context.
- `main_every_run` is `io_every_run` applied to it, unchanged: every run from the empty memory,
  under every allocator, continues to a value at the empty memory.
- `main_eval`: the interpreter runs it to `(1, [105, 72, 105, 72])` ("HiHi", most recent first)
  with no cell left. A wrong expected byte list is rejected by the same `decide`.

**Where the coeffect view is more permissive than `CDerives`:**

- **`⊛` for `Mut`.** `seq` shares one `Mut` demand between two sequential computations, which
  no `SplitP` does. It is not more permissive, though: `seq` elaborates to the reborrow, which
  `d_seqD` derives. No new semantic proof is needed.
- **`⊕` for `Mut`.** A flat coeffect λ rule that uses the demand at both declaration site and
  call site would need `Mut 'x U ⊸ Mut 'x U ⊗ Mut 'x U`. That is not derived, and no
  obstruction was verified here. It would need a new compatibility lemma, against the frame
  invariant of the typed world, and nothing in this spike suggests it holds. The layer does not
  have that rule: a `Mut` demand is either captured (a linear thunk) or latent, never both.
- **Promotion over a demand.** A `!` function cannot capture a `Mut` demand, since `!Γ` needs
  persistent slots. A persistent function that needs `stdout` therefore has the need latent in
  its type, never captured.

**Not built.**
- The dependent bind (`Dem A ⊸ (A ⊸ Dem B) ⊸ Dem B`, result-passing sequencing). It is the same
  reborrow twice with an application between; `seq` pairs the results instead.
- A `KDem` layer for `Imm` demands; only `d_parI` exists.
- Several distinct needs (bundles). The design is a tuple payload or nested providers.
- Needs inside higher-order callbacks.

## 7. Rewrite cost

**Kernel route (grades or a demand set as an index on `CDerives`).**
- It violates decision 19 (no new index on `CDerives`).
- The Grades experiment measured the cost for usage grades: more than +100 lines before churn,
  about 201 rule-application sites, and every induction over `CDerives` (`fundamentalC`,
  `Weaken`, `Embedding`, the checker).
- A flat demand set costs the same kind of thing: a split of the set at every binary rule, and
  `∧` at λ.
- Its semantic content is nil. `KDem.elab` shows a demand is a callback binder, which the
  relation already interprets.
- **Not recommended.**

**Elaboration route (kernel unchanged).** `needs cap` elaborates into today's explicit capability
passing:
- A function with `needs stdout` takes a borrow parameter `mut 'a output`, under its lifetime
  binder.
- A call inside a body that has the need lends it on. This is §11's lend (`lendCall`,
  `lendBorrow` in `Frontend/Sugar.lean`), with the lent place resolved to the innermost
  provider or to the caller's own need, instead of being written as `&mut c`.
- Two calls in sequence reborrow (`d_seqD`, `reprovide_wf`).
- `provide c { … }` is the existing borrow block (`withbor2`).
- `main` is the top provider of `stdin`, `stdout` and `stderr`. This replaces the `main`-only
  ambient sugar with the same mechanism at every function, tracked in each signature.

Cost, grounded in the frontend as it stands (`Frontend/` is 9,238 lines; `Sugar.lean` is 1,557):

1. **A surface reborrow of a `mut` borrow.** The frontend rejects it today ("a reborrow is not
   provided", decision 38). The kernel has it (`withbor` form 3), and `d_seqD`/`reprovide_wf`
   type the elaboration. This is a prerequisite.
2. **Need inference in declaration order.** It is the same one-pass scheme as `div`'s
   (`headLoops`, `loopsAt` and `elabDef` are about 100 lines of `Sugar.lean`).
3. **Implicit argument resolution at calls,** reusing the lend (`lendParam` to `lendCall`, about
   60 lines).
4. **Bundles, a module default, and `needs nothing` checks.**
5. **Higher-order polymorphism over needs.**
   - Needs carried as borrows are lifetime polymorphism, which the callback's `∀'x` already
     gives.
   - Named needs on callbacks go through #81's specialization at the callback's type (SPEC §14):
     the need is the callback's computation type, inference is the need analysis, and
     elaboration is the lend.

The honest total estimate is **roughly 400–800 lines of `Frontend/`, plus corpus sugar pairs.
Kernel, `Core/`, `SPEC.md` §§1–14's theorems and every proof: unchanged.** The checker
re-derives `CDerives` for the elaborated program, as for every other sugar.

**Staged path.**
- **Stage 0:** the surface reborrow.
- **Stage 1:** `needs`/`provides` for capabilities, with `main` as the top provider.
- **Stage 2:** bundles and defaults; `needs alloc` as a checker discipline, and arenas as library
  providers.
- **Stage 3,** only if a program needs the theorem: `alloc` taking a capability, which is a
  kernel entry.

Control effects stay on codata, with handlers as observers, throughout.

## 8. Surface sketch (hypotheses, not decisions)

The user was thinking out loud; nothing here is decided. The words are `needs`/`provides` for
availability and `match`/`handle` on the consumer side. One option has `data`, `codata` and
`effect` as primitive declaration forms, with the familiar names as library declarations.

    data List a = nil | cons(a, List a)                  -- built by constructors, consumed by `match`/fold
    codata Iter a r = { next : a + r, close : r }       -- built by `unfold`, consumed by observations

    fn log(b: i32) needs stdout = put(b)                 -- an implicit demand; elaborates to a `mut 'a output` parameter
    fn greet() needs stdout = { log(72); log(105) }      -- the two calls reborrow the one demand
    needs io = stdin, stdout, stderr                     -- a bundle provides each member

    main(inp) = provide stdout = mk_output(1) {          -- a provider: `withbor` on the capability's cell
      greet(); greet()
    }
    let (c, n) = provide &mut cell { count() }           -- a borrow block is a provider with no operations

    effect Yield a performs yield : a -> 1               -- a control effect: needs the rest of the run
    handle gen() { yield(x) => k -> … }                  -- elaborates to codata (`ν`) and its observer, as `div` does

`asks` was considered and set aside in favour of `needs`. The effect side's signature word
(`does` or `performs`) is open. Tail-resumptive effects (I/O, state, logging, allocation) are
written with `needs`. `effect`/`handle` is reserved for control.

## 9. Recommendation

**Adopt as an elaboration layer, not in the kernel.** The coeffect reading is correct for our
borrows and capabilities: a borrow is a demand on the context, and a borrow block is its
provider. Both are already in `CDerives` (`KDem.elab`), so the kernel gains nothing from a
coeffect judgment and would pay decision 19's tax.

What adopting it buys:

- one surface mechanism, `needs`/`provides`, in place of three sugars;
- capability tracking in every function's type rather than `main` only;
- a precise statement of Wagner's intuition: a borrow block is a tail-resumptive handler with no
  operations.

Handlers that capture a continuation remain a second, genuinely different interface, on codata.
The "effects/coeffects are dual like μ/ν" claim is a rhyme, and it should not drive a rewrite.

## Sources

- https://tomasp.net/academic/papers/structural/coeffects-icfp.pdf
- https://tomasp.net/academic/papers/coeffects/coeffects-icalp.pdf
- https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-906.pdf
- https://www.cis.upenn.edu/~stevez/papers/BGMZ14.pdf
- https://pure-oai.bham.ac.uk/ws/portalfiles/portal/23697858/esop14.pdf
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- https://granule-project.github.io/papers/esop22-paper.pdf
- https://arxiv.org/pdf/2310.18166 (Marshall, Orchard, OOPSLA 2024)
- https://www.cse.chalmers.se/~abela/icfp20.pdf
- https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf
- https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- https://arxiv.org/pdf/2207.03402 (CC<:)
- https://arxiv.org/pdf/2311.11795 (Torczon et al.)
- https://arxiv.org/pdf/2407.11816 (Tang et al.)
- https://arxiv.org/pdf/1312.1399 and https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf
- https://arxiv.org/pdf/1910.11629 (Ahman, Bauer)
- https://arxiv.org/pdf/1912.13477 (Katsumata, Rivas, Uustalu)
- https://cs.ioc.ee/~tarmo/papers/essence.pdf
