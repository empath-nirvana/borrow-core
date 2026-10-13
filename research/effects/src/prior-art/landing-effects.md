# Prior art: how effect-handler and capability languages landed resources, linearity and finalisation

This chapter is part B of a three-part prior-art survey. It asks one question of each system: **what did it actually ship (or prove), what did it give up to get there, and what failed?** It is a landing survey, not a mechanism survey, so it does not repeat material that sibling chapters already cover in depth. Those are cited instead:

- [`borrow-core/survey.md`](../../../../../borrow-core/survey.md) §2.3 (languages table), §2.4 (research calculi), Appendix A (bibliography);
- [P8/P5 linearity, drop and finalisation](p8-p5-linearity-drop.md) (Tang et al., Affect, Hazel, Dynamic Wind, Runners, Congard et al., OCaml `discontinue`, Koka finalisers in detail);
- [P2 effect safety](p2-effect-safety.md), [P12 abstraction safety](p12-abstraction.md) (Zhang–Myers, Biernacki et al. in detail), [P10/P9 exclusivity and lifetimes](p10-p9-exclusivity-lifetimes.md) (System Ξ/C, CC/Capless/Capybara, OxCaml `handled_effect`, Flix/Effekt/Koka state under resumption), [I2 capture and resume](i2-capture-resume.md), [P13 zero-cost](p13-zero-cost.md), [rows vs capabilities](rows-vs-capabilities.md);
- `borrow-core/docs/prior-art-effects-coeffects.md`, `borrow-core/docs/second-class-and-system-c.md`;
- Ante: `borrow-core/research/effects/ante-deep-dive.md` (not redone here).

**Marks.**
- **[read]**: read in the primary source (paper text, official docs, or source code) during this survey; quotes are copied.
- **[relayed]**: taken from a sibling chapter or `survey.md`, not re-read here.
- **[unverified]**: from memory, or a secondary source only.
- **[synthesis]**: my reading of the sources, not a source's claim.

**Scope.** Nothing here proposes a mechanism for borrow-core. §12 maps observations onto our open items OA1–OA6 and tier 1 only.

---

## 0. Summary table

"Rank" means where effect polymorphism can be quantified. "Stored callback" means a higher-order effectful function value kept in a data structure or closure beyond the call that received it.

| system | effect polymorphism (rows/capabilities, rank) | higher-order / stored effectful callbacks | continuation linearity | finalisation / cancellation | resources or ownership in continuations | key negative result |
|---|---|---|---|---|---|---|
| **OCaml 5** (shipped) | none: effects untyped, `Effect.Unhandled` at run time [read] | unrestricted (no tracking) | one-shot, **checked dynamically** (`Continuation_already_resumed`) [read] | `discontinue` raises an exception at the perform site; `Fun.protect` [read] | none tracked; a dropped continuation "will leak … any resources that the suspended computation may hold" [read] | typed effects never landed: "I tried to get people to work on typed effects specifically for OCaml, but I failed to gather steam" (maintainer, 2026) [read] |
| **OxCaml** modes + `handled_effect` (shipped at Jane Street; library) | capabilities: handlers are `local` arguments; a typed handler list `'es`; ordinary OCaml (rank-1) polymorphism over it [read] | `local` callbacks are effect-polymorphic; a callback that captures a `local` handler cannot escape [read]/[synthesis] | continuations `@ unique`, resumed with `continue`/`discontinue`; double use "only achievable with `Obj.magic_unique`" [read] | `discontinue` (exception) [read] | modes on values: `once`, `unique`, `portable`, `contended`; a `yielding` axis for functions that may perform effects handled in the parent stack [read] | no published formalisation of modes **with** handlers (relayed from Yarrow) [relayed] |
| **Koka** (research language, released) | rows, HM rank-1 inference; **rank-2** only to scope first-class handler names [read: abstract] | rows on function types; storing is unrestricted (GC + Perceus RC) | `fun`/`val` tail-resumptive, `ctl` may resume 0..n times, `final ctl` never; `linear effect` = tail-resumptive only [read] | `finally`/`initially` library functions; finally runs on return or on unwinding a non-resuming op [read] | none tracked; Perceus RC makes multi-shot safe by sharing | `finally` is not robust to multi-shot: "the second time it resumes the file handle will be closed again"; "active research" [read] |
| **Leijen 2018** (tech report; partly in Koka) | rows | — | any | `finalize` = resume with a special `cancel`; **deep finalisation** protects operation clauses [read] | "external resources with linearity constraints" [read] | without deep finalisation, an exception in an operation clause skips finalisers of handlers below it [read] |
| **Effekt / System Ξ / System C** (research language, released) | **capabilities, no effect variables**; contextual polymorphism via second-class blocks [read] | blocks second-class; **boxing** makes them first-class with a capture set `at {…}` [read] | one-shot and multi-shot; local state (regions) backtracked under multi-shot [relayed] | Dynamic Wind (OOPSLA 2025): pre/postlude well-defined under arbitrary control [read: abstract] | regions as capabilities; "cannot return unboxed computations that capture capabilities" [read] | first-class effectful values need boxes and capture sets; the second-class discipline alone cannot store callbacks [read] |
| **Scala 3 CC + separation** (experimental in compiler) | capture sets, capture polymorphism; reach capabilities for capabilities in generic data [read] | capability-capturing closures carry capture sets; boxes at type-variable instantiation [read] | n/a (no native continuations; Gears uses library async) | scoped capabilities; no finaliser semantics specific to effects [unverified] | separation checking: `consume`, fresh `cap`, `Mutable`/`update` [read] | capture tracking could not scale to generic collections until reach capabilities (Capless) [read]; separation checking "less mature … less sure we got the balance … right" [read] |
| **Flix** (released) | set effects with complement/intersection [read]; rank-1 [unverified] | effect-polymorphic HOFs [read] | `resume` 0, 1 or many times [read] | none documented [read] | lexical regions; region values cannot escape [read] | regions combined with handlers undefined (relayed from Yarrow citing Madsen) [relayed]; no unhandled effects in `spawn`/`new` [read] |
| **Unison** (shipped) | ability variables (ordinary type variables) [read]; rank [unverified] | `A ->{e} B` everywhere [read] | handler "can choose to call the continuation or not, or to call it multiple times" [read] | no bracket/finaliser in the abilities reference [read] | none | no linearity at all; resource safety is not a type-level property [synthesis] |
| **Frank** (research prototype) | implicit "ambient ability", no effect variables in source [read: abstract] | operators are multihandlers [read: abstract] | multi-shot | none | none | — (no resource story to fail) |
| **Links** (research language) | rows; F°eff is System F-style [read] | rows on arrows | multi-shot, plus linear session channels [read] | exceptional session types (EGV) [relayed] | linear channels | **soundness bug**: Choose + Fail duplicated a linear channel and segfaulted [read] |
| **Lexa** (research) | lexical handlers passed as arguments [read: abstract] | lexically scoped | stack switching, direct jumps [read: abstract] | — | — | dynamic handler search costs can be quadratic; lexical scoping removes it [read: abstract] |
| **WasmFX / stack switching** (Wasm phase 3) | typed continuations `cont $ft`, tags; no polymorphism | continuations are first-class references | **single-shot; second invoke traps** [read] | `resume_throw` aborts at the suspension point [read] | none; reclamation of un-resumed continuations not specified in the explainer [read] | linearity enforced only dynamically (trap) [read] |
| **Roc** (pre-1.0) | **two arrows**: `->` pure, `=>` effectful; no handlers; effects come only from the platform [read] | effectful HOFs are separate names (`for_each!`) [read] | n/a | n/a | platform owns resources (host side) | colouring at higher-order functions: purity, not effect polymorphism [synthesis] |
| **Tang et al. F°eff/Q°eff** (POPL 2024) | rows with linearity kinds `Row°/Row•`; Q°eff qualified types [read] | — | control-flow linearity per operation [read] | — | linear values captured only by control-flow-linear ops [read] | rows make control-flow linearity coarse; needs qualified types [read]; Quill had a semantic soundness bug [read] |
| **Affect** (POPL 2025) | rows; bounded polymorphism via `!`/`¡` and use types [read] | `Cell`-style references storing continuations [read] | **affine** one-shot and multi-shot; capturing condition [read] | none; "a linear … version with a `discontinue` operation" is future work [read] | affine resources | naive "affine continuation for one-shot ops" is insufficient without a capturing condition; several natural polymorphic types are unsound [read] |
| **Zhang–Myers / Biernacki et al.** (POPL 2018–2020) | tunnelling / lexical labels | — | — | — | — | dynamic handler lookup breaks abstraction (accidental handling) [relayed: P12] |

---

## 1. OCaml 5

**Status.** Shipped in OCaml 5.0 (2022) on a stackful-fiber runtime (Sivaramakrishnan et al., PLDI 2021) [relayed].

**Mechanism.**
- Untyped deep and shallow handlers. "Effect handlers in OCaml do not provide effect safety; the compiler does not statically ensure that all the effects performed by the program are handled." An unhandled effect raises `Effect.Unhandled` [read].
- Continuations are one-shot, enforced at run time: "Attempting to use a continuation more than once raises a `Continuation_already_resumed` exception" [read].
- `discontinue k e` resumes the continuation by raising `e` at the perform site, so ordinary exception handlers and `Fun.protect` inside the suspended computation run [read].

**Trade-offs accepted.**
- No effect types at all, in exchange for backwards compatibility and a cheap runtime (no copying, since one-shot).
- Cleanup is the programmer's job. The manual is explicit: "Not resuming continuations will leak the memory allocated for the fibers as well as any resources that the suspended computation may hold" [read]. The manual's own example shows `Fun.protect` is not enough when a task "becomes blocked via an unmatched effect" [read].
- `Fun.protect`: if `finally` raises, `Fun.Finally_raised` replaces the original exception, which is lost; asynchronous exceptions inside `finally` are not protected [read].

**What was given up.** Static effect safety, multi-shot, and any guarantee that suspended resources are released.

**Negative results.**
- Typed effects stalled. The 2026 OCaml Discuss thread: no active implementation; obstacles named are retrofitting cost, resemblance to checked exceptions, and "no conclusive research … on how to best type polymorphic effect demands" [read; maintainer's summary].
- Ecosystem libraries (Eio) wrap untyped effects instead of waiting for types [read].

Sources: https://ocaml.org/manual/5.2/effects.html ; https://ocaml.org/manual/5.2/api/Fun.html ; https://discuss.ocaml.org/t/whats-the-status-of-typed-effects/18439 ; https://doi.org/10.1145/3453483.3454039

## 2. OxCaml: modes, and `handled_effect`

**Status.** Jane Street's OCaml branch, used in production there; modes paper at ICFP 2024; `handled_effect` is a public library [read]. Public release date [unverified].

**Mechanism: modes.** The OxCaml docs list nine axes [read]:

| axis | tracks | default |
|---|---|---|
| locality | may the value escape its region | global |
| uniqueness | are there other references | aliased |
| linearity | may the function be aliased (`once`/`many`) | many |
| portability | may it cross threads | nonportable |
| contention | has it been shared between threads | uncontended |
| forkable | may it access shared values in the parent stack | depends on locality |
| **yielding** | "whether a function is permitted to perform effects that will be handled in its parent stack" | depends on locality |
| visibility | access to mutable parts | read_write |
| statefulness | reads/writes captured mutable state | stateful |

"Future" axes (locality, linearity, portability, yielding) restrict how a value may be used later; "past" axes (uniqueness, contention) record how it was used before [read]. Lorenzen et al. (ICFP 2024) present the first three (affinity, uniqueness, locality) as "fully backwards compatible with existing OCaml code and can be completely inferred" [read: abstract].

**Mechanism: `handled_effect`** (source read: `raises_in_jsoo/handled_effect_intf.ml`) [read].
- A handler is a capability passed as a `local` argument: `val divide : ExnHandler.t @ local -> int -> int -> int`. "Functions accepting `local` functions are then effect-polymorphic" (`val map : 'a list -> f:('a -> 'b) @ local -> 'b list`).
- Several effects are a typed list `'es` (`Handler.List.t`).
- `continue : ('a,'b,'es) Continuation.t @ unique -> 'a @ once unique -> …`; `discontinue` likewise. "Exception raised when a continuation is continued or discontinued more than once. Only achievable with `Obj.magic_unique` or similar escape hatches."
- `portable`/`contended` variants of fibers and continuations are generated by mode polymorphism (`[@mode portable nonportable]`).

**Trade-offs accepted.**
- Effect safety comes from **locality**, not from an effect system: a `local` handler cannot outlive the stack frame that installed it [read: README]. This is capability-style (cf. Effekt), reusing a mode that already existed for stack allocation [synthesis].
- A callback that closes over a `local` handler is itself `local`, so it cannot be stored in a global structure [synthesis from mode rules]. Storing an effectful callback means passing the handler as an argument at call time instead.
- Uniqueness makes one-shot static; multi-shot is not offered [relayed: survey §2.3].

**What was given up.** Multi-shot; storing handler-capturing closures; an effect row in types.

**Negative results / gaps.**
- No formalisation of handlers *with* modes was found by the Yarrow authors [relayed: survey §2.3, Yarrow].
- Modal Effect Types (Tang, White, Dolan, Hillerström, Lindley, Lorenzen, OOPSLA 2025) is the OCaml-oriented typed-effects design; its motivation is that "a traditional effect system would require adding extensive effect annotations to the millions of lines of existing code" [read: abstract]. Rows and Capabilities as Modal Effects (Tang & Lindley, POPL 2026) encodes both rows and capabilities in it [relayed: P2]. Neither is shipped in OxCaml as far as I could verify [unverified].

Sources: https://oxcaml.org/documentation/modes/intro/ ; https://github.com/janestreet/handled_effect ; https://doi.org/10.1145/3674642 ; https://arxiv.org/abs/2407.11816 ; https://doi.org/10.1145/3704859

## 3. Koka, and Leijen's resources and deep finalisation

**Status.** Koka is a research language with releases; effect rows since Leijen 2014/2017; Perceus (PLDI 2021) and FP² `fip`/`fbip` keywords (ICFP 2023, Koka v2.4.2) [read: book release notes].

**Mechanism.**
- **Rows**, inferred with HM, rank-1 [relayed: P2].
- Operation clauses by control class: `fun`/`val` (tail-resumptive), `ctl` (general, may resume many times), `final ctl` (never resumes; replaced `brk`) [read: book].
- **`linear effect`**: "effects whose operations are always tail-resumptive and use only linear effects themselves (and thus resume exactly once). This removes monadic translation for such effects" [read: book §3.4.12]. Here "linear" is a **compilation class**, not a resource discipline.
- **Named and scoped handlers** (Xie, Cong, Ikemori, Leijen, OOPSLA 2022): names are first-class values bound by lambdas and "guaranteed not to escape using standard rank-2 polymorphism" [read: abstract]. Book §3.4.13 is still "Todo" [read].
- **`finally`/`initially`** are library functions: `finally(fin, action)` runs `fin` "when either returning normally, or when unwinding for a non-resuming operation"; `initially` reruns its initialiser on each extra resumption [read: book §3.4.11].

**Leijen 2018 (MSR-TR-2018-10)** is the design behind this [read: §8].
- Finalisation cannot be decided statically, because a handler may store `resume` in a scheduler queue.
- So a handler that will not resume calls an implicitly bound **`finalize`**, which "actually call[s] resume but with a special `cancel` expression (which can be regarded as a special builtin exception)". Cancel propagates through ordinary frames, running each `finally`. Not calling `finalize` means "no finalizers are run (as per the original semantics of algebraic effect handlers)".
- A `finally` clause is **not run under the handler that defines it**, to avoid an infinite loop.
- A finaliser that itself performs a finalising operation starts a nested unwinding, "a bit like throwing an exception inside an exception handler"; this "might cut a finalization short".
- **Deep finalisation** (§8.2–8.3): if an exception is raised inside an operation clause before it resumes or stores `resume`, the frames below are not on the stack, so their finalisers never run. The fix is that a clause which neither resumed nor finalised is **implicitly finalised** when finalisation passes through it.

**Trade-offs accepted.**
- Resources are external (`fhandle` is not linear in the type system); safety is by convention through `finally`.
- Multi-shot is kept, and Perceus' reuse check copies when a value is shared, so in-place update and multi-shot coexist dynamically [relayed: survey].

**What was given up.** Static resource linearity. Static control-flow linearity (Brachthäuser & Leijen's *Qualified Effect Types*, MSR-TR-2023-42, written 2018, tracks control-flow linearity with qualified types but is a report, not shipped Koka [read: abstract page]).

**Negative results.**
- The book itself: with `finally`, "If someone calls `choice()` inside the action, the second time it resumes the file handle will be closed again … There is active research into using the type system to statically prevent this" [read].
- Leijen 2018: shallow finalisation is unsound for resources across operation clauses (the three-handler async example) [read].
- `finalize` is opt-in: a handler that forgets it silently skips finalisers [read].

Sources: https://koka-lang.github.io/koka/doc/book.html ; https://www.microsoft.com/en-us/research/publication/algebraic-effect-handlers-resources-deep-finalization/ (PDF: https://www.microsoft.com/en-us/research/wp-content/uploads/2018/04/resource-v1.pdf) ; https://doi.org/10.1145/3563289 ; https://www.microsoft.com/en-us/research/publication/qualified-effect-types/ ; https://doi.org/10.1145/3453483.3454032 ; https://doi.org/10.1145/3607840

## 4. Effekt, System Ξ, System C

**Status.** Effekt is a research language with releases. System Ξ (OOPSLA 2020), System C (OOPSLA 2022, Coq), From Capabilities to Regions (OOPSLA 2023), Dynamic Wind (OOPSLA 2025), Multiple Resumptions and Local Mutable State, Directly (ICFP 2025) [relayed: survey].

**Mechanism.**
- "Effect types express which capabilities a computation requires from its context." This "significantly simplifies the treatment of effect polymorphism and the related issues of effect parametricity and effect encapsulation" [read: OOPSLA 2020 abstract].
- "To guarantee effect safety, we separate functions from values and treat all functions as second-class" (System Ξ) [read: abstract].
- System C adds **boxes**: "Boxing converts a computation to a value while making captures explicit in the type", e.g. `(() => Unit / {}) at {exc}`; "boxed computations can only be used after unboxing … when all captures are in scope"; "Functions cannot return unboxed computations that capture capabilities" [read: Effekt tour].
- Capture sets range over handler capabilities, **regions** and built-ins such as `io` [read]. "Effects express a requirement on the context"; "Captures express a restriction on where a computation can be used" [read].
- **Rank** [synthesis]. There are no effect variables. A block parameter's effects are discharged by the caller's context, so a HOF taking a block is polymorphic in that block's capabilities at every call. This gives the reach of higher-rank effect polymorphism for called-only callbacks, without a quantifier in the type. Stored callbacks need capture-set polymorphism on boxes.
- **Dynamic Wind** (Voigt, Schuster, Brachthäuser): a dynamic-wind variant for lexical handlers in which "the behavior of capturing and resuming continuations in the pre- or postlude is well-defined and respects resource bracketing", used for "backtracking of external state and finalization of external resources" [read: abstract]. The detailed laws are in [P8/P5 §1.4](p8-p5-linearity-drop.md).

**Trade-offs accepted.** Second-class by default; a visible `box`/capture-set annotation whenever an effectful computation is stored [read]. Multi-shot kept, with region state restored on resumption [relayed: P10 §1.16].

**What was given up.** First-class functions by default. Effect rows, and so any type-level account of *which effects* a stored value may perform beyond its capture set.

**Negative results.**
- The second-class discipline alone cannot express stored callbacks; boxes were added in System C for exactly this [read].
- System C refuses an aliased stateful capability (our `twoBlocks_refused` reproduces this) [relayed: rows-vs-capabilities O2].

Sources: https://doi.org/10.1145/3428194 ; https://ps.cs.uni-tuebingen.de/publications/brachthaeuser20effekt/ ; https://doi.org/10.1145/3527320 ; https://effekt-lang.org/tour/captures ; https://doi.org/10.1145/3622831 ; https://doi.org/10.1145/3763155 ; https://doi.org/10.1145/3747529

## 5. Scala 3: capture checking, capabilities for effects, separation checking

**Status.** Experimental behind a language import in Scala 3. Separation checking is a further experimental layer; Scala 3.8.2 changed `Mutable`, added an `Unscoped` classifier and refined freeze wrappers and `consume` [read: release notes via search]. Research line: CC<:□ / Capturing Types (TOPLAS 2023), Capless (OOPSLA 2025, Lean), Classifying Capabilities (OOPSLA 2026, Lean), Capybara (arXiv 2026, Lean), Degrees of Separation (OOPSLA 2024) [relayed: survey].

**Mechanism.**
- Capture sets on types; capabilities are values whose types are tracked in capture sets; effect polymorphism is capture polymorphism [relayed: P10 §1.10].
- **Reach capabilities** name "what's in the box": System Capless "refines the universal capability notion into a new scheme with existential and universal capture set quantification", fully mechanised in Lean; the collections library and an async library were migrated "with minimal changes" [read: abstract].
- **Separation checking** "enforces unique, un-aliased access to capabilities". `cap` is read as a fresh instance; after `x: T^` is created from `y`, "previously existing aliases such as `y` … are inaccessible as long as `x` is also visible"; `consume` parameters kill the argument; `Mutable` classes declare `update` methods [read: docs].

**Trade-offs accepted.** Capabilities rather than effect rows, so no native continuations: async is a library (Gears) using the platform's threads/continuations [relayed]. Annotation cost is moved into inference and reach capabilities.

**What was given up.** Native handlers and continuations, hence no continuation linearity at all.

**Negative results.**
- Capturing types "have had insufficient expressiveness for tracking capabilities embedded in generic data structures, preventing them from scaling to the standard collections library", because the system could not name capabilities inside boxes [read: Capless abstract]. The first published design had to be re-founded.
- The separation-checking docs: it is "less mature than capture checking proper, so we are less sure we got the balance of safety and expressivity right for it at the present time" [read].

Sources: https://doi.org/10.1145/3618003 ; https://arxiv.org/abs/2509.07609 (Capless, https://doi.org/10.1145/3763112) ; https://scala-lang.org/api/docs/experimental/capture-checking/separation-checking.html ; https://arxiv.org/abs/2607.09383 ; https://doi.org/10.1145/3649853

## 6. Flix

**Status.** Released language with effects, handlers, regions and effect exclusion (Lutze, Madsen et al., ICFP 2023; Associated Effects, PLDI 2024) [relayed].

**Mechanism.**
- Effect sets with union, complement, intersection and difference [read]. Effect-polymorphic HOFs: "If `map` is given a function `f` with effects `ef` then calling `map` has the effects `ef`" [read].
- Handlers: `run { … } with handler E { def op(x, resume) = … }`; `resume` may be called "zero, one, or multiple times"; a `Void` return makes an operation non-resumable [read].
- **Regions**: `region rc { … }` scopes mutable memory; "regions and all memory associated with them cannot outlive their lexical scope" ("The region variable escapes its scope") [read].

**Trade-offs.** No sub-effecting for top-level functions, only at lambdas and instance definitions [read]. "Flix does not permit unhandled effects in new object expressions nor in spawn expressions" [read].

**Negative results.** Regions combined with handlers is undefined behaviour (relayed from Yarrow, citing Madsen) [relayed: survey §2.3]; I could not find this in the Flix docs [unverified]. No finaliser construct is documented [read].

Sources: https://doc.flix.dev/effects-and-handlers.html ; https://doc.flix.dev/regions.html ; https://doc.flix.dev/effect-polymorphism.html ; https://doi.org/10.1145/3607846 ; https://doi.org/10.1145/3656393

## 7. Unison, Frank, Links

**Unison** (shipped).
- `A -> B` "is really syntactic sugar for a type `A ->{e} B`"; an empty ability set "explicitly disallows any abilities", unlike Frank [read].
- "A handler can choose to call the continuation or not, or to call it multiple times" [read]. No finaliser or bracket in the abilities reference [read].
- Rank of ability polymorphism: [unverified].
- Source: https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/

**Frank** (research prototype).
- "Effect typing in Frank employs a novel form of effect polymorphism which avoids mentioning effect variables in source code … by propagating an ambient ability inwards, rather than accumulating unions of potential effects outwards" [read: abstract].
- Multihandlers interpret several commands at once; **adaptors** support effect encapsulation and rewiring [read: abstract].
- Source: https://doi.org/10.1017/S0956796820000039 ; https://arxiv.org/abs/1611.09259

**Links** (research language).
- Row-typed, multi-shot handlers plus linear session-typed channels. This combination produced the canonical soundness bug [read: Tang et al. §1].
- `outch()` forks a child expecting `?Int.?String.End`. The parent performs `Choose` (resumed twice) then `Fail` (never resumed). The parent sends 42, aborts, re-enters at `Choose`, sends 84, and the child treats 84 as a string: "Running the program causes a segmentation fault" [read].
- Fixed by implementing F°eff's control-flow linearity in Links, "fixing a long-standing type-soundness bug" [read].
- Sources: https://arxiv.org/abs/2307.09383 ; https://doi.org/10.1145/3632896

## 8. Lexa and WasmFX (how a low-level target exposes resumptions)

**Lexa** (research; Ma, Ge, Lee, Zhang, OOPSLA 2024; Zero-Overhead Lexical Effect Handlers, OOPSLA 2025).
- Lexically scoped handlers compiled "to low-level stack switching"; existing implementations "risk incurring costs similar to run-time searches for dynamically scoped handlers"; runtime "from quadratic to linear in some cases" [read: abstract].
- Zero Lexa walks the stack using "static handler provenance" when an effect is raised, so effect-free code pays nothing [read: summary].
- Sources: https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf ; https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf

**WasmFX / stack switching** (Wasm proposal at phase 3, per search summary [relayed]).
- "Continuations in the current proposal are single-shot (aka linear) … An attempt to invoke a continuation more than once results in a trap" [read: explainer].
- `resume_throw` aborts a continuation by raising at its suspension point (cancellation); `cont.bind` partially applies; `switch` is symmetric switching; `suspend` targets the innermost matching handler by tag [read].
- Dropping a never-resumed continuation is not given a cleanup semantics in the explainer [read].
- Iris-WasmFX (PLDI 2026) mechanises type soundness and a program logic [relayed].
- **Observation** [synthesis]: the low-level target makes linearity a dynamic check and cancellation an exception. A source language that wants static linearity and non-interceptable cancellation must enforce both before lowering; the target does not supply them.
- Sources: https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md ; https://doi.org/10.1145/3622814 ; https://doi.org/10.1145/3808271

## 9. Roc (platform effects)

- Roc has **no user handlers**. "Roc's standard library does not include any effectful functions; they all come from the platform", and every app names exactly one platform [read: tutorial].
- Pure functions use `->`, effectful ones `=>`, and effectful names end in `!` by convention [read].
- Iteration with effects uses a separate effectful HOF, `for_each!`; a `for_each!` callback cannot reassign outer `var`s [read]. Whether `List.map` accepts `=>` callbacks: [unverified].
- **Trade-off** [synthesis]: purity inference gives a single bit (pure or effectful) with no handlers, and it reintroduces colouring at higher-order functions (`for_each!` alongside pure combinators). That is the axis our no-colouring decision targets.
- Source: https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md ; https://www.roc-lang.org/platforms

## 10. Linear and affine effect theory: the negative results

**Tang, Hillerström, Lindley, Morris, *Soundly Handling Linearity* (POPL 2024)** [read].
- Statement of the problem: "linear type systems bake in the assumption that continuations are invoked exactly once, effect handlers allow continuations to be discarded (e.g. for exceptions) or invoked more than once (e.g. for backtracking). This mismatch leads to soundness bugs."
- **Control-flow linearity**: "a control-flow-linear context must be entered exactly once; a control-flow-unlimited context may be entered zero, one, or multiple times". Tracked per operation (`A ↠^Y B`) and lifted to row kinds, with subkinding `Row° ≤ Row•`, the reverse of value linearity.
- Negative findings:
  - Rows force sequenced computations to share one effect type, which makes control-flow-linearity tracking coarse ("it does introduce some imprecision, and this can become more pronounced when control-flow linearity is brought into the mix"). Q°eff needs qualified types.
  - They "identify a semantic soundness bug in Quill and conjecture a fix".
  - Shallow handlers that capture linear resources need a separate extension (§6).
- Detail is in [P8/P5 §1.1](p8-p5-linearity-drop.md).

**van Rooij & Krebbers, *Affect* (POPL 2025)** [read].
- Multi-shot "break[s] key rules of reasoning and thus render[s] certain standard transformation/optimisations unsound". The rule broken is "every code block entered is exited at most once". Multi-shot also needs a stack copy.
- "One might expect that supporting both one- and multi-shot effects can simply be done by having two distinct signatures and have the type system restrict the continuations of one-shot signatures to be affine … this restriction is insufficient as one additionally needs a capturing condition."
- In ML, almost every binary operator sequences, so the capturing condition must be enforced by every rule (two-context judgements). Several natural polymorphic types (for example a `list2iter`) "are unsound for a similar reason".
- Affect is **affine**. "A linear (instead of affine) version of Affect with a 'discontinue' operation for unused continuations" is future work. Soundness is by a semantic logical relation in Iris/Coq.

**Zhang & Myers (POPL 2019); Biernacki, Piróg, Polesiuk, Sieczkowski (POPL 2018, 2019, 2020)** [relayed: P12].
- Dynamic handler lookup lets a HOF's internal handler capture its callback's operations: accidental handling, which breaks parametricity.
- Fixes: tunnelling (lexically bound handlers), lexical labels or binders, `lift`/coercions.
- These are the reasons Effekt, Lexa and our static per-site names avoid dynamic search.

**Leijen 2018** (§3 above). Finalisation must be **deep** to be robust across operation clauses that raise before resuming [read].

**Effect polymorphism rank.**

| system | rank |
|---|---|
| Koka | rank-1 rows, with rank-2 reserved for name scoping [read: abstract] |
| Links / F°eff | System F-style in the core calculus [read] |
| Effekt | no effect variables; contextual polymorphism through second-class blocks [read]; reach comparable to rank-2 for called-only callbacks [synthesis] |
| Scala | capture-set quantification, existential and universal (Capless) [read: abstract] |
| Frank | implicit ambient ability, no source-level variables [read] |
| OxCaml | ordinary ML polymorphism over the handler list `'es`, with `local` doing the scoping [read] |

- Inference with higher-rank effect polymorphism is still research: Balik, Jędras & Polesiuk 2025, *Deciding not to Decide* [relayed: survey].
- The OCaml maintainers name "how to best type polymorphic effect demands" as unsolved for OCaml [read].

---

## 11. NEGATIVE RESULTS

1. **Links / Tang et al. POPL 2024**: multi-shot `Choose` plus abortive `Fail` duplicated a linear session channel and segfaulted; a long-standing type-soundness bug. https://arxiv.org/abs/2307.09383
2. **Tang et al. POPL 2024**: Quill (qualified linear types) has a semantic soundness bug; a fix is conjectured. Same source.
3. **Tang et al. POPL 2024**: row-based effect typing makes control-flow-linearity tracking coarse, because sequenced computations share a row; qualified types are needed to recover precision. Same source.
4. **Affect POPL 2025**: affine continuations for one-shot operations are insufficient without a capturing condition; natural polymorphic types such as `list2iter` are unsound. https://iris-project.org/pdfs/2025-popl-affect.pdf
5. **Affect POPL 2025**: multi-shot invalidates standard optimisations ("every code block entered is exited at most once"). Same source.
6. **Affect POPL 2025**: a linear version with `discontinue` is left open. Same source.
7. **Koka book**: `finally` re-runs on each multi-shot resumption (double close); static prevention is "active research". https://koka-lang.github.io/koka/doc/book.html
8. **Leijen 2018**: shallow finalisation skips finalisers when an operation clause raises before resuming or storing `resume`. Deep finalisation is required, and `finalize` is opt-in, so a handler that returns without calling it runs no finalisers. https://www.microsoft.com/en-us/research/wp-content/uploads/2018/04/resource-v1.pdf
9. **Leijen 2018**: a `finally` must not run under its own handler, or it loops; a finaliser that triggers finalisation "might cut a finalization short". Same source.
10. **OCaml 5 manual**: an un-resumed continuation leaks its fiber "as well as any resources that the suspended computation may hold"; `Fun.protect` does not cover a task blocked on an unmatched effect. https://ocaml.org/manual/5.2/effects.html
11. **OCaml `Fun.protect`**: a raising `finally` replaces and loses the original exception (`Finally_raised`). https://ocaml.org/manual/5.2/api/Fun.html
12. **OCaml typed effects**: no implementation underway; typing polymorphic effect demands is unsolved for OCaml. https://discuss.ocaml.org/t/whats-the-status-of-typed-effects/18439
13. **OxCaml `handled_effect`**: one-shot is enforced by uniqueness but escapable with `Obj.magic_unique`; there is no published formal model of modes with handlers [relayed]. https://github.com/janestreet/handled_effect
14. **Scala capture checking**: the TOPLAS 2023 design could not track capabilities inside generic collections; it was re-founded as Capless with reach capabilities. https://arxiv.org/abs/2509.07609
15. **Scala separation checking**: officially "less sure we got the balance of safety and expressivity right". https://scala-lang.org/api/docs/experimental/capture-checking/separation-checking.html
16. **System Ξ → System C**: purely second-class functions cannot store effectful callbacks; boxes with capture sets were added. https://doi.org/10.1145/3527320
17. **Flix**: regions combined with handlers are reported undefined [relayed via Yarrow, unverified in Flix docs]; unhandled effects are banned in `spawn` and `new`. https://doc.flix.dev/effects-and-handlers.html
18. **WasmFX**: single-shot is a dynamic trap, not a static guarantee; there is no cleanup semantics for dropped continuations in the explainer. https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md
19. **Zhang–Myers POPL 2019**: dynamically scoped handlers cause accidental handling and break abstraction. https://doi.org/10.1145/3290318
20. **Lexa OOPSLA 2024**: dynamic handler search can make running time quadratic; lexical handlers make it linear. https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf
21. **Roc** [synthesis]: purity inference without handlers keeps colouring at HOFs (`for_each!`). https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md

---

## 12. Mapping onto our open items (observations only)

- **OA1 (free model)**: none of the shipped systems states handlers as homomorphisms once finalisers exist. Leijen 2018 models `finalize` as "resume with `cancel`", so finalisation sits inside the resume side of the theory, not beside it.
- **OA2 (answering effects)**: Koka's `linear effect` and `fun`/`val` are a **compilation class** (tail-resumptive) declared on the signature, not a separate structure. OxCaml and Effekt get the same effect from capabilities passed as arguments.
- **OA3 (names)**: Koka's named handlers scope names by rank-2 polymorphism. Effekt, Lexa and OxCaml (`local`) scope them lexically or by mode. None treats ν laws as user-visible equations.
- **OA4 (rank)**: every shipped system that avoids higher-rank row quantifiers reaches HOF polymorphism some other way (Effekt's second-class blocks, OxCaml's `local`, Frank's ambient ability). Koka keeps rank-1 and still needed rank-2 for names. Stored callbacks are where each system pays: boxes, `local` non-escape, or GC.
- **OA5 (η)**: no source examined here states handler η for its shipped calculus.
- **OA6 (Model-only laws)**: L3 independence is the Affect/Tang "capturing condition"; both treat it as a typing obligation at every sequencing rule, not as an equation.
- **F1–F5 (finalisation)**: Leijen's §8 corner cases (no `finally` under its own handler; nested finalisation may cut short; deep protection of clauses) line up with our F3 frame deadness and F5. OCaml's `Finally_raised` is a "last error wins" policy, against our "first error wins".
- **L1/L2 (linear vs affine)**: Affect stops at affine and leaves "linear plus `discontinue`" open. WasmFX and OCaml enforce one-shot dynamically, OxCaml by uniqueness. None of the systems surveyed has a static *linear* (no-drop) continuation together with a cancel.
- **Tier 1, OQ-28 (storing a continuation)**: OxCaml stores `unique` continuations; Effekt stores only boxed, capture-annotated values. Neither attaches a lifetime bound to the stored continuation.
- **Tier 1, K3 (cancel returning an owned value)**: `discontinue` and `resume_throw` return through the continuation's own result type. Leijen's `finalize(v)` returns `v` after unwinding. None of the cancels found hands back an owned value from inside the suspended computation.
- **Tier 2**: no surveyed system lets a suspension hold a borrow-like resource with static checking. Hazel and Yarrow (program logics) remain the nearest neighbours, per [tier2-status](../tier2-status.md).

---

## Sources (primary, consulted in this survey)

- OCaml manual, effects: https://ocaml.org/manual/5.2/effects.html ; `Fun`: https://ocaml.org/manual/5.2/api/Fun.html
- Scherer et al., OCaml Discuss, typed effects status: https://discuss.ocaml.org/t/whats-the-status-of-typed-effects/18439
- OxCaml modes: https://oxcaml.org/documentation/modes/intro/ ; `handled_effect`: https://github.com/janestreet/handled_effect (file `raises_in_jsoo/handled_effect_intf.ml`)
- Lorenzen, White, Dolan, Eisenberg, Lindley, *Oxidizing OCaml with Modal Memory Management*, ICFP 2024: https://doi.org/10.1145/3674642
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen, *Modal Effect Types*, OOPSLA 2025: https://arxiv.org/abs/2407.11816
- Koka book: https://koka-lang.github.io/koka/doc/book.html
- Leijen, *Algebraic Effect Handlers with Resources and Deep Finalization*, MSR-TR-2018-10: https://www.microsoft.com/en-us/research/wp-content/uploads/2018/04/resource-v1.pdf
- Xie, Cong, Ikemori, Leijen, *First-Class Names for Effect Handlers*, OOPSLA 2022: https://doi.org/10.1145/3563289
- Brachthäuser, Leijen, *Qualified Effect Types*, MSR-TR-2023-42: https://www.microsoft.com/en-us/research/publication/qualified-effect-types/
- Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020: https://doi.org/10.1145/3428194
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA 2022: https://doi.org/10.1145/3527320
- Effekt tour, captures: https://effekt-lang.org/tour/captures
- Voigt, Schuster, Brachthäuser, *Dynamic Wind for Effect Handlers*, OOPSLA 2025: https://doi.org/10.1145/3763155 ; https://se.cs.uni-tuebingen.de/publications/voigt2025dynamic.pdf
- Boruch-Gruszecki et al., *Capturing Types*, TOPLAS 2023: https://doi.org/10.1145/3618003
- Xu, Bračevac, Pham, Odersky, *What's in the Box* (Capless), OOPSLA 2025: https://arxiv.org/abs/2509.07609
- Scala separation checking: https://scala-lang.org/api/docs/experimental/capture-checking/separation-checking.html
- Flix docs: https://doc.flix.dev/effects-and-handlers.html ; https://doc.flix.dev/regions.html ; https://doc.flix.dev/effect-polymorphism.html
- Unison abilities: https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/
- Convent, Lindley, McBride, McLaughlin, *Doo Bee Doo Bee Doo*, JFP 2020: https://doi.org/10.1017/S0956796820000039
- Tang, Hillerström, Lindley, Morris, *Soundly Handling Linearity*, POPL 2024: https://arxiv.org/abs/2307.09383
- van Rooij, Krebbers, *Affect*, POPL 2025: https://iris-project.org/pdfs/2025-popl-affect.pdf ; https://doi.org/10.1145/3704841
- Zhang, Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019: https://doi.org/10.1145/3290318
- Ma, Ge, Lee, Zhang, *Lexical Effect Handlers, Directly*, OOPSLA 2024: https://cs.uwaterloo.ca/~yizhou/papers/lexa-oopsla2024.pdf
- WebAssembly stack switching explainer: https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md
- Roc mini-tutorial: https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md
