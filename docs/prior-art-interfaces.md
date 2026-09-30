# Prior art: interfaces, generics, and whether they are handlers

This is a literature survey. It records what other work establishes, and it decides nothing. It
answers the user's question, "interfaces and generics: how an implementation is found for a type,
and whether that's the same thing as handlers", and tests the user's earlier remark, "I don't
think we need traits since effects are pretty much what you want traits for". It also covers the
three lenses the user added while it was being written:

- "a way to attach a handler to a data structure, or vice versa" (§8, position C);
- the effect/coeffect split (§6);
- "multiple things interacting at cuts" (§7).

**Why now.** Several features were built with a local special case because no interface mechanism
exists:

- the `for` loop picks its iteration by the source's type (decision 47: "by `y`'s type (Rust's
  `IntoIterator`)");
- a `sized` source is recognised by its type (decision 47, *Totality from data*);
- iterator adapters of one name (`map` of `lib/adapters.bc` and of `lib/iters.bc`) are "one name chosen by the arguments' types: the first whose parameters the
  arguments match" (SPEC §15, *Generic functions*);
- a buffer's `filler[A]` is "chosen by the element type" (SPEC §17);
- `clone` is inserted by a rule "by type" (decision 39);
- borrow blocks behave differently on buffers and on literals (SPEC §17);
- #141 proposes `impl encode[N] = f` with coherence and an orphan rule
  (`docs/type-declarations-design.md` §7.4, branch `type-declarations`);
- printing needs a `display` per type;
- `Map` wants several implementations (`corpus/effects-map.bc`);
- platforms are bundles of capabilities (E14);
- tests swap real clients for fakes.

Some of these want **type-directed** resolution (one implementation per type, found from the type).
Others want **lexical** resolution (installed by scope, several allowed, swappable).

**Inputs read (internal).**

- `docs/effects-scoping.md` §§0–1, 2 (E2, E3, E14), 4, 6.6–6.7 and 7;
- `docs/decisions.md` 39, 45, 47 and 48–53;
- `docs/ideas-handlers-and-borrows.md`;
- `docs/prior-art-effects-coeffects.md`;
- SPEC §2 (`!T`), §6 (folds), §15 (*Generic functions*), §17 (buffers, text) and §18 (effects);
- `docs/type-declarations-design.md` §§6.3, 7 and 12 (branch `type-declarations`);
- the BoLo paper, `[CONF]`, abstract and §§1–3 (`~/repos/borrow_lang/3764117.pdf`).

**Reading tags**, as in `docs/prior-art-sessions.md`:

- *(full)*: the whole text was read;
- *(sections)*: the named sections were read, and the rest skimmed;
- *(abstract)*: only the abstract, the first page or a publisher's record was read;
- *(docs)*: a language's official documentation, reference or design document.

Each quotation was copied from text fetched over HTTPS, and PDFs were converted with `pdftotext`.
Where `pdftotext` split a word at a line break it has been rejoined, and nothing else was changed.
Remarks marked *(ours)* are this survey's reading, not something a source prints.

---

## 0. Summary

**Has someone written the paper?** Not as one paper. I found no paper that presents type classes
and effect handlers as one mechanism with coherence as a parameter and a theorem about it. I did
find a connected body of work that states every piece of the correspondence, and three language
designers who say in print that the two are the same thing seen from different sides:

- **Effekt's tour:** "there is a close correspondence between interfaces and effect signatures, as
  well as capabilities and objects" (tour, *Objects*).
- **Brachthäuser's thesis** gives the correspondence as a table: effect signatures are interfaces,
  handlers are implementations, capabilities are objects. It adds: "While the translation of
  dynamic binding to dictionary passing is not new (Lewis et al., 2000; Kammar et al., 2013), we
  embrace explicit passing of capabilities as part of the user facing syntax."
- **Effekt in Scala** (JFP 2020) found capabilities with Scala's type-class machinery: "implicit
  search is performed at compile time, is lexically scoped, and type-directed."
- **Handlers in Action** (Kammar, Lindley, Oury, ICFP 2013) encodes handlers *as* type classes:
  "Each instance of this class defines the clause of handler h that handles operation op".
- **Fusion for Free** (Wu, Schrijvers, MPC 2015) needs that encoding for speed: "all handlers
  should be made instances of TermAlgebra".
- **Effect Handlers, Evidently** (Xie et al., ICFP 2020) calls its evidence translation "similar
  to the dictionary translation in Haskell for type classes [Jones 1992], or capability passing in
  Effekt". It then shows where the analogy breaks: "dictionary translation may partially apply
  functions with their dictionaries which is not legal for handler evidence".
- **Coeffects.** Petricek (thesis, 2017) puts type classes and implicit parameters in one class:
  "Haskell provides two examples of flat coeffects – type class constraints and implicit
  parameter constraints".

**Where the rhyme holds** (§5.1). Both elaborate to an implicit argument that is resolved at
compile time. Both compile to a direct call once the implementation is known: Rust monomorphises,
Swift specialises, Effekt stages, and our S1a copies each function per handler. Both fall back to
an indirect call (a vtable, witness table or evidence vector) only when the implementation is not
known. A tail-resumptive handler with state is Ahman and Bauer's runner, "simply a restricted form
of handlers, which apply the continuation at most once in a tail call position". A type-class
method is a runner with no state and a key that is a type.

**Where it breaks** (§5.2). Three differences are real, and each is a parameter one mechanism
could carry:

1. **Coherence.** Consumers such as `Set`/`Ord` and `HashMap`/`Hash` rely on one instance per
   type (COCHIS §2.4), while handlers exist to be several and swapped.
2. **Grade.** A dictionary is persistent (`!`), and a handler's state is linear.
3. **Control.** An interface method never touches the continuation.

A fourth difference, resolution *site*, is not a parameter. Dynamic resolution (innermost at run
time, as in Koka and OCaml) cannot be dictionary passing (Evidently). Lexical resolution, our
standing decision (E3), can. With canonical instances, "it does not matter where a constraint is
resolved" (modular implicits §4.1). So lexical and global resolution coincide exactly when there
is one candidate.

**The signal from practice.** Every language I read that has both mechanisms keeps them apart:

- Koka added "syntactic implicit parameters and static overloading" (Leijen and Whiting, PLDI 2026)
  beside its handlers;
- Flix has traits with *associated effects*;
- Ante: "Unlike traits where impl search is automatic, effect handlers are manually inserted by the
  programmer" (2023 docs);
- Roc has abilities (type classes) and platform-provided effects;
- Unison has no type classes: "For effectful programming, you use algebraic effects, no need to
  pass dictionaries around", but "The only thing that Unison has which is as general as
  typeclasses is explicit dictionary passing".

Unison's FAQ lists "mconcat : [a] ->{Monoid a} a , where Monoid a is an ability" as one of its two
candidate designs. That is the user's hypothesis, considered by a handler-first language and not
yet adopted.

**The "abilities" name collision is a signal** (§4.7). Frank's and Unison's "abilities" are
effects. Roc's are type classes. Ante's handlers are "holdovers from Ante's previous abilities
feature". Four languages give one word to both sides of the question.

**The coeffect split** (§6) sorts the audit's cases, but only with two coordinates, not one:
grade (`!` or linear) and key (type or scope). It fails at a named case: `Kube` answers under a
`block_on` handler and suspends under the scheduler (#52). So the class belongs to the (operation,
handler) pair, not to the interface. That is already our standing rule: the class is "read off
the handler's type" (E4). "Coherence belongs to coeffects" is also too strong: `Map` is a coeffect (lent,
linear) and is not coherent.

**Candidate positions** (§8), as hypotheses:

- **(A)** one mechanism: keyed capabilities resolved lexically, with a type's declared default as
  the outermost provider;
- **(B)** two mechanisms, bridged by associated effects (Flix);
- **(C)** the user's attached handler: a type declares its default handler, `&mut m` yields the
  capability, and `with` overrides it. This is (A) with the key taken from the receiver's type,
  and Eff's 2012 "resources" are its closest precedent;
- **(D)** Koka-style static overloading plus syntactic implicits, with handlers separate.

Each has a cost and a list of the special cases it removes.

---

## 1. The closest prior work on "are interfaces handlers?"

This is the priority section. It is ordered by closeness to the question.

### 1.1 Effekt: interfaces *are* effect signatures (docs; thesis *(sections)*; JFP 2020 *(sections)*; OOPSLA 2020 *(sections)*)

- **The tour states it.** "We declare the effect signature as an interface (like those that
  objects implement)" (*Effects*). And, on objects: "The instantiation of an object might be
  reminiscent of how handlers implement effect signatures. This is no coincidence: there is a
  close correspondence between interfaces and effect signatures, as well as capabilities and
  objects. In fact, we can also implement the Counter interface with an effect handler"
  (*Objects*).
- **The compilation is the same.** "As part of its compilation pipeline, and guided by the
  type-and-effect system, the Effekt compiler performs this translation from implicitly handled
  effects to explicitly passed capabilities" (*Objects*).
- **The thesis gives the table.** Brachthäuser, *Design and Implementation of Effect Handlers for
  Object-Oriented Programming Languages* (Tübingen, 2020), Figure 4.1, "Mapping concepts from
  effect handlers to object-oriented programming":
  - Effect Signatures → Interfaces;
  - Effect Operation → Method;
  - Effect Handlers → Implementations (Classes);
  - Effectful Programs → Interface Users;
  - Effect Capability → Instances / Objects.

  The contributions list says: "Effect signatures correspond to interfaces; handlers correspond
  to implementations of the interfaces". On capability passing: "we do not perform a search for
  the implementation of effect operations at runtime. Instead, effect operations are methods on
  effect instances amb and exc, which drunkFlip receives as arguments."
- **The thesis also names the lineage to dictionaries.** "Lewis et al. (2000) show how implicit
  parameters can be elegantly implemented using regular parameter passing. This is similar to the
  dictionary passing translation of type classes (Wadler and Blott, 1989; Jones, 1992)."
- **The thesis names the cost of resolving by type.** "Resolving by type leads to issues with
  coherence, and stability under type substitution, as well as problems when combined with
  polymorphism (Schrijvers et al., 2019)." Its own "ambient values" are "resolved by name, not by
  type" and "dynamically scoped", and the chapter introduces "effect handlers by step-wise
  generalizing dynamic binding".
- **Effekt in Scala (JFP 2020, §6.3.1) used the type-class machinery for capabilities.**
  - "Implicit parameters (now called “given-clauses” or “contextual parameters” in Scala 3) can
    help to automatically pass function arguments based on their type (Odersky et al., 2017).
    This makes implicits a perfect fit for the Eﬀekt library."
  - "it is enough to understand that implicit search is performed at compile time, is lexically
    scoped, and type-directed. Implicit resolution results in a program like the explicit
    capability-passing variant above."
  - Ambiguity is resolved by naming: "This is important to resolve conflicts in case of ambiguous
    implicits, which would otherwise result in a compile time error."
- **Today's Effekt has name-based implicits as a separate feature.** "implicit value parameters
  use any value binding of the correct name at the call site" (tour, *Name-based implicits*).
- **Effects as coeffects.** OOPSLA 2020 §7.3: "Effekt can thus be seen as a combination of a
  coeffects, second-class values, and delimited control."

*For us (ours).* This is the strongest statement of the "same thing" view by the system our
effects follow (decision 48). Effekt, though, never had *type-keyed, coherent* resolution. Its
Scala library borrowed Scala's lexical implicits, which are not coherent (§2.5), and its language
resolves capabilities by effect name and scope.

### 1.2 Handlers encoded as type classes (Kammar, Lindley, Oury, *Handlers in Action*, ICFP 2013 *(sections)*)

- **Instances are clauses.** "Lines 3–6 define a ternary type class (h ‘Handles‘ op) e. Each
  instance of this class defines the clause of handler h that handles operation op with
  existential type arguments bound to e."
- **Effect typing is class constraints.** "we simulate one, encoding sets of operations as type
  class constraints". Also: "the constraint [| handles | h {Op } |] really means: handler h
  handles operation Op."
- **The encoding's limits are stated.** "because handlers are encoded as type classes and type
  classes are not first-class, neither are handlers." And: "the order in which open handlers are
  composed can leak into types". Then: "All of these limitations arise from attempting to encode
  handlers in Haskell. None is inherent to handlers."
- **Performance.** The Effekt JFP paper (see §1.1) credits the encoding: "Using type classes and the associated
  dictionary passing helps Kammar et al. (2013) to achieve good performance results, since it
  prevents the materialization of constructors for effect operations. It also avoids any search
  for the matching handler implementation in some kind of handler stack".

### 1.3 Handlers must be instances to be specialised (Wu, Schrijvers, *Fusion for Free*, MPC 2015 *(sections)*)

"GHC is keen to create type-specialised copies of (constraint) polymorphic recursive definitions
and to inline the definitions of typeclass methods in the process. In short, if we wish to get
good speed-ups from effect handler fusion, we need to make sure that the effectful programs are
polymorphic in the term monad and that all the algebras are held in typeclass instances. For this
reason, all handlers should be made instances of TermAlgebra."

*For us (ours).* In Haskell, the path from a handler to a direct call runs through the
type-class specialiser. Ours runs through decision 45's per-instance elaboration and S1a's copy
per handler (`f__h`, decision 51). These are the same move.

### 1.4 Monad transformer classes as algebraic effects (Schrijvers, Piróg, Wu, Jaskelioff, Haskell 2019; read as KU Leuven CW 699 *(sections)*)

- **The correspondence.** "we show that every modular algebraic effect gives rise to a monad
  transformer. Moreover, every monad transformer for algebraic operations gives rise to a modular
  effect handler."
- **The difference is how the semantics is chosen.** For transformers: "The instance that is used
  is decided by specifically stating the desired concrete type." For handlers: "In the
  algebraic-effect approach, the handlers are in charge of assigning semantics by folding the
  syntax tree into a particular carrier by means of a particular algebra."
- **Order is semantics in both.** Both `StateT s (MaybeT Id)` and `MaybeT (StateT s Id)` "satisfy
  the constraints (MonadState s m, MonadFail m), but give rise to different interactions between
  state and failure handling."
- **Why a class is the wrong fit for an effect.** "Using a type class restricts every type to (at
  most) one monadic interpretation".
- **mtl's single-instance problem.** Kiselyov, Sabry, Swords, *Extensible Effects*, Haskell 2013
  *(sections)*: "The type class (MonadReader e m) has a functional dependency constraining m to
  uniquely determine the type of the environment e. A MonadReader may have only one layer of
  Reader effects." And: "Thus MonadReader in MTL is less expressive (insisting on a single Reader
  effect for a given monad) but more convenient (requiring few annotations)."

### 1.5 Evidence passing is dictionary passing, except at partial application (Xie, Brachthäuser, Hillerström, Schuster, Leijen, *Effect Handlers, Evidently*, ICFP 2020 *(sections)*)

- **The analogy.** "we define a type-directed evidence translation (Section 4) where a vector of
  handlers is passed down as an implicit parameter to all operation invocations; similar to the
  dictionary translation in Haskell for type classes [Jones 1992], or capability passing in
  Effekt".
- **Where it fails.** "Another design that does not quite work is to regard evidence translation
  as an instance of qualified types [Jones 1992] and use a dictionary passing translation. In
  essence, in the theory of qualified types, the qualifiers are scoped over monomorphic types,
  which does not fit well with effect handlers." Then: "it may well be that foo itself applies f1
  under a new handler for the l1 effect and thus needs to pass different evidence than ev 1 !
  Effectively, dictionary translation may partially apply functions with their dictionaries which
  is not legal for handler evidence."

*For us (ours).* This objection is to **dynamic** resolution. Koka's evidence must be "the dynamic
innermost" handler (the paper's wording, §1). Under lexical resolution (E3, Effekt), a closure
keeps the capability it was made with, which is exactly what partially applying a dictionary
does. So this objection does not apply to our standing decision. It does apply to any design that
lets a callback pick up "whoever runs it" (effects-scoping §7.6).

### 1.6 Implicit parameters: the common ancestor (Lewis, Shields, Meijer, Launchbury, POPL 2000 *(sections, OCR copy)*; GHC User's Guide *(docs)*)

- **Scope.** "Implicit parameters are lexically distinct from regular identifiers, and are bound
  by a special with construct whose scope is dynamic, rather than static as with let."
- **The translation.** "Our translation borrows the technique of dictionary passing [16], used to
  give a semantics for overloading in Haskell." Also: "the implementation leverages off of the
  existing type class mechanism, with implicit parameters as a new kind of type predicate."
- **The paper's own framing.** "This paper elevates the dictionary translation into a
  self-contained language feature, rather than just a semantics for type classes left “under the
  hood.”"
- **The one semantic difference from classes.** "Thus, while with type classes, two unconstrained
  uses of an overloaded construct must be assumed to be different, with implicit parameters they
  must be assumed to be the same."
- **GHC's caveat.** GHC forbids implicit parameters in instance contexts: "exactly which implicit
  parameter you pick up depends on exactly where you invoke a function. But the “invocation” of
  instance declarations is done behind the scenes by the compiler, so it’s hard to figure out
  exactly where it is done. Easiest thing is to outlaw the offending types."
- **GHC's surprise.** "Adding a type signature dramatically changes the result!"

*For us (ours).* The GHC caveat is the whole question in miniature. A *coherent* provider may be
resolved anywhere, but a *scoped* one depends on where resolution happens. Mixing the two inside
one resolution step is what GHC outlaws.

### 1.7 Coeffects: classes and implicit parameters are one kind of context demand

- **Petricek, Orchard, Mycroft, ICFP 2014 *(sections)*:** "Implicit parameters are the prime
  example of a flat coeffect system, but other examples include rebindable resources [17] and
  Haskell type classes [13]."
- **Petricek, *Context-aware programming languages* (UCAM-CL-TR-906, 2017), §3.2.1 *(sections)*:**
  - "Haskell provides two examples of flat coeffects – type class constraints and implicit
    parameter constraints". Both "introduce additional constraints on the context requiring that
    the environment provides certain operations for a type (type classes) or that it provides
    values for named implicit parameters."
  - "Type classes could be modelled as a coeffect system. The type system would annotate the
    context with a set of required type classes. … The interpretation of the body is a function
    that takes α together with a hidden dictionary of operations: α × Numα → α."
- **ICALP 2013 *(sections)*: resolution site as a coeffect choice.** "Function bodies can access
  the union of the parameters (or resources) available at the declaration-site (C r Γ ) and at
  the call-site (C s τ1 )." ICFP 2014 calls these "immediate (declaration-site) and latent
  (call-site) coeffects".

*For us (ours).* "Immediate" is lexical capture, the capability taken where the closure is made.
"Latent" is resolution at the call. For a coherent provider the two agree (§5.2).

### 1.8 Koka's designer built a *separate* mechanism (Leijen, Whiting, *Syntactic Implicit Parameters with Static Overloading*, PLDI 2026; read as MSR-TR-2025-56 *(sections)*)

This is the strongest recent evidence *against* routing interfaces through handlers. It comes from
the author of Koka's effect handlers and evidence passing.

- **Two orthogonal features.** "we take a fresh look at the design space with an arguably simpler
  approach based on two orthogonal features: syntactic implicit parameters and static
  overloading."
  - Syntactic implicit parameters "are parameter names that are supplied literally as arguments at
    the call site." The paper calls this "a form of dynamic binding (but with a static
    declaration!)".
  - "Static overloading elaborates plain names to fully qualified names based on the local type
    context."
- **Pure elaboration.** "As a pure elaboration, there are no new semantic features (like an
  “instance”, or special “implicit scopes” etc.) – it is all just names, functions, and
  parameters."
- **Against type classes' global scope.** "type classes are resolved strictly by their type using
  class- and instance declarations. These declarations are in a separate global scope which is
  outside the regular scope of values and functions. This open-world approach is essential as type
  classes require global uniqueness of instances in order to have coherent semantics." And: "it
  is also difficult to locally override instance declaration."
- **Coherence by construction.** "In our system, coherence follows more directly from the
  deterministic resolution by qualified names".
- **Lexical scope only.** Against C++'s argument-dependent lookup: "In our approach the set of
  candidates is strictly determined by what is in scope, not by the types of arguments."
- **Handlers appear only as a tool.** "By specifying the algorithm under an effect handler we can
  modularly optimize the algorithm". The paper does not propose handlers as the implicit
  mechanism. The book's release notes give the surface history, per the second reader: "Implicit
  parameters are a new experimental feature that allow parameterized overloading of equality,
  show, etc."

### 1.9 Flix: traits with *associated effects* (Lutze, Madsen, PLDI 2024 *(abstract via search record; the ACM text was not reachable)*; Flix book *(docs)*)

- **Two mechanisms.** "Traits, also known as type classes, support abstraction and modularity.
  … Traits in Flix support associated types, associated effects, and higher-kinded types."
  Separately: "Flix has three types of effects:" primitive, algebraic and heap effects (a list in
  the book).
- **The bridge.** "Associated effects work in the same manner, but concern effects."
  `Dividable[Int32]` declares `type Aef = { DivByZero }`, and `Dividable[Float32]` declares `type
  Aef = { Pure }`.
- **It is our `for` problem.** The book's `ForEach` trait gains `type Aef: Eff` so that one trait
  covers `List[t]` (pure) and `MutList[t, r]` (effect in region `r`).

*For us (ours).* This is position (B)'s cleanest precedent. The effect an interface's method has
is a function of the instance, computed at the instance. Decision 45 already computes rows per
instance (effects-scoping §7.2).

### 1.10 Ante: implicits for traits, handlers kept apart (Ante language tour *(docs)*; the 2023 archived tour *(docs)*)

- **2023:** "Unlike traits where impl search is automatic, effect handlers are manually inserted
  by the programmer. This allows for multiple handlers to be defined for any effect."
- **Now: traits are implicit values.** "Implicits are most commonly used for passing around trait
  values." And: "Unlike trait implementations or typeclasses in other languages, trait values in
  Ante are normal values, and like other normal values, they can be named and imported/exported
  by name."
- **No global coherence.** "Ante has no concept of global coherence for traits, so it is perfectly
  valid to define overlapping implementations or define implementations for types outside of the
  modules the type or trait were declared in."
- **Its answer to the hash-map problem.** "Q: What about constructs like HashMap which rely on a
  consistent Hash implementation? A: The plan is to have these types parameterized over the
  implementation chosen for them."
- **Compilation.** "Any captured data in closures is stored after each function in the trait
  struct, effectively making it a vtable." Also: "Overhead from passing around trait values may be
  optimized out by the compiler but is not currently guaranteed."
- **Handlers and implicits interact.** "Since the ~> operator introduces a new implicit, for
  patterns where you’re threading through many implicits of the same effect (most notably
  generators), you may get “multiple matching implicits” errors". I have not established from
  the docs whether Ante's handlers are implemented as implicits. The sentence suggests they
  interact.

### 1.11 Genus: lexical default models, several models per constraint, models in types (Zhang, Loring, Salvaneschi, Liskov, Myers, PLDI 2015 *(sections)*)

This is the nearest *type-class* design to position (C). Handlers do not appear in it.

- **Several models.** "Genus allows multiple models witnessing a given constraint instantiation
  to coexist in the same context."
- **Natural models are the defaults.** "types automatically generate natural models when they
  structurally conform to constraints. Natural models, when they exist, are always enabled as
  default candidates."
- **Lexical enabling.** A declaration "`use ArrayListDeepCopy;` enables the specified model as a
  potential default way to clone ArrayLists in the compilation unit in which the declaration
  resides."
- **Ambiguity is an error.** "If more than one model is enabled, programmer intent is ambiguous.
  In this case, Genus requires that programmers make their intent explicit using a with clause."
- **The model is part of the type.** In `TreeSet[? extends T with c]`, "Including the choice of
  model as part of the type is unusual". This is Genus's answer to `Set`/`Ord`.
- **Models are persistent.** "Models are immutable: they provide method implementations but do not
  have any instance variables."

### 1.12 Eff: a handler's default attached to an instance (Bauer, Pretnar, arXiv 1203.1539, 2012 *(sections)*); runners (Ahman, Bauer, ESOP 2020 *(sections)*)

This is the nearest *handler* design to position (C).

- **Instances.** "The computation new E generates a fresh effect instance of effect type E."
- **Resources attach default behaviour to an instance.** "The extended form of new creates an
  effect instance with an associated resource, which determines the default behaviour of
  operations". Also: "A resource carries a state and prescribes the default behaviour of the
  operations n # opi."
- **An enclosing handler overrides the default.** "If the evaluation of c encounters an operation
  e # op e′ that is not listed in h, the control propagates to outer handling constructs, and
  eventually to the toplevel, where the behaviour is determined by the resource associated with
  e."
- **I/O is a built-in resource.** "In eff the interaction with the real world is accomplished
  through built-in resources."
- **Runners** (Ahman, Bauer, *Runners in Action*):
  - the definition: "A runner R for a signature Σ is given by a carrier set |R| together with, for
    each op P Σ, a co-operation opR : Aop Ñ p|R| ñ Bop ˆ |R|q". Read `Ñ` as `→`, `ñ` as `⇒` and
    `ˆ` as `×`; the arrows were garbled by `pdftotext`;
  - their relation to handlers: "runners are simply a restricted form of handlers, which apply the
    continuation at most once in a tail call position."

*For us (ours).* Eff 2012 already has the user's candidate (1) and (3): a value carries its
default handler, and a lexically enclosing handler overrides it. A runner's co-operation `A → (R ⇒
B × R)` is S1a's clause `h__op(c: mut 'l S, x) -> mut 'l S * B` (decision 51) with `R` lent.

### 1.13 Lexical handlers passed like implicits (Zhang, Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019 *(sections)*)

- **Handlers are objects with state.** The paper's example declares `handler printInt for
  Yield[int] {` with the field `var cnt = 0 // State of the handler`. The code comments beside the
  using code read `// Using code allocates a handler object` and `// with state cnt initialized to
  0`.
- **Implicits as handlers.** On Effekt in Scala: "the encoding passes handlers down to the place
  where effect operations are invoked, using Scala’s implicits feature [Oliveira et al. 2010] and
  in particular, implicit function types [Odersky et al. 2017], to resolve implicit arguments as
  handler objects in scope."
- **Dynamic scoping's hazard.** "a higher-order function may accidentally override variables that
  its functional argument expects from the dynamic scope, a phenomenon known in the Lisp community
  as the “downward funarg problem” [Steele 1990]."

### 1.14 The implicit calculus and COCHIS: resolution separated from interfaces

- **Oliveira, Schrijvers, Choi, Lee, Yi, PLDI 2012 (arXiv 1203.4499) *(sections)*.**
  - The abstract: "Well-known GP mechanisms, such as type classes and the C++0x concepts
    proposal, usually combine two features: 1) a special type of interfaces; and 2) implicit
    instantiation of implementations of those interfaces. Scala implicits are a GP language
    mechanism, inspired by type classes, that break with the tradition of coupling implicit
    instantiation with a special type of interface."
  - On scoping: "Rules can be nested and resolution respects the lexical scope of rules."
- **Schrijvers, Oliveira, Wadler, Marntirosian, *COCHIS*, JFP 2019 *(sections)*:**
  - "Unlike type classes, implicits are locally scoped. Consequently, Scala does not have the
    global uniqueness property, since different “instances” may exist for the same type in
    different scopes."
  - On `Set`: "If two distinct instances of Ord could be used in different parts of the program
    for the same type, then it would be possible to construct within the same program two sets
    using two different orderings (say ascending and descending order), and then break the
    ordering invariant by union-ing those two sets."

*For us (ours).* The implicit calculus is the formal statement that *resolution* is a mechanism
separate from *what is resolved*. That is the premise of positions (A) and (C). Neither paper has
effects, control or linear values.

### 1.15 Verdict on "someone surely has written a paper"

**No paper unifies them.** No paper I found defines one resolution mechanism in which type classes
and effect handlers are instances, with coherence, grade and control as parameters, and proves
something about it. I searched for combinations of "type classes", "effect handlers", "dictionary
passing", "capability passing", "implicit parameters", "instances as handlers" and "coherence".

**Three pieces of work come nearest, each covering part of it:**

1. the Effekt line (§1.1): interfaces are effect signatures, objects are capabilities, and
   capabilities were once resolved by Scala's type-directed implicits. It has no coherent
   type-keyed resolution;
2. Kammar et al. and Wu–Schrijvers (§§1.2–1.3): handlers are type-class instances, which the
   specialiser turns into direct calls. It has no first-class handlers and no multiple instances;
3. the implicit calculus, COCHIS and Genus (§§1.11, 1.14): one lexical, type-directed resolution
   with local instances and a coherence story. It has no effects, no control and no linearity.

**Where the analogy fails:** Evidently (§1.5), at partial application under dynamic resolution,
and GHC's implicit-parameter caveat (§1.6), for scoped values reached by coherent resolution.
**Who built a separate mechanism deliberately:** Koka's implicits (§1.8), Flix (§1.9), Ante
(§1.10) and Unison (§4.3).

**Not found:** a paper that makes *linearity* a parameter of such a mechanism. Scala's capture
checking tracks capabilities and has no coherence (§4.6). Granule grades values and has no type
classes or handlers (`docs/prior-art-effects-coeffects.md` §2).

---

## 2. Type-directed resolution

### 2.1 Haskell type classes (Wadler, Blott, POPL 1989 *(sections)*; Haskell 2010 Report; GHC User's Guide *(docs)*)

- **Resolution by type, compiled to dictionaries.** "How is the appropriate dictionary determined?
  By its type." And: "If the type of a function contains a class, then this is translated into a
  dictionary that is passed at runtime."
- **Coherence.** "A type may not be declared as an instance of a particular class more than once
  in the program." (Report §4.3.2.)
- **Overlap is an opt-in.** "GHC also provides a way to loosen the instance resolution, by allowing
  more than one instance to match, provided there is a most specific one." With incoherent
  instances: "If all the remaining candidates are incoherent, the search succeeds, returning an
  arbitrary surviving candidate."
- **Orphans cost separate compilation.** "Here, neither D nor T is declared in module Orphan. We
  call such modules “orphan modules”. GHC identifies orphan modules, and visits the interface file
  of every orphan module below the module being compiled."
- **Specialisation is on request.** SPECIALIZE: "Ask that GHC create a copy of a function with
  specific arguments; most commonly, a copy of an overloaded function with specific class
  dictionary arguments."
- **Linear or stateful instances:** none in the sources read.

### 2.2 Rust traits (Reference; the Book; RFC 2451 *(docs)*)

- **The orphan rule.** "The orphan rule states that a trait implementation is only allowed if
  either the trait or at least one of the types in the implementation is defined in the current
  crate. It prevents conflicting trait implementations across different crates and is key to
  ensuring coherence." Also: "A trait implementation is considered incoherent if either the
  orphan rules check fails or there are overlapping implementation instances."
- **Several implementations take a newtype.** "It’s possible to get around this restriction using
  the newtype pattern, which involves creating a new type in a tuple struct."
- **Monomorphisation.** "Rust accomplishes this by performing monomorphization of the code using
  generics at compile time."
- **`dyn` as the fallback.** "When we use trait objects, Rust must use dynamic dispatch. …
  Instead, at runtime, Rust uses the pointers inside the trait object to know which method to
  call. This lookup incurs a runtime cost that doesn’t occur with static dispatch."
- **Associated types.** "Associated types are type aliases associated with another type."
- **Receivers are ordinary parameters (ours).** A method takes `self`, `&self` or `&mut self`. A
  receiverless method (`Default::default`) is found from the expected type alone.

### 2.3 Swift protocols (the Swift book; swift repo docs; SE-0364 *(docs)*)

- **Retroactive conformance.** "You can extend an existing type to adopt and conform to a new
  protocol, even if you don't have access to the source code for the existing type."
- **Uniqueness is global and not enforced.** "protocol conformances are globally unique within a
  process in the Swift runtime, and if multiple modules declare the same conformance, it can
  cause major problems for library clients". On overlap: "their application will exhibit
  undefined behavior, as it is indeterminate which definition of this conformance will "win"."
- **Witness tables.** "witness table: The SIL (and runtime) representation of a conformance;
  essentially a vtable but for a protocol instead of a class." (Lexicon.)
- **Specialisation when visible.** "If the generic function's definition is visible to the
  optimizer and the concrete type is known, the Swift compiler will emit a version of the generic
  function specialized to the specific type." And: "The optimizer can only perform specialization
  if the definition of the generic declaration is visible in the current Module."
- **Boxing.** "Boxed protocol types don't preserve type identity".
- **Associated types.** "it's sometimes useful to declare one or more associated types as part of
  the protocol's definition."

### 2.4 Lean 4 instances and Agda instance arguments (*Theorem Proving in Lean 4*, ch. 10; Agda docs; Devriese, Piessens, ICFP 2011 *(abstract)*)

- **Lean: a database of instances.** "The main idea behind type classes is to make arguments such
  as Add α implicit, and to use a database of user-defined instances to synthesize the desired
  instances automatically through a process known as typeclass resolution."
  - Several instances are allowed, and the later or higher-priority one wins: "Instances which are
    declared last are tried first." And: "You can change the order that type class instances are
    tried by assigning them a priority."
  - Local instances: "you can use the local modifier to indicate that they only have effect until
    the current section or namespace is closed, or until the end of the current file."
  - `outParam` plays the role of associated types.
- **Agda: uniqueness required.** "a unique instance of the required type can be built from
  declared instances and the current context." And: "if there are multiple candidates that could
  be used to solve an instance goal, a type error is raised."
- **Devriese–Piessens.** Instance arguments are "resolved from call-site scope in a type-directed
  way", and "All values in scope are automatically candidates for instance resolution."

### 2.5 Scala 3 givens (Scala 3 reference *(docs)*; Oliveira, Moors, Odersky, OOPSLA 2010 *(abstract)*; Odersky et al., *Simplicitly*, POPL 2018 *(sections)*)

- **Givens.** "Given instances (or, simply, "givens") define "canonical" values of certain types
  that serve for synthesizing arguments to context parameters."
- **Explicit passing stays possible.** "The (using intOrd) part passes intOrd as an argument for
  the ord parameter."
- **Contrasted with type classes.** "An implicit parameter directly leads to an inferred argument
  term that could also be written down explicitly. By contrast, type class based designs are less
  direct since they hide term inference behind some form of type classification and do not offer
  the option of writing the inferred quantities (typically, dictionaries) explicitly."
- **The innermost wins.** "This will now resolve the implicitly call to j, because j is nested
  more deeply than i."
- **Implicit scope includes companions.** "If T is a reference to a class, S includes a reference
  to the companion object of the class".
- **One mechanism for classes and capabilities** (*Simplicitly*):
  - "They are widely used in Scala, where they model type classes [Oliveira et al. 2010; Wadler
    and Blott 1989], configurations, capabilities, type constraints [Emir et al. 2006] and many
    other forms of contextual abstractions."
  - On coherence: "Choices of implicit values can affect the outcome of a program, which means
    ambiguous implicit resolutions causes a loss of coherence."
- **Stability** (COCHIS): "Unlike Haskell type classes, however, with Scala implicits there is no
  way to enforce stability."

### 2.6 OCaml modular implicits (White, Bour, Yallop, arXiv 1512.01895 *(sections)*)

- **Mechanism.** "Modular implicits are based on type-directed implicit module parameters, and
  elaborate straightforwardly into OCaml’s first-class functors."
- **Search space.** "The implicit search space consists of those modules which have been bound
  with implicit module or let implicit module, or which are in scope as implicit parameters."
- **Canonicity is dropped, coherence kept.** "giving up canonicity – without losing the motivating
  benefit of coherence (Section 4) – makes it possible to support local instances".
  - "Uniqueness In order to maintain coherence, modular implicits require the module returned by
    resolution to be unique."
- **Why canonicity makes the resolution site irrelevant.** "If type class instances are canonical
  then it does not matter where a constraint is resolved, as there is only a single instance to
  which it could be resolved. Thus, with canonicity, the inference of show_as_list’s type cannot
  affect the dynamic semantics of the program, and coherence is preserved."
- **The diamond.** "This is a kind of “diamond” problem: we can restrict Ord_int to an Eq and then
  lift it using Eq_list, or we can lift Ord_int using Ord_list and then restrict the result to an
  Eq."

### 2.7 C++20 concepts (cppreference *(docs)*)

- **Concepts.** "Named sets of such requirements are called concepts. Each concept is a predicate,
  evaluated at compile time, and becomes a part of the interface of a template where it is used as
  a constraint".
- **Satisfaction is structural.** "Satisfaction of an atomic constraint is checked by substituting
  the parameter mapping and template arguments into the expression E."
- **Instantiation is per type, and needs the definition.** "At link time, identical instantiations
  generated by different translation units are merged." And: "The definition of a class template
  must be visible at the point of implicit instantiation".
- **No instance notion,** so no coherence and no associated types. *(ours)* This is decision 45's
  model: bodies are checked per instance, and no bound is needed to check one.

### 2.8 Carbon generics (design docs *(docs)*)

- **Explicit implementation, at most once.** "Types must explicitly _implement_ interfaces to
  indicate that they support their functionality. A given type may implement an interface at
  most once."
- **Coherence and orphans.** "To ensure coherence, an `impl` may only be declared in a library
  defining some name from its type structure." And: "**Orphan rule:** Some name from the type
  structure of an `impl` declaration must be an _anchor name_".
- **Checked generics against templates.** "The definition of a _checked_ generic is typechecked
  once, without having to know the specific argument values of the generic parameters it is
  instantiated with." Against that: "with a Carbon or C++ template, … more checking of the
  definition is required after seeing the call sites once all the instantiations are known."
- **Witness tables only for dynamic dispatch.** "We originally considered following Swift and
  using a witness table implementation strategy for checked generics, but ultimately decided to
  only use that for the dynamic-dispatch case."
- **Alternate implementations through adapters.** "the user will have to explicitly cast to that
  type in order to select those alternate implementations."

### 2.9 Roc abilities (archived abilities page, 2024 *(docs)*; Roc FAQ *(docs)*)

- **Abilities are type classes.** "An Ability defines a set of functions that can be implemented
  by different types. Abilities are used to constrain the types of function arguments to only
  those which implement the required functions."
- **Derived, with overrides.** "you can automatically derive the Eq and Hash abilities using
  implements [ Eq, Hash ]." And: "You can provide a custom implementation for an ability. This may
  be useful if a type is composed of other types which do not implement an ability, or if you
  would like to override the default behaviour."
- **Monomorphisation.** "Roc compiles programs by monomorphizing".
- **No linearity.** "The plan is for Roc to never have linear types, dependent types, refinement
  types, or uniqueness types."
- **The page has gone.** The live abilities page returns "Page Not Found", and the second reader
  found no mention of Unison's abilities.

---

## 3. Explicit and module-based resolution

### 3.1 ML modules, functors, 1ML (OCaml manual *(docs)*; Rossberg, 1ML project page *(abstract)*)

- **Explicit application.** "Functors are “functions” from modules to modules. Functors let you
  create parameterized modules and then provide other modules as parameter(s) to get a specific
  implementation."
- **Two implementations, two types.** The manual builds sets over two orderings of strings. "Note
  that the two types AbstractStringSet.set and NoCaseStringSet.set are not compatible, and values
  of these two types do not match. This is the correct behavior: even though both set types
  contain elements of the same type (strings), they are built upon different orderings of that
  type, and different invariants need to be maintained by the operations".
- **First-class modules.** "A typical use of first-class modules is to select at run-time among
  several implementations of a signature."
- **1ML.** "In this "1ML", functions, functors, and even type constructors are one and the same
  construct".

*For us (ours).* Functors solve the `Set`/`Ord` problem by putting the implementation in the type,
as Genus and Ante's plan do. That costs explicit application at every use.

### 3.2 Go interfaces (Go spec; generics implementation design doc *(docs)*)

- **Structural satisfaction.** "A type T implements an interface I if T is not an interface and is
  an element of the type set of I".
- **Coherence by locality.** "A receiver base type cannot be a pointer or interface type and it
  must be declared in the same package as the method."
- **Dynamic dispatch.** "Variables of interface type also have a distinct dynamic type, which is
  the (non-interface) type of the value assigned to the variable at run time".
- **Generics as shape stencils plus dictionaries.**
  - "we pass a **dictionary** along with every call to a generic function/method."
  - "Two concrete types are in the same gcshape grouping if and only if they have the same
    underlying type or they are both pointer types."

### 3.3 Zig comptime (language reference; `std/mem/Allocator.zig` *(docs)*)

- **Comptime duck typing.** "Compile-time parameters is how Zig implements generics. It is
  compile-time duck typing."
- **No ambient default.** "However, by convention, there is no default allocator in Zig. Instead,
  functions which need to allocate accept an Allocator parameter." And: "Generally, you will set
  up exactly one in your main function, and then pass it or sub-allocators around to various parts
  of your application."
- **The runtime interface is a pointer and a vtable.** "/// The type erased pointer to the
  allocator implementation." The struct holds `ptr: *anyopaque,` and `vtable: *const VTable,`.

*For us (ours).* Zig's allocator is a capability passed by hand, which is the SPEC §11 form before
#18. Its generics are decision 45's templates.

---

## 4. Lexical and effect-based resolution

Effekt, Koka, Unison, Frank and Scala are surveyed for effects in `docs/effects-scoping.md` §4.
This section adds only what bears on interfaces.

### 4.1 Effekt

See §1.1. Two further points:

- **Lexical resolution.** "we pass a value to be yielded to the lexically nearest handler" (tour,
  *Effects*).
- **Effects are demands, captures are restrictions.** "Effects express a requirement on the context
  – certain capabilities still need to be provided by the caller." And: "Captures express a
  restriction on where a computation can be used – the handler is already fixed in its lexical
  scope." (tour, *Captures*.)

### 4.2 Koka

- **A handler is dynamic binding.** "Intuitively, we can view the handler with fun emit … as a
  (statically typed) dynamic binding of the function emit … over the rest of the scope." (book)
- **Implicits resolve uniquely, inner scopes preferred.** "Implicit parameter resolving _must be
  unambigious_ now (and we no longer use the _shortest chain_ rule). However, we still prefer names
  declared in an inner scope." (release notes)
- **Named handlers,** for several instances: "Effect handlers enable concisely programming with
  different effects, but they do not offer a convenient way to program with different instances
  of the same effect." (Xie et al., OOPSLA 2022, abstract)
- **The implicits paper** is §1.8.

### 4.3 Unison (docs, FAQ, and the blog post it links)

- **An ability pairs an interface with handlers.** "An ability pairs an interface which describes
  an effect's operations with handlers that dictate how the effect should actually be performed."
- **No type classes, and two candidate designs.** "Does Unison have Haskell-style type classes?
  No, or at least, not yet." The FAQ's two ideas are "mconcat : [a] ->{Monoid a} a , where Monoid a
  is an ability" and "mconcat : Monoid a -> [a] -> a , where Monoid a is a record type". Both
  "would require a set of supporting language enhancements, for example to supply the Monoid a
  handlers/values automatically."
- **The first meetup post** (the FAQ's link) says:
  - "For just name overloading, Unison supports that via type-directed name resolution. For
    effectful programming, you use algebraic effects, no need to pass dictionaries around."
  - "The only thing that Unison has which is as general as typeclasses is explicit dictionary
    passing."
  - "there's no approach that's a total slam dunk".

*For us (ours).* The user's remark ("effects are pretty much what you want traits for") is
Unison's first sentence. Unison's own conclusion is that it covers effectful programming, not
bounded polymorphism: `Monoid a`, `Ord a`, `==` at a user type.

### 4.4 Frank (Lindley, McBride, McLaughlin, *Do Be Do Be Do*, arXiv 1611.09259 *(sections)*)

- "Abilities (Frank’s realisation of algebraic effects) are collections of parameterised
  interfaces, each of which describes a choice of commands".
- "Effect typing in Frank employs a novel form of effect polymorphism which avoid mentioning effect
  variables in source code."
- On shadowing: "the ambient ability at its second port will include the State S interface,
  shadowing any other State A interfaces which might have been present already."

### 4.5 Implicit parameters (Lewis et al., POPL 2000)

See §1.6.

### 4.6 Scala 3 capabilities and capture checking

See `docs/effects-scoping.md` §4.12. Relevant here:

- "It is quite natural to model capabilities with implicit parameters since it greatly reduces the
  wiring overhead once multiple capabilities are in play." (Capture Checking reference.)
- "In the fourth version, the parameter ct acts as an (object) capability." (Boruch-Gruszecki et
  al., arXiv 2207.03402.)

*Simplicitly*'s sentence (§2.5) puts type classes and capabilities under one mechanism, and COCHIS
says that mechanism is not coherent.

### 4.7 The name "abilities", as a signal

| language | "ability" means | source |
|---|---|---|
| Frank | a collection of effect interfaces | "Abilities (Frank’s realisation of algebraic effects)" |
| Unison | an effect with handlers | "An ability pairs an interface … with handlers" |
| Roc | a type class | "An Ability defines a set of functions that can be implemented by different types" |
| Ante | an earlier handler feature | "holdovers from Ante’s previous abilities feature" |

*(ours)* The word names "what a context can do". Two communities reached for it from opposite
sides. The question the user asks is already in the vocabulary.

---

## 5. Are interfaces handlers?

### 5.1 The strongest argument FOR one mechanism

1. **They elaborate to the same thing.** An interface constraint and an answering effect are both
   an implicit argument, resolved at compile time, carrying `!` code:
   - dictionaries: Wadler–Blott, "translated into a dictionary that is passed at runtime";
   - capabilities: Effekt, "explicitly passed capabilities";
   - evidence: Evidently, "similar to the dictionary translation";
   - implicit parameters: Lewis et al., "borrows the technique of dictionary passing".

   Decision 51's elaboration of a handler (`h__op(c: mut 'l S, x) -> mut 'l S * B`, a function
   over a lent state) is dictionary passing with a state.
2. **They compile the same way, and cost parity needs that:**
   - Rust: "monomorphization";
   - Swift: specialisation "if the definition … is visible";
   - Haskell handlers are fast only as instances (Wu–Schrijvers: "all handlers should be made
     instances");
   - our S1a: "A function with a row is copied per handler (`f__h`), as a generic function is per
     instance: no dispatch" (decision 51).

   All four fall back to an indirect call (vtable, witness table, evidence, capability object) only
   when separate compilation hides the implementation.
3. **The resolution machinery has been shared in practice.** Effekt-in-Scala resolved
   capabilities with Scala's type-class implicits ("lexically scoped, and type-directed").
   *Simplicitly* lists type classes and capabilities as uses of one feature, Ante passes trait
   values as implicits, and Kammar et al. encoded handlers as instances.
4. **Semantically, both are context demands.** Petricek classes both as flat coeffects (§1.7). An
   answering handler is a runner (§1.12), and a type-class method is a runner with no state.
5. **The combinations the user wants already exist.**
   - Eff 2012 attaches a default handler to an instance and lets an enclosing handler override it.
   - Genus has type-directed defaults (natural models), lexical enabling (`use`), several models
     per constraint, and the model recorded in the type when an invariant depends on it.
6. **In our setting the Evidently objection does not apply,** because resolution is lexical
   (E3). A closure captures its capabilities as a partially applied dictionary would.

### 5.2 The strongest argument AGAINST

1. **Coherence is load-bearing for some consumers, and handlers exist to break it.** `Set`/`Ord`
   and `HashMap`/`Hash` keep invariants that "break … by union-ing those two sets" (COCHIS §2.4)
   if two instances meet. Handlers are designed to be several and swapped. mtl, the attempt to
   make effects classes, hit the converse: "insisting on a single Reader effect" (Kiselyov et al.),
   and "restricts every type to (at most) one monadic interpretation" (Schrijvers et al.).
2. **Every language with both keeps them apart,** including Koka, whose designer wrote both
   (§§1.8–1.10, 4.3). Ante: "Unlike traits where impl search is automatic, effect handlers are
   manually inserted". Leijen–Whiting chose a lexical, name-based mechanism for overloading, not
   handlers.
3. **Mixing scoped and coherent resolution in one step is unsound in practice.** GHC outlaws
   implicit parameters in instance contexts because "it’s hard to figure out exactly where it is
   done" (§1.6). Under one mechanism, every instance that uses a scoped capability inherits the
   question.
4. **Receiverless and return-type dispatch.** `filler[A]`, `Default`, `from_str` and a decoder
   are found from the *expected* type, with no value to carry a handler. Handlers are found from
   the scope, and interfaces from a type anywhere in the signature.
5. **Grade.** A coherent provider may be resolved at any site and any number of times (canonicity,
   §2.6), so it must be persistent (`!`). A handler's state is linear and lent once per scope. A
   "coherent linear capability" is not well defined (§7, cell G×T).
6. **Associated types depend on the instance.** Rust, Swift, Flix and Lean `outParam` compute
   types from the instance. If the provider were chosen by scope, a type would depend on which
   handler is installed. That is well defined only under per-instance elaboration (decision 45),
   and it would make error messages depend on scope.

### 5.3 The precise differences, and whether each can be a parameter

| difference | type classes | handlers (ours) | a parameter of one mechanism? | evidence |
|---|---|---|---|---|
| key | a type (or tuple of types) | an effect name, or a named instance | **yes**: resolution is separate from what is resolved | implicit calculus (§1.14); Effekt-in-Scala used types; Koka implicits use names |
| resolution site | global instance table | lexical, innermost in scope | **yes when there is one candidate**: canonical ⇒ site irrelevant | modular implicits §4.1; Petricek's immediate/latent |
| resolution site: dynamic | — | not ours (Koka, OCaml) | **no**: dictionary passing breaks | Evidently §4 |
| multiplicity | ≤ 1 per key per program (coherence) | many; innermost or named | **yes, as a restriction**, but consumers relying on uniqueness need the choice in their type | Genus models-in-types; OCaml functor types; Ante's `HashMap` plan |
| grade | `!` (dictionary) | linear state, lent `mut` | **yes**: the provider's grade; a stateless handler is state `1` | SPEC §2; decision 51 |
| control | never touches the continuation | call, abort, suspend (class read off the handler) | **yes**: interfaces are the call class | Koka's `fun` "similar to virtual method calls"; runners |
| receiverless | found by expected type | needs a value in scope | **yes if the key is a type**; **no** if the key is a value | §8 position C |
| associated types/effects | computed per instance | effect rows computed per instance (decision 45) | **yes at type keys**, **risky at scope keys** | Flix; effects-scoping §7.2 |
| provider lifetime | static | a scope; captured lexically | **yes**: global is the top lifetime | Effekt boxes; our lifetimes (effects-scoping §7.1) |
| laws | informal (Monad laws) | handler laws per class (decision 53) | **yes**: laws per class carry over | decision 53 |

*(ours)* **Reading the table:** one resolution mechanism can carry every row except dynamic
resolution, which we have already excluded. The rows that need care are coherence against
override, and associated types at scope keys. In both, a type's meaning would depend on what the
scope installed.

---

## 6. The coeffect lens

**The hypothesis (the user's):** interfaces, whether type-directed and coherent or lent services,
are coeffects. Genuine effects are only the operations that touch the continuation.

### 6.1 The mathematics, briefly

- **Effects.** A signature `Σ = {op : A_op → B_op}` generates an algebraic theory. A handler is a
  `Σ`-algebra, and handling is the unique homomorphism out of the free model (Plotkin–Pretnar,
  per `docs/prior-art-effects-coeffects.md` §4).
- **Coeffects.** A graded comonad `D_r` has `ε : D_1 A → A` and `δ : D_{r·s} A → D_r (D_s A)`. A
  flat coeffect annotates the whole context, and implicit parameters and type classes are its
  prime instances (§1.7).
- **An answering handler with no state is an environment,** by currying: `op : E × A → B ≅ A → (E
  → B)`. The program is a co-Kleisli arrow of the environment comonad `E × −`: a flat coeffect
  `{E}` (*ours*, from Petricek's `α × Numα → α`).
- **With state it is a runner:** `A → (R ⇒ B × R)` (Ahman–Bauer). In our core `R` is lent `mut`
  for the scope, so the demand has grade 1 *and* a lifetime.
- **An interface is a type-indexed environment.** Give each type `T` a dictionary `Dict_I(T)`. A
  constraint `I[T]` is a flat coeffect demanding the component at `T`. Coherence says the family is
  a *function* of `T` (at most one component per `T`), fixed for the program, which forces grade
  `ω` (*ours*).
- **Effects and coeffects meet through a distributive law.** Gaboardi, Katsumata, Orchard,
  Breuvart, Uustalu (ICFP 2016 *(sections)*):
  - "In the non-graded case, a distributive law of a comonad over a monad is an operation of
    type: distA : DT A → T DA. This can be understood as taking a capability for an effectful
    computation and transforming it into an effectful computation of a capability."
  - Without one, "the graded monad and the graded comonad cannot interact, simply coexisting
    independently in the same world."
  - With exceptions and reuse bounds, the law says that "if an effectful computation is known to
    definitely throw an exception, then only one copy of that effectful computation is needed to
    satisfy any number of copies of A."

### 6.2 Does the split classify the audit's cases cleanly?

With one coordinate (coeffect or effect): **no**. With two coordinates for the coeffect side, grade
(`ω` or `1`) and key (type or scope), plus effects read off the handler: **yes, except one case**.

| case | coeffect or effect | grade | key | clean? |
|---|---|---|---|---|
| `for` source dispatch | coeffect: `IntoIter[T]` chosen by the source's type | ω | type | yes. The *iteration* is a second demand: pull `next` is answering (a lent iterator, grade 1), push `Yield` is an effect |
| `sized` | coeffect: a type provides its bound (`len(D)`) | ω | type | yes |
| overloading by trial elaboration (`map` of two modules) | neither: static name resolution | — | type | **outside the split**. It is Koka's static overloading, a naming mechanism. It becomes a coeffect only if `map` becomes an interface method |
| `filler[A]` | coeffect: a receiverless value by type | ω | type | yes, and it is the receiverless case (§8 C) |
| `clone` | coeffect: a deep copy by type | ω | type | yes (a `poly` in #141's terms) |
| `display` | coeffect: `Display[T]` by type, plus a linear `Out`/`Log` demand to write | ω, 1 | type, scope | yes, as two demands |
| borrow blocks on `buf`/`lit` | coeffect: the view protocol chosen by the type | ω | type | yes |
| `Map` with two handlers | coeffect: a lent service | 1 | scope | yes, and it is **not coherent**: "coherence belongs to coeffects" fails here |
| `Fail` | effect: continuation used 0 times | — | scope (which `try`) | yes |
| `Yield` | effect: continuation resumed later | — | scope | yes |
| `Log` | coeffect: a lent writer | 1 | scope | yes |
| `Kube` | coeffect under `block_on`; **effect** (suspends) under the scheduler (#52) | 1 | scope | **no: fails.** The class depends on the handler, not the interface |
| test fakes | coeffect: the fake is a lent or stateless provider at a scope | 1 or ω | scope | yes when the real provider is answering; **fails** like `Kube` when the real one suspends and the fake answers |

**Where it fails, precisely:**

1. **`Kube` and fakes.** One signature is a coeffect under one handler and an effect under
   another. The split is per (operation, handler), which is the standing rule (effects-scoping
   E4: the class is "read off the handler's type"). It is not a property of the interface.
2. **Coherence is not a coeffect property.** It is a property of the key. `Map` and `Log` are
   coeffects keyed by scope and are not coherent. `Ord` is keyed by type and is coherent.
3. **Static overloading is not a context demand.** The trial-elaboration case needs a naming rule,
   not a coeffect.

*(ours)* **Verdict.** The split is not mushy at two coordinates. Every clean case is (grade, key),
and every failure is the effect/coeffect *class*, which the handler decides. "Tail-resumptive
handlers are coeffects in effect clothing" holds as stated: runners are exactly the restricted
handlers that apply the continuation once in tail position.

---

## 7. The interaction matrix at a cut

A cut composes a producer with a consumer (`let x = M in N`, a call, a `with`, a `|>`). The things
that can meet there:

| label | meaning |
|---|---|
| **G** | coeffect grade: `!_ω` (persistent) or `!_1` (linear) |
| **B** | borrows: lifetime frames (BoLo) |
| **T** | environment chosen by type (coherent interface) |
| **S** | environment chosen by scope (handler, lexical) |
| **A** | answering provider (tail-resumptive, a runner) |
| **Z** | abort (continuation used 0 times) |
| **L** | suspension (continuation resumed once, later) |
| **M** | multi-shot (continuation used many times) |

**Cells.**

- **C:** commute;
- **C|s:** commute under a side condition, which is stated;
- **F:** must be forbidden.

**Status tags.**

- **[lit]:** the law is stated in the literature;
- **[repo]:** stated or proved in this repository;
- **[open]:** neither.

| | G | B | T | S | A | Z | L | M |
|---|---|---|---|---|---|---|---|---|
| **G** | C [lit] | C\|s [repo] | C\|s [open] | C\|s [repo] | C\|s [repo] | C\|s [lit, repo] | C\|s [repo] | F unless ω [lit, repo] |
| **B** | | C [lit] | C\|s [repo] | C [repo] | C\|s [repo] | C\|s [repo] | **open (K1)** | F [open] |
| **T** | | | C\|s [lit] | C\|s [lit, open] | C [lit] | C\|s [lit] | C\|s [open] | F [repo] |
| **S** | | | | C\|s [lit, repo] | C [lit, repo] | C\|s [lit, repo] | open [open] | F [repo] |
| **A** | | | | | C [lit] | C\|s [repo] | open (K1) | F [repo] |
| **Z** | | | | | | C [lit] | C\|s [repo, open K3] | C\|s [lit] |
| **L** | | | | | | | C\|s [repo] | F [repo] |
| **M** | | | | | | | | F [repo] |

**The side conditions and their sources.**

- **G×G.** Grades compose by the semiring (Brunel et al., Granule).
- **G×B.** A `!` value holds no borrow: `Imm̲ 'b (!T) ≜ !T` and `!T ⊐ @a` at every `@a`, with
  resource `∅` (SPEC §2). Closures capture only `!` values (F5). **Maps:** stored callbacks that
  capture capabilities (F5, S4c); `fold_imm`'s "R outlives every lifetime" (SPEC §6) is this cell,
  since a borrowed fold's result must be borrow-free, which is BoLo's outlives modality: "An
  inhabitant of [] T is an inhabitant of T that outlives (i.e., does not use) any borrow."
- **G×T.** A coherent provider must be `ω`. Genus: "Models are immutable". Canonicity lets
  resolution happen anywhere, so the provider may be duplicated. **[open]:** a *linear* coherent
  provider (a global allocator) is ill-defined without a scope. It is really S at the top level.
- **G×S.** A lent capability of grade 1 inside a `withbor` scope (decision 51). A stored effectful
  callback needs lifetime-bounded capture (effects-scoping §7.1; S4c) **[repo, open part]**.
- **G×A.** The clause code is `!`, and its state is linear and lent `mut` (decision 51). Runners
  "guarantee linear usage of resources" by linear state-passing (Ahman–Bauer).
- **G×Z.** An abort drops the continuation, so every abandoned linear value needs a destructor
  (SPEC §12 class 3; decision 52: "An abort cannot abandon a value with no destructor"). Gaboardi
  et al.'s law for a definite exception is the graded form. **K4** (a `raise` in a `fold_own` or
  `fold_imm` algebra, which is total `!` code) is this cell's open part.
- **G×L.** A suspended continuation is used once, so linear captures are fine if they outlive the
  suspension (SPEC §15).
- **G×M.** Copying `k` needs everything it holds to be `!` ("resume more than once: not provided",
  effects-scoping §1.1). Koka's book warns of the hazard: "the file handle will be closed again".
- **B×B.** The borrow frame rule composes borrows. BoLo: "a variation of the frame rule called the
  borrow frame rule, which borrows a framing proposition instead of hiding it completely".
- **B×T.** A dictionary is `!`, so it holds no borrow (as G×B).
- **B×S.** A stateful handler *is* a borrow block. The slogan in `docs/ideas-handlers-and-borrows.md`:
  "A stateful handler is a borrow presented through an interface" (spike #100).
- **B×A.** An operation that returns a borrow into handler state is **F** at the handler's own
  lifetime (SPEC §5 Open: "excluded by the update relation"). It is **C|s** as a projection at a
  fresh, shorter lifetime (effects-scoping §7.3; S4b).
- **B×Z.** An abort out of a borrow block ends the borrow, and the lender gets the state back.
  **Maps:** "handler state not rolled back under abort". SPEC §18: "the capability is handed back
  on the abort path, and the handler's state is used after it". This is a *choice*, as the
  handler order is in mtl (Schrijvers et al.: order gives "different interactions between state
  and failure handling"). A transactional handler would snapshot.
- **B×L.** A borrow held across a suspension: **K1**, open (`experiments/LoopBorrow`).
- **B×M.** A live `mut` borrow duplicated by copying `k` breaks exclusivity. Yarrow's abstract (in
  `docs/prior-art-effects-coeffects.md` §4) reports that multi-shot handlers break the
  exit-a-region-at-most-once invariant.
- **T×T.** Canonical instances compose; the diamond is harmless by canonicity (modular implicits
  §4.1). Overlap is forbidden (Rust, Carbon, #141 §7.4).
- **T×S: coherence against override** (the hash-map cell). A scope-installed provider for a
  type-keyed interface breaks any data built under the default (COCHIS §2.4). **C|s:** the choice
  is recorded in the type of the data that depends on it (Genus `TreeSet[T with c]`, OCaml functor
  types, Ante's plan), or overriding is refused for interfaces declared coherent. **[open]** for us.
- **T×A.** An interface method is a tail-resumptive call (Koka: `fun` operations have "a
  performance cost very similar to virtual method calls").
- **T×Z.** An interface method that raises: the instance's effect enters the row. Flix's
  associated effects state this per instance, and decision 45 computes rows per instance.
- **T×L.** An interface method that suspends, such as an iterator's `next` over a generator. It
  commutes by specialisation (SPEC §15 makes a yielding callback a `yield from`). Unstated for
  interfaces.
- **S×S.** Nested handlers of one effect: the innermost wins, and a name is needed when two are in
  scope (Effekt, Koka named handlers, Helium; S2a).
- **S×A.** A tail-resumptive handler is a direct call on the lent state (decision 51; SPEC §18
  "**call** (`fun`…)").
- **S×Z.** Whether an abort rolls a handler back depends on handler order (as B×Z).
- **S×L.** A handler's capability captured by a suspended computation: K1 when the capability is
  a lent borrow.
- **A×Z.** An abort inside a clause of an answering handler is not allowed in S1a ("an operation
  inside a clause" is not in S1a, decision 51).
- **Z×L.** Abandoning a suspended computation runs `ν`'s mandatory `close` (SPEC §7). A destructor
  that does I/O or fails is **K3**, open.
- **Z×M.** An abort under a multi-shot handler: Gaboardi et al.'s definite-exception law gives
  one copy.
- **L×L, L×M.** One-shot continuations compose (SPEC §15, `yield from`). Multi-shot is excluded.

**Known problems on the matrix.**

| problem | cell | status |
|---|---|---|
| K1: a borrow across a suspension | B×L (also S×L, A×L) | open |
| an abort abandoning a linear obligation | G×Z | repo (decision 52; SPEC §12 class 3) |
| coherence against override (hash maps) | T×S | lit (COCHIS, Genus, OCaml); open for us |
| stored callbacks capturing capabilities (F5, S4c) | G×S, G×B | repo (F5), open (S4c) |
| `fold_imm`'s outlives restriction | G×B (the outlives modality) | repo (SPEC §6; BoLo) |
| handler state not rolled back under an abort | B×Z, S×Z | repo (SPEC §18); lit (mtl order) |
| K4: an abort in a kernel fold | G×Z | open |
| K3: a finaliser that does I/O | Z×L | open |

*(ours)* **What the matrix says about interfaces.** The T row and column are the cheap ones: T
commutes with everything except S (coherence against override) and M. So type-keyed providers
could live in one mechanism with handlers, *provided* the T×S cell has a rule.

---

## 8. Candidate positions for borrow-core

These are hypotheses, not recommendations. "Removes" lists which of our special cases each one
would turn into library code.

### (A) One mechanism: keyed capabilities, resolved lexically

**The idea.**

- **Keys.** Every provider is an implicit capability parameter (E3). Its key is either an effect
  (name, several allowed, innermost or named) or an interface at a type (`Display[T]`).
- **Defaults.** A type-keyed provider declared with the type or the interface (`impl`, `derives`)
  is installed as the outermost scope, the "top-level handler", at grade `ω`.
- **Coherence** is a check: at most one default per (interface, type head) in the program, plus
  #141's orphan rule.
- **Overriding** a type-keyed provider inside a scope is allowed only for interfaces not declared
  `coherent`. When an invariant depends on the choice, the choice goes in the type (Genus).
- **Precedents:** Effekt-in-Scala, *Simplicitly*, the implicit calculus, Genus, Ante.

**Cost.**

- One resolution algorithm in the elaborator: keys, the scope stack, defaults and names. There is
  no new core, since both sides elaborate to parameters (decisions 48, 51).
- The coherence and orphan checks from #141 §7.4.
- A rule for the T×S cell.
- The receiverless cases need the expected type at the resolution point. Decision 45's
  per-instance elaboration supplies it.
- Lexical capture must still exclude dynamic resolution (§1.5).
- Cost parity is S1a's copy per provider: a direct call when known, `dyn` only for separate
  compilation.

**Removes:**

- `for` dispatch by source type, and `sized`;
- the two-module `map` overload;
- `filler[A]`, `clone`, `display`, and the `buf`/`lit` borrow-block cases;
- derive overrides (`impl encode[N]` becomes a default at a type key);
- `Map` with two handlers, platform bundles and test fakes, as scope keys.

**Risk:** the T×S cell and associated types at scope keys (§5.2 items 1 and 6).

### (B) Two mechanisms, bridged by associated effects

**The idea.**

- **Interfaces:** type-keyed, coherent, `ω`, specialised per instance. This is #141's `impl p[N] =
  f` generalised to named sets (#141 Q6).
- **Handlers:** scope-keyed, linear state, with control classes, as now.
- **The bridge:** an interface method's row is an associated effect per instance, as in Flix.
- **Precedents:** Flix; Koka (implicits beside handlers); Roc (abilities beside platform effects);
  Rust (traits beside explicit capability passing).

**Cost.**

- Two resolution rules, and the user must learn which a feature uses.
- A method that needs a lent service (a `display` that writes) takes both, and the language needs a
  story for that: an interface method with a row, which is Flix's.
- Coherence is simple, since interfaces cannot be overridden and handlers can.

**Removes:**

- the same type-keyed list as (A);
- `Map`, fakes and platforms stay handlers;
- a `Map` as a *type* with a `Hash` bound uses both.

**Risk:** duplication. `Iterator` (interface) and `Yield` (effect) cover one idea twice. The Flix
book's `ForEach` shows the seam.

### (C) Attached handlers: a type declares its default handler (the user's candidate)

**The idea**, as the coordinator relayed it.

- **A data structure is its handler's state.** `&mut m` yields the capability, `m.insert(k, v)`
  performs `insert` against `m`'s own clauses, and `for x in v` performs "iterate" by `v`'s type's
  handler.
- **Vice versa.** A handler with its state is a first-class value that can be stored and returned
  (S4c).
- **Override.** `with other { … }` replaces the attached default in a scope.
- **Receiverless operations** attach to the *type*, not a value.

**Precedents.**

- Eff 2012 resources: a default attached to an instance, overridden by an enclosing handler.
- Runners: co-operations on a carrier.
- Genus natural models, with lexical `use`.
- Rust's `&self`/`&mut self` traits, read as handlers.
- Effekt objects: "capabilities and objects".

**Relation to (A)** *(ours)*. (C) is (A) with the key read off the receiver's type, and with the
default provider's state being the receiver itself. The receiverless strain the user named is
exactly where (C) must fall back to (A)'s type keys (`filler`, `Default`, decoders).

**Cost.**

- **Everything in (A).**
- **The borrow reading of `&mut m` as a capability:** a projection when an operation answers a
  borrow (B×A cell; S4b).
- **Override versus data.** A `with` over a *value's* operations changes the behaviour of data
  already built under the default. For a `Map` that is the point (a different map). For a `Hash`
  used inside a `HashMap` it breaks invariants, so the same T×S rule is needed.
- **Grade.** The attached default for a linear value is linear (the value is the state), while a
  type-keyed default is `ω`. One mechanism then carries both grades by construction, which is
  §5.3's grade row.
- **Stored handlers** (the "vice versa") are S4c, and need lifetime-bounded capture.

**Removes:**

- `for` dispatch (a type's attached "iterate"), `sized` (an attached bound);
- `display`, `encode`, `clone` and `filler` (at type keys);
- `Map` as data (`m.insert`), with two implementations as two types or an override;
- test fakes (`with fake { … }`) and the borrow blocks on `buf`/`lit` (attached views).

It does not remove the `map` overload unless `map` becomes an attached operation of the source.

### (D) Static overloading plus syntactic implicits; handlers separate (Koka 2026)

**The idea.**

- **Overloading.** A plain name elaborates to a qualified name by the local type context, which
  formalises today's "first whose parameters the arguments match".
- **Implicits.** A generic function takes `?show`-style implicit parameters, supplied by name from
  the call site's scope.
- **No instances and no global table.** Handlers stay as they are.

**Cost.**

- The least new machinery. It is "a pure elaboration", and it fits decision 45, where bodies are
  elaborated per instance at known types, so static overloading always has a type.
- Coherence is by construction.
- Generic code names its implicits (`?cmp`).
- `Set`/`Ord` consistency is the programmer's, as with Ante's plan.
- The paper warns that the combination made "general type checking undecidable" and needed a
  "finite" rule set.

**Removes:**

- the `map` overload and `for` dispatch (overload `iter` by type);
- `filler`, `clone`, `display` and `encode` overrides, as qualified names;
- not `Map` with two handlers, platforms or fakes, which stay handlers.

**Risk:** no bound on generic code to say *what* an implicit is for; derive (`derives Json`) needs
its own story.

### 8.1 Summary table

| | removes type-keyed cases | removes scope-keyed cases | new resolution rules | coherence story | nearest precedent |
|---|---|---|---|---|---|
| A one mechanism | yes | yes | 1 (keyed) | a check plus the T×S rule | Effekt-in-Scala, Genus, implicit calculus |
| B two mechanisms | yes | yes (as handlers) | 2 | trivial for interfaces | Flix, Koka, Roc |
| C attached handlers | yes | yes | 1 (receiver or type key) | the T×S rule, now at every override | Eff 2012 resources, runners, Genus |
| D overloading + implicits | yes | no (handlers) | 1 plus handlers | by construction | Koka 2026 |

---

## 9. Open questions for the user

1. **The T×S cell.** When a scope overrides a type-keyed provider, must data that depends on it
   (a `HashMap` built with one `Hash`) carry the choice in its type (Genus, OCaml functors), or are
   some interfaces declared non-overridable? Every one-mechanism position needs this answer.
2. **Is receiverless dispatch wanted?** `filler[A]`, `Default`, decoders and `from_str` choose by
   the *expected* type. If yes, attachment to values (C) cannot be the whole mechanism.
3. **Grade of a type-keyed provider.** Is every type-keyed provider `!`? A global allocator or a
   platform `Stdout` would then be a scope key at the top level, not a type key.
4. **Associated types.** Must an interface compute types (an iterator's element type, `Aef`)? If
   so, may a *scope* key do so? The survey found no precedent for scope-keyed associated types.
5. **Separate compilation.** Is the `dyn` fallback (§5.1 item 2) in scope now, or only whole-program
   specialisation? The answer decides whether coherence must be checked across packages (orphan
   rule) or only within a program.
6. **Interfaces with rows.** Should an interface method be allowed an effect row per instance
   (Flix's associated effects), or must interface methods be pure call-class?

---

## 10. What I have not established

- **ACM Digital Library returned 403.** For Lutze–Madsen (associated effects) I read the Flix
  book, not the paper. For Leijen–Whiting I read MSR-TR-2025-56. For *Effects as Capabilities*
  and *First-Class Names*, abstracts came from Crossref and the author copies.
- **Not read:**
  - the Kammar et al. OCaml/SML libraries;
  - Brachthäuser et al., *Effect Handlers for the Masses* (the PDF did not download; its thesis
    chapter was read instead);
  - Helium's *Binders by Day, Labels by Night*;
  - Bottu et al., *Coherence of Type Class Resolution*;
  - Kiselyov–Shan, *Implicit Configurations*;
  - Dreyer et al., *Modular Type Classes*;
  - *Lexical Effect Handlers, Directly* (downloaded, not read);
  - the Pestov/McCall talk on Swift generics;
  - Carbon's `DynPtr` design;
  - RFC 1023;
  - 1ML beyond its abstract.
- **Lewis et al. 2000** was read from an OCR copy (Wayback). Only cleanly scanned passages are
  quoted.
- **Ante.** I have not established whether its handlers are implemented as implicits. The docs
  sentence about `~>` introducing "a new implicit" is quoted as is.
- **Roc.** No source states Roc's coherence or orphan rule. Its abilities page is gone, and the
  archived copy was read.
- **Matrix cells marked [open]** are this survey's reading and are not proved. The matrix is not a
  theorem.
- **Search.** A search result claimed that Ante describes traits as "a restricted form of effects
  which must resume in a tail position and have an automatic impl search". I could not find that
  sentence in any Ante page, and it is not quoted.

---

## Sources

**Internal.** The files listed at the head. `~/repos/borrow_lang/3764117.pdf` (BoLo, `[CONF]`).

**The unification question (§1).**

- Effekt tour: https://effekt-lang.org/tour/objects, /effects, /captures, /name-based-implicits
- Brachthäuser, *Design and Implementation of Effect Handlers for Object-Oriented Programming
  Languages*, PhD thesis, Tübingen 2020,
  https://publikationen.uni-tuebingen.de/xmlui/bitstream/handle/10900/102021/thesis-v1.1.pdf
- Brachthäuser, Schuster, Ostermann, *Effekt: Capability-passing style …*, JFP 2020,
  https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A19680B18FB74AD95F8D83BC4B097D4F/S0956796820000027a.pdf/effekt_capabilitypassing_style_for_type_and_effectsafe_extensible_effect_handlers_in_scala.pdf
- Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020,
  https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf
- Kammar, Lindley, Oury, *Handlers in Action*, ICFP 2013,
  https://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf
- Wu, Schrijvers, *Fusion for Free*, MPC 2015,
  https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/mpc2015.pdf
- Schrijvers, Piróg, Wu, Jaskelioff, *Monad Transformers and Modular Algebraic Effects*, Haskell
  2019 (report CW 699), https://www.cs.kuleuven.be/publicaties/rapporten/cw/CW699.pdf
- Kiselyov, Sabry, Swords, *Extensible Effects*, Haskell 2013,
  https://okmij.org/ftp/Haskell/extensible/exteff.pdf
- Xie, Brachthäuser, Hillerström, Schuster, Leijen, *Effect Handlers, Evidently*, ICFP 2020,
  https://www.microsoft.com/en-us/research/wp-content/uploads/2020/07/evidently-5f0b7dbc1a998.pdf
- Lewis, Shields, Meijer, Launchbury, *Implicit Parameters*, POPL 2000,
  https://web.archive.org/web/2024id_/https://www.cs.tufts.edu/comp/150FP/archive/jeffrey-lewis/implicit-parms.pdf
- GHC User's Guide, implicit parameters,
  https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/implicit_parameters.html
- Petricek, Orchard, Mycroft, ICALP 2013,
  https://tomasp.net/academic/papers/coeffects/coeffects-icalp.pdf; ICFP 2014,
  https://tomasp.net/academic/papers/structural/coeffects-icfp.pdf; Petricek, UCAM-CL-TR-906,
  https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-906.pdf
- Leijen, Whiting, *Syntactic Implicit Parameters with Static Overloading*, PLDI 2026,
  https://doi.org/10.1145/3808336; extended version MSR-TR-2025-56,
  https://www.microsoft.com/en-us/research/wp-content/uploads/2025/11/implicits-tr-v6.pdf
- Flix book, https://doc.flix.dev/print.html; Lutze, Madsen, *Associated Effects*, PLDI 2024,
  https://doi.org/10.1145/3656393 (not read)
- Ante language tour, https://antelang.org/docs/language/ and the 2023 copy,
  https://web.archive.org/web/2023id_/https://antelang.org/docs/language/
- Zhang, Loring, Salvaneschi, Liskov, Myers, *Lightweight, Flexible Object-Oriented Generics*
  (Genus), PLDI 2015, https://www.cs.cornell.edu/andru/papers/genus/genus.pdf
- Bauer, Pretnar, *Programming with Algebraic Effects and Handlers*, https://arxiv.org/pdf/1203.1539
- Ahman, Bauer, *Runners in Action*, ESOP 2020, https://arxiv.org/pdf/1910.11629
- Zhang, Myers, *Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019,
  https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf
- Oliveira, Schrijvers, Choi, Lee, Yi, *The Implicit Calculus*, https://arxiv.org/pdf/1203.4499
- Schrijvers, Oliveira, Wadler, Marntirosian, *COCHIS*, JFP 2019,
  https://homepages.inf.ed.ac.uk/wadler/papers/cochis/cochis.pdf
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, *Combining Effects and Coeffects via
  Grading*, ICFP 2016,
  https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf

**Type-directed (§2).**

- Wadler, Blott, https://homepages.inf.ed.ac.uk/wadler/papers/class/class.ps
- Haskell 2010 Report ch. 4, https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
- GHC User's Guide: instances, separate compilation, pragmas,
  https://downloads.haskell.org/ghc/latest/docs/users_guide/
- Rust Reference, https://doc.rust-lang.org/reference/items/implementations.html and
  associated-items.html; the Book ch. 10, 18, 20; RFC 2451,
  https://raw.githubusercontent.com/rust-lang/rfcs/master/text/2451-re-rebalancing-coherence.md
- Swift book (Protocols, Generics, OpaqueTypes),
  https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/; swift
  docs Lexicon.md, OptimizationTips.rst, GenericsManifesto.md; SE-0364
- *Theorem Proving in Lean 4*, ch. 10, https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/
- Agda instance arguments, https://agda.readthedocs.io/en/latest/language/instance-arguments.html;
  Devriese, Piessens, ICFP 2011,
  https://lirias.kuleuven.be/retrieve/98e3d4dd-e718-4cf1-bc62-2dd4f505e203
- Scala 3 reference, contextual abstractions and implicit resolution,
  https://docs.scala-lang.org/scala3/reference/; Oliveira, Moors, Odersky, OOPSLA 2010,
  https://i.cs.hku.hk/~bruno/papers/TypeClasses.pdf; Odersky et al., *Simplicitly*, POPL 2018
  (Wayback copy of https://infoscience.epfl.ch/record/229878/files/simplicitly_1.pdf)
- White, Bour, Yallop, *Modular Implicits*, https://arxiv.org/pdf/1512.01895
- cppreference, constraints and templates, https://en.cppreference.com/w/cpp/language/constraints
- Carbon generics, overview.md, details.md, goals.md,
  https://raw.githubusercontent.com/carbon-language/carbon-lang/trunk/docs/design/generics/
- Roc abilities (archived), https://web.archive.org/web/2024id_/https://www.roc-lang.org/abilities;
  Roc FAQ, https://www.roc-lang.org/faq

**Modules and explicit (§3).**

- OCaml manual, https://ocaml.org/manual/5.3/moduleexamples.html and firstclassmodules.html
- 1ML, https://people.mpi-sws.org/~rossberg/1ml/
- Go spec, https://go.dev/ref/spec; generics dictionaries design,
  https://raw.githubusercontent.com/golang/proposal/master/design/generics-implementation-dictionaries-go1.18.md
- Zig reference, https://ziglang.org/documentation/master/; Allocator.zig,
  https://raw.githubusercontent.com/ziglang/zig/master/lib/std/mem/Allocator.zig

**Lexical and effect-based (§4).**

- Koka book, https://koka-lang.github.io/koka/doc/book.html; release notes,
  https://raw.githubusercontent.com/koka-lang/koka/dev/support/vscode/koka.language-koka/whatsnew.md;
  Xie, Cong, Ikemori, Leijen, OOPSLA 2022 (Crossref abstract, DOI 10.1145/3563289)
- Unison: https://www.unison-lang.org/docs/usage-topics/general-faqs/,
  https://www.unison-lang.org/docs/fundamentals/abilities/using-abilities-pt1/,
  https://www.unison-lang.org/blog/writeup-of-our-first-unison-meetup/
- Lindley, McBride, McLaughlin, *Do Be Do Be Do*, https://arxiv.org/pdf/1611.09259
- Scala capture checking, https://docs.scala-lang.org/scala3/reference/experimental/cc.html;
  Boruch-Gruszecki et al., https://arxiv.org/pdf/2207.03402
