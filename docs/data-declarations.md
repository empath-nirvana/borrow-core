# Data declarations, faces and interfaces: design (#489)

Status: decided (§11, 2026-10-20). U1 is built: SPEC §42 (`data` declarations, transparent,
monomorphic and generic; blocks and `box`; the single-root rule; constructors, record literals,
fields; the match compiler), except §11.1 A7, which waits for a block lowered as one object
(SPEC §42, *No automatic boxing*). The rest of this document is the design as decided. **Every
spelling is provisional.** The user asked to see several syntax paradigms side by side (an
explicit exception to "mechanism before syntax"), so §5 shows four, all over the one mechanism of
§3–§4.

Labels, as on #489: **E** established (a citation, or a program checked and run here), **B**
believed, **NC** not checked.

Companion files, outside the gate:

- [`data-declarations/paradigms/`](data-declarations/paradigms/): the same four examples in each
  paradigm, in proposed surface. They do not parse.
- [`data-declarations/lowered/`](data-declarations/lowered/): hand lowerings to today's language,
  each checked with `bcc check` and run with `bcc interp` at `9aa27c3`:
  - `faces.bc`: one interface at three binding times (§4);
  - `resource.bc`: a Kubernetes-style resource round-tripped through JSON, as `derive` would
    specialise it (§7).

---

## 1. What exists today

Checked at `9aa27c3` (SPEC 0.86).

### 1.1 Implementation and feature table

| feature | state | where | what it gives this design |
|---|---|---|---|
| `data` declarations | built in U1 (SPEC §42); this table is as of the design | `corpus/data-box-tree.bc` | the thing to build |
| `type N[T]<'a> = A` | built: transparent, parameterised, substituted at each use | SPEC §22 *The checker*; decision 60 | the structural target every declaration elaborates to |
| records and variants | derived forms over `⊗`, `⊕`; no labels in the core | SPEC §5 | records and constructors with no kernel former |
| `μX. A`, `roll`/`unroll` | built; folds at `FShape` (closed leaf, `Ref X`, `X`, `⊗`, `⊕`) | SPEC §6 | recursive declarations; `X` under an array is outside `FShape` (B14) |
| `νX. C`, `nu_in`/`nu_out`, `unfold` | built; observations may take closed arguments, the rest may be boxed `[@c]` | SPEC §7, §22 | codata declarations and materialised interface values, with the state hidden |
| `&` products of computations | built; `.1`/`.2` select an observation | `Frontend/Parser.lean`, `compSuffixes` | an interface's observations are a `&` tree |
| the affine closure `Aff[A, B]<'c>` | library, `lib/aff.bc` | SPEC §22 | the pattern every `mut` observation of an object follows |
| `pull`, `iter`, `loop`, `stream`, `delay`, `sized` | frontend abbreviations over `ν` | `Frontend/Syntax.lean`; #141 decision 6 says delete them for library declarations | the first library `codata` declarations |
| generators | `Yield[T]` effect; `for` is a handler site | SPEC §15 | iteration methods are generators (`items(imm) with Yield[imm T]`) |
| generic functions | templates, monomorphised; first-order matching | SPEC §15, decision 45 | generic declarations are type-level templates |
| generic recursion | built, one set of type and lifetime parameters per group; templates of one name where one is recursive are rejected (D1) | SPEC §31 | a namespace per type removes D1's commonest case (§6.1) |
| `poly` families | built: one case per type, the most specific head chosen, overlap rejected; no case at `μ`; no structure view | SPEC §36 | one provider per type; derive needs the structure view added (§7.2) |
| operators | `poly (+)` etc., machine cases at the integer widths | SPEC §36 | operators on declared types by a case |
| providers `equal`, `hash`, `order` | `lib/key.bc`, over views | SPEC §36 | providers for declared types |
| the map | `lib/map.bc`, a plain value; `map_len(&m)`, `map_get(r, k)` through the map lent fieldwise | SPEC §36 | today's "method" is a function with the type in its name |
| `n.op(v)` | built: `op` at the handler named `n` | SPEC §38 | dot already means "an operation at the context binding time" |
| value-state handlers `handler h(mut s: S)`, lent ones `handler h(&mut s: S)` | built | SPEC §18, §34 | a type's face installed as a handler is a handler over its state |
| computation parameters, `\|>` | built: `e \|> f(a)` is `f(e, a)` | SPEC §33, decision 50 | first-argument application exists as `\|>` |
| effect instances, names, abstraction safety | built | SPEC §38 | interfaces in the context form can have two instances in scope, told apart by name |
| `f(&x)`, `f(&mut x)`, lent for the call | built | SPEC §35; #577's decisions | receiver modes need only the `&` inserted (§6.6) |
| one box a node | built, in the backend: the back edges of a type's cycles are boxed, or a sum's payload when that boxes fewer | SPEC §35 | not used by declarations: a declared recursive type writes its `box` (§6.11, decided) |
| `box e`, a written heap allocation | specified: "the only surface heap allocation, apart from arrays" | `docs/typed-elaboration.md` §5.3 | the layout of recursive declarations (§6.11) |
| cell classes | built: each cell as wide as the widest type its swaps reach | SPEC §5 *Cell classes*; #570 (C2b) | a declared type's cells are its structure's; declarations add no layout question at cells |
| typed attributes, `derives`, `attr` | **absent** | #141 §8 | needed for serde |
| `codata` declarations | **absent** | #141 §6 | needed for interfaces |
| abstraction (a hidden iso) | **absent**; no modules (#63) | #141 §3.4 | needed for abstract types; §6.4 proposes a boundary that needs no modules |

### 1.2 What the corpus writes today

In `corpus/` and `lib/`: 0 `data` declarations, 243 `type` declarations (66 over `μ`, 13 over
`ν`), 43 `poly` declarations, 106 `effect` declarations and 99 `handler` declarations (E, grep).
`docs/ergonomics.md` M1 counts 2197 written `inl`/`inr` and 459 `match … inl … | inr` across the
corpus, `lib/`, `bench/` and `book/`.

Today's "methods" are functions whose names carry the type (`map_insert`, `map_len`, `set_insert`,
`heap_push`, `aff_call`), called with the receiver first and often handed back
(`map_len(m: Map[K, V]) -> Map[K, V] * i32`). The corpus writes codata in core:
`(nu_out (force g)).1` is an observation.

### 1.3 Already decided, and treated as requirements here

From #141 (2026-10-02), #489's comments (2026-10-16, -17, -19) and this pass's brief:

1. **Identity**: a declaration is a name plus an isomorphism to a structural type, nominal in the
   elaborator and structural in the core. The elaborator alone enforces abstraction.
2. **Providers**: one per type (option D, then #508's `poly` families with one case per type).
   Hand-written cases are fine. Traits remain possible.
3. **Derive** is `poly`, the restricted first case of compile-time evaluation, and **`derives` is
   explicit**.
4. **Mutual recursion** uses the single-root rule now, and the kernel entry comes later.
5. **The codata abbreviations** in the frontend are deleted in favour of library declarations.
6. **Generics**:
   - operators are `poly add`;
   - the map is a plain value (a trial);
   - `get` returns a view;
   - nested datatypes and polymorphic recursion (D2) are accepted in principle;
   - the bounds layer (`ability`) comes later, as its own unit.
7. **Methods are codata.** A type has two faces: data inside its declaration, codata to its
   clients. Transparent declarations also expose constructors; abstract ones expose only
   observations.
8. **Self-methods are not a different kind.**
   - For a known type, `m.len()` is `len(&m)`.
   - What differs is the binding time: static, by the value, or by the context.
   - There is one call syntax, and the type tells which binding time applies.
   - Codata materialises only for the binding time by the value.
9. **Recursion's layout keeps a written `box`** (2026-10-20, on item 13 of §11): "I think heap
   allocations should be explicit re:boxing." A recursive declaration elaborates as typed
   elaboration §5.3 says, and building a recursive node without `box` is an error that asks for
   it. One box a node, placed by rule, is not used for declarations (§6.11).

---

## 2. Summary

**One mechanism.** A declaration is #141's name plus an iso. It has two faces:

- **The data face**: constructors, patterns and fields, which are `into_N`/`out_N` over a
  structural type of `⊗`, `⊕` and `μ`.
- **The codata face**: a set of observations. Each is a function whose first parameter is the
  receiver, at an observation mode (`imm`, `mut` or owned).

An **interface** is a `codata` declaration: a named set of observation signatures. All of it
elaborates to formers the kernel already has.

**Three binding times of one observation**, `x.len()`:

| binding time | the receiver | what `x.len()` is | core | cost |
|---|---|---|---|---|
| static | a value of a named type `N` | `N.len(&x)`, from `N`'s face | a direct call | none |
| by the value | a value of an interface type `I` | an observation of a codata value | an observation of a `νX. C` built by `unfold` | a `switch` on the closure's tag, or a direct call when the flow knows the code |
| by the context | a handler name `z` | `z.len()`, an operation | a handler over `N`'s state whose clauses call `N`'s face | the clause, at a static site |

- `lowered/faces.bc` writes one interface at all three binding times. It is checked and run, with
  `indirect 0` (E).
- The state type disappears in the value form, because `ν` hides it. So **interface values need
  no existential type former**: `Tally` and `Hist` objects have one type, and one `drive` body
  serves both (E).

**The friction between methods and effects resolves for answering operations, not for control
operations.**

- Methods as functions and methods as answering effects are one interface at two binding times.
  Each can be generated from the other: a type's face installed as a handler, or a handler's
  operations called on a value.
- What only effects have is capturing the caller's continuation. `ctl` operations (suspend, abort,
  resume) have no reading as a method.
- What only values have is being stored. Implementations bound by the context cannot be (#161).
- For operations that bear an invariant (`equal`, `hash`, `order`), coherence fixes the binding
  time; the caller does not choose it.

§4.5 lists where the reading does not resolve the friction, as six findings.

**No new kernel former.** None is needed for declarations, faces, interfaces, materialised values
or serde of typed resources: E for the two lowerings, B for the rest, by the elaboration tables of
§3 and §4.

- **Kernel constants and lemmas already on the work list are reached by ordinary method code**:
  - K2′, for an `imm` observation called from a `mut` one on an array-holding type;
  - a shortened family, for a one-lifetime `&self` view of a type holding two arrays;
  - `FShape` over arrays (B14), for the untyped `Json` value.
- **One possible kernel item is new**: an `imm` observation of a materialised codata value (F3,
  §8). Today such a value can only be forgotten behind an `imm` borrow.

**Serde round-trips a Kubernetes-style resource**, with derive specialising to plain functions,
one per type (E, `lowered/resource.bc`):

- the resource is encoded, decoded with its keys in any order, modified and encoded again;
- a missing required field raises `Fail[i32]` at its offset;
- `live 0`, `indirect 0`.

It needs the structure view and typed attributes in `poly`, which is elaboration. It needs no
kernel change.

**Recommendations in brief** (the menu is §11):

- the native paradigm's shape, with Rust-style receivers;
- a namespace per declared type;
- dot resolving at every binding time, by the receiver's type;
- interfaces as `codata` declarations, with conformance written at the type;
- abstraction per declaration, with the declaration's own face as the boundary (CLU's cluster), so
  it needs no module system;
- serde of abstract types only through a transparent view and a constructor.

**Decided**: recursion's layout keeps a written `box` (§6.11, 2026-10-20).

**The cited papers, read in full for this pass (§9).** None changes the design's direction. They
confirm the two faces, the three binding times, dot at every binding time and a namespace per
type. They refine three things:

- **F2 is about complex operations, not binary ones.** Cook separates a binary method from a
  complex one, which inspects the representation of two values (§4.2 of his essay). Objects have
  simple binary methods; *Codata in Action* types one (`Union : Set → Set → Set`, §2.3). So the
  value form's lack of binary methods is `NuOk`'s restriction, not codata's. The recommendation
  (keep them static) stands, with that reason (§4.5, item 15).
- **The static face of an abstract type is an ADT, in Cook's sense; only the value form is an
  object.** That is Cook's own reading of CLU, and it is why complex operations such as `equal`
  can live inside the boundary (§3.2, §6.4).
- **Attributions.** "`ν` hides the state, so no existential is needed" is Cook's §3.9, not
  *Codata in Action*. Effekt's capabilities are second-class blocks, not stored objects (§6.3).

---

## 3. The mechanism every paradigm shares

### 3.1 The data face

A declaration `data N[P…]<'l…> = S` gives the following (#141 §3–§5, decided):

| surface | core | kernel rule |
|---|---|---|
| record `{ f₁: A₁, …, fₙ: Aₙ }` | `A₁ ⊗ (… ⊗ Aₙ)`, in declaration order | `⊗` |
| variant `C₁(…) \| … \| Cₙ(…)` | `P₁ ⊕ (… ⊕ Pₙ)` | `⊕` |
| one constructor of one field | the field's type | none |
| `Option[T]` | `T + 1`: `Some` is `inl`, and the left summand gives the filler (SPEC §17) | `⊕` |
| recursion | `μX. ⟦S⟧[X/N]`, with the single-root rule for groups | `μ`, `roll`/`unroll` |
| parameters | substitution | none |
| constructor `Cᵢ(e…)` | `into_N (inj_i (e…))` | the identity, or `roll` |
| `match v { Cᵢ(x…) -> … }` | `case (out_N v)` along the `⊕` spine | `case` |
| field `v.f`, with `v` owned or a view | destructure `v`, or take the component of its fieldwise view (SPEC §5: "`Imm̲` acts fieldwise") | derived rules |
| field update `v.f = e`, with `v` a `mut` place | `modify` of the place, rebuilding the record (SPEC §5) | derived |

The name lives in the elaborator's types (the TIR's `named N args`), and lowering erases it.
Nothing here is new to this pass.

### 3.2 The codata face

A declaration's **face** is a table in the elaborator from names to functions. Each function takes
a receiver at an **observation mode**:

| mode | written (native paradigm) | the function's first parameter | Rust's receiver |
|---|---|---|---|
| shared observation | `on imm x: N { m(…) -> B }` | `x: imm 'a N` (a view) | `&self` |
| exclusive observation | `on mut x: N { m(…) -> B }` | `x: mut 'a N` | `&mut self` |
| consuming observation | `on x: N { m(…) -> B }` | `x: N` | `self` |
| introduction | `on N { m(…) -> N }` | none | an associated function |

- Each entry is an ordinary `fn` named `N.m` (mangled), a template in `N`'s parameters.
- **Inside the face, `x` has the data face**: constructors, patterns and fields. A client outside
  sees only the names and signatures.
- This is CLU's cluster: a type's operations and its representation are declared together, and
  only those operations reach the representation (Liskov et al. 1977, p. 565, requirement 2; E,
  read). Inside the cluster `cvt` changes the viewpoint between the abstract type and its
  representation, and it is "a change in viewpoint only; no computation is required" (p. 568,
  fn. 4). That is §3.1's iso, which lowering erases.
- CLU names an operation by its type, `wordbag$insert(wb, w)`, because "operations of two
  different data abstractions may have the same name" (p. 567). That is §6.1's N1 and §6.9's
  qualified introductions (`wordbag$create()`).

**Why "codata".** To a client, `N` is known only by what its observations answer. The face is a
record of observations, `&ₘ (mode_m N ⊗ Aₘ ⊸ F_Σₘ Bₘ)`, from which the elaborator selects
statically. A static selection from a known record is a projection of a known `&`, which reduces
to the component: a direct call. So the static face is the codata reading with the record **never
built**. That is "reify late".

**Cook's refinement** (*On Understanding Data Abstraction, Revisited*, 2009; E, read). Cook
separates two kinds of data abstraction:

- an **ADT** hides a representation behind a type name (type abstraction, §2), and its operations
  may inspect the representation of several values at once (§2.2);
- an **object** is known only through its interface (procedural abstraction, §3), and it can see
  no other object's representation ("autognosis", §3.3).

Read through that lens, the faces of §3 split as follows:

- A hidden declaration's static face is an **ADT**. Cook places CLU's cluster on that side (§6),
  and `poly equal at N` written inside the boundary inspects two representations, which only an
  ADT may do.
- The materialised value of §4.2 is the **object**.
- A unary observation reads the same either way, so for unary observations the static face is
  the codata reading with the record never built, as above.
- Cook's §5.2 says the same of modern languages: "when a class name is used as a type, it
  represents an abstract data type"; an interface used as a type is an object. That is the line
  between §4.1 and §4.2.

### 3.3 Interfaces

An interface is a `codata` declaration: a named set of observation signatures, each with its mode.

    codata Sized { len(imm) -> i32 }
    codata Counter { add(mut, n: i32) -> 1; get(imm) -> i32 }

- A type **gives** an interface when its face has each observation at its mode (`Stack[T] gives
  Sized`). That is checked at the declaration (§6.3).
- An interface type `I` used as a value type is the materialised form (§4.2).
- Used as a row entry, `I` is the context form (§4.3).

### 3.4 What the kernel sees

Nothing new. The checker sees `⊗`, `⊕`, `μ`, `ν`, `&`, functions and handlers.

- Every program that a declaration, a face or an interface elaborates to is a core term, checked
  by the unchanged checker.
- So `fundamentalC` and `adequacyC` cover it. This is decision 26's argument, as SPEC §36's
  baseline states it for `poly`.

---

## 4. Methods as codata: one interface, three binding times

### 4.1 Static: the receiver's type

`x.len()` with `x : N` (or `imm 'a N`, or `mut 'a N`) is `N.len(&x)`; §6.6 covers the `&`.

- It is a direct call, exactly today's `map_len(&m)`.
- Generic code over a type parameter `T` resolves `x.len()` at each instance, as a template body is
  elaborated per instance (decision 45).
- With the bounds layer (`ability`, later), the call is checked where it is written instead.

### 4.2 By the value: the codata value materialised

`x as I`, or an implicit conversion at an expected `I` (§6.8), builds a value of the interface
type:

    I<'c> = U (νX. (&ₘ Oₘ) & F 1)

- An observation at mode `mut` or `imm` is `Aₘ ⊸ F_Σₘ (Bₘ ⊗ [@c] U X)`: it hands back the rest, as
  `Aff`'s `call` does (SPEC §22).
- A consuming observation is `Aₘ ⊸ F_Σₘ Bₘ`.
- `F 1` is `close`, which runs the state's destructor (SPEC §12, class 2).
- The value is `unfold step s` over the state `s`, with `step` built from `N`'s face.
- An observation through a `mut` borrow of the object is `withswap` around the call (`d_callMut`,
  SPEC §22).

**The state type is hidden by `ν`.** `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` leaves no `S` in the
result.

- So a heterogeneous container of interface values (`Vec[Counter]`) is a container of one type,
  and a function over it is one body.
- Cook gives the correspondence (2009, §3.9; E, read): an implementation with hidden state,
  `∃ rep. rep × (rep → F(rep))`, "is the encoding of a final coalgebra", and it "corresponds to the
  greatest fixedpoint of F", the object type. `unfold` is that encoding read backwards.
- *Codata in Action* (§2.3; E, read) names codata "the language-agnostic representation of
  procedural abstraction", against ADTs as existential types (modules). It does not state the
  point about existentials itself.
- Here it is E: `lowered/faces.bc`'s `drive` is one definition, used at `Tally` and at `Hist`
  objects.

**Cost.**

- Each object is a closure, which the backend defunctionalises into a tag and the state's words.
- `faces.bc` compiles with `indirect 0`, because the flow knows the codes at each call.
- A call that two objects reach is dispatched by a `switch` on the tag (Backend README,
  *Closures*), not through a pointer.

**Constraints from the kernel**, all from `NuOk` (SPEC §7, §22):

- an observation's arguments may not mention `X`, so there is no binary method, even a simple
  one (F2, §4.5);
- the rest appears only under `⊗`, `⊕` and `[@a]`;
- each observation's row has closed operation types (`EffLeaf`).

### 4.3 By the context: the face installed as a handler

An interface `I` whose observations all answer has an effect form `E_I`: the same operations, with
the receiver erased. `with z = x as I { … z.len() … }` installs a handler over `x`'s state, whose
clauses are `N`'s face:

    handler N_as_I(mut s: N): E_I = { len() = N.len(&s); add(n) = N.add(&mut s, n) }

- This is §18's value-state handler. `with h(&mut c)` lends the cell, and each clause runs on the
  value swapped out.
- So the face's `imm` and `mut` functions are called on a fresh lend of the state, with no
  reborrow (E: `faces.bc`'s `tally_as` and `hist_as`).
- A client written against `E_I` (`fn client() -> i32 with CounterE`) is generic in the
  implementation.
- That client is served by the innermost handler of its instance or by the handler named, with
  §38's abstraction safety.

### 4.4 The other direction

A handler of `E_I` is not a value: it cannot be stored or returned (decision 57 R5, second class).

- Inside the handler's scope, its operations can be observed as a value only by wrapping them in a
  codata value whose observations perform the effect.
- That is a stored callback with a row: SPEC §33 *Open*, #161 part B.
- Effekt makes the same trade (Brachthäuser, Schuster and Ostermann 2020, §1.6; E, read). Blocks,
  capabilities among them, "can neither be returned nor stored in data structures", and that is
  what keeps effects safe with a light effect system. Its §7.2 lists what this costs: handlers that
  return functions, schedulers that store continuations, operations that take blocks.

So the four conversions stand as follows:

| from → to | how |
|---|---|
| static → value | generated from the face (§4.2) |
| static → context | generated from the face (§4.3) |
| value → context | §4.3, over the object's own observations |
| context → value | open, exactly where #161 is open |

### 4.5 Where the codata reading resolves the friction, and where it does not

The friction, as the user put it on #489:

- **methods as functions**: an explicit receiver, static, storable, state in the value;
- **methods as effects**: installed by `with`, in the row, swappable, able to suspend or abort,
  state in the handler, hard to store.

**Resolved.**

- **An explicit receiver against an installed capability.** These are two binding times of one
  interface (§4.1, §4.3), generated from one face, with one call syntax (§6.8).
- **State in the value against state in the handler.** It is the same state. The value form's
  `unfold` state and the context form's handler state are both `N`'s data face, and `faces.bc`
  uses the same functions for both.
- **"Can abort" is not a difference.** A static method has a row (`fn decode(t) -> N with
  Fail[DecodeError]`), and errors are a control-flow effect wherever the method is bound.
- **Swappable** is available wherever swapping is lawful: write the client against `E_I` (the
  context form) or against the interface type `I` (the value form).

**Not resolved.** Each is a finding, not something designed around.

- **F1. Control operations have no method reading.**
  - A `ctl` operation's implementation receives the caller's continuation, to suspend, abort or
    resume it. A method, at any binding time, is called and returns.
  - So "methods are codata" covers answering (`fn`) operations. `Yield`, `Async` and `Fail` stay
    effects.
  - An interface whose signature has a `ctl` operation has no static form and no value form.
- **F2. Binary operations are static only.** Cook (2009, §4.2; E, read) splits these in two, and
  the two halves have different causes:
  - A **complex** operation inspects the representation of two values: `equal`, `order`, or a
    `union` that merges two sorted lists. Cook: "Pure object-oriented programming does not
    support complex operations". Only an ADT, here the data face inside the boundary, has both
    representations. This is the ADT/object line, and no kernel change moves it.
  - A **simple** binary operation takes a second value of the interface type and uses only its
    observations: Cook's `union = λs. Union(this, s)` (§3, Fig. 8), or *Codata in Action*'s
    `Union : Set → Set → Set`, whose implementations combine sets "because both definitions of
    `Union` know nothing of the internal structure of the other `Set`" (§2.3). Objects have
    these; they are where Cook places the object's flexibility (§3.4).
  - Our value form has neither. A simple binary observation's argument mentions `X`, which is
    outside `NuOk` (SPEC §22 *Open*: "An argument mentioning `X` (a sink of the codata itself)
    stays outside `NuOk`"). That is a restriction of our kernel, not of codata. Cook's §3.9 notes
    the same point: with `union`, the interface's functor "is not a covariant functor".
  - Lifting it would be a kernel entry. **It is not recommended now**: the operations that bear an
    invariant are complex, and stay `poly` families, one case per type (§6.7, F5). A simple binary
    observation is worth the entry only when a program needs one.
- **F3. A shared observation of a materialised value is not provided.**
  - `Imm̲` takes a thunk to `Unk` (SPEC §22 *Observable view*: "A closure behind an `Imm` borrow is
    only forgotten"). So `xs: imm Vec[HasArea]` cannot call `x.area()` on its elements.
  - Today's routes: an object whose state is persistent can be `!`-typed (copied, and observed by
    value); any other object is lent `mut`.
  - The general fix is a kernel item: a relation clause for `Imm̲` at a `U(νX. C)` whose
    observations are all shared.
  - **This is the one new kernel question the design raises.** B: the clause has not been stated,
    and whether the paper's clause (4) allows it is NC.
- **F4. Implementations bound by the context are not storable.**
  - This is by design (decision 57 R5). Effekt pays the same price for the same reason (§4.4).
  - A program that wants a stored service uses the value form; one that wants scoped swapping
    uses the context form. The reading names the choice; it does not remove it.
- **F5. Operations that bear an invariant have a fixed binding time.**
  - A map's `hash[K]` must not depend on the handler in scope (one provider per type, decided).
  - So for those interfaces, the interface's laws decide the binding time; each caller does not
    choose it.
- **F6. `&self` calls between methods reuse one view.**
  - `d.ready()` calling `d.replicas()` uses the view `d` twice, which needs an `imm` borrow copied
    (#58, E1). `copy` exists (`docs/expressiveness.md`, B9).
  - On an array-holding type, an `imm` method called from inside a `mut` method needs K2′ (SPEC §9
    *Open*), or a `peek`.
  - Neither is new; ordinary method code reaches both.

---

## 5. Four syntax paradigms over the one mechanism

Each file in `data-declarations/paradigms/` writes the same four examples:

- **A.** A Kubernetes-style resource: nested records, optional fields, enums with payloads, lists,
  maps, defaults, renames and validation.
- **B.** A recursive tree, with `depth`, `contains`, a generator `in_order` and a consuming
  `insert`.
- **C.** An enum with payloads, and an interface that transposes it (`HasArea`).
- **D.** An abstract generic container `Stack[T]`, with:
  - introductions;
  - `imm`, `mut` and consuming observations;
  - a provider;
  - a serde view;
  - an interface;
  - one observation at all three binding times.

### 5.1 Paradigm A: ML/Haskell (`ml.bc`)

    data Strategy = Recreate
                  | RollingUpdate { max_surge : IntOrString, max_unavailable : IntOrString }
    module Stack : { type Stack a; fn len(s : imm Stack a) -> i32; … } = { data Stack a = … }
    class Sized a = { len : imm a -> i32 }
    instance Sized (Stack a) = { len = Stack.len }
    Stack.push(&mut s, 1); let a = Stack.len(&s)

- Operations live in a companion module named after the type.
- Abstraction is a signature that names the type without its definition.
- Interfaces are classes over a type parameter, with instances.
- Dot is not first-argument sugar here; `s |> Stack.len` is the chaining form.
- "Any `HasArea`" is written as an existential (`exists HasArea`), which here is the codata value
  of §4.2.
- **Fit**: the cleanest data face, but the codata face is second class (a module beside the type).
  An ML signature is the natural home of abstraction, and it presumes modules (#63).

### 5.2 Paradigm B: Rust (`rust.bc`)

    pub enum Strategy { Recreate, RollingUpdate { max_surge: IntOrString, max_unavailable: IntOrString } }
    impl Deployment { pub fn replicas(&self) -> i32 { … } pub fn scale(&mut self, n: i32) { … } }
    pub trait HasArea { fn area(&self) -> i32; }
    impl HasArea for Square { … }
    pub struct Stack[T] { items: buf T }        -- abstract, by the missing `pub`

- An inherent `impl` is the static face, and `&self`, `&mut self` and `self` are the modes.
- A trait is an interface, with conformance declared apart from the type.
- `dyn` is the materialised value.
- `pub` is per field.
- Kept different from Rust:
  - a recursive node is allocated by `box` at its constructor, not by a `Box` field type (§6.11);
  - typed attributes in place of macro attributes;
  - explicit `derives`.
- **Fit**: familiar, and receivers map exactly onto modes. It has two costs here:
  - `impl Trait for T`, written anywhere, needs an orphan rule (§6.3);
  - `pub` per field makes half-transparent types, whose constructibility depends on field
    visibility (§6.4).

### 5.3 Paradigm C: record-first, TypeScript-ish (`record.bc`)

    data Strategy =
      | { type: "Recreate" }
      | { type: "RollingUpdate", rollingUpdate: { maxSurge: IntOrString, maxUnavailable: IntOrString } }
    data DeploymentSpec = { replicas?: i32, selector: Map[string, string], strategy?: Strategy, template: PodSpec }
    data Stack<T> implements Sized = { private items: buf T   imm len(): i32 { … }   mut push(x: T) { … } }

- Everything is a record.
  - A variant is a record whose literal discriminant field is also its wire tag.
  - `?` marks an optional field.
  - Methods are written in the record's body, with the mode before the name.
  - Anonymous nested records are named after their position (#141 Q11).
- **Fit**: the best match for wire-format data. Kubernetes objects are written this way, and the
  discriminant field *is* the JSON tag, so serde needs no tagging attribute.
- Three costs:
  - The nominal identity already decided means TypeScript's structural typing does not carry
    over: two declarations with equal fields stay distinct.
  - Literal-typed tags are new surface. A union of literal records elaborates to a `⊕` whose
    summands are named by the literals.
  - Anonymous unions of leaf types (`i32 | string`) need the elaborator to choose the order of
    summands canonically.

### 5.4 Paradigm D: native to the calculus (`native.bc`)

    data Strategy @json(tagging = Adjacent(tag = "type", content = "rollingUpdate"))
      = Recreate | RollingUpdate(max_surge: IntOrString, max_unavailable: IntOrString)
    data Stack[T] hidden = { items: buf T }
    on Stack[T]          { new() -> Stack[T] = Stack { items: buf_new(4) } }
    on imm s: Stack[T]   { len() -> i32 = s.items.len()   items() with Yield[imm T] = … }
    on mut s: Stack[T]   { push(x: T) = s.items.push(x)   pop() -> Option[T] = s.items.pop() }
    on s: Stack[T]       { into_buf() -> buf T = s.items }
    codata Sized { len(imm) -> i32 }
    Stack[T] gives Sized

- `data` and `codata` are duals, each a single core former.
- **The face is grouped by observation mode**, which is how the borrow calculus types it:
  - everything in `on imm s` is an observation of the view `imm 'a Stack[T]`, checked with `s`
    lent shared;
  - everything in `on mut s` is checked with `s` lent exclusively;
  - the consuming block is visibly the one that moves.
- Introductions (`on Stack[T]`) are visibly not observations, since they have no receiver (§6.9).
- The face is the abstraction boundary (`hidden`). This is CLU's cluster: the representation is
  visible in the declaration's own `on` blocks and `poly … at` cases, and nowhere else (§6.4).
- **Fit**: the only paradigm whose organising principle is the borrow modes. A reader sees at a
  glance which observations can run while a view is out.
- **Cost**: it is unfamiliar. No mainstream language groups methods by receiver mode; Go's
  per-method receiver syntax, `func (s *Stack) Push`, is the nearest. A Rust-style per-method
  receiver (`fn len(imm self)`) can be offered inside the same `on Stack[T] { … }` block at no cost
  to the mechanism.

### 5.5 Comparison

| | A ML | B Rust | C record | D native |
|---|---|---|---|---|
| where operations live | a companion module | an `impl` block | the record's body | `on` blocks, by mode |
| the receiver's mode | in the parameter's type | `&self`, `&mut self`, `self` | `imm`, `mut`, `own` before the name | the block's mode |
| dot | not used (`\|>`) | first argument | first argument | an observation, at any binding time |
| abstraction | a signature | `pub` per field | `private` per field | `hidden` per declaration |
| interface conformance | `instance`, anywhere | `impl Trait for T`, anywhere | `implements`, at the type | `gives`, at the type |
| fit to wire formats | needs tagging attributes | needs tagging attributes | the discriminant is the tag | needs tagging attributes |
| the codata face is | second class | first class, per method | first class, per method | first class, per mode |
| needs modules (#63) | yes, for abstraction | yes, for `pub` | yes, for `private` | no |

**Recommendation**: D's structure (a boundary per declaration, faces grouped by mode, `gives` at
the type), with B's per-method receivers allowed inside a face block, and C's record literals for
construction (`Stack { items: … }`). Spellings stay provisional.

---

## 6. The open questions

### 6.1 Namespacing: how `m.len()` finds `len`

| option | how | for | against |
|---|---|---|---|
| **N1. A namespace per declared type** | the face is `N`'s namespace. `m.len()` looks in the namespace of the head of `m`'s type, after stripping `imm`/`mut`; `N.len(&m)` is the qualified form | one `len` per type by construction. It fixes D1's commonest case: `List.map` and `Iter.map` are different names, so the clash of `lib/list.bc`'s and `lib/iters.bc`'s `map` (`corpus/reject/rec-name-clash.bc`) becomes two functions. No global overloading | built-in heads (`array`, `buf`, `i32`) need faces, declared by the library that owns each |
| N2. Free functions, with dot as first-argument sugar (Koka) | `m.len()` is `len(m)`. Koka: "`s.encode(3)` … is simply syntactic sugar for the function call `encode(s,3)`" (Koka book §3.1.2; E, read) | no new scoping; one rule | `len` at many types needs overloading by type. Today's first-match template selection does not give that coherently, which is why SPEC §36 had to add specificity for `poly`. Koka adds static overloading for this (NC beyond its release notes) |
| N3. A module per type (ML) | `Map.len(m)` only | familiar to ML users | presumes #63; dot unused |

**Recommendation: N1.** It is what N2 becomes once overloading is added, without the overloading:
the receiver's type is the key. Free functions remain callable as `f(x)` and as `x |> f`.
Extensions by other packages are free functions (§6.3).

Three of the papers read for §9 do the same (E, read):

- CLU writes every operation with its type, `wordbag$insert(wb, w)`, and the authors "have found
  in using CLU that the compound form enhances the readability of programs" (Liskov et al. 1977,
  p. 567).
- *Copatterns* overloads destructors across record types and resolves `t.d` by the type inferred
  for `t` (Abel et al. 2013, §3.2, *Bidirectional Type Checking*), noting that "Overloading
  projections is standard in object-oriented programming".
- Binder et al. name a consumer function by its type, `cfun Expr:searchPos`, and call it with dot,
  `e.searchPos(cnt)` (2020, §3.4, Fig. 3).

### 6.2 Resolution by receiver type, against "one provider per type"

A face maps each name to one function, so a type has at most one `len`: one per type by
construction. The question is how faces interact with `poly` families, which are names across
types.

| option | rule | for | against |
|---|---|---|---|
| **R1. The face first, then families** | `x.m()` resolves to `N.m` when `N`'s face has `m`; otherwise to the family `m` when it has a case at `x`'s type (`x.hash()` is `hash(&x)`). A face member named like a family that has a case at `N` is an error at the declaration | dot reaches providers too; no silent shadowing | two lookups to explain |
| R2. Faces only | families are called only as functions | simplest | `x.hash()` and `a.order(b)` do not read naturally |
| R3. Faces are families | every face member is a case of a family named `m` | one mechanism | a family has one signature at every type (SPEC §36), but faces have per-type signatures (`Map.get(k)`, `Vec.get(i)`). This forces one signature per method name across the program |

**Recommendation: R1.** A family is an interface with one observation and the same signature at
every type; a face is per type. They are different things, and should stay so.

A generic receiver (`x.len()` with `x : T`, a type parameter) resolves per instance (decision 45),
so its error appears at the instance. The `ability` layer, when built, moves it to the call.

### 6.3 How an interface is declared, and what implementing one means

| option | declaration | conformance | for | against |
|---|---|---|---|---|
| **I1. A `codata` declaration, `gives` at the type** | `codata Sized { len(imm) -> i32 }` | `Stack[T] gives Sized`, written with the type's declaration and checked: the face has each observation at its mode | one per type by construction, with no orphan rule (as option D on #141); one declaration serves all three binding times | an interface written after a library type cannot be met by that type without a newtype |
| I2. `ability` (the bounds layer) | a bundle of `poly` families | `gives`, `given` | already planned; static and coherent | static only: no value form, no context form |
| I3. An effect signature as the interface (Effekt: a handler introduces a capability, passed as a second-class block) | `effect Sized { fn len() -> i32 }` | handlers | already built, for the context form | no receiver, so no static form; the capability cannot be stored, so no value form (Effekt §1.6; F4); `ctl` operations have no value form in any case (F1) |
| I4. Structural conformance (Go; CLU's `where` clauses) | `codata Sized { … }` | any type whose face matches | no declaration needed | conformance by accident: "no correct by convention" argues against meaning by matching names. CLU's bounds match by name and signature, and its authors note that the laws are not checked: `lt` "must also define a … ordering" that the compiler cannot see (Liskov et al. 1977, p. 571) |

**Recommendation: I1, with I2 as its static-only special case.**

- An `ability` is the static reading of a `codata` declaration whose observations may be binary
  (F2). An interface with a complex binary observation can have no value form in any language
  (Cook 2009, §4.2), and one with a simple binary observation has none under `NuOk`. Either is
  exactly an `ability`.
- Effekt groups several operations under one effect signature (`effect Lexer { def peek() …;
  def next() … }`, §6.3.1), which is I3's shape. Its formal calculus has one operation per
  capability (§3.1).
- Conformance is declared at the type, or by the library that declares a built-in head, until #63
  gives packages. Then the orphan question is #63's.
- An interface whose observations all answer also gives its effect form `E_I` (§4.3). A `ctl`
  operation makes it an `effect`, not a `codata`.

### 6.4 Transparent against abstract: how it is spelled, and per field or per declaration

**The boundary.** #141 put the boundary between packages (`export data N` against exporting the
name only), which presumes #63. The user's reading, "inside its declaration it is data", suggests a
boundary that needs no modules:

| option | boundary | for | against |
|---|---|---|---|
| **B1. The declaration's own face (CLU's cluster)** | the representation is visible in the declaration's `on` blocks and its `poly … at N` cases, in the same file | works without #63; matches "two faces"; one place to read an abstract type's invariant | every operation that needs the representation is written in the face, so a large abstract type has a large face |
| B2. The module or package (#141, Rust) | visible anywhere in the defining module | familiar; helpers need not be methods | needs #63 |
| B3. B1 now, widened to B2 when #63 lands | as B1, later as B2 | no waiting | two rules over time |

**Granularity.**

| option | for | against |
|---|---|---|
| **G1. Per declaration** (`data N hidden = …`) | one bit per type; derive, match and serde each have one answer (§6.5) | "public data with one private field" is written as an abstract type plus accessor observations |
| G2. Per field (Rust's `pub`) | half-transparent types | a type with one private field cannot be constructed or matched outside, so it is abstract with extra accessors anyway; and derive must say what it sees field by field |
| G3. Per constructor | hides some constructors (smart construction of some variants) | rarely needed |

**What the papers say** (E, read):

- B1 is CLU's rule, and CLU enforces it by type checking. Only the code inside a cluster may use
  `cvt` (Liskov et al. 1977, p. 570, §3.3), and "conventions are no substitute for enforced
  constraints" (p. 575).
- Cook calls what B1 builds an ADT, not an object (§3.2 above). He lists its strengths: complex
  operations can be implemented efficiently, and it has sound proof techniques (§2.6).
- He also gives its cost: one implementation of the abstraction per program, unless modules allow
  more (§2.3–§2.4). G1 per declaration has that cost; the value form (§4.2) is how two
  implementations of one interface meet.

**Recommendation: B3 with G1.**

- Per-field visibility is sugar over G1: an abstract declaration whose face has a derived accessor
  observation for each "public" field.
- So G1 is the primitive, and G2 can be added later as that sugar, with nothing to undo.
- Spelling: transparent is the default (the serde and Kubernetes case); `hidden` (provisional)
  makes the representation private.

### 6.5 What derive, match and serde see across the boundary

| | transparent | abstract |
|---|---|---|
| construct | constructors, record literals, `..r` update | introductions only |
| match | yes | no (there is no `out_N` outside) |
| fields | read and update | observations only |
| `derives` | over the structure, everywhere | **written in the declaration only**, so the author decides what the derived code sees. A derived `equal` over a hash map's slots would be wrong, and it is the author's to refuse |
| `poly` cases at `N` | by anyone the coherence rule allows | inside the boundary only |
| serde | structural, driven by `@json` | **only through a transparent view**, `encode via V by (to_view, from_view)`. `from_view` is an introduction, so decoding goes through the same checks as any construction (§7.4) |

**Recommendation**: as the table. The serde row is the one that matters for "no correct by
convention". A decoder cannot break an abstract type's invariant, because it has no constructor
other than the public ones.

### 6.6 Receiver modes as observation modes

The modes are the calculus's own (`imm 'a N`, `mut 'a N`, owned), so the checker already types
every method. The question is what the call site writes.

| option | `v.len()`, with `len(imm self)` | for | against |
|---|---|---|---|
| **M1. The `&` inserted from the declared mode** (Rust's auto-ref) | `len(&v)`, lent for the call: SPEC §35's scoped cell, and #577's decision that "`f(&mut x)` lends `x` for the call" | the mode is in the face's signature; lexical, so nothing outlives the call; no ceremony | a `mut` lend is not visible at the call site |
| M2. Written at the site | `(&v).len()`, `(&mut v).push(x)` | every lend visible | the ceremony the user rejected in #577 |
| M3. A marker on the dot for `mut` | `v.len()`, `v!.push(x)` | `mut` visible, `imm` light | a new sigil |

**Recommendation: M1.** The lend is the call's, as `f(&mut x)` already is, and its extent is
lexical.

- A consuming observation (`v.into_buf()`) moves `v`; a later use is the usual "used after move"
  error, which linearity gives.
- A receiver that is already a borrow (`d: imm 'a N`) is passed as it is: `d.len()` passes `d`.
  That is F6's second use of one view (#58).
- Inside a face, the modes nest as the calculus allows:
  - an `imm` observation called from an `imm` one passes the view (F6, #58);
  - a `mut` called from a `mut` one reborrows through `withswap`;
  - an `imm` called from a `mut` one needs K2′ on arrays (F6), and is a `peek` until then.

### 6.7 Codata providers against one per type

Should interface values have `equal` and `hash`?

| option | for | against |
|---|---|---|
| **P1. None by default** | consistent with SPEC §36 ("No case at a function"): a materialised value is a thunk | a set of interface values cannot be written |
| P2. Each object brings its own (`equal` as an observation) | open to every implementer | F2 (binary, so not codata); and incoherent across two objects of different underlying types: whose `equal` applies? |
| **P3. Through a key observation** | `codata Named { key(imm) -> string }`, then `poly equal at Named = equal(x.key(), y.key())`: one case at the interface type, coherent | the interface must expose a key |

**Recommendation: P1, with P3 when a program needs it.** P3 is the key-projection pattern of
#489's C5 at an interface type, and it keeps one provider per type.

Cook supports both halves (E, read). An ADT has "no predefined notion of equality", so it must be
written into the interface (2009, §2). And COM, the purest object model he cites, has "no
built-in notion of equality" (§3.3). P3's `equal` compares two objects through an observation
only, so it is a simple binary operation in Cook's sense (F2). A family case at the interface type
gives it, with no `NuOk` change.

### 6.8 Is dot reserved for the function reading, or does it resolve at any binding time?

Dot already means two things today:

- `.1` and `.2` select an observation of a `&`: a codata projection;
- `n.op(v)` performs `op` at the handler named `n` (SPEC §38).

| option | for | against |
|---|---|---|
| D1. Static only | a dot always costs a direct call | interface values and named handlers need another syntax, and `n.op` already exists |
| **D2. Any binding time, by the receiver's kind** | one call syntax. The syntax or the type determines the receiver's kind: a value of a named type (static), a value of an interface type (by the value), a handler name (by the context). The three never overlap, since handler names are not values | the cost of a dot is read off the receiver's type, not off the dot |
| D3. A sigil per binding time | the cost is visible at the site | three syntaxes for one idea, against the user's "one call syntax; the type tells which" |

**Recommendation: D2**, which is the user's direction.

Binder et al. (2020; E, read) type the two readings of dot by one rule. In `e.d(ē)`, `d` is a
destructor of a codata type or a consumer function of a data type (Fig. 11, T-Dtor/Cfun). Their
transposition turns one into the other while keeping the call's syntax (§6.3: it "happens to have
the same syntax"). That is D2 for the static and value binding times.

- Zero cost holds: the static case is a direct call, and the value case is reified only where a
  value of interface type is formed. That is `x as I`, or an implicit conversion at an expected
  interface type.
- Whether that conversion may be implicit (`let o: Sized = s`) is a sub-choice. **Recommended:
  explicit (`s as Sized`) for now.** The conversion builds a closure, which allocates where the
  state does not fit in a value, and it fixes the state's lifetime bound `'c`.

### 6.9 Introductions: kept visibly distinct from observations?

| option | for | against |
|---|---|---|
| **E1. Yes: no receiver, called qualified** (`Stack.new()`, `Deployment.decode(t)`) | an introduction makes a value, while an observation consumes or inspects one; `N.f(…)` says which | an `N.` prefix at each construction |
| E2. Free functions | shortest | an introduction of `N` is then not found from `N` |
| E3. Constructors only | the data face is enough | abstract types have no public constructors, so they need E1 anyway |

**Recommendation: E1.** For transparent types the constructors are introductions too
(`RollingUpdate(…)`, `Deployment { … }`), unqualified, as #141 has them.

### 6.10 Traits, compared honestly

What this design builds, set against Rust's traits:

| traits give | here | difference |
|---|---|---|
| inherent methods | the face (§3.2) | the same; grouped by mode in paradigm D |
| interfaces with static dispatch | `codata` and `gives` (§6.3) | conformance at the type, not anywhere |
| bounds checked at the call | the `ability` layer, later | the same, when built |
| coherence | `poly`, one case per type (SPEC §36) | built already, at the family rather than the trait |
| blanket impls | `poly equal[A, B] at A * B` (SPEC §36) | built already |
| associated types | the `ability` layer, later | the same |
| default methods | not proposed | can be added to `codata` declarations with no kernel change (B) |
| `dyn Trait` | `x as I`, a `νX` value (§4.2) | no existential former; binary methods are excluded (F2), as Rust's object safety excludes `Self` arguments |
| the orphan rule | none needed: conformance is at the type | an interface cannot be retrofitted onto a foreign type without a newtype |
| — | the context binding (`with z = x as I`) | traits have no counterpart |

So this is a trait system in all but three respects:

1. conformance is declared with the type: option D's narrowest orphan rule;
2. operations that must be coherent are families, not trait methods;
3. every interface also has a context form.

Cook (2009, §5.3; E, read) places Haskell's type classes on the ADT side. They are "based on
algebraic signatures as in abstract data types" but "do not enforce any hiding of
representations", and "a type can only be an instance of a class in one way". `poly` families
and the `ability` layer are that side here, coherent because a type has one case (SPEC §36). The
object side is `x as I` (§4.2). Rust's traits mix both: `impl Trait for T` with static dispatch is
the first, and `dyn Trait` the second.

**Recommendation**: say so plainly in the docs and the book. Whether to call `codata` declarations
"traits" is a naming choice. Keeping our own names avoids importing Rust's rules along with the
word (decision 60's practice).

### 6.11 Recursion's representation: a written `box` (decided)

**Decided on 2026-10-20** (item 13 of §11): "I think heap allocations should be explicit
re:boxing." A recursive declaration keeps a written `box`, as typed elaboration §5.3 has it.
Automatic boxing, one box a node placed by rule, is rejected for declarations.

**The rule**, from §5.3 and #141's answer 5 ("recursion under `box` or a block"):

- A constructor with fields is a **block**, one cell per field, each a place. In
  `data Tree[T] = Leaf | Node(left: Tree[T], value: T, right: Tree[T])`, `Node` is a block.
- Building a block node is written `box Node(l, v, r)`. That is one heap allocation a node,
  visible where the node is built (§5.3: `box Cons(x, t)` is
  `roll (inr (alloc_s[List_Cons] (x, t)))`).
- `Node(l, v, r)` without `box` is **an error that asks for `box`**, never a silent promotion. The
  one exception is §5.3's reassembly: `Node(c₁, c₂, c₃)` applied to existing cells rebuilds a node
  without allocating, and it is taken only when the arguments are cells.
- A constructor with no fields (`Leaf`) allocates nothing.
- The pattern `box Node(l, v, r)` frees the block and binds the values. `Node(c₁, c₂, c₃)` on an
  owned node binds its cells (§5.3), and on a view it binds the fields' views (SPEC §5, fieldwise).
- A field may instead have type `box A`, a cell of its own. A recursive occurrence under neither a
  block nor `box` is **an error at the declaration that asks for `box`**.
- Recursion under an array (`Arr(Vec[Json])`) is under the array's allocation, the other written
  heap allocation §5.3 names. It needs no `box` (built, SPEC §61, #722). Its destructor is the
  owned fold at the class `P` (§61); the borrowed fold and a fold block over it wait (U2 of
  #595).

**What it changes.**

- The four `paradigms/` files build tree nodes with `box` (example B). Matching an owned tree
  frees the node, and rebuilding allocates one. Both are written, so the allocation count can be
  read off the source.
- `lowered/` needed no change. `faces.bc` boxes its objects' state explicitly (`boxed['c]`), and
  `resource.bc` has no recursive declaration.
- SPEC §35's one box a node stays a backend rule for recursive types written in core. A declared
  type's elaborated `μ` has a `ref` on every cycle already, so the rule finds nothing to add. B, to
  check in U1 with `bcc-counts`.
- Whether SPEC §35's rule should also go for core-written `μ` types, so that no recursive layout
  allocates without a written `box`, is **not decided**. It touches the corpus's core-written
  types, and is a question for the user, not settled by this item.

Cell classes (C2b) add nothing here: a declared type's cells are its structure's cells.

### 6.12 Variants in place (#19)

A `mut` observation of an enum that changes a payload in place (`match self { Circle(r) -> *r = …
}`) needs a `mut` borrow of the active payload. `Ref` does not distribute over `⊕` (SPEC §5
*Open*).

- Until #19, such a method takes the value out and rebuilds it (`modify`).
- That is correct, and costs the rebuild (L-1's load and store question).

**Recommendation**: keep #19 separate; nothing in this design depends on it.

---

## 7. Serde: the test of `derive`

### 7.1 What a Kubernetes resource needs

From example A of `paradigms/*.bc`:

- nested records;
- `Option` fields, absent on the wire;
- defaults (`@default`);
- renamed keys (`containerPort`, `rename_all = Camel`);
- a C-like enum (`RestartPolicy`);
- an enum with payloads, adjacently tagged: `Strategy`, Kubernetes' `DeploymentStrategy` with
  `type` and `rollingUpdate`;
- an untagged union (`IntOrString`);
- lists (`Vec[T]`);
- maps with string keys (`labels`, `selector`);
- validation (`@schema(minimum)`);
- the OpenAPI schema for a CRD, which cannot use `$ref` (#141 §9.4).

### 7.2 The mechanism as decided, and what it lacks

The derived functions are `poly encode[T]<'a>(v: view 'a T) with Emit` and `poly decode[T]<'a>(c:
mut 'a Cursor<'t>) -> T with Fail[DecodeError]`.

- They are written by cases on the **structure view** (#141 §9.2): `data(d) A`, `record F`,
  `field(f) A`, `variant C`, `con(c) F`, the spines, the leaves, and `N[A…]`.
- Each is specialised at each type by decision 45's instantiation, and the output is checked by
  the unchanged checker.
- The format is the handler (`Emit`), so one traversal serves several formats (#489 §5: "the best
  fit any design found").

SPEC §36's `poly` has no structure view and no attributes, and no case at a recursive type. So
derive needs the following, all elaboration:

1. **The structure view** as case heads, over the declaration table's labels, constructors and
   attributes (`TypeInfo`, #141 §9.1).
2. **Typed attributes** (`attr json on field = { rename: Option[lit], … }`, #141 §8.2), branched on
   at elaboration.
3. **Cases at recursive types.**
   - SPEC §36 refuses them, because a recursive case is a recursion that the effects pass groups by
     name before types are known (D1).
   - The resource is recursive only through `Vec` and `List`; `Json` and trees are recursive
     themselves.
   - The fix is #489's C2 (instantiate, then group), already on the list.

### 7.3 The round trip, lowered

`lowered/resource.bc` writes by hand what `encode` and `decode` specialise to at `Deployment`,
`Meta`, `Label`, `Spec`, `Strategy`, `Container` and `Port`: one function per type, field by field,
with the keys as literals.

- **Encode.** Each record writes `{`, then `"key":value` per field in declaration order, then `}`.
  An absent `Option` field is omitted (#141 Q8), and `Strategy` is adjacently tagged.
- **Decode.**
  - Each record reads its fields **in any order** into one option slot per field, recursing once
    per member (`port_fields(c, name, cp)`), then assembles the record.
  - A missing required field raises `Fail[i32]` at its offset; a missing `Option` field is `None`.
  - The adjacently tagged `Strategy` reads its tag and its content into slots, and chooses the
    variant at the end.
- **Run** (E):
  - the resource is encoded, decoded from that text, its `replicas` changed from 3 to 5 by a field
    update, and encoded again;
  - an input whose `metadata` lacks `labels` raises at offset 26;
  - `live 0`; `bcc-counts` gives allocs 51, indirect 0, copies 0.

What the lowering found (each E, from `bcc check`):

- **A generic recursive decoder over a decoder passed as an argument is refused**: "`dec_vec_rest`
  is recursive and takes a computation parameter: not provided (SPEC §33)".
  - Specialisation does not produce that shape: `decode` at `Vec[Port]` calls `decode[Port]`
    directly. So the lowering has one list decoder per element type, as a `poly` instance would.
  - It is not a blocker for derive. It is one for hand-written generic combinators.
- **The encoder takes each value and hands it back.** Reading an element of a `buf` of records
  through a view means a `withload` per element (SPEC §36, *Elaboration that the map uses*). The
  derived form takes a view, and the generated code has the same shape as `map_get`'s.
- **The cursor is an owned string, threaded through**, as `awfy/json.bc` does. The natural form is
  a borrowed cursor that raises across the input's borrow: B10, `docs/expressiveness.md` unit 8.
- **The `Map[string, string]` labels are written as `Vec[Label]` in the lowering.**
  - `map_iter` at a key that is not its own view copies the key out of its slot, and it is not
    provided for `string` keys (SPEC §36 *Not provided*).
  - That is a gap in the library (unit 18, "map iteration over owned keys"), not in the language.
  - The abstract map's serde goes through its observations (§7.4).

### 7.4 Abstract types across the wire

`Map[K, V]` is abstract, so its derived encoding must not walk its slots. The declaration says how
it crosses the wire:

    data Map[K, V] hidden = { … }
      encode via Vec[(K, V)] by (m -> m.entries(), v -> Map.from_entries(v))

- `encode[Map[K, V]]` is `encode[Vec[(K, V)]]` of the view. Without allocating, it is instead a
  case of `encode` written inside the boundary over `m.entries()`.
- `decode` builds through `Map.from_entries`, which is an introduction.
- A JSON object `{"app": "web"}` for `Map[string, V]` is the `via` view `Vec[(string, V)]` with
  `@json(as_object)`.

This is the key-projection idea of #489's C5, applied to the codec.

### 7.5 The untyped `Json` value

`data Json = Null | Bool(bool) | Num(i64) | Str(string) | Arr(Vec[Json]) | Obj(Map[string, Json])`
puts `Json` under an array. That is outside `FShape` (SPEC §6), so today it has no fold and no
destructor.

- Two routes are on the list:
  - spike S-D: inline the container's constructors into one `μ` (elaboration);
  - spike S-H: `FShape` over arrays (a kernel lemma).
- **The typed resource needs neither.** Its `Vec`s are of non-recursive records, and a `buf` of a
  non-recursive type has a destructor today (E, `resource.bc`).
- Only the untyped value waits on B14, with `@json(flatten) extra: Map[string, Json]` for unknown
  fields.

### 7.6 Kernel formers

**None needed.** This is E for the typed round trip, and B for the attributes and the structure
view, which #141 §9.1 shows are elaboration. The schema (`derives schema`) is text generated over
the same view.

---

## 8. Findings

### 8.1 Kernel

| item | kind | needed by | status |
|---|---|---|---|
| none, for declarations, faces, interfaces, materialised values, the context binding, and serde of typed data | — | — | E (`faces.bc`, `resource.bc`); B for the parts not lowered |
| **F3: an `imm` observation of a materialised codata value** | a relation clause for `Imm̲` at a `U(νX. C)` whose observations are shared | `xs: imm Vec[HasArea]` calling `x.area()` | **new**; not stated; NC whether sound |
| F2: an observation whose argument mentions `X` | an extension of `NuOk` (SPEC §7 *Open*) | simple binary methods in the value form (Cook's `union`); complex ones need the representation and no kernel entry gives them | not recommended until a program needs one (§4.5) |
| K2′: the `imm` reborrow of a `mut` family | a constant, with its proof (SPEC §9 *Open*, #174) | an `imm` method called inside a `mut` one, on an array-holding type | on the list, unit 17 |
| a shortened family (`[Imm 'k A] ⊑ [Imm 'x A]`) | a constant (SPEC §36 *Not provided*) | `&'a self` views of a type holding two arrays at one lifetime (`MapRef<'k, 'x>` today) | on the list, unit 19 |
| `FShape` over arrays, or nested `μ` | a lemma (S-H) or elaboration (S-D) | the untyped `Json`; trees whose children are a `Vec` | on the list, units 5–6 |

### 8.2 Elaboration and library

- A namespace per declared type (§6.1) removes D1's commonest case.
- `poly` needs the structure view, attributes, and cases at recursive types (§7.2).
- Any `&self` method that calls another reaches #58, an `imm` borrow used twice (F6).
- `map_iter` over owned keys (§7.3).
- A recursive function over a computation parameter (§7.3): not needed by derive.

### 8.3 Where the codata reading did not resolve the friction

§4.5 states each:

- F1, control operations;
- F2, binary operations (complex ones are static by nature; simple ones by `NuOk`);
- F3, a shared observation of an object;
- F4, storing implementations bound by the context;
- F5, operations that bear an invariant have a fixed binding time;
- F6, reusing a view, and K2′.

---

## 9. Prior art

**Read in full for this pass, 2026-10-20** (E for what is quoted; PDFs fetched to the session's
scratch directory):

- **The Koka book**, at koka-lang.github.io.
  - §3.1.2 *Dot selection*: "the expression `s.encode(3)` does not select the `encode` method from
    the string object, but it is simply syntactic sugar for the function call `encode(s,3)`".
  - §3.3.1 *Structs*: "Koka automatically generates accessor functions for each field".
- **Barbara Liskov, Alan Snyder, Russell Atkinson and Craig Schaffert, *Abstraction Mechanisms in
  CLU*, Communications of the ACM 20(8):564–576, August 1977** (13 pp.).
  - Clusters: only a cluster's operations reach the representation (p. 565), through `cvt`, "a
    change in viewpoint only" (p. 568, fn. 4; p. 575). That is §3.1's iso and §6.4's B1.
  - Operations are named `type$op` (p. 567): §6.1's N1, §6.9's E1.
  - `where t has lt, equal: proctype (t, t) returns (bool)` (p. 571): bounds checked at each use,
    by name and signature, with the laws left unchecked (§6.3's I4).
  - Iterators, `iter … yields`, several per abstraction, on the program stack (pp. 572, 575): the
    generators of a face (`items() with Yield[imm T]`).
  - "Conventions are no substitute for enforced constraints" (p. 575).
- **William R. Cook, *On Understanding Data Abstraction, Revisited*, OOPSLA 2009, pp. 557–572**
  (15 pp.).
  - ADTs are type abstraction; objects are procedural abstraction, and know only themselves
    (autognosis, §3.3). The static face of a hidden type is an ADT, and `x as I` an object (§3.2
    above).
  - Simple against complex binary operations (§4.2): F2 in §4.5.
  - An ADT with only simple operations converts to objects without loss (§4.2, the `wrap`
    construction). That is §4.2's "static → value, generated from the face", with the same
    condition `NuOk` imposes.
  - The ∃-encoding of an object's state is the greatest fixed point (§3.9): §4.2's "`ν` hides the
    state".
  - Type classes are ADT-side, one instance per type (§5.3): §6.10.
  - The extensibility trade-off, new representations against new operations (§4.3): I1's cost in
    §6.3.
- **Paul Downen, Zachary Sullivan, Zena M. Ariola and Simon Peyton Jones, *Codata in Action*, ESOP
  2019, LNCS 11423, pp. 119–146** (28 pp., the authors' version).
  - Codata is the representation of procedural abstraction, against ADTs as existential types
    (§2.3).
  - Its codata observations may take the codata type as an argument (`Union : Set → Set → Set`,
    §2.3; Fig. 3 puts no restriction on `τ`), so binary observations are codata's, and their
    absence here is `NuOk`'s (F2).
  - Intermezzo 1 (§2.4) asks for linear codata in which some observations take "full ownership of
    the object itself" and others "merely borrow the object for the duration of the action", with
    Rust's ownership as the model. That is §3.2's consuming and `imm`/`mut` observation modes.
  - The visitor (data → codata, §3.2) and tabulation (codata → data, §3.3) are compositional
    encodings. They are not the transposition of example C (Binder et al., §9, say the same).
- **Andreas Abel, Brigitte Pientka, David Thibodeau and Anton Setzer, *Copatterns: Programming
  Infinite Structures by Observations*, POPL 2013, pp. 27–38** (13 pp.).
  - Definition by observation. A copattern's head is the hole of the function being defined
    (`q ::= · | q p | q.d`, §3.3). So the copattern definition here is the materialised object's
    (`(x as I).len() = N.len(&x)`, §4.2's `step`). The `on` blocks of paradigm D are consumer
    functions of the data face (Binder et al.'s `cfun`), grouped by mode, not copatterns.
  - Positive types (`1`, `×`, `μ`) and negative ones (`→`, `ν`), by focusing (§3.1): the kernel's
    split, which the two faces follow.
  - Destructors overloaded across record types, resolved by the type of the head (§3.2): N1.
  - `docs/surface-cbpv.md` declined copattern definitions for steps; faces are a different use.
- **David Binder, Julian Jabs, Ingo Skupin and Klaus Ostermann, *Decomposition Diversity with
  Symmetric Data and Codata*, PACMPL 4 (POPL), Article 30, January 2020** (28 pp.).
  - Constructorization and destructorization generalise defunctionalisation and
    refunctionalisation into total, mutually inverse transpositions of a whole program (§2, §6,
    Thm. 7.3–7.6). Example C (`Shape` and `HasArea`) is one. An automatic transposition is not
    proposed here.
  - Consumer functions, `cfun T:d`, are functions with a top-level match on their first argument,
    called with dot (§3.4). That is the static face; generator functions are introductions.
  - One typing rule for `e.d(ē)` over destructors and consumer functions (Fig. 11): D2.
  - Their outlook (§8, *Separate Compilation*) raises importing a type as data or as codata, which
    is §4's choice of binding time made at the boundary.
- **Jonathan Immanuel Brachthäuser, Philipp Schuster and Klaus Ostermann, *Effects as
  Capabilities: Effect Handlers and Lightweight Effect Polymorphism*, PACMPL 4 (OOPSLA), Article
  126, November 2020** (30 pp.).
  - Effect types are read as the capabilities a computation requires from its context (§3.2). A
    handler introduces a capability, passed as an extra block argument in System Ξ (§4–§5, Fig. 4):
    §4.3's context form.
  - Blocks, capabilities included, are second class: "can neither be returned nor stored in data
    structures" (§1.6), which is the price of effect safety. §7.2 lists the programs that costs.
    That is F4 and §4.4's open conversion.
  - One effect signature may group several operations (§6.3.1, `effect Lexer`); the calculus has
    one per capability. "Capabilities as objects" is not this paper's phrasing.
  - Accidental capture and lexical handling (§7.1) are what SPEC §38's named handlers address.

**Quoted from repository documents**:

- via #141 §15: generics-sop, PolyP, serde, kube-rs, Haskell 2010's `newtype`, GHC.Generics, Zig,
  Swift Codable and Lean 4's deriving;
- as SPEC §38 cites them: Zhang and Myers, Helium and Effekt.

**Recalled, not read (NC):**

- **Koka's static overloading** (Leijen and Whiting, *Syntactic Implicits with Static
  Overloading*), known only from the Koka release notes.
- **Go's method receivers and structural interfaces** (§6.3's I4).

## 10. Proposed units, after approval

This refines #593 (§19 unit 4), #595 (unit 6) and #65 (unit 7). Each unit lands with its SPEC
entry, its lowering and running corpus programs (decision 17), and runs `make gate-full` where it
touches `Frontend/`.

| # | unit | needs | refines | done when |
|---|---|---|---|---|
| U1 | **`data`, monomorphic and generic, transparent**: records, variants, `Option` and `Vec` as library declarations, constructors, record literals, `match`, fields, field update through `mut`, the single-root rule; recursion under a written `box` (§6.11, decided): `box C(…)` builds a block node, and a recursive constructor or field without `box` is an error that asks for it | — | #593 | `data-box-tree`, and T07, T09, T10, T11 as written; the #593 programs; `bcc desugar` of each equal to its hand lowering; a tree built without `box` rejected with a message that asks for `box` |
| U2 | **Faces and dot**: `on` blocks (or the chosen spelling), a namespace per type, dot at the static binding time, the `&` inserted by mode, introductions. `lib/map.bc`, `lib/buf.bc` and `lib/aff.bc` get faces; the old names stay as aliases until the corpus has moved | U1 | #593 | `m.insert(k, v)` and `m.len()` on the map; the D1 clash (`List.map` against `Iter.map`) accepted; counts unchanged |
| U3 | **Abstraction**: `hidden`, with the face as the boundary (§6.4's B1) | U2 | #593 | `Map` and `Stack` abstract; a client's `match` on them rejected, with a message |
| U4 | **`codata` declarations and interfaces**: observations with modes; `gives`, checked; `x as I` by `unfold`; dot on interface values; the frontend's five `CTy` abbreviations deleted for library declarations (#141 decision 6) | U2 | #141 D3 | `faces.bc` written in the surface, with the same core; `pull` and `iter` as library declarations; counts unchanged |
| U5 | **The context binding**: `with z = x as I { … }`, with the effect form `E_I` generated | U4 | — | `faces.bc`'s handlers generated |
| U6 | **Derive**: `attr`, the structure view, `derives`, cases at recursive types (C2); `eq`, `debug`, `clone`, `hash`, `order` | U1; C2 | #593, #65 | the providers derived for the corpus's declarations; `poly-providers` unchanged |
| U7 | **JSON**: `encode`, `decode` and `schema`, with `@json` and `@schema`, and `via` for abstract types; over unit 8 (aborts across a borrow) | U6, U3, §19 unit 8 | #65 | `resource.bc` in the surface: a Deployment read, changed and printed byte for byte; malformed input raising across the input's borrow |
| U8 | **Recursive data under arrays** (`Json`), by S-H or S-D | U1, S-H | #595 | as #595 says |
| K? | **F3**, if wanted. A spike, yes or no: is an `imm` observation of a `U(νX. C)` with shared observations sound in the relation, as one clause? Kill criterion: materialised values are observed by value (`!`) or through `mut` | U4 | — | the answer |

Not in these units: the `ability` layer (its own unit, decided), #19, K2′ (unit 17), and the
shortened family (unit 19).

---

## 11. Decision menu

Each item gives the options, the trade-offs and a recommendation. **All items are decided,
2026-10-20.** Item 13 was decided first; the user then accepted every other recommendation, and
the additions A1–A8 below: "Let's just go with that menu as is."

1. **Syntax paradigm** (§5).
   - Options: A, ML (companion modules); B, Rust (`impl`, `pub` fields); C, record-first
     (discriminant fields, `?`); D, native (faces grouped by mode, `hidden` per declaration).
   - Trade-off: familiarity (B) against the borrow modes as the organising principle (D) and the
     best fit to wire formats (C).
   - **Recommended**: D's structure, with B's per-method receivers allowed inside a face and C's
     record literals.
2. **Namespacing** (§6.1).
   - Options: N1, a namespace per declared type; N2, Koka's free functions with overloading; N3, a
     module per type.
   - **Recommended: N1.** It also removes D1's commonest case.
3. **Faces and `poly` families** (§6.2).
   - Options: R1, the face first and then a family with a case at the type, with a shadowing
     member an error; R2, faces only; R3, faces as families.
   - **Recommended: R1.**
4. **Interfaces** (§6.3).
   - Options: I1, `codata` with `gives` at the type; I2, `ability` only; I3, effect signatures; I4,
     structural conformance.
   - **Recommended: I1, with `ability` as its static-only case.** Conformance outside the type
     waits for #63.
5. **The abstraction boundary** (§6.4).
   - Options: B1, the declaration's face (CLU); B2, the module (#63); B3, B1 now and B2 later.
   - **Recommended: B3.**
6. **Granularity of abstraction** (§6.4).
   - Options: G1, per declaration; G2, per field; G3, per constructor.
   - **Recommended: G1**, with per-field visibility as later sugar over accessor observations.
7. **What crosses the boundary** (§6.5).
   - **Recommended**: an abstract type derives only inside its declaration, and its serde goes only
     `via` a transparent view and an introduction.
8. **Receivers** (§6.6).
   - Options: M1, the `&` inserted from the declared mode, lent for the call; M2, written at the
     site; M3, a `mut` marker on the dot.
   - **Recommended: M1.**
9. **Providers for interface values** (§6.7).
   - Options: P1, none; P2, one per object; P3, through a key observation.
   - **Recommended: P1, then P3 when a program needs it.**
10. **Dot** (§6.8).
    - Options: D1, static only; D2, every binding time, by the receiver's kind; D3, a sigil per
      binding time.
    - **Recommended: D2**, with materialisation explicit (`x as I`) for now.
11. **Introductions** (§6.9).
    - Options: E1, receiverless and qualified; E2, free functions; E3, constructors only.
    - **Recommended: E1.**
12. **Traits** (§6.10).
    - Options: adopt the word and Rust's rules; or keep `codata`, `gives` and `poly`, with
      conformance at the type.
    - Trade-off: familiarity, against importing orphan rules with the name.
    - **Recommended**: our names, and the book says plainly that this is a trait system with
      conformance at the type and a context form.
13. **Recursion's representation** (§6.11). **Decided, 2026-10-20: a written `box`.**
    - The user: "I think heap allocations should be explicit re:boxing."
    - So typed elaboration §5.3 stands: a recursive node is built `box C(…)`, and a recursive
      declaration or constructor without `box` is an error that asks for it.
    - Automatic boxing (one box a node by rule, and its variant that kept `box` for block nodes) is
      rejected for declarations.
14. **F3, a shared observation of objects** (§4.5, §8.1).
    - Options: spike it as a kernel clause; or keep materialised values observed by value or
      through `mut`.
    - **Recommended: spike it after U4**, and only if a program needs a shared container of
      objects.
15. **Binary methods in the value form** (F2).
    - Complex binary operations (`equal`, `order`, a merging `union`) need two representations,
      so they are static in any design (Cook 2009, §4.2).
    - Options for simple ones (Cook's `union` through the other's observations): extend `NuOk`
      to let an observation take the interface type; or keep them static.
    - **Recommended: static** (families and `ability`), until a program needs a simple binary
      observation.
16. **Units** (§10).
    - **Recommended**: U1–U3 as #593; U4–U5 as a new unit (codata declarations and interfaces);
      U6–U7 as #65, with derive split out first; U8 as #595.


### 11.1 Additions (decided 2026-10-20)

Added after the Bend deep dive (`docs/research/prior-art-bend.md`, PR #620) and the law-system
discussion (#624).

- **A1. A fold's recursive positions are unordered.** A fold promises no left-to-right order between
  its recursive positions, and allocation order is not output. Fold algebras are `F_∅`, so results
  cannot observe the order. Gated counts are those of the sequential order. This keeps parallel
  folds open.
- **A2. A `fold` block in which the recursive fields arrive already folded.** It is sugar into the
  kernel's proved folds. It is available inside the declaration, and exported to clients only as an
  observation the type chooses to give.
- **A3. Unfold (anamorphism) for data**, paired with `unfold` for codata. Data is built by unfold and
  consumed by fold; codata is built by unfold and consumed by observation. A data unfold carries a
  depth bound, or `Div` in its row. It needs stack-overflow detection first. An unfold whose results
  are folded at once is a hylomorphism and builds nothing.
- **A4. A match compiler**: nested and multi-scrutinee patterns, with exhaustiveness and redundancy
  reports.
- **A5. Three names for three concepts:**
  - `fold`: the structural catamorphism, one per declared type, positions unordered;
  - `for`: ordered iteration with an accumulator;
  - `reduce`: an associative combine licensed by a law (#620, #624).

  There is no foldl/foldr pair. foldr on a cons list is its `fold`, and foldl is iteration. No
  library function over iterators is named `fold`.
- **A6. A type's boundary is where its invariants are checked**, at runtime in debug and test builds
  (#624), on entry to and exit from the declaration's own functions.
- **A7. No automatic boxing anywhere.** SPEC §35's one box per node for recursive types written in
  core is removed too, so every heap allocation is written.
- **A8. `&` is inserted automatically at ordinary call arguments, for shared borrows only.** Mutable
  lends stay written, as in pre-NLL Rust. This extends item 8 from receivers to every argument.

Names follow formal terms (fold/catamorphism, unfold/anamorphism, hylomorphism), not another
language's in-house names.

**Sequencing.** U1 starts when #626 (`let mut` as a place) reports, because field update through
`mut` depends on it. Its elaboration is written as a rule table from the start, under CLAUDE.md's
`STOP: KERNEL WORK`, in its own elaborator module.
