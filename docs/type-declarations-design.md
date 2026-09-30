# Type declarations — design

Status: design only. Nothing here is implemented. Spellings are provisional unless a section says
a choice is a one-way door. The target declarations are in
[`type-declarations/proposed/`](type-declarations/proposed/), in the proposed surface, which does
not parse. Their hand-lowerings to today's language are in
[`type-declarations/lowered/`](type-declarations/lowered/), and
[`type-declarations/run.sh`](type-declarations/run.sh) checks, interprets, compiles and counts
them. The script is outside the gate.

It builds on SPEC §5 (records, blocks), §6 (`μ`, folds), §7 (`ν`), §9 (arrays), §11 (externs and
opaque host types), §12 (destructors) and §15 (generators). It also builds on
[`typed-elaboration.md`](typed-elaboration.md) §5.3 (`data`, `box`), the strings design §2 and
S6, the decisions (9, 23, 24, 26, 27, 41, 45), and the operator sketch's N8
([`operator/README.md`](operator/README.md)).

## 0. Summary

**A declaration is a name plus an isomorphism to its structure.** The name is nominal, and only
the elaborator sees it. The structure is an ordinary core type: `⊗` for records, `⊕` for
variants, `μ` for recursion, `ν` for codata. The iso is what constructors, patterns and field
access elaborate through. In the core it is the identity, or `roll`/`unroll` at a recursive
type, and both erase. Generic code, derivation included, goes through the iso. Abstraction means
not exporting the iso. The kernel is not changed by any of this: decision 9's "a structural
core; nominal types and abstraction are a surface or module concern" is kept, and made concrete.

| question | recommendation | § |
|---|---|---|
| 1. Identity | Nominal in the elaborator: a name plus an iso that erases. The core stays structural. `type` stays a transparent alias. | 2 |
| 2. Parameters | Type parameters `[T]` and lifetime parameters `<'a>`, instantiated by substitution: a parameterised declaration is a template, as a generic `fn` is (decision 45). Recursive uses must be regular. No bounds. Outlives facts come from the substituted structure, with no declared variance. | 3 |
| 3. Labels | Erased from the core. They live in the declaration table, which the elaborator already has, and polytypic functions are specialised at named types, before erasure. No labelled `VTy` former. | 6.1 |
| 4. Data and codata | `data` declares constructors (a `+` of `*`s, maybe under `μ`). `codata` declares observations (a `&` of `F`s under `ν`, `Self` for the rest), built by `unfold` with one arm per observation. `iter`, `gen` and `loop` become library `codata` declarations, and the frontend's built-in nodes for them are deleted. | 4 |
| 5. Layout | Unboxed by default. Recursion only under `box` or a block constructor. A backend n-ary tag and niches, with no kernel change. `layout C` is a keyword clause: declaration order, C alignment, C-representable fields, a contiguous block (#77). | 5 |
| 6. JSON and CRD | `Option[T]` fields are optional (omitted, not `required`). `@default(v)` is typed at the field's type. C-like enums are strings with `enum`; payload enums are tagged by a typed `Tagging` value. `@schema(minimum = …, …)` is typed, published in the schema and checked by the decoder. | 8 |
| 7. Overrides | `impl encode[Duration] = f`: one function per (polytypic function, type), resolved at specialisation. `derives encode` is the exported structural instance. `impl I for N { … }` is left for interfaces, as sugar over these. | 7.4 |

**Derive falls out** of three things that exist or are designed already. Monomorphization
elaborates a generic body at each instance's types (decision 45). The core type *is* the generic
representation, since it is structural (GHC.Generics needs a separate `Rep T` and conversions).
And the declaration table supplies labels and typed metadata. A `poly` function is written once,
by cases on the structure view (`data`, `record`, `field`, `variant`, `con`, `*`, `+`, leaves,
`rec`). Specialised at `N`, it is ordinary core code over `N`'s structure, checked by the
unchanged checker (§6).

**Metadata without comments** comes in two checked forms. A *keyword clause* covers what the
language or backend interprets (`derives`, `drop f`, `linear`, `layout C`). A *typed attribute*
covers what a library's polytypic function reads (`@json(rename = "containerPort")`,
`@schema(minimum = 1)`, `@default(Pending)`). An attribute is declared with `attr` as a record of
typed parameters with defaults, and every use is checked against it. A misspelled attribute name
or parameter, or a value of the wrong type, is an error (§7).

**Kernel changes.** None for declarations, parameters, labels, derive, attributes, abstraction,
codata declarations or declared destructors. Two items are adjacent, and each needs its own
entry:

- **Recursion under an array or a nested `μ`** in `FShape` (SPEC §6), for the JSON value type and
  any mutually recursive declarations (§6.5, §9.2).
- **#77's block allocation primitive**, for C layout (§5.4). It is already planned.

The rest is frontend (the elaborator), backend (tags, niches, byte layout) and a policy amendment
to SPEC §12 (declared destructors).

**What runs today** (`run.sh`, §9): hand-lowerings of the CRD encoder and validator, the JSON
value type and its encoder, the Intcode instruction type with a decoder, a printer and an
interpreter, the graph with node ids, an association-list map, a record of views, a
three-observation codata type, and a handle with its destructor calls inserted. All eight end
with `live 0`. A ninth program, the map with generic functions, is rejected today, and is kept as
evidence (§3.1). The C struct has no runnable form.

**Three findings from the lowerings.**

- A generic `fn` cannot mention a type parameter inside a `μ` (§3.1).
- A polytypic function over a *borrowed* recursive value has only data carriers. A thunk does not
  outlive, and a `!` closure cannot capture a payload. So the derived encoder over a borrowed
  tree materialises its text (§6.4).
- A declared type with recursion under an array is outside `FShape`, and so has no fold and no
  destructor (§6.5).

## 1. The state today

Verified in this worktree (`main` at `a30d65b`):

- `type X = …` occurs 105 times in `corpus/` and `lib/`
  (`grep -rn '^\s*type [A-Za-z_]* *\(\[\|=\)' corpus lib | wc -l`). The checker expands it before
  checking (`Frontend/Check/Elab.lean` looks the name up in the declarations). Syntax-core §10
  states "`type` and `shape` are abbreviations, expanded before checking, in declaration order,
  and not recursive." `Decl.type` has no parameters (`Frontend/Syntax.lean`:
  `type (sp : Span) (n : Ident) (A : VTy)`). The three most common right-hand sides are the list
  `mu X. 1 + (ref i32 * ref X)` (14), `B = 1 + 1` (12) and the unboxed list
  `mu X. 1 + (i32 * X)` (10).
- `data` occurs once, in `corpus/pending/data-box-tree.bc`. Its golden is the parse error
  "expected a declaration (`type`, `shape`, `def`, `extern` or `main`), found name `data`". The
  design in typed elaboration §5.3 is monomorphic: "`data List = Nil | Cons(head: i32, tail:
  List)`".
- SPEC §5: "A record is a binary tree of `⊗` (no trailing `1`); a variant is a nest of `⊕`." No
  label survives into the core.
- There are no type parameters on declarations. Generic *functions* exist: `fn f[A]<'a>`, as
  templates elaborated per instance (decision 45). A generic instance's types "have no
  lifetimes" (SPEC §15, *Generic functions*).
- Codata are abbreviations built into the frontend: `CTy.delay`, `stream`, `iter`, `loop`, `gen`
  in `Frontend/Syntax.lean`, each documented as an abbreviation over `nu`. SPEC §7: "a new codata
  shape is a new abbreviation".
- There are no nominal types and no abstraction. Decision 9 reads: "A structural core. Names are
  abbreviations; nominal types and abstraction are a surface or module concern, via opaque types."
  The only opaque types are the host's (SPEC §11: `VTy.opq k`, "a leaf with no introduction and no
  elimination rule").
- There is no C layout. The backend's layout is word-granular and type-directed: "Every word is an
  `i64` local", and `A ⊕ B` is "a tag word (`0` for `inl`), then the payload's words, padded"
  (`Backend/README.md`, Representation). The one byte-granular case is arrays of `u8`. A record
  allocated by `alloc_s` is several allocations, "contiguous only on some runs" (#77).
- The backend already boxes an unboxed `μ` silently. "Boxed fields. A recursive type would be
  infinitely wide, so the fields that close a cycle … are stored as a pointer … `μX. 1 + (A ⊗ X)`
  is a tag and a payload `A ⊗ X` whose `X` is a pointer: `nil` allocates nothing, each `cons` one
  object." (`Backend/README.md`). This is an allocation the source does not write. §5.1 makes a
  declaration unable to produce it.

## 2. Identity: a name and an isomorphism

### 2.1 The candidate

A declaration

    data N[P…]<'l…> = S

introduces three things:

- **A name** `N`, applied to arguments, `N[T…]<'x…>`. The elaborator's types (the TIR type
  mirror of typed elaboration §1.1) gain one constructor, `named N args`. Unification compares
  two named types by name and arguments, and never unfolds them.
- **A structure** `⟦S⟧[T…/P…, 'x…/'l…]`, a core value type: `⊗` of the fields, `⊕` of the
  constructors, `μ` when `N` occurs in `S`.
- **An iso** `into_N : ⟦S⟧ → N` and `out_N : N → ⟦S⟧`. In the core both are the identity when
  `N` is not recursive, and `roll`/`unroll` when it is (SPEC §6: "`roll`/`unroll` on the same
  term (no machine step)"). Constructors are `into_N ∘ inj_i`. Patterns are `out_N` then a
  `case`. A field access is `out_N` then a projection path.

Lowering erases `named` to the structure, so the checker never sees a name. `type N = S` stays as
it is: a transparent alias, which unifies with its right-hand side.

This is Haskell's `newtype` generalised to every declaration. The Haskell 2010 report (§4.2.3)
says a `newtype` "introduces a new type whose representation is the same as an existing type",
that "it creates a distinct type that must be explicitly coerced to or from the original type",
and that "these coercions may be implemented without execution time overhead". It is also
GHC.Generics' `Generic` class with the representation made literal. GHC.Generics: "Datatype-generic
functions are based on the idea of converting values of a datatype T into corresponding values of
a (nearly) isomorphic type Rep T", with laws "from . to ≡ id to . from ≡ id". Here `Rep N` is the
core type itself, so `from`/`to` are not code.

### 2.2 What it gives

- **Derive.** A polytypic function specialised at `N` goes through `out_N`. It sees the structure
  and the declaration's metadata: labels, constructor names, attributes (§6). The instance is
  code over `⟦S⟧`, because the iso is the identity there.
- **Abstraction.** A package that exports `N` without its iso exports a type that outside code
  can only pass around and hand back to the package's functions (§2.4).
- **Error messages.** Types print as written: `expected NodeId, found EdgeId`, where today's
  printer would show `i32` twice. Typed elaboration §3 already wants "a generated `μ` by its
  `data` name". The name is the key the printer needs.
- **Inference.** A constructor synthesizes its type (`Cons(x, t) : List[T]` with `T` read off
  `x`). The `(inl () : B)` ascriptions typed elaboration §4 removes by checking also go at named
  types, where no expected type flows in. Matching a generic parameter against `List[i32]`
  (decision 45's first-order matching) compares a name and one argument, not a `μ` body. Two
  structurally equal `μ`s written separately never have to be compared.
- **Zero cost.** Nothing is added at run time. `NodeId(3)` is the word `3`.

### 2.3 Why not the alternatives

- **Structural with labels in the core.** A labelled `⊗` would be a new `VTy` former, "about 100
  match arms across `Core/`" (CLAUDE.md, growth discipline). It would carry no semantic content,
  since the relation would ignore the label. It would also make two records with the same fields
  but different labels unequal in the core, which the checker has no reason to care about.
  Rejected (§6.1).
- **Nominal in the kernel** (a sealing former `N⟨A⟩` with introduction and elimination rules).
  This buys a theorem: representation independence of an abstract type, by parametricity. Nothing
  planned needs that theorem. The strings design's UTF-8 invariant is "a correctness property of
  the text library … stated in Lean, if wanted", and needs no rule (strings §2.1). It costs a
  former plus two rules. Rejected; §12 Q1 records when to revisit it.
- **Structural in the surface too** (names as aliases, labels in a side table keyed by structure).
  Two declarations with the same structure would collide in the table: `NodeId` and `EdgeId` are
  both `i32`. This is the state today, and it is what makes N8's option (ii) in the operator
  README need "named fields in the core or a side table".

### 2.4 Abstraction

A package exports a declaration in one of two ways (provisional spelling):

    export data Point = { x: i32, y: i32 }     -- name and iso: constructors, patterns, fields
    export data Map[K, V]                      -- the name only: abstract

Outside the package, an abstract `N` has no constructors, no patterns, no fields and no
structural derivations (§7.4). Inside, it is transparent. Because the checker sees only
structure, abstraction is enforced by the elaborator, as Rust's privacy is enforced by `rustc`
and not by a type theory. That is decision 9's "a surface or module concern", and it is enough
for the uses on the table:

- the strings design's `str` (its stage T2, "only the text library may build a `str` from
  bytes");
- `Map[K, V]` hiding its representation (§9.5);
- a C struct whose pointer fields only the binding package may touch (§9.7, decision 27).

It is not a proof of representation independence (§2.3).

**Monomorphization and hiding.** An instance of `Map[string, Json]` is checked at its structure
(decision 45), so the use site needs the representation to lay out and check the instance. The
iso is hidden, but the representation's layout is not. Rust's and C++'s generics work the same
way. This is #63's "how monomorphized generics cross module boundaries". Separate compilation of
an abstract type's clients is not offered.

## 3. Parameters

### 3.1 Type parameters

    data List[T] = Nil | Cons(head: T, tail: List[T])
    data Map[K, V] = { keys: buf K, vals: buf V }

- **Instantiation is substitution.** `List[i32]` is `⟦S⟧[i32/T]`, a closed core type. A
  parameterised declaration is a type-level template, exactly as a generic `fn` is a term-level
  one (decision 45, "made and elaborated on first use"). The core has no type `∀` (decision 8),
  and it gets none.
- **Regular recursion only.** Inside `N[P…]`'s body, every occurrence of `N` must be `N[P…]`
  with the parameters in order. That makes the expansion one finite `μ`. A nested datatype
  (`data Nest[T] = Nil | Cons(T, Nest[T * T])`) would expand forever and is rejected at the
  declaration. Polymorphic recursion is rejected with it.
- **Mutual recursion** among declarations (`Json` and `Member`, §9.2) expands by Bekić's rule to
  a `μ` inside a `μ`. The inner one is not a closed leaf, so the outer `μ` is outside `FShape`
  and has no fold and no destructor. §6.5 covers this.
- **Today a generic `fn` cannot mention a type parameter inside a `μ`.**
  `lowered/map-generic.bc` declares `fn insert[K, V](m: mu X. 1 + ((K * V) * X), …)`, and its call
  at `[i32, i32]` is rejected: "the type of `insert` does not elaborate here". Decision 45 names the
  cause: "a free type variable standing for `A` is rejected inside a `μ` (`elabV` requires a `μ`
  closed)". Parameterised recursive declarations need the instance's signature substituted
  before it is elaborated, as its body already is. This is D2's first item (§11).
- **Type arguments are inferred** the way decision 45 infers them for functions: by first-order
  matching, where a named type matches by name and then arguments.
- **No bounds.** What a declaration does with `T` is decided at each instance, as for a generic
  `fn`: "what a body may do with an `A` … is decided there" (decision 45). The only type-indexed
  dispatch is a polytypic function's override (§7.4).

### 3.2 Lifetime parameters

    data Field<'a> = { name: slice 'a u8, value: slice 'a u8 }
    data Tok<'a> = Punct(u8) | Str(slice 'a u8) | Num(i32) | Word(slice 'a u8) | End

This is strings S6 (typed elaboration §5.3 "with lifetime parameters", strings Q5).

- **Substituted like types.** `Field<'x>` is `array_imm 'x u8 * array_imm 'x u8`.
- **Outlives from the structure.** `Δ ⊢ Field<'x> ⊐ @b` holds when the checker's `VOutlives`
  holds of the substituted structure (`Core/Types.lean`; at `[L]`, SPEC §9's rule). No variance
  or outlives clause is declared. The structure says it, and the checker decides it.
- **Shortening.** `:>` shortens one borrow (typed elaboration §2.3). A record of borrows is
  shortened by destructuring, shortening each leaf and rebuilding, which erases to nothing. That
  is a derived function (`shorten`, by cases, §6). Families (`array_imm`) cannot be shortened
  today (decision 45: "an argument that is not a borrow (a family `array_imm`) cannot be"), so
  `Field<'x>` cannot be passed at a shorter lifetime until they can. §12 Q4 records this.
- **Instances with lifetimes.** Decision 41/45: "instances are at types without lifetimes".
  `buf[Field<'x>]`, which P6 of the strings design needs (`buf (str 't * str 't)`), is an
  instance of a generic declaration at a type with a lifetime. Defs are already "re-checked at
  that use's Δ" (syntax-core §10), so the check has somewhere to happen. The restriction has to
  be lifted for parameterised declarations to reach the strings programs. I have not established
  what in the implementation depends on it (§13).

### 3.3 Anything else

- **Capabilities** need no parameter kind. A record may hold a borrow of one
  (`data Parser<'s> = { src: mut 's input, pos: i32 }`), and the lifetime parameter covers it.
  A record that owns one (`ref output`) has no destructor, as the capability has none (SPEC §12,
  class 3), and the record is handed back as the capability is.
- **Sizes** (`[T; N]`, const generics) are #72's size sort, and out of scope. `@schema(minimum =
  1)` stands in for refinements (§8.4).
- **Effects.** None on declarations: decision 6 of typed elaboration fixes a stored callback's
  effect to its written type.

## 4. Data and codata declarations

### 4.1 `data`: constructors

    data Phase = Pending | Running | Failed                          -- a C-like enum
    data Spec = { size: i32, container_port: i32, version: Option[i32] }   -- a record
    data Param = Pos(i32) | Imm(i32) | Rel(i32)                      -- a variant
    data NodeId = NodeId(i32)                                        -- a newtype
    data List[T] = Nil | Cons(head: T, tail: List[T])                -- recursive

| surface | elaborates to |
|---|---|
| a record `{ f₁: A₁, …, fₙ: Aₙ }` | `A₁ ⊗ (A₂ ⊗ (… ⊗ Aₙ))`, right-nested in declaration order, with no trailing `1` (SPEC §5) |
| a variant `C₁(…) \| … \| Cₙ(…)` | `P₁ ⊕ (P₂ ⊕ (… ⊕ Pₙ))`, each `Pᵢ` the record of `Cᵢ`'s fields, or `1` when it has none |
| a constructor use `Cᵢ(e…)` | `into_N (inl/inr path (e₁, (…)))` |
| a record literal `N { f₁: e₁, … }` | `into_N (e₁, (…))`, fields reordered to declaration order |
| `match v { Cᵢ(x…) -> … }` | `case (out_N v) { … }`: one arm per constructor, nested `case`s along the `⊕` spine |
| `v.f` on an owned record | `let (…, x, …) = out_N v`, with the other fields dropped (SPEC §12) |
| `v.f` on a view `view 'a N` | the component, since a view of a record is the tuple of its fields' views (SPEC §5, "`Imm̲` acts fieldwise") |
| `N { ..r, f: e }` (update) | destructure `r`, rebuild with `e`. The old `f` is dropped |
| a recursive `N` | `μX. ⟦S⟧[X/N]`; `into_N` is `roll`, `out_N` is `unroll` |

Nested patterns and match compilation stay as typed elaboration §5.3 leaves them: "A pattern is
one constructor over variables, `_`, `()`, tuples, and `box p`."

**Values, not allocations.** A declared value is built in place, with no allocation, unless the
program writes `box` (§5.1). That answers strings Q5 ("`data` constructors without `box` for
non-recursive types") yes.

### 4.2 `codata`: observations

    codata Countdown {
      next      : F (i32 * Self + 1)
      remaining : F (i32 * Self)
      close     : F 1
    }

- **Elaboration.** `νX. (F(i32 ⊗ U X ⊕ 1) & F(i32 ⊗ U X)) & F 1`: the observations as a `&` tree,
  and `Self` as `U X`. The shape of the tree does not matter to the user, since observations are
  called by name. The elaborator balances it, or nests it right, and records each label's
  projection path.
- **Positivity is SPEC §7's `NuOk`,** checked at the declaration with the checker's function: at
  least two observations, each an `F A` with `Self` only under `⊗`/`⊕`. `close` is not special in
  the declaration. A codata type has a destructor when its last observation is a `close : F R`
  with `R` in `HasDtor` (SPEC §7, *Destructor*). So the declaration names it, and §4.5's clauses
  do not apply.
- **Observation.** `c.next` is `(nu_out (force c)).path` and is bound with `<-`: it is a
  surviving force (surface-cbpv §1: "codata observation … **visible**: `d.poll`, `s.next`").
- **Construction** is coiteration, SPEC §7's `unfold`, at the declared `C`, with one arm per
  observation over an explicit state:

      unfold n { s ->
        next      -> if s == 0 { None } else { Some((s, s - 1)) }
        remaining -> (s, s)
        close     -> ()
      }

  Each arm returns the next state where the type says `Self`. The arms are the step
  `!U(S ⊸ C[S/X])`, with the `&` built from the arms by label. The eta-expansion the corpus
  writes by hand (`thunkv nu_in < (nu_out (force f s)).1, (nu_out (force f s)).2 >`,
  `corpus/iter-range.bc`) is generated from the declaration. This is draft 0's §2.8 promise:
  "observation names come from the codata declaration".
- **Codata parameters** follow §3 (`codata Iter[A, R, R2] { … }`).

Copatterns (Abel, Pientka, Thibodeau and Setzer, cited in surface-cbpv §6) define codata "by
what each observation returns". The `unfold` block is that, restricted to one step function over
explicit state (decision 24). No self-reference is possible, because the step returns states and
never a `Self` (SPEC §7: "the step returns states, never a `νX. C`").

### 4.3 Generators and iterators become declarations

`lib/gen.bc` declares

    codata Iter[A, R, R2] { next: F (A * Self + R)           close: F R2 }
    codata Gen[A, B, R]   { next: F (A * Self + (B + Self))  close: F R }
    codata Loop[A, B]     { next: F (A + Self)               close: F B }

The five `CTy` nodes `delay`, `stream`, `iter`, `loop` and `gen` of `Frontend/Syntax.lean` are
then deleted, along with their cases in the parser, printer and checker elaboration. This is the
growth rule "Generalize by deleting" applied to the frontend: a general form lands with the
deletion of the fixed ones. `gen fn f(…) -> A, B` elaborates to `… => Gen[A, B, R]`, as it does
to `U (gen A B R)` today.

**`for` over a declared codata.** Today `for` accepts a source of type `U (iter …)`,
`U (gen …)` or `U (loop …)`, recognised by the type's shape. With declarations, `for` accepts
`Iter[…]`, `Gen[…]` and `Loop[…]` by name, and any other codata that provides
`impl iterate[N]` (§7.4), a function into one of them. `Countdown` (three observations) is
iterable only through such an `impl`. This keeps `for`'s meaning tied to two named protocols,
and not to a structural match that a type could fall into by accident.

**Relation to the iteration design** (PR #133, `docs/iteration-design.md` on branch
`iteration-design`). There, "Pull is codata. A generator is stepped by its consumer (`gen`,
`iter`, `loop`, SPEC §7, §15)", and push producers are data or `rf → rf` functions. A `codata`
declaration is a pull producer's type. Push stages are functions and need no declaration kind.

### 4.4 Records of places

A declared record is a value, so it is borrowed as any value is, in a cell. `box r` of a record
makes a **block** with one cell per field (decision 6: "`Box<struct>` is a block"), so each field
is a separately borrowable place (SPEC §5, family borrows). The one-cell `Ref (A ⊗ B)` is not
what `box` makes of a record.

- `borrow mut r.f { … }` on a boxed record lends the leaf cell of `f`.
- On a `let mut` record value, `&mut r.f` is the scoped cell of typed elaboration §5.1 around the
  field, with the record destructured and rebuilt around it.

A boxed *variant* is one cell, `Ref (A ⊕ B)`, whose payload fields are not places, because `Ref`
does not distribute over `⊕` (SPEC §5 Open, #19). A recursive constructor sidesteps this: its
tag is outside the block (`roll (inr (alloc_s …))`, typed elaboration §5.3). #19 remains open
for non-recursive boxed variants.

### 4.5 Destructors and linear types

    data Session drop end_session = { id: box i32, uses: i32 }
    data Tx linear = { log: buf Op }

- **`drop f`.** Where an owned `N` goes unused on a path, the elaborator inserts `f(x)` with SPEC
  §12's placement: "immediately before the path's terminal computation … in reverse binding
  order". It does not insert the structural destructor of `⟦S⟧`. `f : !(N ⇒ 1)` must be total.
  It runs in the declaring package, so it may use the iso.
- **`linear`.** An unused `N` is an error naming `N` (SPEC §12's class 3, made a property of the
  type rather than of a binder: the `linear x <- M` opt-out generalised).
- **No clause.** The structural destructor of `⟦S⟧`, as today.

**Where this lives.** The checker sees only structure, and `⟦S⟧` may have a structural
destructor, so the elaborator must act before the checker does. It runs the insertion itself on
the TIR, where types are named, so that the checker finds every such variable consumed. If the
elaborator missed one, the checker would insert the structural destructor. That would be
memory-safe, since any placement is a `CDerives` derivation (SPEC §12, *Soundness*), but it
would be the wrong behaviour. The elaborator therefore compares the checker's inserted drops
against the origin table (typed elaboration §3) and reports an inserted drop at a `drop`/`linear`
type as `internal: elaboration disagreed with the checker`. SPEC §12's insertion policy gains one
sentence. No rule changes.

**Host resources.** A file handle's representation is an opaque host type (SPEC §11, a new
`VTy.opq k` per resource, from the platform design), which has no destructor. `drop f` names the
extern that closes it. A destructor that can fail is SPEC §12 Open. Until that is decided, a
declared destructor returns `1`, and the explicit `close` reports the error (§9.9).

## 5. Layout

### 5.1 Unboxed by default; recursion under `box` or a block

- A non-recursive declaration is a value: a record is its fields' words, a variant a tag and the
  widest payload (`Backend/README.md`: "a pair is never an object"). Nothing allocates.
- A recursive occurrence must be under `box` (a `ref` field) or in a constructor that is a block
  (typed elaboration §5.3, decision 1 of its §8: "A node is one block with a cell per field";
  `box Cons(x, t)`). An occurrence that is under neither is an error at the declaration: "A
  recursive occurrence that is under neither a block nor `box` is an error" (typed elaboration
  §5.3). This is what keeps the backend's silent boxing of an unboxed `μ` (§1) out of declared
  types. A declaration never elaborates to `μX. … X …` with a bare head `X`.
- **The two forms differ in what is a place.** `Cons(head: T, tail: box List[T])` gives
  `μX. 1 + (T ⊗ Ref X)`: the head is inline in the parent's cell, one allocation per node, as
  Rust's `Box<Node>`. `box Cons(head: T, tail: List[T])` gives `μX. 1 + (Ref T ⊗ Ref X)` through
  a block: every field is a cell and a place, and `fold_reuse` refills it in place. The
  declaration says which, and both are one allocation per node once blocks are contiguous (#77).

### 5.2 Tags

Today a right-nested `⊕` nests tag words: `|A ⊕ B| = 1 + max |A| |B|`. A ten-constructor variant
is up to ten tag words on its deepest path, and `Instr` (§9.3) is 17 words where one tag word
would give 7. **Recommendation:** the backend gives each maximal `⊕` nest one n-ary tag word,
numbering the summands left to right. `case` on the outer `⊕` becomes a range test on the tag,
and on an inner one a narrower range. This is a layout-type change in `Clos/Types.lean` and
`Flat/Lower.lean`. The model, the checker and the kernel do not see it. It applies to every
`⊕`, declared or not, which the corpus's hand-written sums welcome too.

### 5.3 Niches

Each of these is a backend representation choice with no kernel change. Each needs the backend's
agreement with the interpreter, which is tested on the corpus today and not proved (SPEC §8
Semantics).

| type | niche | why it is sound |
|---|---|---|
| `1 ⊕ Ref A` (`Option[box T]`) | the null word for `inl` | no cell is at address 0 (the empty family's base is "the source term's location `0`, which the closure IR's interpreter never allocates", `Backend/README.md`) |
| `1 ⊕ [L]` (`Option[array T]`, `Option[slice 'a T]`) | a length word `≥ 2³¹` for `inl` | not the base: the empty array's base is `0`. The length bound does it: "A family in the relation has `tab`'s length: `len(c) = c`", `c < 2³¹` (SPEC §9, *The length bound*) |
| a tag beside a 32-bit or 8-bit payload | the tag in the spare bits of the payload's `i64` word | the word is 64 bits and the payload uses 32 or 8 |
| `1 ⊕ 1`, and C-like enums | already one word | — |

Rust guarantees the first row for its pointer types: "Rust guarantees to optimize the following
types T such that Option<T> has the same size, alignment, and function call ABI as T … This is
called the "null pointer optimization" or NPO" (`std::option`, *Representation*). Beyond that
list, Rust's layout is unspecified: "There are no other guarantees of data layout made by this
representation" (Reference, type layout, `repr(Rust)`). The recommendation is the same here.
Niches are optimisations, and only `layout C` (§5.4) fixes a layout.

### 5.4 C layout

    data ZStream layout C = { next_in: cptr u8, avail_in: c_uint, …, reserved: c_ulong }

- **Requested by a keyword clause**, `layout C`, and not by an attribute. It changes what the
  backend does, and the grammar owns it. Zig makes the same choice with a keyword: "An extern
  struct has in-memory layout matching the C ABI for the target" (Zig language reference,
  master). A misspelling (`layout c`, `layuot C`) is a parse error, not an ignored annotation.
- **What it fixes.** Declaration order, and each field at the next offset that is a multiple of
  its C alignment. Rust's `repr(C)` algorithm: "For each field in declaration order in the
  struct, first determine the size and alignment of the field. If the current offset is not a
  multiple of the field's alignment, then add padding bytes to the current offset until it is a
  multiple of the field's alignment" (Reference, type layout).
- **What it checks.** Every field is C-representable: the C integer aliases (`c_int`, `c_uint`,
  `c_ulong`, …, each an `i32` or `i64` per target: `c_ulong` is `i32` on wasm32 and `i64` on
  LP64), another `layout C` declaration, and the platform design's raw pointer and function
  pointer types. Those last are allowed only in `layout C` declarations and extern contracts
  (decision 27: "raw pointers never flow into safe code").
- **Where it lives.** A `layout C` value is used through a block: `box ZStream::zeroed()` is one
  contiguous allocation at the C size, each field a leaf cell at its C offset. zlib is why a
  block is required and a per-call copy is not. It keeps a pointer back to the stream, and
  `inflateStateCheck` fails when `state->strm != strm` (zlib, `inflate.c`), so the stream must
  keep one address for its life.
- **What it needs.** (1) #77's block allocation primitive, so that a block is contiguous on
  every run. (2) SPEC §5 Open's block provenance, so that a handle lowers to one pointer: "lowering
  a handle to one word needs it". (3) Byte-granular block layout in the backend. The backend
  then needs the offsets, which are a property of the declaration and not of the structure: two
  declarations with the same fields can differ in `layout`. **Recommendation:** lay out every
  block in declaration order with natural alignment, the C rule, and have the elaborator build
  each block's shape `σ` in declaration order (it does already). The layout is then a function
  of `σ` alone, and no annotation reaches the core. `layout C` becomes a check (C-representable
  fields) plus a promise that this type's order will not be optimised later. The cost against
  Rust's default is padding that reordering would remove, in blocks only. Values in locals stay
  word-flattened.
- **Offsets of `ZStream`,** computed from those rules (not measured):

  | field | LP64 offset | wasm32 offset |
  |---|---:|---:|
  | `next_in` | 0 | 0 |
  | `avail_in` | 8 | 4 |
  | `total_in` | 16 | 8 |
  | `next_out` | 24 | 12 |
  | `avail_out` | 32 | 16 |
  | `total_out` | 40 | 20 |
  | `msg` | 48 | 24 |
  | `state` | 56 | 28 |
  | `zalloc`, `zfree`, `opaque` | 64, 72, 80 | 32, 36, 40 |
  | `data_type` | 88 | 44 |
  | `adler`, `reserved` | 96, 104 | 48, 52 |
  | size | 112 | 56 |

C enums with a fixed width (`repr(u8)`) are `layout C` on a C-like enum with a width clause,
`data Level layout C(u8) = Debug | Info | …`. Rust: "For field-less enums, primitive
representations set the size and alignment to be the same as the primitive type of the same
name." Enums with payloads in C layout (Rust: "a repr(C) union of repr(C) structs for each
variant") are not proposed: no FFI target on the table needs them.

### 5.5 Byte-level layout in memory

Outside arrays of `u8`, memory is word-granular. A `u8` field in a cell takes a word, and an array
of `u8 * u8` pairs takes two words per element where Rust and C take two bytes. §5.4's byte
layout for blocks is the start. Arrays of small records (the Intcode memory, a pixel buffer) need
the same for array slots, since a slot is `sizeof A` wide ("`s = sizeof A`", SPEC §9,
*Lowering*). That is a backend follow-up against the zero-cost target, with no language change,
and is listed in §11.

## 6. Labels and derivation

### 6.1 Labels are erased; the declaration table carries them

The elaborator has every declaration, with its labels, constructor names, attributes and
parameter list. It specialises generic code at named types (§6.3), before lowering erases the
names. So derive needs no label in the core, and the "side table" of N8's option (ii) is the
declaration table itself, keyed by name, not by structure (§2.3). `bcc desugar` prints core
without labels. The origin table (typed elaboration §3) maps each generated span back to the
`derives` clause or `poly` case it came from, so errors in derived code point at the
declaration.

What derive needs from a declaration, all of which it has:

- the type's name, package and parameters (for messages, schema titles, `$ref`s);
- constructor names and indices, and field labels and indices, in declaration order;
- each field's and constructor's attributes, as typed values (§7);
- which occurrences are recursive (for the fold, §6.4);
- the iso, which is visible or not.

### 6.2 The structure view

A polytypic function (`poly`) is written by cases on this view of a type `T`:

| case | matches | binds |
|---|---|---|
| `data(d) A` | a declared type `N` | `d : DataMeta` (name, package), and `A` its structure through `out_N` |
| `newtype(d) A` | a declared type with one constructor of one field | as `data`. serde's `newtype_struct`, encoded as the field alone |
| `record F` | a declaration's product | `F`, a `*`-spine of `field(f) A` |
| `field(f) A` | one field | `f : FieldMeta` (label, index, attributes) |
| `variant C` | a declaration's sum | `C`, a `+`-spine of `con(c) F` |
| `con(c) F` | one constructor | `c : ConMeta` (name, index, arity) and its fields `F`, or `1` |
| `A * B`, `A + B` | the spines, or an anonymous tuple or sum | |
| `i32`, `i64`, `u8`, `1`, `lit`, `slice 'a A`, `array A`, `box A`, … | leaves | |
| `rec` | a recursive occurrence, inside a fold (§6.4) | the carrier value |
| `_` | anything not matched above | |

This is the sum-of-products view of generics-sop, over the core's own binary formers. Its
abstract page: "each datatype is a single n-ary sum, where each component of the sum is a single
n-ary product", and "A major plus of the SOP view is that it allows to separate function-specific
metadata from the main structural representation" (de Vries and Löh, *True Sums of Products*,
WGP 2014). The metadata here is typed data, as GHC.Generics' is: "The name of the datatype
(unqualified)", "The name of the constructor", "The name of the selector" (the docstrings of
`datatypeName`, `conName`, `selName`).

`v` in a `poly` over borrowed values is a **view**, `view 'a T` (`Imm̲ 'a T`, SPEC §5). A view of
a record is the tuple of its fields' views, so the `A * B` case destructures it for free, and a
leaf `box A` is an `imm 'a A`, read through `withload`. The entry point is
`encode_value[T](o, x: imm 'a T) = load x { v -> encode[T](o, v) }`.

### 6.3 A `poly`, and its specialisation

    poly encode[T]<'a>(o: Out, v: view 'a T) -> Out {
      i32        -> put_dec(o, v)
      data(d) A  -> encode[A](o, v)
      record F   -> let o = write(o, "{"); let (o, _) = members[F](o, v, true); write(o, "}")
      variant C  -> if nullary[C] { write_quoted(o, con_name[C](v)) } else { tagged[C](o, v) }
      A + B      -> match v { inl a -> encode[A](o, a) | inr b -> encode[B](o, b) }
      …
    }

(The whole of it, with `members`, `present`, `schema`, `eq` and the attribute declarations, is
[`proposed/derive.bc`](type-declarations/proposed/derive.bc).)

- **Specialisation is decision 45's instantiation, extended by one step.** A call `encode[N]` is
  a call of the instance at `N`, made on first use and shared by later calls. Its body is the
  first case whose pattern matches `N` in the structure view: `data(d) A` binds `d` to `N`'s
  metadata as a constant and `A` to `N`'s structure. The recursive calls `encode[A]` are
  instances at smaller types. The result is ordinary core code, checked by the unchanged checker.
  Elaboration may be type-directed (decision 26), and this is.
- **Termination of elaboration.** Each case's calls are at proper components of the matched
  type, except `data(d) A`, which unfolds a name. Unfolding a name at which the same `poly` is
  already being specialised is a recursive occurrence (§6.4) and becomes `rec`. So
  specialisation is structural recursion on the finite set of (poly, type) pairs, with a memo
  table, and the existing fuel bound (`elabDecl`) is a guard.
- **Overrides first.** Before matching cases at `N`, the elaborator looks for `impl encode[N]`
  (§7.4). This is how `Option[T]`'s presence, `Duration`'s string form and `Json`'s own encoder
  enter.
- **Metadata are constants.** `d`, `f`, `c` and the attribute records are persistent values of
  declared types (`lit`, `bool`, `i32`, enums). A `match` on one is resolved at elaboration when
  its scrutinee is a known constructor, so `if json(f).skip { … }` leaves no branch in the
  output.
- **Cost.** An instance is the hand-written code: `lowered/crd.bc` is what `encode[Memcached]`
  would be. The iso is the identity, so nothing converts, and there is no `from`/`to` for an
  optimiser to remove, as there is in GHC.Generics.

### 6.4 Recursive types: the carrier

At a recursive `N` a `poly` cannot call itself (decision 24: no general recursion; "a `def` may
not refer to itself or a later one", syntax-core §10). The instance at a recursive `N` is instead
a fold over `N`'s `μ`. `fold_imm` covers a view and `fold_own` an owned value (SPEC §6). The
algebra is the `poly`'s case at the unrolled structure, with each recursive occurrence (`rec`)
bound to the fold's result `R`, the **carrier**, which the `poly` declares:

    poly encode[T]<'a>(o: Out, v: view 'a T) -> Out  carrier Txt  { … rec(t) -> append(o, t) … }

This is where writing derive once runs into the core's discipline. Three constraints hold, each
established by a checked or rejected program in `lowered/`:

1. **`fold_imm`'s result must outlive every lifetime** (SPEC §6: "R outlives every lifetime"),
   and a thunk does not: `VOutlives` has cases for `1`, `⊗`, `⊕`, `Ref`, `!`, borrows, `μ`,
   integers, opaque types and `[L]`, and none for `U C` (`Core/Types.lean`). So a streaming
   encoder cannot take "a function of the output" as its carrier over a borrowed tree. That
   carrier is the one `corpus/gen-lines.bc` uses (`type Run = U (Out -o F (Out * 1))`), over an
   *owned* list with `fold_own`.
2. **A `!` closure does outlive** (`VOutlives.bang`), but it may capture only `!`-typed
   variables. SPEC §2: "`!Γ` means every live slot of `Γ` has a `!`-type". An `i32` key is
   persistent, but it is not `!`-typed. The checker rejects the lookup carrier `!(i32 ⇒ i32 ⊕ 1)`
   built over a node's key: "`!thunk` promotes only over `!` types, but `v`, of type `i32`, is
   used inside". So no `!` carrier can hold a node's payload.
   **An owned fold** (`fold_own`) has no outlives condition, and its carrier may be a thunk
   (`lowered/map.bc`'s `get`, over a `clone` of a persistent map). That thunk is linear, so each
   entry's function runs the rest of the chain even after it finds the key.
3. **Data carriers always work**: text as a byte list (`lowered/json.bc`) or a buffer. They
   allocate the output before writing it: 172 allocations for a 35-byte document in `json.bc`
   (§9).

**Recommendation.** Derivations over recursive types use a data carrier for now: `eq`, `hash`
and `debug` use `bool`, `i64` and text, and `encode` uses a buffer. `clone` over an owned value is
`fold_own` with the type as carrier. The streaming, non-allocating encoder over a borrowed tree
needs a borrowed traversal with an explicit stack. Decision 24 names this ("borrowed folds use an
explicit stack"), and SPEC §7 Open lists it as missing ("Lifetime-indexed iteration … not yet
written as a program"). When that traversal exists, the `rec` case of a streaming `poly` becomes a
push onto its stack, and derived encoders use it with no change to their text.

**Decoding recursive types** is the dual problem. Parsing into a `μ` of unknown depth is a loop
with an explicit stack of partial nodes, not a fold. Derived decoders cover non-recursive types
by cases. A recursive type's decoder is library code (the JSON value's pull parser, §9.2) or an
override.

### 6.5 Nested recursion is outside `FShape`

`data Json = … | Arr(Vec[Json]) | Obj(Vec[Member])` puts the recursive position under an array.
So does every mutually recursive pair after Bekić. `FShape` (`Core/FoldImm.lean`: `leaf`,
`refX`, `varX`, `tensor`, `sum`, with a leaf closed) does not contain it. The type is
well-formed (positivity is only `NoMut`), but it has no fold. With no fold it has no structural
destructor, which puts it in class 3 (SPEC §12: "`μ` outside `FShape`"). Every `Json` value would
then have to be consumed by hand.

- **Without a kernel change**, a declaration can use the "left child, right sibling" encoding,
  one `μ` in `FShape` in which every node carries its next sibling (`lowered/json.bc`). It is
  typed and runs today, but a `Json` array is then not a `Vec`, and `Vec`'s functions do not
  apply to it.
- **With one**, `FShape` gains `arr F`: an array of recursive positions, `[Ref X]` or
  `[Ref (A ⊗ X)]`. The fold's algebra receives the array of the children's results, and
  termination is by the witness size, as for `Ref X`: each element's witness is strictly smaller
  than its parent's. `foldOwn`'s destructor for it is `array_free` with the fold as the consumer.
  This is a new spec entry with a proof plan: the three fold rules and `dtor_wf` at the new case,
  plus the one lemma that an array leaf's witness is below its node's.

**Recommendation.** The spec entry, and until it lands, the sibling encoding for `Json`. The
elaborator rejects any other declaration with nested recursion, naming the occurrence.

## 7. Metadata without comments

### 7.1 Two mechanisms, split by who reads them

| | keyword clause | typed attribute |
|---|---|---|
| read by | the elaborator or the backend | a library's `poly` |
| examples | `derives encode, schema`; `drop f`; `linear`; `layout C` | `@json(rename = "containerPort")`, `@schema(minimum = 1)`, `@default(Pending)`, `@kube(group = …)` |
| declared by | the grammar | an `attr` declaration in the library that reads it |
| a misspelling | a parse error | an unknown-name error at the use |
| a wrong value | a type error in the clause (`drop` of a function of the wrong type) | a type error against the `attr`'s parameter type |

A comment is never read. There is no marker syntax inside comments, and no build tag or
`generate` line.

### 7.2 Attribute declarations

    attr json on field = { rename: Option[lit] = None, skip: bool = false, flatten: bool = false }
    attr json on data  = { rename_all: Case = Keep, tagging: Tagging = External, deny_unknown: bool = false }
    attr default on field of T = T
    attr json_with on field of T = poly encode at T
    attr schema on field, data = { minimum: Option[i64] = None, maximum: Option[i64] = None,
                                   pattern: Option[lit] = None, … }

- An `attr` names its **targets**: `data`, `con`, `field`, `codata`, `obs`. One name may have a
  different parameter record per target (`json` on a field and on a type), as serde's container,
  variant and field attributes do. serde: "There are three categories of attributes: Container
  attributes … Variant attributes … Field attributes".
- The parameters are a **record with defaults**. A use `@json(rename = "x")` is elaborated as a
  record literal against it. A missing parameter without a default, an unknown parameter or a
  value of the wrong type is an error at the use.
- A parameter's type may be **the target's type** (`of T = T`), so `@default(3)` is checked at the
  field's type. It may also be **a function at the target's type** (`= poly encode at T`), so
  `@json_with(f)` is checked to have `encode`'s signature at that type.
- **Values are constants.** A value is a literal, a constructor of a declared type applied to
  constants, `lit` text, or the name of a function. Constants are the values an elaborator can
  compare and a `poly` can branch on at elaboration (§6.3). No code runs at compile time. Zig's
  comptime is the more general answer, and it is not needed.
- **An attribute no `poly` reads is an error at the declaration**, unless its `attr` is marked
  `inert`. So a `@json(…)` on a type with no `derives encode` is reported, not silently kept.
  Rust does the opposite for tool attributes: "When a tool is not in use, the tool's attributes
  are accepted without a warning" (Reference, attributes).

### 7.3 Against the prior art

| system | form | who checks it | a misspelling |
|---|---|---|---|
| Go struct tags | "an optional string literal tag … made visible through a reflection interface and take part in type identity for structs but are otherwise ignored" (Go spec) | the library, at run time, by parsing the string | not seen by the compiler ("otherwise ignored") |
| Go directives | `//go:generate`, `//go:build`: "go generate does not parse the file, so lines that look like directives in comments or multiline strings will be treated as directives" (`cmd/go`) | the tool | not seen by the compiler |
| Kubebuilder markers | "Markers are single-line comments that start with a plus, followed by a marker name, optionally followed by some marker specific configuration" (Kubebuilder book); e.g. `// +kubebuilder:validation:Minimum=0` | controller-gen | I have not established what controller-gen does: neither page read says |
| Rust attributes | "Attr → SimplePath AttrInput?", "AttrInput → DelimTokenTree \| = Expression"; derive macros "operate over token streams instead of AST nodes" (Reference) | the derive macro that declares the helper attribute, on tokens | the macro's choice; unknown tool attributes are accepted |
| OCaml attributes | "“decorations” of the syntax tree which are mostly ignored by the type-checker but can be used by external tools" (manual) | the ppx | the ppx's choice |
| C# attributes | "a class that derives directly or indirectly from Attribute"; "The constructor's parameters are the custom attribute's positional parameters" (Microsoft docs) | the compiler, against the class | not stated in the pages read |
| Java annotations | element types restricted: "A primitive type String Class … An enum class type An annotation interface type An array type …" (JLS §9.6) | the compiler | not stated in the pages read |
| Kotlin | "`@Serializable` annotation instructs the Kotlin Serialization plugin to automatically generate and hook up a _serializer_" (kotlinx.serialization docs) | compiler plugin | not stated in the pages read |
| Zig | no attributes; layout is a keyword (`extern struct`, `packed struct`); reflection is `@typeInfo` at comptime | the compiler | not stated in the pages read |
| **here** | keyword clauses; `@attr(…)` against an `attr` declaration | the elaborator | an error |

The design takes C#'s and Java's typed attributes, whose declaration is a type in the language.
Two things differ. The reader is a polytypic function at elaboration, not reflection at run time.
And a parameter may be typed by the target's type (`@default`), which neither C# nor Java can
express. It takes Zig's keyword for layout. Kubebuilder markers are the anti-pattern the user
named. Their `// +kubebuilder:validation:Minimum=0` is here `@schema(minimum = 0)`, a checked
value that the decoder also enforces (§8.4).

F# type providers go the other way: "a component that provides types, properties, and methods
for use in your program … based on an external data source" (Microsoft docs). Generating
declarations *from* a CRD's schema (to read someone else's resource) would be that direction. It
is not proposed. A generator that writes declarations into a file, as a build step, would serve,
and it needs no language feature.

### 7.4 Per-type overrides

    impl encode[Duration] = encode_duration
    impl present[Option[A]] = is_some[A]
    impl schema[Json] = schema_any

- **One form:** `impl p[N] = f` supplies the instance of the `poly` `p` at `N`. `f` must have
  `p`'s signature at `N`, which is checked. Parameters are allowed (`Option[A]`). Such an `impl`
  is a template, instantiated with `A` as `p[Option[i32]]` is requested.
- **Resolution.** When specialising `p[T]`, the elaborator first looks for an `impl` whose head
  matches `T`, then uses `p`'s cases (§6.3).
- **Coherence.** At most one `impl` per (`poly`, head) in a program. Overlapping heads are
  rejected: `impl p[Option[A]]` beside `impl p[Option[i32]]` is an error. There is no
  specialization.
- **Orphans.** An `impl p[N]` is written in the package of `p` or of `N`, as Rust requires.
- **`derives p`** on a declaration is `impl p[N] = <p's cases at N>`, exported with `N`. For an
  abstract `N`, this is the only way outside code gets `p[N]`, since `p`'s cases need the iso.
  Swift does the same: "Implementation can be synthesized by the compiler in cases where all
  properties are also `Encodable` or `Decodable`", and "This synthesis can always be overridden
  by a manual implementation" (SE-0166).
- **Per field**, `@json_with(f)` overrides one field's encoder. That is serde's `with`,
  "Combination of serialize_with and deserialize_with" (serde field attributes).

**`derives` is explicit.** A `poly`'s cases could apply to any type whose iso is visible, with no
opt-in. Starting explicit is the reversible choice: dropping the requirement later breaks no
program, while adding it would break every program that relied on it. Explicit opt-in also keeps
a type's wire format from changing because a field was added in another package.

**The open overlap with interfaces.** An interface (the packages hypothesis) is a named set of
function signatures over a type. `impl Json for N { encode = f; decode = g }` is then sugar for
the two single-`poly` `impl`s. `derives Json` means every member by its cases, and a bound
`T: Json` means the instances exist. The bound is only needed if a generic body is checked
*once*, not per instance, and decision 45 checks per instance. What remains undecided: whether an
interface may have members that are not `poly`s (plain generic functions with a default body),
and whether an `impl` may be found through an interface bound at a type the elaborator has not
specialised (dynamic dispatch). Neither is needed by any target here. §12 Q6 recommends a
resolution.

## 8. JSON and CRD needs

### 8.1 Optional fields

`Option[T]` is a library declaration, `data Option[T] = None | Some(T)`, which is `1 + T`.

- `encode` omits a field whose value is not `present` (§7.4, `impl present[Option[A]] = is_some`).
  A `None` field is absent, not `null`. serde's default is different (it writes `null` unless
  `skip_serializing_if` is given), and Kubernetes objects are written with absent fields.
- `decode` gives `None` for a missing key.
- `schema` leaves an `Option` field out of `required`.

### 8.2 Defaults

`@default(v)` is checked at the field's type (§7.2). `decode` uses `v` for a missing key, and
`schema` writes `"default": v`. A field that has a default is not `required`. A type-wide
default (Rust's `Default`) is a `poly default[T]() -> T` with `derives default`. `@default`
without a value would read it, and is not proposed until a target needs it.

### 8.3 Enums

- **C-like** (every constructor nullary): `encode` writes the constructor's name as a string, or
  `@json(rename = …)` on the constructor. `schema` writes `{"type": "string", "enum": [names]}`.
  In memory it is one tag word (§5.2).
- **With payloads:** externally tagged by default (`{"Status": {…}}`). `@json(tagging =
  Internal(tag = "type"))`, `Adjacent(…)` or `Untagged` choose serde's other forms. They are
  constructors of the declared type `Tagging`, so `tagging = "internal"` is a type error. serde
  spells them `tag = "…"` and `untagged`: "On an enum: Use the internally tagged enum
  representation, with the given tag", and "Use the untagged enum representation for this enum"
  (serde container attributes).

### 8.4 Validation constraints

- **Typed values:** `@schema(minimum = 1, maximum = 3)`, `min_length`, `max_length`, `pattern`,
  `format`, `description`. These are the schema keywords kube-rs reaches through schemars:
  "#[schemars(range(min = 1, max = 10))] Sets the minimum/maximum properties for number schemas"
  (schemars attributes).
- **Checked on both sides.** `schema` publishes them, and the derived `decode` checks the numeric
  and length ones, failing with `Invalid(field, constraint)`. A constraint the server enforces is
  then also enforced for a value the operator decodes from anywhere else. `pattern` is published
  only: there is no regex engine, so it is not checked on decode.
- **On the type, to make it an invariant.** `data Replicas @schema(minimum = 1, maximum = 3) =
  Replicas(i32)`, exported abstract with a checked constructor `replicas(i32) -> Option[Replicas]`,
  carries the constraint wherever `Replicas` goes. Its derived `decode` checks it, and no other
  code can build an out-of-range one (§2.4). This is the strings design's T2 pattern. A refinement
  in the type itself (`i32{1..3}`) would need #72's sizes and is not proposed.
- **CEL rules** (`x-kubernetes-validations`) are a string in another language, which the API
  server checks. `@kube_rule(rule = "self.minReplicas <= self.replicas")` would be a typed
  attribute whose value is text. The rule is not checked here, and the design says so, rather
  than pretending otherwise.

### 8.5 CRD specifics

- **No `$ref`:** the Kubernetes CRD documentation lists "These fields cannot be set: definitions ,
  dependencies , deprecated , discriminator , id , patternProperties , readOnly , writeOnly ,
  xml , $ref". So `schema` inlines every named type, and at a recursive type it has no answer.
  Its `rec` case is an error that asks for an override (§9.2: `impl schema[Json] = schema_any`,
  the preserve-unknown-fields schema). A JSON Schema generator for other uses would write `$ref`s
  to `DataMeta.name`, and the type name is what makes that possible.
- **The resource itself:** `@kube(group = …, version = …, kind = …, plural = …)` on the root, read
  by `derives resource`. kube-rs's `#[kube(group = "clux.dev", version = "v1", kind = "Foo",
  namespaced)]` "will generate a root object containing your spec and metadata"
  (`kube::CustomResource`). Here the root is written (§9.1) and the attribute supplies what the
  CRD manifest and the API paths need.

## 9. The target declarations

Each target has a proposed form (`proposed/`) and, where the language can express it today, a
hand-lowering (`lowered/`). The lowering writes by hand what the elaboration would produce: the
types as structural aliases, and the derived functions specialised. The results below are
`run.sh`'s. Its format is the output of `bcc run`, then `bcc-counts`' allocations, dispatched
calls and copies. `bcc interp` agreed with `bcc run` on every program.

| program | output (`bcc run`) | allocs | indirect | copies |
|---|---|---:|---:|---:|
| `crd.bc` | `{"spec":{"size":2,"containerPort":11211},"status":{"phase":"Running","readyReplicas":2}}`, `{"spec":{"size":7,"containerPort":80,"version":3}}`, `i32[1]`, `live 0` | 1 | 0 | 0 |
| `json.bc` | `{"a":[1,true,"hi"],"b":null,"c":{}}`, `i32[0]`, `live 0` | 172 | 85 | 0 |
| `intcode.bc` | `Mul(Pos(4), Imm(3), Pos(4))`, `Halt`, `i32[99]`, `live 0` | 2 | 0 | 0 |
| `graph.bc` | `2 1 1 0`, `i32[4]`, `live 0` | 3 | 0 | 0 |
| `map.bc` | `(i32[3], (i32[20], i32[0]))`, `live 0` | 19 | 8 | 2 |
| `map-generic.bc` | rejected, as expected: "the type of `insert` does not elaborate here" | | | |
| `views.bc` | `8080`, `(i32[4], i32[4])`, `live 0` | 2 | 0 | 0 |
| `codata.bc` | `(i32[3], (i32[2], i32[1]))`, `live 0` | 0 | 0 | 0 |
| `handle.bc` | `i32[7]`, `live 0` | 2 | 0 | 0 |

The derived code of the non-recursive targets allocates only what the program writes (the
output capability's cell, the arrays) and makes no dispatched call. `json.bc`'s 172 allocations
and 85 dispatched calls are the text carrier of §6.4: a list cell per byte, and `append` as an
owned fold into closures. That is the price of constraint 1, measured.

### 9.1 A CRD spec and status

[`proposed/crd.bc`](type-declarations/proposed/crd.bc),
[`lowered/crd.bc`](type-declarations/lowered/crd.bc).

- **Declarations.** `Phase` (C-like), `MemcachedSpec` (`size` with `@schema(minimum = 1, maximum
  = 3)`, `container_port` renamed, `version: Option[i32]`), `MemcachedStatus` (`phase` with
  `@default(Pending)`, `ready_replicas` optional and renamed), and the root `Memcached` with
  `@kube(…)`.
- **Elaboration.** `Phase = 1 + (1 + 1)`, `Spec = i32 * (i32 * (1 + i32))`,
  `Status = Phase * (1 + i32)`, `Memcached = Spec * (1 + Status)`. There is no `μ`, and nothing
  is boxed.
- **Layout.** `Spec` is 1 + 1 + 2 = 4 words and `Status` 1 + 2 = 3 today. The whole object is 10
  words on the stack.
- **Derived.** `encode[Memcached]` writes
  `{"spec":{"size":2,"containerPort":11211},"status":{"phase":"Running","readyReplicas":2}}`.
  `validate[Spec]` rejects `size = 7` naming field 1. `schema[MemcachedSpec]` is the inlined
  object schema in the proposed file's comment. The lowering does not print the schema: it is a
  constant, and without text literals (strings S5) it would be several hundred `putb`s.

### 9.2 The JSON value type

[`proposed/json.bc`](type-declarations/proposed/json.bc),
[`lowered/json.bc`](type-declarations/lowered/json.bc).

- **Declaration.** `Null | Bool(bool) | Num(f64) | Str(string) | Arr(Vec[Json]) |
  Obj(Vec[Member])`, with `Member = { key: string, value: Json }`, and overrides for `encode`,
  `decode` and `schema`: it *is* the data model.
- **Elaboration.** A `μ` with `X` under an array, which is outside `FShape` (§6.5). Today:
  the sibling encoding, `J = μX. (1 + i32) * (Kind * (1 + ref X))`, with `Arr`/`Obj` pointing at a
  first child.
- **Layout.** Each node is one cell holding a key, a tag and the widest kind, plus a sibling
  pointer: one allocation per node. With `FShape`'s `arr` case, an array's elements would be one
  allocation of fixed-width slots.
- **Derived.** `encode` is a `fold_imm` whose carrier is text (§6.4, constraint 1), and it prints
  `{"a":[1,true,"hi"],"b":null,"c":{}}`. `decode` is not derived: a recursive type's decoder is a
  pull parser with an explicit stack (§6.4). `schema` is `x-kubernetes-preserve-unknown-fields`
  by override.

### 9.3 An Intcode instruction type

[`proposed/intcode.bc`](type-declarations/proposed/intcode.bc),
[`lowered/intcode.bc`](type-declarations/lowered/intcode.bc).

- **Declarations.** `Param = Pos(i32) | Imm(i32) | Rel(i32)` and a ten-constructor `Instr` (the
  lowering keeps five).
- **Elaboration.** Nested `+` of nested `*`, with no `μ` and no `box`.
- **Layout.** This is where §5.2 matters. `Param` is 3 words today and `Instr` 17. With n-ary
  tags they are 2 and 7. With a tag packed beside an `i32` (§5.3) they are 1 and 4, which is what
  Rust's `enum` gives with explicit `i32` payloads.
- **Derived.** `debug[Instr]` prints `Mul(Pos(4), Imm(3), Pos(4))`. The lowering decodes,
  prints and runs `1002,4,3,4,33` to 99.

### 9.4 A graph with node ids

[`proposed/graph.bc`](type-declarations/proposed/graph.bc),
[`lowered/graph.bc`](type-declarations/lowered/graph.bc).

- **Declarations.** `NodeId(i32)` and `EdgeId(i32)`, both newtypes, and `Edge = { from: NodeId,
  to: NodeId }`.
- **Elaboration.** `NodeId = i32`, `Edge = i32 * i32`. `NodeId` and `EdgeId` are different types
  to the elaborator only. That is the point of §2.
- **Layout.** A `NodeId` is one word, and an `array Edge` is one allocation of two-word slots.
- **Derived.** `encode[NodeId]` is `3`, by the `newtype` case.

### 9.5 `Map[K, V]`, declaration side

[`proposed/map.bc`](type-declarations/proposed/map.bc),
[`lowered/map.bc`](type-declarations/lowered/map.bc).

- **Declaration.** `export data Map[K, V]` (abstract) and its functions. The representation is
  private, and so are the exported `impl`s built from it.
- **Elaboration.** A template. The lowering is an association list, `μX. 1 + ((K * V) * X)`, with
  `empty` and `insert` written at `[i32, i32]`. The generic form, `map-generic.bc`, is rejected
  today (§3.1). The `μ` is written in every signature, because `type` takes no parameters. `size`
  is a `fold_imm` with a data carrier. `get` is a `fold_own` over a copy, whose carrier is a
  function of the key (§6.4, constraint 2).
- **Layout.** Per the representation. The recommended `buf K ⊗ buf V` is two `(ptr, cap, len)`
  headers inline and two allocations.

### 9.6 A record of views, with a lifetime parameter

[`proposed/views.bc`](type-declarations/proposed/views.bc),
[`lowered/views.bc`](type-declarations/lowered/views.bc).

- **Declarations.** `Field<'a> = { name: slice 'a u8, value: slice 'a u8 }`, and the strings
  design's `Tok<'a>`.
- **Elaboration.** `array_imm 'x u8 * array_imm 'x u8`, substituted at the borrow's lifetime. The
  record lives inside the borrow block, and its type says why.
- **Layout.** Four words, unboxed. No allocation beyond the buffer.

### 9.7 A C struct for FFI

[`proposed/zstream.bc`](type-declarations/proposed/zstream.bc). There is no lowering: there is
no FFI and no byte-level block layout.

- **Declaration.** `data ZStream layout C = { … }`, fourteen fields in zlib's order, with C integer
  aliases and the platform design's pointer types. It is declared in the binding package and
  exported abstract (decision 27), and wrapped in a linear owner `ZStreamBox` whose end is the
  extern `inflate_end`.
- **Elaboration.** A record type. `box ZStream::zeroed()` makes a block.
- **Layout.** §5.4's table: 112 bytes on LP64 and 56 on wasm32, one allocation, and one address
  for its life.

### 9.8 A declared codata iterator

[`proposed/codata.bc`](type-declarations/proposed/codata.bc),
[`lowered/codata.bc`](type-declarations/lowered/codata.bc).

- **Declaration.** `codata Countdown { next; remaining; close }`, and `Iter`, `Gen`, `Loop` as
  library declarations (§4.3).
- **Elaboration.** `νX. (F (i32 * U X + 1) & F (i32 * U X)) & F 1`. The observations are the
  paths `.1.1`, `.1.2` and `.2`. `unfold` with one arm each builds it.
- **Layout.** A thunk: its code's tag and its state's words (`Backend/README.md`, closures). No
  allocation for a non-recursive closure type.

### 9.9 A linear handle with a destructor

[`proposed/handle.bc`](type-declarations/proposed/handle.bc),
[`lowered/handle.bc`](type-declarations/lowered/handle.bc).

- **Declarations.** `Session drop end_session`, `Tx linear`, and `File drop close_quietly` over
  an opaque host type.
- **Elaboration.** The inserted `end_session(s)` calls at the end of each path. The lowering
  writes them by hand, one per arm, and ends with `live 0`.
- **Layout.** A `Session` is `ref i32 * i32`, two words.

## 10. Kernel, spec and backend changes

| change | where | kind | justification |
|---|---|---|---|
| declarations, parameters, iso, constructors, patterns, fields | frontend (TIR `named`, elaboration) | elaboration | none needed: nothing reaches the core |
| `poly`, `impl`, `derives`, `attr` | frontend | elaboration | decision 26 (type-directed sugar) |
| `codata` declarations; `Iter`, `Gen`, `Loop` in `lib/gen.bc`; delete the `CTy` abbreviation nodes | frontend, `lib/` | elaboration, deletion | growth rule "Generalize by deleting" |
| `drop f`, `linear` | frontend; SPEC §12's insertion policy | policy | placement never affects soundness (SPEC §12, *Soundness*) |
| abstraction (`export data N`) | frontend, with #63 | elaboration | decision 9 |
| instances at types with lifetimes | frontend | lifts decisions 41 and 45's restriction | §3.2 |
| n-ary tags; niches | backend layout types | representation | §5.2, §5.3 |
| byte-granular blocks in declaration order; `layout C` | backend | representation | §5.4 |
| contiguous blocks | SPEC §5, #77 | **kernel**: an allocating head step | already planned; needed by `layout C` |
| `arr` in `FShape` (recursion under arrays) | SPEC §6 | **kernel**: three fold rules and `dtor_wf` extended | §6.5; JSON and every mutually recursive declaration |

The two kernel items each need their own entry, with the baseline theorems they must preserve.
This design depends on them but does not specify them.

A SPEC entry for declarations would read like §15's baseline: "No `CDerives` rule, relation
clause, machine step or kernel type is added."

## 11. Staging

| # | stage | needs | unblocks |
|---|---|---|---|
| D1 | `data` without parameters: records and variants, constructors, patterns, fields, `box` of a record as a block, the recursion check; TIR `named`, errors by name | typed elaboration §5.3 | `pending/data-box-tree.bc`; strings P2 |
| D2 | type and lifetime parameters; regularity; `type` with parameters; a generic `fn`'s signature substituted before it is elaborated (§3.1) | D1 | strings S6 and P8 (`Tok<'a>`); `Option[T]`; `List[T]` in the prelude |
| D3 | `codata` declarations, `unfold` blocks, observations by name; `Iter`/`Gen`/`Loop` as declarations and the frontend nodes deleted | D2 | iteration design's pull types by name |
| D4 | `drop f`, `linear` | D1 | handles; platform design's resources |
| D5 | `attr`, `poly`, `impl`, `derives`; the structure view; `eq`, `debug`, `clone`, `hash` | D2 | the operator's derived types |
| D6 | `encode`/`decode`/`schema` for JSON, with a text carrier over recursive types | D5, strings S5 (literals, `buf`) | #65, the operator's CRD |
| D7 | backend: n-ary tags, niches | none | the Intcode layout |
| D8 | `layout C`, byte-granular blocks | #77, block provenance, platform design | zlib |
| D9 | `export`/abstract | #63 | strings T2, `Map` |
| K | `FShape` over arrays | its own entry | `Json` as declared |

Each stage lands with its entry, its lowering, and running corpus programs (decision 17).

## 12. Open questions, with recommendations

1. **Q1. Should abstraction ever be a theorem?** Recommendation: no, until a trusted boundary
   needs representation independence proved. Then add a sealing former, costed then.
2. **Q2. Spelling of the declaration forms.** `data … = { … }` for records and `data … = C | …`
   for variants (one keyword, as typed elaboration §5.3 and the operator sketch use), `codata …
   { obs : C }`, clauses after the name and parameters. Recommendation: keep. This is not a
   one-way door.
3. **Q3. Explicit `derives`.** This *is* a one-way door in one direction (§7.4). Recommendation:
   explicit, as proposed.
4. **Q4. Shortening records of borrows.** Recommendation: a derived `shorten` (§3.2), plus
   shortening for families, which would unblock it. Their absence is decision 45's.
5. **Q5. Nested recursion.** Recommendation: the `FShape` entry (§6.5), with the sibling encoding
   meanwhile.
6. **Q6. Overrides and interfaces.** Recommendation: `impl p[N] = f` now. An interface, when it
   comes, is a named set of `poly`s and generic signatures, and `impl I for N { … }` is sugar for
   the per-`poly` `impl`s. No dynamic dispatch through bounds until a program needs it.
7. **Q7. Where layout is decided for blocks.** Recommendation: declaration order with natural
   alignment for every block (§5.4), which makes `layout C` a check. The alternative, an
   annotation carried on the core allocation constant, is a syntactic kernel change for no
   gain until the backend reorders fields.
8. **Q8. `None` fields: absent or `null`?** Recommendation: absent, with `@json(null_if_none =
   true)` if a target needs `null`.
9. **Q9. Streaming derived encoders over recursive data.** Recommendation: text carrier now
   (§6.4). The streaming form waits for the borrowed traversal of SPEC §7 Open.
10. **Q10. Anonymous records** (the operator sketch's `spec: { replicas: i32 }` inline).
    Recommendation: an inline record type is a declaration named after its position
    (`DeploymentScale.spec`), so it has labels and derives with its parent. Two identical inline
    records are then different types.

## 13. What I have not established

- I have not established that `fold_imm`, `fold_own` and `fold_reuse` extend soundly to
  recursion under arrays (§6.5). The witness-size argument is the plan, not a proof.
- I have not established what in the implementation depends on "instances are at types without
  lifetimes" (decisions 41, 45), or what lifting it costs (§3.2).
- I have not established that SPEC §12's insertion, as implemented in `Frontend/Check/`, can
  report its inserted drops with enough position to compare against the elaborator's (§4.5).
- I have not established a streaming, non-allocating derived encoder over a borrowed recursive
  value (§6.4). The data carrier and the owned thunk carrier run in `lowered/`. The `!` carrier
  is rejected by the checker.
- I have not established why a pair literal passed as `at`'s default is checked against `i32`
  (`lowered/graph.bc` binds it to an ascribed `let` first). It looks like an inference-order
  issue in decision 45's matching, unrelated to declarations.
- I have not established the C offsets by compiling C. §5.4's table follows the C rules for LP64
  and ILP32 as Rust's reference states them.
- I have not established what controller-gen does with a misspelled Kubebuilder marker. The two
  Kubebuilder pages read do not say.
- I have not read the generics-sop paper itself, only its abstract page and the Hackage docs. I
  have not read a Generic Haskell source. The polytypic definition is from the Chalmers PolyP page.
- I have not measured the layout sizes in §5.2 and §9.3. They are computed from
  `Backend/README.md`'s formulas.

## 14. Prior art

Every quotation below was read from the page named, in September 2026.

- **Rust.** The Reference, *Type layout*
  (https://doc.rust-lang.org/reference/type-layout.html).
  - Default representation: "The ordering does not have to be the same as the order in which the
    fields are specified in the declaration of the type", and "There are no other guarantees of
    data layout made by this representation."
  - `repr(C)`: "The C representation is designed for dual purposes. One purpose is for creating
    types that are interoperable with the C Language."
  - `repr(transparent)`: "Structs and enums with this representation have the same layout and ABI
    as the only non-size 0 non-alignment 1 field".
  - *Attributes*: "An attribute is a general, free-form metadatum that is interpreted according
    to name, convention, language, and compiler version."
  - *Procedural macros*: derive macros "are given the token stream of a struct, enum, or union
    definition and can emit new items after it. They can also declare and use derive macro helper
    attributes".
  - Taken: `repr(C)`'s algorithm for `layout C`, NPO as a niche, `transparent` as the newtype
    case.
  - Not taken: attributes as token trees that only their macro checks.
- **serde** (https://serde.rs/data-model.html, attributes pages).
  - "a way of mapping every Rust data structure into one of 29 possible types"; "The Serde data
    model is a simplified form of Rust's type system."
  - Taken: the three attribute targets; rename, skip, default and with; the four enum taggings.
  - Here the data model is the core's structure view, so there is no separate model to map
    into.
- **kube-rs and schemars** (https://docs.rs/kube/latest/kube/derive.CustomResource.html,
  https://graham.cool/schemars/).
  - kube-rs: "Server-side validation require mutation of your generated schema, and can in the
    basic cases be achieved through the use of schemars's validation attributes".
  - schemars: "Schemars will check for any #[serde(...)] attributes on types that derive
    JsonSchema, and adjust the generated schema accordingly".
  - Taken: one attribute read by both the codec and the schema (§8.4).
- **Haskell.**
  - Haskell 2010 §4.2.3, `newtype` (quoted in §2.1).
  - GHC.Generics (https://hackage.haskell.org/package/base/docs/GHC-Generics.html): V1, U1, K1, M1,
    `:+:` ("Sums: encode choice between constructors") and `:*:` ("Products: encode multiple
    arguments to constructors"). The generic default method: "We need the default encode
    signature because ordinary Haskell default methods must not introduce additional class
    constraints, but our generic default does."
  - Taken: the iso, and metadata as typed data.
  - Not needed: `Rep` as a separate type, and `from`/`to` as code.
- **generics-sop** (https://www.andres-loeh.de/TrueSumsOfProducts/,
  https://hackage.haskell.org/package/generics-sop). Quoted in §6.2. Also: "There is a class
  Generic, which for a given datatype A, associates the isomorphic SOP representation with the
  original type under the name Rep A." Taken: the sum-of-products view, with metadata kept
  separate from structure.
- **Polytypic programming** (Chalmers PolyP page, https://www.cse.chalmers.se/~patrikj/poly/).
  "A polytypic function is a function that is defined by induction on the structure of
  user-defined datatypes", motivated by "pretty printers, parsers, equality functions …". A
  `poly` is one, and the recursive case is a fold (§6.4).
- **OCaml** (https://ocaml.org/manual/latest/attributes.html,
  https://github.com/ocaml-ppx/ppx_deriving).
  - Attributes are quoted in §7.3.
  - `[@@unboxed]` "tells the compiler to optimize the representation of the type by removing the
    block that represents the record or the constructor".
  - ppx_deriving: "_deriving_ is triggered by a `[@@deriving plugin]` annotation attached to a type
    declaration".
  - OCaml boxes by default and unboxes on request; here it is the other way round.
- **Swift Codable** (SE-0166). Quoted in §7.4. Renaming is a nested `CodingKeys` enum: "When this
  enumeration is present, its cases serve as the authoritative list of properties that must be
  included when instances of a codable type are encoded or decoded" (Apple, *Encoding and
  Decoding Custom Types*). That is renaming written as code, and it is checked. `@json(rename)` is
  terser for the common case.
- **Zig** (https://ziglang.org/documentation/master/).
  - `extern struct` is quoted in §5.4.
  - "Zig gives no guarantees about the order of fields and the size of the struct but the fields
    are guaranteed to be ABI-aligned."
  - `@typeInfo` "Provides type reflection", with fields "guaranteed to be in the same order as
    appearance in the source file".
  - Taken: layout as a keyword, and reflection in declaration order.
  - Not taken: general comptime evaluation.
- **F# type providers** (https://learn.microsoft.com/en-us/dotnet/fsharp/tutorials/type-providers/).
  Quoted in §7.3. The inverse direction, not proposed.
- **Lean 4** (https://lean-lang.org/doc/reference/latest/).
  - "Structures are inductive types that have only a single constructor and no indices … projection
    functions are generated for each field".
  - "Instance deriving uses a table of deriving handlers that maps type class names to metaprograms
    that derive instances for them."
  - Taken: records as one-constructor data, and `derives` resolved per name.
  - Not taken: handlers as metaprograms. A `poly` is ordinary code by cases.
- **Idris 2** (https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html). "Idris provides
  syntax for defining records and automatically generating field access and update functions",
  and "Each record is defined in its own namespace, which means that field names can be reused in
  multiple records." Taken: field names scoped to their declaration.
- **Kubebuilder** (https://book.kubebuilder.io/reference/markers.html). "This code and config
  generation is controlled by the presence of special "marker comments" in Go code." It is the
  anti-pattern (§7.3).
- **C#, Java, Kotlin, Go.** Quoted in §7.3.
