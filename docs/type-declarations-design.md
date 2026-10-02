# Type declarations — design

Status: design only, revision 2. Nothing here is implemented. **Spellings are provisional
throughout** (`data`, `codata`, `poly`, `@attr(…)`, `derives`, `box`): they are written so that
the examples can be read, and are not the design. The design is the mechanism each one
elaborates to, which is stated in core terms beside it.

- The target declarations are in [`type-declarations/proposed/`](type-declarations/proposed/),
  in the proposed surface. They do not parse.
- Their hand-lowerings to today's language are in
  [`type-declarations/lowered/`](type-declarations/lowered/). Each is what the elaboration would
  produce, written by hand, and each is checked by `bcc check` against `main` (`620c82c`).
  [`type-declarations/run.sh`](type-declarations/run.sh) also runs and counts them. It is outside
  the gate.

It builds on SPEC §2 (`!`), §5 (records, blocks), §6 (`μ`, folds), §7 (`ν`), §9 (arrays), §12
(destructors), §15 (generators), §18–§21 (effects, recursion as the fixed point of a generator).
It also builds on [`typed-elaboration.md`](typed-elaboration.md) §5.3 (`data`, `box`),
[`effect-polymorphism.md`](effect-polymorphism.md) §5.9 (objects have observations), and
decisions 6, 9, 24, 26, 27, 39, 45 and 54–59. The inventory of what the language writes today
(#235) is the baseline for what reads naturally.

## 0. Summary

**A declaration is a name plus an isomorphism to a structural type.** The name is nominal, and
only the elaborator sees it. The structure is an ordinary core type, built from the formers the
kernel has: `⊗` for records, `⊕` for variants, `μ` for recursion, `ν` or `&` for codata. The iso
is what constructors, patterns, field access and derived code elaborate through. In the core it
is the identity, or `roll`/`unroll` at a recursive type, and both erase. No kernel rule is added
for declarations, parameters, labels, codata declarations, derive or attributes.

| question | answer | § |
|---|---|---|
| 1. Identity | Confirmed: a name plus an iso. Nominal in the elaborator, structural in the core. At boundaries, structural where data leaves the program (wire formats by field label, FFI by layout) and nominal between packages (abstraction). | 3 |
| 2. Parameters | Type `[T]` and lifetime `<'a>` parameters, instantiated by substitution (a declaration is a template, as a generic `fn` is). Regular recursion only. Mutual recursion elaborates to one `μ` when one member lies on every cycle. **No kernel change**, except recursion under an array or a nested `μ` (`Vec[Json]`), which is the existing `FShape` entry. | 4 |
| 3. Labels and fields | Labels are erased; the declaration table keeps them. A `let mut` record is its fields as places; a boxed record is a block (decision 6), a cell per field. Constructor patterns are `out_N` then `case`. | 5 |
| 4. Data and codata | `data` declares constructors; `codata` declares observations, each with its own row (§5.9). With `Self` it is a `ν`, built by `unfold`; without, a `&`. The pull types (`Pull`, `Iter`, `Loop`) become library declarations, and the frontend's five abbreviations go. Generators stay functions that perform `Yield`, not declarations. Pipelines stay flat: a `ν` hides its state. | 6 |
| 5. Layout | Unboxed by default. Recursion only under `box` (a field pointer) or in a block (`box Node(…)`). n-ary tags and niches in the backend. `layout C` is a keyword clause, which needs #77. | 7 |
| 6. Derive | A `poly`, a function by cases on the structure view, specialised at elaboration and checked by the unchanged checker. It is the restricted first case of a compile-time evaluator (open: whether to build the general one). Metadata is typed attributes and keyword clauses. **Where derived results are found (traits or handlers with ambient defaults) is open**; §9.5 runs the deciding test under each candidate. | 8, 9 |
| 7. Driving programs | JSON with a parser, a CRD, a tree and a graph, a hash map, an Intcode VM, a regex AST and a Brainfuck interpreter: each has a proposed form and a lowering that `bcc check` accepts. | 10 |

**What this revision changes**, against revision 1 (the PR's first commit):

- The per-type overrides (`impl encode[N] = f`, its coherence and orphan rules) are withdrawn. A
  `poly` names declared types in its own cases (`present` at `Option`); a field takes
  `@json_with(f)`. Where generic code finds `hash`, `eq` and `cmp` for a type parameter is laid
  out as the open question of §9.5, with traits, declaration-attached providers and handlers
  with ambient defaults side by side.
- Codata declarations shrink to the pull types and objects. `Gen` and the `iterate` override are
  gone: generators are `Yield` handlers (SPEC §15), and iterating a codata value is a generator
  over it.
- Recursion is now SPEC §20–§21's: derived and hand-written functions over recursive types may
  recurse, under `bounded`. §9.3 says which derived functions recurse and which fold, and what
  the lowerings found about each.
- Instances of generic functions may now carry lifetimes (SPEC §15, *Generic functions*), so
  revision 1's blocker for `buf[Field<'x>]` is gone.
- Seven driving programs, five of them new (JSON parser, tree, hash map, regex, Brainfuck), each
  lowered and checked.

## 1. Decisions needed from the user

Each item says what is recommended and what changes if the other way is chosen. None blocks the
first stage (D1, §12) except where it says so.

1. **Identity (§3).** Confirm: a name plus an iso, nominal in the elaborator and structural in
   the core; abstraction enforced by the elaborator only (no sealing former in the kernel).
2. **Where derived results are found (§9.5).** Traits (T), providers attached to their type's
   declaration (D), or handlers with ambient defaults (H), with H's coherence handled by static
   names in the type (H1), by data that carries its provider (H2), or by a run-time check (H3).
   The deciding test: both cases come out clean under T, D and H1, and H1 at those structures is
   type-directed resolution of named providers. Under H2, `union` is clean and `merge` needs a
   run-time check or the slow algorithm. Not decided here. It blocks stage D6 (hash maps, #211),
   not D1–D5.
3. **Derive as a `poly` or as comptime (§9.1).** Recommended: build `poly` (case analysis on the
   structure view, nothing else at compile time) as the first instance of an effect-restricted
   comptime, and defer the general evaluator until a program needs more than case analysis.
4. **Explicit `derives` (§9.1).** Recommended: explicit. Under H the structural handler is
   ambient for every transparent type, and `derives` would then be needed only to export a
   derivation of an abstract type. That is the one-way-door direction: adding the requirement
   later breaks programs, dropping it does not.
5. **Mutual recursion (§4.3).** Recommended: elaborate a group with one member on every cycle to
   one `μ` (it covers the Brainfuck tree, any `List[T]`-of-children tree, and every non-nested
   ADT), and reject the rest with a message naming the nested occurrence until the `FShape`
   entry lands. The alternative is to put the `FShape` entry first, which `Vec[Json]` needs.
6. **The pull types as library declarations (§6.3).** Recommended: delete the frontend's
   `delay`, `stream`, `iter`, `loop` and `pull` nodes when `codata` lands, and have the
   elaborator find the library's declarations by structure, as it finds `Yield`.
7. **Recursion inside loops (§10.1, SPEC §21 *Open*).** Not part of this design, but the JSON
   parser needs it: a parser of a wide array either loops inside a recursion (rejected today) or
   recurses once per element (each call spends budget, so more than 10 000 elements raise
   `Exhausted`). Decide whether that entry is prioritised with declarations.

## 2. The state today

Checked in this worktree at `620c82c` (`main`, after #232):

- `type X = …` is a transparent abbreviation with no parameters (`Decl.type (sp) (n) (A)` in
  `Frontend/Syntax.lean`), expanded before checking.
- `data` does not parse; `corpus/pending/data-box-tree.bc` pins the parse error. Its program is
  the spelling the user decided in typed elaboration §5.3: `data Tree = Leaf | Node(left: Tree,
  val: i32, right: Tree)`, a node one block with a cell per field, allocated by `box Node(…)`.
- No label survives into the core: "A record is a binary tree of `⊗` (no trailing `1`); a variant
  is a nest of `⊕`" (SPEC §5).
- Generic functions exist (`fn f[A]<'a>`, decision 45), elaborated per instance. An instance's
  type arguments may mention lifetimes, which become lifetime parameters of the instance (SPEC
  §15, *Generic functions*; `corpus/for-adapters.bc`).
- A generic `fn` whose signature has a type parameter inside a `μ` is rejected at its call:
  matching does not look inside a `μ` (`lowered/map-generic.bc`, §4.1).
- Codata are five frontend abbreviations over `ν`: `delay`, `stream`, `iter`, `loop` and `pull`
  (`CTy` in `Frontend/Syntax.lean`). `gen` is gone (decision 56).
- Recursion (SPEC §20–§21): a recursive group is the bounded fixed point of its generator. Its
  members take no lifetime parameters; a generic recursive function is rejected ("groups are
  formed before generic functions are instantiated", `docs/second-class-and-system-c.md`); a
  member whose body loops is rejected (`corpus/reject/rec-loop.bc`).
- Text literals and `buf` exist (SPEC §17): `write_lit(o, "…")`, `push_lit`, `push_dec`.
- Decision 54 ("tentative: no traits") is reopened: the user called traits "very much up in the
  air" (PR #141, 2026-10-01).
- The backend boxes an unboxed `μ` silently ("the fields that close a cycle … are stored as a
  pointer", `Backend/README.md`). §7.1 keeps declared types from producing that.

## 3. Identity: a name and an isomorphism

### 3.1 The mechanism

A declaration `data N[P…]<'l…> = S` introduces:

- **a name** `N`, applied to arguments `N[T…]<'x…>`. The elaborator's types (the TIR) gain one
  constructor, `named N args`. Unification compares two named types by name and arguments, and
  never unfolds them;
- **a structure** `⟦S⟧[T…/P…, 'x…/'l…]`, a core value type;
- **an iso** `into_N : ⟦S⟧ → N` and `out_N : N → ⟦S⟧`. In the core both are the identity when `N`
  is not recursive, and `roll`/`unroll` when it is (SPEC §6: "`roll`/`unroll` on the same term (no
  machine step)").

Lowering erases `named` to the structure, so the checker never sees a name. `type N = S` stays a
transparent alias that unifies with its right-hand side.

This is Haskell's `newtype` generalised to every declaration. The Haskell 2010 report (§4.2.3)
says a `newtype` "introduces a new type whose representation is the same as an existing type",
that "it creates a distinct type that must be explicitly coerced to or from the original type",
and that "these coercions may be implemented without execution time overhead". It is also
GHC.Generics' `Rep` made literal: "converting values of a datatype T into corresponding values of
a (nearly) isomorphic type Rep T". Here the core type is `Rep N`, and `from`/`to` are not code.

### 3.2 What it gives

- **Derive** goes through `out_N` and sees the structure and the declaration's metadata (§9).
- **Abstraction**: a package that exports `N` without its iso exports a type outside code can only
  pass around (§3.4).
- **Error messages** print the names: `expected NodeId, found EdgeId`, where the core has `i32`
  twice.
- **Inference**: a constructor synthesizes its type. A parameter of type `Map[K, V]` matches an
  argument `Map[i32, i32]` by name and arguments, which is what today's matching cannot do with
  the `μ` written out (`lowered/map-generic.bc`).
- **Zero cost**: `NodeId(3)` is the word `3`.

### 3.3 Nominal and structural, by boundary

| boundary | identity | why |
|---|---|---|
| within a program, at elaboration | nominal | `NodeId` and `EdgeId` are both `i32`; the name is what keeps them apart |
| the core and the checker | structural | decision 9; a name carries no semantic content the checker could use |
| anonymous tuples and sums (`A * B`, `A + B`) | structural | they have no name; they unify by structure, as today |
| `type` aliases | structural (transparent) | an abbreviation, as today |
| between packages | nominal, with the iso exported or not | abstraction (§3.4) |
| generic instances | nominal in the key | `Map[i32, Json]` is one instance however its structure is spelled |
| wire formats (`encode`/`decode`) | structural over labels | a JSON object is matched by field label and value shape, never by the type's name; the name only titles a schema |
| FFI (`layout C`) | structural over layout | C sees offsets and widths (§7.4) |

Two declarations with the same structure are different types. Converting between them is
explicit: `B(a.0)` for newtypes, or destructure and rebuild, which erases to nothing. A
`coerce` between two types whose isos are both visible and whose structures are equal would be
sugar for that, and is not proposed until a program needs it.

### 3.4 Abstraction

A package exports a declaration in one of two ways (spelling provisional):

    export data Point = { x: i32, y: i32 }     -- name and iso: constructors, patterns, fields
    export data HashMap[K, V]                  -- the name only: abstract

Outside the package, an abstract `N` has no constructors, no patterns, no fields and no
structural derivations. Inside, it is transparent. The checker sees only structure, so the
elaborator enforces this, as `rustc` enforces Rust's privacy. That is decision 9's "a surface or
module concern". It is not a proof of representation independence; a sealing former in the
kernel would give that, and nothing planned needs it (Q1).

Monomorphization needs the representation at the use site to lay out an instance, so an abstract
type's layout is visible to its clients even though its iso is not, as with Rust's and C++'s
generics (#63).

## 4. Parameters, and how a declaration elaborates

### 4.1 Type parameters

    data List[T] = Nil | Cons(head: T, tail: box List[T])
    data HashMap[K, V] = { slots: array Slot[K, V], len: i32 }

- **Instantiation is substitution.** `List[i32]` is `⟦S⟧[i32/T]`, a closed core type. A
  parameterised declaration is a type-level template, as a generic `fn` is a term-level one
  (decision 45). The core gets no type `∀` (decision 8).
- **Regular recursion only.** Inside `N[P…]`'s body every occurrence of `N` is `N[P…]`, the
  parameters in order. A nested datatype (`data Nest[T] = Nil | Cons(T, Nest[T * T])`) would
  expand forever and is rejected at the declaration, with polymorphic recursion.
- **Type arguments are inferred** by decision 45's first-order matching, where a named type
  matches by name and then arguments.
- **No bounds.** What a body does with a `T` is decided at each instance (decision 45). Whether a
  bound ever appears depends on §9.5.
- **The signature of a generic `fn` is substituted before it is elaborated.** Today a parameter
  of type `mu X. 1 + ((K * V) * X)` does not match an argument at `[i32, i32]`
  (`lowered/map-generic.bc`: "this argument of `insert` has type `mu X. 1 + (i32 * i32) * X`, which
  is not `mu X. 1 + (K * V) * X`"). Named types remove the need to match under a `μ`, and the
  instance's types are substituted as its body already is.
- **Generic recursive functions** (`fn length[T](l: List[T]) -> i32` calling itself) are rejected
  today because recursive groups are formed before instantiation. The fix recorded by the
  second-class spike is "instantiate first, then group". A library of generic containers needs
  it; it is elaboration only.

### 4.2 Lifetime parameters

    data Field<'a> = { name: slice 'a u8, value: slice 'a u8 }
    data Tok<'a> = Punct(u8) | Str(slice 'a u8) | Num(i32) | Word(slice 'a u8) | End

- **Substituted like types.** `Field<'x>` is `array_imm 'x u8 * array_imm 'x u8`.
- **Outlives from the structure.** `Δ ⊢ Field<'x> ⊐ @b` holds when `VOutlives` holds of the
  substituted structure. No variance or outlives clause is declared.
- **Instances at types with lifetimes** now work for functions (SPEC §15); a parameterised
  declaration's instance is a type, so it needs nothing more.
- **Shortening.** `:>` shortens one borrow. A record of borrows is shortened by destructuring,
  shortening each leaf and rebuilding, which erases. A family (`array_imm`) has no shortening
  today (decision 45), so `Field<'x>` cannot be passed at a shorter lifetime until it does (Q4).

### 4.3 Elaboration to existing formers

| surface | core | kernel rule used |
|---|---|---|
| record `{ f₁: A₁, …, fₙ: Aₙ }` | `A₁ ⊗ (A₂ ⊗ (… ⊗ Aₙ))`, declaration order, no trailing `1` | `⊗` (SPEC §5) |
| variant `C₁(…) \| … \| Cₙ(…)` | `P₁ ⊕ (P₂ ⊕ (… ⊕ Pₙ))`, each `Pᵢ` its fields' record, or `1` | `⊕` |
| one constructor of one field (a newtype) | the field's type | none |
| recursive `N` | `μX. ⟦S⟧[X/N]`, each recursive occurrence under `ref` (`box` field) or in a block | `μ`, `roll`/`unroll` (§6) |
| `box C(…)` (a node as a block) | `roll (inj (alloc_s[σ] (…)))`, `σ` the constructor's shape | blocks (§5) |
| `codata` with `Self` | `νX. C`, `Self` as `U X`, observations a `&` tree | `ν`, `unfold` (§7) |
| `codata` without `Self` | `C₁ & … & Cₙ` | `&` |
| `codata … on S` (methods with arguments) | `S ⊗ !U(&ⱼ (S ⊗ Aⱼ ⊸ F(S ⊗ Bⱼ)))` | `!` (§2), the `FnMut` row |
| type and lifetime parameters | substitution | none |
| `export data N` | the elaborator's visibility | none |

**Mutual recursion.** The declarations a recursive declaration mentions, instantiated, form a
graph; its strongly connected component is the group. When one member lies on every cycle of
the group, the group elaborates to one `μ` rooted at that member (Bekić's rule with that member
outermost), and every other member is the root substituted into its structure. Example
(`lowered/bf.bc`):

    data Op = Add(i32) | Move(i32) | Put | Get | Loop(body: box List[Op])
    data List[T] = Nil | Cons(head: T, tail: box List[T])

`List[Op]` is on every cycle (`List[Op] → Op → List[Op]`, and `List[Op] → List[Op]`), so

    List[Op] = μX. 1 + (Op[X] ⊗ Ref X)        Op[X] = i32 ⊕ (i32 ⊕ (1 ⊕ (1 ⊕ Ref X)))
    Op       = Op[List[Op]]

This is one `μ` in `FShape`, with a fold and a destructor. The iso is consistent because
lowering is by name: `unroll ⟦List[Op]⟧ = 1 ⊕ (⟦Op⟧ ⊗ Ref ⟦List[Op]⟧)`. A generic function on
`List[T]`, instantiated at `T = Op`, is elaborated at the named type and so works on it.

When no single member lies on every cycle, the group needs a `μ` inside a `μ` (Json's
`List[Json]` and `List[Member]` are two disjoint self-loops), or recursion under an array
(`Vec[Json]`). Both are outside `FShape` (§4.5).

**Every cycle must cross a `box` or a block.** `Loop(body: List[Op])` with `List`'s head inline
would make `Op` infinitely wide: the cycle `List[Op] → Op → List[Op]` passes through no pointer.
The check is per cycle, at the declaration, and names the cycle.

### 4.4 Capabilities, sizes and effects

- **Capabilities** need no parameter kind. A record may hold a borrow of one (`data Parser<'s> =
  { src: mut 's input, pos: i32 }`). A record that owns one (`ref output`) has no destructor, as
  the capability has none (SPEC §12, class 3).
- **Sizes** (`[T; N]`, const generics) are #72's size sort, and deferred.
- **Effects on stored functions** are effect-polymorphism R6 (ports, #161): a field of function
  type keeps the row its type says. Codata observations carry rows (§6.2).

### 4.5 Kernel changes

None for declarations. One existing entry is needed by some declarations:

- **Recursion under an array or a nested `μ` in `FShape`** (SPEC §6). `FShape` has a closed
  leaf, `Ref X`, `X`, `⊗` and `⊕`. `data Json = … | Arr(Vec[Json])` puts `X` under an array; a
  mutually recursive group with two disjoint cycles needs a `μ` under a `μ`. Either way the type
  is well-formed (positivity is only `NoMut`) but has no fold and no structural destructor
  (SPEC §12: "`μ` outside `FShape`"). The entry is `arr` in `FShape`, an array of recursive
  positions whose fold receives the array of the children's results, terminating by witness size
  as `Ref X` does; and the nested `μ` case, by the same argument with the inner `μ`'s fold as the
  map. It extends the three fold rules and `dtor_wf`.

Until it lands, `Json` uses the sibling encoding (`lowered/json.bc`), and the elaborator rejects a
nested occurrence by name.

## 5. Labels, fields and places

### 5.1 Labels

Labels are erased. The elaborator keeps every declaration's labels, constructor names,
attributes and parameters in its declaration table, and specialises generic and polytypic code
at named types before lowering erases the names (§9.1). So no labelled `VTy` former is needed: a
labelled `⊗` would be about a hundred match arms across `Core/` and carry nothing the checker
uses. Field names are scoped to their declaration, so two records may share one (Idris: "Each
record is defined in its own namespace, which means that field names can be reused in multiple
records").

### 5.2 Fields of values and of views

| form | elaborates to |
|---|---|
| record literal `N { f₁: e₁, … }` | `into_N (e₁, (…))`, fields in declaration order |
| `v.f`, `v` owned | destructure `out_N v`; the other fields are dropped (SPEC §12) |
| `v.f`, `v` a view `&'a N` | the component: a view of a record is the tuple of its fields' views ("`Imm̲` acts fieldwise", SPEC §5) |
| `N { ..r, f: e }` | destructure `r`, rebuild with `e`; the old `f` is dropped |
| `let N { f, g } = v` | destructure, field punning |

Projecting one field of a borrowed record drops the other fields' views, which must be `Affine`.
`Affine` has no `μ` case, so `v.f` past an unboxed `μ`-typed field of a view is not available,
and destructuring is (SPEC §5).

### 5.3 Places

- **A `let mut` record is its fields as places.** `let mut m: Machine` elaborates to one `let
  mut` per field, `m.pc = e` assigns that variable, and `&mut m.mem` lends it as any `let mut` is
  lent. A whole use (`f(m)`) rebuilds the tuple. This is elaboration only (scalar replacement),
  and it is what `lowered/intcode.bc` writes by hand: the VM is one `while` over three `let mut`
  variables, where today's corpus threads a state tuple through `count_fold` (inventory §2.7).
- **A boxed record is a block** (decision 6): `box r` makes one cell per field, and each field
  is a place. `borrow mut b.f` lends the leaf cell; `borrow mut (b.f, b.g)` is a family borrow
  (SPEC §5, `withborS`, whose leaves must be lifetime-free).
- **A boxed variant is one cell**, `Ref (A ⊕ B)`, whose payload fields are not places: `Ref`
  does not distribute over `⊕` (SPEC §5 *Open*, #19). A recursive constructor that is a block
  sidesteps this, since its tag is outside the block.

### 5.4 Constructor patterns

`match v { Cᵢ(x…) -> … }` is `case (out_N v)`, one arm per constructor, nested `case`s along the
`⊕` spine. A pattern is one constructor over variables, `_`, `()`, tuples and `box p` (typed
elaboration §5.3). On a block constructor, the pattern binds the cells, and taking a field's
value is `free` of its cell (`lowered/tree.bc`). On a view, it binds the fields' views. Arms may
come in any order; the lowering orders them by the `⊕` spine, as the core requires (`inl` first).

## 6. Data and codata

### 6.1 `data`: constructors

    data Phase = Pending | Running | Failed                                -- a C-like enum
    data Spec = { size: i32, container_port: i32, version: Option[i32] }  -- a record
    data Param = Pos(i32) | Imm(i32) | Rel(i32)                            -- a variant
    data NodeId = NodeId(i32)                                              -- a newtype
    data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)             -- recursive, block nodes

A declared value is built in place, with no allocation, unless the program writes `box` (§7.1).

### 6.2 `codata`: observations

effect-polymorphism §5.9: "A function `A ⊸ F_Σ B` is codata with one observation (apply) whose
result is effectful. A codata type `C₁ & … & C_k`, or `νX. C` with `C` a `&`-tree of
observations, has an effectful leaf at each observation that has one." A `codata` declaration is
that, named:

    codata Countdown { next: F (i32 * Self + 1)  remaining: F (i32 * Self)  close: F 1 }
    codata Reader[A, E] { next: F (A * Self + 1) with Log   close: F 1 with Fail[E] }

- **With `Self`**, it is `νX. C`, observations a `&` tree, `Self` as `U X`. It must satisfy SPEC
  §7's `NuOk`, checked at the declaration: at least two observations, each an `F A` with `Self`
  only under `⊗`/`⊕`. A destructor exists when the last observation is a `close : F R` with `R` in
  `HasDtor`.
- **Without `Self`**, it is a `&` of computations: an object whose one method is chosen once.
- **Rows per observation.** Each observation has its own row; the kernel admits effectful leaves
  in a `ν` (`EffLeaf`, `NuLeaf`). Passing such an object second class is effect-polymorphism R5;
  storing it is R6 and SPEC §15 *Open* ("stored generators over a row").
- **Observation** is `(nu_out (force c)).path`, bound with `<-`: a surviving force.
- **Construction** is SPEC §7's `unfold`, with one arm per observation over an explicit state;
  each arm returns the next state where the type says `Self`. The eta-expansion the corpus writes
  by hand (`thunkv nu_in ⟨(nu_out (force f s)).1, …⟩`) is generated from the declaration.

### 6.3 Generators, pull types and `for`

- **A generator is a function that performs `Yield`** (SPEC §15), not a declaration. It is push:
  a `for` over its call is a handler site.
- **The pull types become library declarations**: `Pull[A, B, R]` (a stored generator, today's
  `pull`), `Iter[A, R, R2]` and `Loop[A, B]` (`proposed/codata.bc`). The frontend's `delay`,
  `stream`, `iter`, `loop` and `pull` nodes are deleted, with their parser, printer and checker
  cases (decision 20: a generalization lands with the deletion of its instances). The elaborator
  finds the library declarations by structure, as it finds `Yield` and `Exhausted`.
- **`for` over a codata value** is a `for` over a generator that observes it (`fn each(c:
  Countdown) -> 1 with Yield[i32]`). No `iterate` interface is needed, and nothing makes a type
  iterable by accident.
- **Flat pipeline types.** A pipeline's type is the generator's row, `with Yield[T]`, or a stored
  generator's `Pull[A, B, R]`, whatever adapters it went through. The state of a `ν` is hidden by
  `unfold`, so it never appears in the type: there is no `Map<Filter<…>>`. That holds for every
  `codata` with `Self`. A `codata … on S` (§6.4) does show its state type, and is not a pipeline
  stage.

### 6.4 Objects with methods that take arguments

An observation of a `ν` takes no argument (`NuOk`: "an observation tree is an `F A` or a `&` of two
observation trees"). An object with state and methods such as `push(x)` is instead SPEC §2's
`FnMut` row with several methods: a state `S` and a persistent record of methods, each taking the
state first and handing it back,

    codata Sink[A] on S { push: A -> F 1   flush: F 1 }
      ≜  S ⊗ !U((S ⊗ A ⊸ F(S ⊗ 1)) & (S ⊸ F(S ⊗ 1)))

called through a `mut` borrow of the state. This is §21's environment-passing record, and
effect-polymorphism §5.9's "one environment shared by all the observations, plus one code per
observation". No kernel change. `FnMut` itself is an open experiment (#236); this form does not
depend on its outcome. The alternative, a `ν` whose observations take arguments, is SPEC §7
*Open* ("other positions of `X`") and would be a kernel entry; no driving program needs it, so
it is deferred.

## 7. Layout

### 7.1 Unboxed by default; recursion under `box` or a block

- A non-recursive declaration is a value: a record is its fields' words, a variant a tag and the
  widest payload. Nothing allocates.
- A recursive occurrence must be under `box` (a field pointer, `ref X`) or in a block constructor
  (`box Node(…)`, a cell per field). Both forms are kept:

  | form | structure | what is a place |
  |---|---|---|
  | `Node(left: Tree, val: i32, right: Tree)` allocated by `box Node(…)` | `μX. 1 ⊕ (Ref X ⊗ (Ref i32 ⊗ Ref X))` | every field (a block) |
  | `Cat(box Re, box Re)` | `μX. … ⊕ (Ref X ⊗ Ref X) …` | the pointed-to values |

  The first is the user's decision for trees (typed elaboration §5.3). The second is Rust's
  `Box`. An occurrence under neither is an error at the declaration, which keeps the backend's
  silent boxing out of declared types.

### 7.2 Tags

A right-nested `⊕` nests tag words today: `|A ⊕ B| = 1 + max |A| |B|`. A ten-constructor `Instr`
is 17 words where one tag word would give 7. **Recommendation:** one n-ary tag word per maximal
`⊕` nest, summands numbered left to right; a `case` on an inner `⊕` is a range test. A
layout-type change in `Clos/Types.lean` and `Flat/Lower.lean`, invisible to the model, the
checker and the kernel. It applies to every `⊕`, declared or not.

### 7.3 Niches

| type | niche | why it is sound |
|---|---|---|
| `1 ⊕ Ref A` (`Option[box T]`) | the null word for `inl` | no cell is at address 0 |
| `1 ⊕ [L]` (`Option[array T]`) | a length word `≥ 2³¹` | the length bound, `c < 2³¹` (SPEC §9) |
| a tag beside a 32-bit or 8-bit payload | spare bits of the payload's word | the word is 64 bits |

Each is a backend choice, checked against the interpreter on the corpus, not proved. Rust
guarantees only the first ("null pointer optimization"); the rest of its default layout is
unspecified. Niches are optimisations, and only `layout C` fixes a layout.

### 7.4 C layout

    data ZStream layout C = { next_in: cptr u8, avail_in: c_uint, …, reserved: c_ulong }

- A **keyword clause**, not an attribute: it changes what the backend does, and a misspelling is
  a parse error.
- **Fixes** declaration order and C alignment (Rust's `repr(C)` algorithm); **checks** that every
  field is C-representable (C integer aliases, another `layout C` declaration, the platform
  design's raw and function pointers, which only `layout C` declarations and extern contracts
  may hold, decision 27).
- **Lives in a block**: `box ZStream::zeroed()` is one contiguous allocation, one address for
  life (zlib's `inflateStateCheck` compares `state->strm` against the stream).
- **Needs** #77's block allocation primitive, SPEC §5's block provenance, and byte-granular block
  layout in the backend. Recommended: lay out every block in declaration order with natural
  alignment, so that `layout C` is a check plus a promise that the order will not be optimised
  later, and no annotation reaches the core (Q7). Offsets for `ZStream` are in
  `proposed/zstream.bc`: 112 bytes on LP64, 56 on wasm32 (computed, not measured).
- **Control over representation** beyond this: `layout C(u8)` for a C-like enum of a fixed width.
  `packed`, explicit field offsets and C unions with payloads are deferred until an FFI target
  needs them.

### 7.5 Bytes in memory

Outside arrays of `u8`, memory is word-granular: an array of `u8 * u8` pairs takes two words per
element. Arrays of small records (an Intcode memory, pixels) need byte-granular slots. A backend
follow-up against the zero-cost target, with no language change.

## 8. Metadata without comments

### 8.1 Two mechanisms, by who reads them

| | keyword clause | typed attribute |
|---|---|---|
| read by | the elaborator or the backend | a library's `poly` |
| examples | `derives eq, encode`; `drop f`; `linear`; `layout C` | `@json(rename = "containerPort")`, `@schema(minimum = 1)`, `@default(Pending)`, `@kube(group = …)` |
| declared by | the grammar | an `attr` declaration in the library that reads it |
| a misspelling | a parse error | an unknown-name error at the use |
| a wrong value | a type error in the clause | a type error against the `attr`'s parameter type |

A comment is never read. There are no marker comments, build tags or `generate` lines.

### 8.2 Attribute declarations

    attr json on field = { rename: Option[lit] = None, skip: bool = false, flatten: bool = false }
    attr json on data  = { rename_all: Case = Keep, tagging: Tagging = External, with: Option[poly encode at T] = None }
    attr default on field of T = T
    attr json_with on field of T = poly encode at T
    attr schema on field, data = { minimum: Option[i64] = None, maximum: Option[i64] = None, … }

- An `attr` names its targets (`data`, `con`, `field`, `codata`, `obs`) and a record of typed
  parameters with defaults. A use is elaborated as a record literal against it.
- A parameter may be typed by **the target's type** (`@default(3)` is checked at the field's
  type) or be **a function at the target's type** (`@json_with(f)` is checked to have `encode`'s
  signature there). Neither C# nor Java can express the first.
- **Values are constants**: literals, constructors applied to constants, `lit` text, names of
  functions. A `poly` branches on them at elaboration, so `if json(f).skip { … }` leaves no
  branch in the output.
- **An attribute no `poly` reads is an error**, unless its `attr` is `inert`. Rust accepts unused
  tool attributes silently ("When a tool is not in use, the tool's attributes are accepted
  without a warning").

Revision 1's comparison with Go struct tags and directives, Kubebuilder markers, Rust, OCaml, C#,
Java, Kotlin and Zig stands, and is in §15. Kubebuilder's `// +kubebuilder:validation:Minimum=0`
is the anti-pattern; here it is `@schema(minimum = 0)`, checked and enforced on decode.

## 9. Derive

### 9.1 The mechanism: `poly`

A **polytypic function** is written once, by cases on the structure view of a type (§9.2):

    poly encode[T]<'a>(o: Out, v: &'a T) -> Out {
      i32        -> put_dec(o, v)
      Option[A]  -> …                                    -- a case may name a declared type
      data(d) A  -> encode[A](o, v)
      record F   -> let o = write(o, "{"); let (o, _) = members[F](o, v, true); write(o, "}")
      variant C  -> if nullary[C] { write_quoted(o, con_name[C](v)) } else { tagged[C](o, v) }
      A + B      -> match v { inl a -> encode[A](o, a) | inr b -> encode[B](o, b) }
    }

(`proposed/derive.bc` has `members`, `present`, `schema`, `eq` and the attribute declarations.)

- **Specialisation is decision 45's instantiation, extended by one step.** `encode[N]` is the
  instance at `N`, made on first use and shared. Its body is the first case whose pattern matches
  `N` in the structure view. The calls in it are at smaller types. The result is ordinary core,
  checked by the unchanged checker; the elaborator stays outside the trusted base (decision 26).
- **Termination of elaboration.** Each case calls at proper components, except `data(d) A`,
  which unfolds a name. Unfolding a name at which the same `poly` is being specialised is a
  recursive occurrence, handled by §9.3. So specialisation is structural recursion on the finite
  set of (poly, type) pairs, memoised.
- **Metadata are constants**, and a `match` on one resolves at elaboration.
- **Cost.** An instance is the code a programmer would write: `lowered/crd.bc` is
  `encode[Memcached]`. The iso is the identity, so nothing converts.

**A `poly` is the restricted first case of compile-time evaluation.** Its compile-time input is a
type and its metadata; its compile-time control is case analysis on the structure view; its
output is core code, which the certifying checker checks. It performs no I/O and terminates by
structural recursion on types. A general comptime (Zig's) would let the same code compute with
the type as a value (`TypeInfo` as data), loop, and build tables. The recommended path (decision
3 of §1): build `poly` so that its structure view is a declared data type, `TypeInfo`, which a
later comptime would take as input, and defer the general evaluator. The restrictions a later
comptime keeps: effect-restricted (no I/O; total or fuelled), and its output checked.

**`derives` is explicit** (decision 4 of §1). `data N derives eq, encode` exports the structural
instances with `N`. For an abstract `N`, it is the only way outside code gets them, since the
cases need the iso. Explicit opt-in also keeps a type's wire format from changing because another
package added a field.

**What derives:**

| derive | over | result | note |
|---|---|---|---|
| `eq`, `cmp` | two views | `bool`, `Ordering` | by tag, then fields in order |
| `hash` | a view | `u64` | structural; the hasher is §9.5's question |
| `debug` | a view | text | constructor and field names; `Debug`-like |
| `display` | — | — | not derived: user-facing text is a function the program writes |
| `clone` | a view | an owned copy | for types not persistent; decision 39's `clone` covers persistent `μ`s |
| `encode`, `decode` | a view; text | text; a value or `Fail` | JSON first; driven by `@json` |
| `schema` | — | text | a CRD's OpenAPI schema; inlined, no `$ref` |
| `default` | — | a value | `@default` per field |

### 9.2 The structure view

| case | matches | binds |
|---|---|---|
| `data(d) A` | a declared type `N` | `d : DataMeta` (name, package), and `A` its structure |
| `newtype(d) A` | one constructor of one field | as `data`; encoded as the field alone |
| `record F` | a declaration's product | `F`, a `*`-spine of `field(f) A` |
| `field(f) A` | one field | `f : FieldMeta` (label, index, attributes) |
| `variant C` | a declaration's sum | `C`, a `+`-spine of `con(c) F` |
| `con(c) F` | one constructor | `c : ConMeta` (name, index, arity) and its fields |
| `A * B`, `A + B` | spines, anonymous tuples and sums | |
| `N[A…]` | a named declared type, by name | its arguments (the `poly`'s author owns these cases) |
| `i32`, `u8`, `1`, `lit`, `slice 'a A`, `array A`, `box A`, … | leaves | |
| `rec` | a recursive occurrence (§9.3) | the carrier value |
| `_` | anything else | |

This is generics-sop's sum-of-products view over the core's own binary formers, with metadata
kept apart from structure ("A major plus of the SOP view is that it allows to separate
function-specific metadata from the main structural representation", de Vries and Löh, WGP 2014).

### 9.3 Recursive types

Since SPEC §20–§21, a function over a recursive type has three lowerings. The lowerings in §10
measured where each works:

| lowering | total | over a view | writes to a capability | example |
|---|---|---|---|---|
| a fold (`fold_imm`, `fold_own`, `fold_reuse`) | yes | yes (`fold_imm`) | no: the carrier must outlive every lifetime, and a thunk does not | `lowered/json.bc`'s encoder |
| a recursion under `bounded` (SPEC §20) | `Exhausted` in its row | no: a group's members take no lifetime parameters; the value is taken and handed back | no: `stdout` has no destructor and cannot be live across a computation that may abort | `lowered/tree.bc`, `regex.bc`, `json.bc`'s parser |
| an explicit stack in a loop | div, or fuelled | needs lifetime-indexed iteration (SPEC §7 *Open*) | yes | not written |

What this means for derive:

- **Consumers into data over a view** (`hash`, `debug` and `encode` to a string, `size`, `clone`):
  `fold_imm` with a data carrier. Total, and no `Exhausted`. The carrier costs allocation when it
  is text as a list (revision 1 measured 172 allocations for a 35-byte document); a `buf`
  carrier threaded through the algebra is the next thing to try, and is not measured.
- **Two values at once** (`eq`, `cmp`): a fold walks one value. They are a recursion over two
  owned values handed back, which puts `Exhausted` in `eq`'s row, or a fold of each into a
  serialization that is then compared. Neither is good. With lifetime parameters on a group's
  members, `eq` would recurse over two views. §20 does not say why members take none. A member's
  type `∀'a. E ⊗ P ⊸ F_Σ(E ⊗ T)` is a computation type, and `bounded_fix[1, R]` is typed at every
  computation type `R`, so this looks like elaboration only; I have not established it (§14).
- **Streaming `encode` to a capability over a borrowed tree** needs either a writer carrier (a
  `U` does not outlive) or a recursion holding the capability (it has no destructor). Both are
  blocked, by different rules. Text into a `string` works today (`lowered/tree.bc` builds its
  output that way).
- **`decode` of a recursive type** is recursive descent (§10.1), a recursion under `bounded`.

**Recommendation.** Folds for derived consumers over views; recursion under `bounded` for
decoders and for programs; and the lifetime-parameter question for recursive groups taken up
as its own item, since it decides `eq` and streaming encoders (Q9).

### 9.4 JSON and CRD needs

- **Optional fields.** `Option[T]` is `data Option[T] = None | Some(T)`. `encode` omits a `None`
  field (the `present` case at `Option`); `decode` gives `None` for a missing key; `schema` leaves
  it out of `required`. Kubernetes objects are written with absent fields, so absent is the
  default (Q8).
- **Defaults.** `@default(v)` is checked at the field's type; `decode` uses it for a missing key,
  `schema` writes `"default": v`.
- **Enums.** A C-like enum encodes as its constructor's name and publishes `"enum": [names]`. A
  payload enum is externally tagged by default; `@json(tagging = Internal(tag = "type"))`,
  `Adjacent(…)` or `Untagged` are constructors of a declared type, so `tagging = "internal"` is a
  type error.
- **Validation.** `@schema(minimum = 1, maximum = 3)`, `min_length`, `max_length`, `pattern`,
  `format`, `description` are typed values, published in the schema and checked by the derived
  `decode` (numeric and length ones; `pattern` is published only until a regex engine exists,
  #225). On a newtype exported abstract with a checked constructor, the constraint becomes an
  invariant of the type. CEL rules (`x-kubernetes-validations`) are text in another language,
  published and not checked here.
- **CRD specifics.** A CRD schema cannot use `$ref` ("These fields cannot be set: … $ref"), so
  `schema` inlines every named type and has no answer at a recursive one: its `rec` case is an
  error asking for the field's schema to be given (`@schema(any)`, the
  preserve-unknown-fields schema). `@kube(group, version, kind, plural, namespaced)` on the root
  is read by `derives resource`.

### 9.5 Where derived results are found: traits, or handlers with ambient defaults

This is open, and not decided here. A derived `encode` at a concrete type needs no lookup: the
elaborator specialises it. The question is generic code that needs `hash`, `eq` or `cmp` *at a
type parameter*, and custom semantics (a case-insensitive key) that differ from the structural
default.

**The candidates** (`proposed/providers.bc` writes each):

- **T, traits.** `trait Hash[T]`, one instance per type, coherent across the program; the
  structural instance by `derives`; custom semantics by a newtype with its own instance. A
  newtype is free here (§3), so the usual cost of the newtype route is only the wrapping. Needs:
  interfaces, impls, a coherence rule and an orphan rule.
- **D, providers attached to the declaration.** The structural `poly` by default; a type's own
  semantics is a typed attribute of its declaration (`data CiText @eq(with = eq_ignore_case) =
  …`), which only the declaring package can write, so there is one per type by construction and
  no orphan rule. A generic body calls `hash[K]` with no bound, and the call is resolved at each
  instance (decision 45). It is T with the narrowest orphan rule and no interface declarations,
  and needs nothing beyond `poly` and `attr`.
- **H, handlers with ambient defaults** (decision 54's `Num[T]` pattern). `Hash[T]`, `Eq[T]`,
  `Ord[T]` are answering effects; a structural handler is ambient for every transparent type; a
  custom one is installed lexically. Generic code performs them and the effects tunnel (decision
  57). Answering handlers erase to direct calls, so the cost equals T's. More flexible than T for
  scoped choices: `sum` against `product`, or a case-insensitive `eq` for one block, need no
  newtype. Its coherence across values is handled in one of three ways:
  - **H1, the provider's static name in the type.** A structure that keeps an invariant
    declares the effects it captures (`data HashSet[K] provides Hash[K], Eq[K]`), and a value's
    type carries the names of the handlers that served them at construction. The ambient default
    has one name per type; a parameterless named handler has its declaration's name. Inside the
    structure's functions the recorded provider serves the effect, not the handler in scope.
  - **H2, data carries its provider** (#211's current constraint): `!` functions stored in the
    structure, captured at construction. The type says nothing.
  - **H3, a run-time check**: H2 plus a comparison of the stored providers where two values meet.

**The deciding test** (posted on #141): `union` of two hash sets and `merge` of two sorted maps.

| | `union(a, b)` | `merge(a, b)`, linear | custom semantics | scoped choice (`sum` vs `product`) |
|---|---|---|---|---|
| T | clean: one `K`, one instance | clean | a newtype | a newtype |
| D | clean | clean | a newtype with an attribute | a newtype |
| H1 | clean when the names agree; rejected at elaboration when they differ | clean when the names agree | `with ci_hash { … }` at construction | `with` around the fold |
| H2 | clean: `b`'s keys re-hashed with `a`'s provider, `a`'s semantics | needs `a` and `b` in one order: H3's check, or `n log n` insertion | `with` at construction | `with` |
| H3 | as H2 | a check of code identity, then linear or `n log n` | `with` at construction | `with` |

What the test shows:

- **`union` of hash sets is not where coherence bites.** A union re-hashes `b`'s keys into `a`'s
  table whatever the providers are, so `a`'s semantics is well defined under every candidate.
  Coherence only buys a table-level merge, which nothing needs.
- **`merge` of sorted maps is.** The linear merge needs one order. T and D have it by
  construction; H1 by the type; H2 has it only by a run-time check or by giving up linearity.
- **H1 is type-directed resolution of named providers.** At the structures that need coherence,
  the provider comes from the value's type, not from the handler in scope. That is what T and D
  do, with names that are allowed to differ (Scala's named givens, OCaml's applicative functors
  `Set.Make(Ord)` whose type is equal at equal module paths; recalled, not re-read). The
  difference from T is the default (ambient, not global) and that several providers per type
  coexist, told apart by name.
- **Parameterised providers** (`seeded(s)`) have no static identity under H1. The options are
  the `with` site's name (generative: sets from two sites never union), a run-time comparison of
  the parameters (H3), or no parameterised providers for invariant-bearing structures.
- **Cost.** T, D and H1 resolve at elaboration and call directly. H2 calls a stored `!` function,
  which is a dispatched call unless the construction site is known (effect-polymorphism's
  specialisation per callback). `lowered/hashmap.bc` is the code T, D and H1 all lower to at
  `K = i32`: `union` is plain code, nothing is stored or checked.
- **Abstract types** need an explicit export of their providers under all of them: an ambient
  structural `eq` on a hash map would compare slot arrays.
- **The second test case**, monoid comprehensions (`Collect[C]`, a named handler or a
  type-directed collector), has the same shape as `sum` against `product`: it needs no
  coherence, so H handles it with no newtype and T needs one.

**Constraint under every candidate**: anything trait-like lives at a pipeline's ends
(collectors, equality and hashing, sources). A pipeline's type stays flat (§6.3).

## 10. Driving programs

Each has a proposed form (`proposed/`) and a hand-lowering (`lowered/`) that is what the
elaboration would produce: the types as structural aliases, constructors and patterns as
`roll`/`inj`/`case`, derived functions specialised. Every lowering is accepted by `bcc check` at
`620c82c`, except `map-generic.bc`, which is kept as the rejection of §4.1. The outputs below are
`bcc interp`'s (the source interpreter); this round compiled nothing, so allocation and dispatch
counts are not re-measured (revision 1's are in the PR description).

| program | proposed | lowered | output |
|---|---|---|---|
| JSON value, parser and encoder | `json.bc` | `json.bc` | `{"a":[1,true,"hi"],"b":null,"c":{}}`, `(i32[0], i32[4])` |
| CRD spec and status | `crd.bc`, `derive.bc` | `crd.bc` | the encoded object twice, `i32[1]` (the second fails validation) |
| binary search tree | `tree.bc` | `tree.bc` | `1 2 3 4 5 6 7`, `7 6 5 4 3 2 1`, `i32[3]` |
| graph with node ids | `graph.bc` | `graph.bc` | out-degrees `2 1 1 0`, `i32[4]` |
| hash map, `union` | `hashmap.bc`, `providers.bc` | `hashmap.bc` | `(i32[5], (i32[30], i32[0]))` |
| Intcode VM | `intcode.bc` | `intcode.bc` | `Mul(Pos(7), Imm(3), Pos(7))`, `Output(Pos(7))`, `99`, `Halt`, `i32[99]` |
| regex AST and parser | `regex.bc` | `regex.bc` | `Cat(Lit(a), Cat(Star(Alt(Lit(b), Lit(c))), Cat(Any, Lit(d))))`, `i32[2]` |
| Brainfuck, flat and tree | `bf.bc` | `bf.bc` | `AB`, `(i32[3], i32[2])` |
| record of views; codata; handle | `views.bc`, `codata.bc`, `handle.bc`, `zstream.bc` | `views.bc`, `codata.bc`, `handle.bc` | `8080`; `(3, (2, 1))`; `i32[7]` |

All end with `live 0`.

### 10.1 JSON: the value type and a parser

- **Declaration.** `Null | Bool(bool) | Num(i32) | Str(string) | Arr(Vec[Json]) |
  Obj(Vec[Member])`, `Member = { key: string, value: Json }`. The parser, encoder and schema are
  the json library's own functions: `Json` is the data model, not a derived type.
- **Elaboration.** `Vec[Json]` puts the recursion under an array, outside `FShape` (§4.5). The
  lowering uses the sibling encoding, one `μ` in `FShape`:
  `J = μX. (1 ⊕ Txt) ⊗ (Kind[X] ⊗ (1 ⊕ Ref X))`, a node holding its key, its kind and its next
  sibling, `Arr` and `Obj` pointing at a first child.
- **The parser** is recursive descent over the input (§9.3's second row): `value`, `elem_list`
  and `member_list` are one recursive group, with `Fail[i32]` for malformed input and
  `Exhausted` for depth. It reads like `corpus/rec-parser.bc`. Two things do not read naturally:
  - the input is an owned byte list passed along, not a borrowed cursor, because members take no
    lifetime parameters;
  - a wide array is parsed by tail recursion, one level of budget per element, because a `loop`
    inside a recursive member is rejected (SPEC §21 *Open*). More than 10 000 elements raise
    `Exhausted`. The proposed parser loops (`proposed/json.bc`), and needs that entry (decision 7
    of §1).
- **The encoder** is `encode[Json]` at a view: `fold_imm` into text, then written.
- **Layout with the `FShape` entry**: a `Json` is a tag and the widest payload (`Str`, a `buf`,
  three words); an array's elements one allocation of fixed-width slots.

### 10.2 A Kubernetes CRD, with serde-like derive

- **Declarations** (`proposed/crd.bc`): `Phase` (C-like), `MemcachedSpec` (`size` with
  `@schema(minimum = 1, maximum = 3)`, `container_port` renamed, `version: Option[i32]`),
  `MemcachedStatus` (`@default(Pending)`, an optional renamed field), and the root with
  `@kube(…)`. Every piece of metadata is typed syntax.
- **Elaboration.** `Phase = 1 ⊕ (1 ⊕ 1)`, `Spec = i32 ⊗ (i32 ⊗ (1 ⊕ i32))`, `Status = Phase ⊗ (1
  ⊕ i32)`, `Memcached = Spec ⊗ (1 ⊕ Status)`. No `μ`, nothing boxed: ten words on the stack.
- **Derived.** `encode[Memcached]` writes
  `{"spec":{"size":2,"containerPort":11211},"status":{"phase":"Running","readyReplicas":2}}`,
  keys as literal views; `validate[Spec]` rejects `size = 7`; `schema` is in the proposed file's
  comment.

### 10.3 A binary tree and a graph (LeetCode)

- **Tree** (`tree.bc`): `data Tree = Leaf | Node(left: Tree, val: i32, right: Tree)`, nodes
  allocated as blocks by `box Node(…)`; `μX. 1 ⊕ (Ref X ⊗ (Ref i32 ⊗ Ref X))` with
  `shape Node`. `insert`, `depth` (LeetCode 104), `invert` (226) and an in-order walk are plain
  recursion. A function that reads the tree takes it and hands it back, and the walk appends to a
  string: it cannot write to `stdout` inside the recursion (§9.3). The proposed form borrows the
  tree and yields from a recursive generator; that needs lifetime parameters on a group's members
  (Q9).
- **Graph** (`graph.bc`): `NodeId(i32)` and `EdgeId(i32)` newtypes, `Edge = { from: NodeId, to:
  NodeId }`. `NodeId` is `i32` in the core; the names differ only at elaboration, which is the
  point of §3. An `array Edge` is one allocation of two-word slots.

### 10.4 A hash map's types

- **Declarations** (`proposed/hashmap.bc`): `Slot[K, V] = Empty | Full(key: K, val: V)` and
  `HashMap[K, V] = { slots: array Slot[K, V], len: i32 }`, exported abstract.
- **Elaboration** at `[i32, i32]`: `Slot = 1 ⊕ (i32 ⊗ i32)`, unboxed, so the table is one
  allocation of fixed-width slots; `HashMap = [Slot] ⊗ i32`.
- **Code.** Probing is a total `for` over a view of the slots (at most `cap` probes, #211's
  "operations are total"); `insert` lends the slots for one write. `union` is plain code (§9.5).
- **What the types need that is not built**: generic declarations (D2), and the answer to §9.5.

### 10.5 An Intcode-style VM

- **Declarations**: `Param = Pos(i32) | Imm(i32) | Rel(i32)`, a ten-constructor `Instr` (the
  lowering keeps five), and `Machine = { mem, pc, base, input, output }`.
- **Elaboration**: nested `⊕` of nested `⊗`, no `μ`, no `box`. `Instr` is 17 words today, 7 with
  n-ary tags, 4 with a tag packed beside `i32` payloads (§7.2–§7.3; computed from
  `Backend/README.md`'s formulas, not measured).
- **The loop** is a `while` over a `let mut` machine, whose fields are places (§5.3). `debug[Instr]`
  prints each instruction; the program `1002,7,3,7,4,7,99,33` writes `99`.

### 10.6 A regex AST (#225) and a Brainfuck interpreter (#226)

- **Regex** (`regex.bc`): `Re = Eps | Lit(u8) | Any | Cat(box Re, box Re) | Alt(box Re, box Re) |
  Star(box Re)`, field boxes, one `μ`. The parser is recursive descent, its depth bounded by the
  pattern; a malformed pattern raises. `show` is `derives debug`. The Pike VM's flat `Inst`
  (`Char | AnyByte | Range | Split | Jmp | Save | Match`) is an unboxed variant in an array,
  the data-and-loops shape #225 asks for; it is in the proposed file and not lowered.
- **Brainfuck** (`bf.bc`): the flat interpreter is `Inst = Add(i32) | Move(i32) | Put | Get |
  Jz(i32) | Jnz(i32)` in a `buf`, compiled by one `for` over the program with a stack of open
  brackets, run by one `while` with a step counter. The tree form `Op = … | Loop(body: box
  List[Op])` shows §4.3's mutual recursion to one `μ`. A gas handler of `Exhausted` around the
  interpreter, as #226 asks, is a handler around a div computation, which is not provided (SPEC
  §21 *Open*); the step bound is in the loop's condition instead.

### 10.7 The rest

- **A record of views** (`views.bc`): `Field<'a>` is two `array_imm 'a u8`, four words, alive
  only inside the borrow it came from.
- **Codata** (`codata.bc`): `Countdown`'s three observations are the paths `.1.1`, `.1.2`, `.2`.
- **A handle with a destructor** (`handle.bc`): `data Session drop end_session`; the inserted
  `end_session` calls are written by hand. `drop f` makes the elaborator insert `f(x)` where an
  owned `N` goes unused, with SPEC §12's placement; `linear` makes an unused one an error. The
  elaborator compares the checker's inserted drops with its own and reports a disagreement as
  internal. SPEC §12's insertion policy gains one sentence; no rule changes.
- **A C struct** (`zstream.bc`): `layout C`, no lowering (no FFI, no byte layout).

### 10.8 Findings from the lowerings

1. A generic `fn` with a type parameter inside a `μ` is rejected at its call (`map-generic.bc`).
2. A recursion cannot write to `stdout`: a capability has no destructor and cannot be live
   across a computation that may abort with `Exhausted`. Recursive printers build a `string`.
3. A recursion cannot take a borrowed value: members take no lifetime parameters. Readers take
   the value and hand it back.
4. A wide container parsed by recursion spends one level of budget per element.
5. Mutual recursion through `List[Op]` is one `μ` in `FShape` today (`bf.bc`).
6. The body of a control `with` (`on_exhausted`, `to_result`) cannot assign an outer `let mut` or
   lend an outer place, so results are bound out of it; and its body's type often needs an
   ascription (`let r : … = with on_exhausted(…) { … }`).
7. `putb` takes a `u8` now; revision 1's lowerings were updated, and keys are literal views.

## 11. Kernel, spec and backend changes

| change | where | kind |
|---|---|---|
| declarations, parameters, the iso, constructors, patterns, fields, places | frontend (TIR `named`) | elaboration |
| mutual recursion to one `μ`; the cycle check | frontend | elaboration |
| a generic `fn`'s signature substituted before elaboration; generic recursion (instantiate, then group) | frontend | elaboration |
| `codata` declarations; `Pull`, `Iter`, `Loop` in `lib/`; delete five `CTy` nodes | frontend, `lib/` | elaboration, deletion |
| `poly`, `attr`, `derives`, keyword clauses | frontend | elaboration (decision 26) |
| §9.5's resolution, whichever is chosen | frontend | elaboration (T, D, H1); library (H2, H3) |
| `drop f`, `linear` | frontend; SPEC §12's insertion policy | policy |
| abstraction | frontend, #63 | elaboration |
| lifetime parameters on recursive groups' members | frontend, SPEC §20 | elaboration, not established (§9.3) |
| n-ary tags, niches, byte-granular blocks, `layout C` | backend | representation |
| contiguous blocks | SPEC §5, #77 | **kernel**: an allocating head step; already planned |
| `arr` and nested `μ` in `FShape` | SPEC §6 | **kernel**: the three fold rules and `dtor_wf` extended |
| `ν` observations that take arguments | SPEC §7 *Open* | **kernel**; deferred, not needed (§6.4) |

A SPEC entry for declarations would read like §15's baseline: "No `CDerives` rule, relation
clause, machine step or kernel type is added."

## 12. Staging

| # | stage | needs | unblocks |
|---|---|---|---|
| D1 | `data` without parameters: records, variants, constructors, patterns, fields, places, `box` nodes, the recursion check; TIR `named` | typed elaboration §5.3 | `pending/data-box-tree.bc`; tree, regex, Intcode, Brainfuck |
| D2 | type and lifetime parameters; regularity; mutual recursion to one `μ`; `type` with parameters; generic signatures substituted; generic recursion | D1 | `Option[T]`, `List[T]`, `Tok<'a>` |
| D3 | `codata` declarations, `unfold` blocks, observations by name, rows per observation; `Pull`/`Iter`/`Loop` as declarations, the `CTy` nodes deleted | D2 | named pull types; objects (§5.9 target 6) |
| D4 | `drop f`, `linear` | D1 | handles |
| D5 | `attr`, `poly`, `derives`; the structure view; `eq`, `debug`, `clone` | D2 | derived types |
| D6 | §9.5's resolution; `hash`; the hash map | D5, decision 2 of §1 | #211, `memo` |
| D7 | `encode`/`decode`/`schema` for JSON | D5, D6 | the operator's CRD |
| D8 | backend: n-ary tags, niches | none | Intcode's layout |
| D9 | `layout C`, byte-granular blocks | #77, block provenance | zlib |
| D10 | `export`, abstract types | #63 | `HashMap`, strings T2 |
| K | `FShape` over arrays and nested `μ` | its own entry | `Vec[Json]` |

Each stage lands with its SPEC entry, its lowering, and running corpus programs (decision 17).

## 13. Open questions

1. **Q1. Abstraction as a theorem?** Recommended: no, until a trusted boundary needs
   representation independence proved; then a sealing former, costed then.
2. **Q2. Spellings** of every form. Provisional; not a one-way door.
3. **Q3. Explicit `derives`.** Decision 4 of §1.
4. **Q4. Shortening records of borrows.** A derived `shorten`, plus shortening for families.
5. **Q5. Nested recursion.** Decision 5 of §1, and the `FShape` entry.
6. **Q6. Traits or handlers.** Decision 2 of §1 (§9.5).
7. **Q7. Where block layout is decided.** Recommended: declaration order with natural alignment
   for every block, so `layout C` is a check.
8. **Q8. `None` fields absent or `null`.** Recommended: absent, with `@json(null_if_none = true)`
   when a target needs `null`.
9. **Q9. Recursion over borrowed data.** Lifetime parameters on recursive groups' members would
   give `eq`/`cmp` over two views, recursive generators over a borrowed tree, and a parser over a
   borrowed cursor. Recommended as its own item, before D5's `eq`.
10. **Q10. A recursion that loops** (SPEC §21 *Open*), for parsers of wide containers. Decision 7
    of §1.
11. **Q11. Anonymous records** (an inline `spec: { replicas: i32 }`). Recommended: a declaration
    named after its position, so it has labels and derives with its parent.
12. **Q12. A general comptime.** Decision 3 of §1. Deferred until a program needs more than case
    analysis on a type.
13. **Q13. Text carriers for derived consumers.** A `buf` threaded through `fold_imm`'s algebra
    in place of a byte list; not measured.

## 14. What I have not established

- That `fold_imm`, `fold_own` and `fold_reuse` extend soundly to recursion under arrays or a
  nested `μ` (§4.5). The witness-size argument is the plan.
- Why SPEC §20's recursive groups take no lifetime parameters, and whether lifting it is
  elaboration only (§9.3).
- That the single-root rule of §4.3 covers every group that has a fold: it is argued, and
  checked on one program (`bf.bc`).
- That H1's provider names can be inferred without annotations at construction sites in
  ordinary programs. `providers.bc` writes them in comments.
- The counts of this round's lowerings. They were checked and interpreted, not compiled.
- The layout sizes of §7.2 and §10.5, and §7.4's C offsets: computed from the rules, not
  measured.
- OCaml's applicative functors and Scala's named givens are cited from memory, not re-read.
- What SPEC §12's insertion, as implemented, can report about its inserted drops (§10.7).

## 15. Prior art

Revision 1's quotations were read from the pages named, in September 2026.

- **Rust.** The Reference, *Type layout*: the default representation gives "no other guarantees
  of data layout"; `repr(C)` "is designed for dual purposes. One purpose is for creating types
  that are interoperable with the C Language"; `repr(transparent)` gives a struct "the same layout
  and ABI as the only non-size 0 non-alignment 1 field". *Attributes*: "an attribute is a
  general, free-form metadatum that is interpreted according to name, convention, language, and
  compiler version." Taken: `repr(C)`'s algorithm, the null-pointer niche, `transparent` as the
  newtype case. Not taken: attributes as token trees only their macro checks.
- **serde.** "a way of mapping every Rust data structure into one of 29 possible types". Taken:
  the three attribute targets, rename, skip, default and `with`, the four enum taggings. Here the
  data model is the core's structure view.
- **kube-rs and schemars.** "Server-side validation require mutation of your generated schema,
  and can in the basic cases be achieved through the use of schemars's validation attributes."
  Taken: one attribute read by both the codec and the schema.
- **Haskell.** Haskell 2010 §4.2.3, `newtype` (§3.1). GHC.Generics: the iso and metadata as
  typed data; not needed, `Rep` as a separate type. Type classes: global coherence, the property
  §9.5's `merge` relies on.
- **generics-sop** (de Vries and Löh, *True Sums of Products*, WGP 2014): the sum-of-products view
  with metadata apart.
- **Polytypic programming** (PolyP): "A polytypic function is a function that is defined by
  induction on the structure of user-defined datatypes". A `poly` is one.
- **OCaml.** Attributes are "“decorations” of the syntax tree which are mostly ignored by the
  type-checker but can be used by external tools"; ppx_deriving's `[@@deriving]`. Functors
  (`Set.Make`) give the provider-in-the-type of §9.5's H1.
- **Swift Codable** (SE-0166): synthesis "can always be overridden by a manual implementation".
- **Zig.** `extern struct` "has in-memory layout matching the C ABI for the target"; `@typeInfo`
  for reflection; comptime as the general form of §9.1's `poly`. Taken: layout as a keyword.
  Deferred: general comptime.
- **Lean 4.** "Instance deriving uses a table of deriving handlers that maps type class names to
  metaprograms." Not taken: derive as metaprograms; a `poly` is code by cases.
- **Idris 2.** Records with field names scoped to their declaration.
- **Go, Kubebuilder, C#, Java, Kotlin, F# type providers**: compared in revision 1's §7.3. Go
  struct tags are "made visible through a reflection interface … but are otherwise ignored";
  Kubebuilder's markers are "special "marker comments" in Go code", the anti-pattern here.
- **Koka and Effekt**: the handler side of §9.5 (decision 48's semantics), and decision 54's
  `Num[T]` pattern.
