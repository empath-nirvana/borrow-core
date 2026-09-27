# Core syntax — draft 1

Status: implemented. The parser (`Frontend/Parser.lean`) and checker (`Frontend/Check/`) accept this
syntax, and the corpus and the book's examples are written in it. Draft 1 resolved the three reviews
of draft 0 (see *Changes from draft 0* at the end).

## 1. Purpose and principles

A textual form of the core calculus (`SPEC.md` §3–§7), for writing the first corpus and for
the parser and checker.

- **One form, one rule.** Every term form is one `CDerives` constructor (`Core/Fundamental.lean`),
  one named constant of `CDerives`, or one named *derived rule* (a Lean theorem whose
  conclusion is a `CDerives` judgment). Each table row cites its rule.
- **The checker produces the erasure.** A parsed program is not an `Expr`. The checker
  elaborates it to a BoLo `Expr` together with a `CDerives Δ Γ e j` derivation of that `Expr`.
  The erasure depends on types: `force x` erases to `x ()` at `F A` and to `x` at every other
  computation type (`forceE`, `Core/Relation.lean:60`). Checker soundness is by construction,
  because Lean checks the derivation.
- **No sugar beyond names.** The additions are named variables, named lifetimes (both resolved
  to numbers), type and shape abbreviations, and top-level `def`s. Each is described below
  together with what it expands to.

<!-- ANCHOR: citations -->
**Citations.** `Fu:N` is `Core/Fundamental.lean` line N. The other files: `Ty` `Core/Types.lean`,
`Co` `Core/Compat.lean`, `Rl` `Core/Relation.lean`, `Fa` `Core/Family.lean`,
`Bl` `Core/Blocks.lean`, `BB` `Core/BlockBorrow.lean`, `FI` `Core/FoldImm.lean`,
`FO` `Core/FoldOwn.lean`, `FR` `Core/FoldReuse.lean`, `Nu` `Core/Nu.lean`,
`Rc` `Core/Records.lean`, `CL` `Core/CommonList.lean`,
`Fo` `Core/Folds.lean`, `S2` `Paper/S2_Statics/Definitions.lean`,
`Cx` `Support/Statics/Contexts.lean`.
<!-- ANCHOR_END: citations -->

## 2. Lexical

<!-- ANCHOR: lexical -->
- Term variables and `def` names: `[a-z_][A-Za-z0-9_']*`, excluding keywords.
- Type abbreviations, shape abbreviations and `μ`-bound type variables: `[A-Z][A-Za-z0-9_]*`.
  A `μ`-bound name shadows an abbreviation of the same name.
- Lifetime variables: `'[a-z][a-z0-9_]*`.
- Comments: `--` to end of line.
- Every Unicode symbol has an ASCII spelling:

  | Unicode | ASCII | | Unicode | ASCII |
  |---|---|---|---|---|
  | `⊗` | `*` | | `⊤` (lifetime and type) | `top` |
  | `⊕` | `+` | | `∀` | `forall` |
  | `⊸` | `-o` | | `⊏` | `<` |
  | `&` | `&` | | `⊓` / `⊔` | `/\` / `\/` |
  | `μ` | `mu` | | `λ` / `Λ` | `fun` / `Fun` |
  | `⊓Δ` | `dom` | | `Imm̲` | `view` |

- `->`, `<-`, `:>`, `-o`, `=>`, `/\`, `\/` are single tokens, so a bare `>` only closes `<M, N>`.
<!-- ANCHOR_END: lexical -->

## 3. Lifetimes

<!-- ANCHOR: lifetimes -->
    lifetime  @ ::= 'x | top | dom | @ /\ @ | @ \/ @ | (@)

`/\` binds tighter than `\/`, and both associate to the right. Lifetimes are Lean's
`Lifetime.Life` (`Paper/S1_Syntax/Definitions.lean:229`) and are compared syntactically:
`'a /\ ('b /\ top)` and `('a /\ 'b) /\ top` are different lifetimes.

**`dom`** stands for `Δ.meetOfDom` (`S2:453`) at the point where it is written: the right fold
`'xₙ /\ (… /\ ('x₁ /\ top))`, innermost binder first, with `top` for the empty context. Every
`withbor`/`withload` callback is bounded by exactly this lifetime, so it must be writable.
Writing it out by hand is also accepted.

**Numbering.** A lifetime binder is `Fun 'x`, `forall 'x`, `all 'x`, or a binder argument of a
constant or derived form (`withbor1['x, …]`). Each binder gets the `LifeVar` number
`Δ'.freshVar` (`S2:632`, one past the largest number in use), where Δ' is the lifetime context
at that point extended by the enclosing binders of the type being written. Names resolve
lexically, innermost first, and are then discarded. Two consequences:

- A type written at one point and a `Fun` or constant written at the same point agree on
  numbers. This is the common case, and it needs no α-conversion.
- Types are compared by number, with **no α-conversion**. Capture-avoiding instantiation
  (`CTy.applyLSub`'s renaming branch, `Ty:1179`) can produce a binder number that differs from
  the one an annotation written at that point would get. The checker then reports a
  mismatch. Section 12 lists the α-equivalence lemma this would need.
<!-- ANCHOR_END: lifetimes -->

## 4. Types

<!-- ANCHOR: types -->
    value  A ::= 1 | 0 | A * A | A + A | U C | ref A | imm @ A | mut @ A | box @ A | !A | unk
               | i32 | i64                                      (VTy.int, SPEC §8)
               | mu X. A | X | Name
               | A => A | all 'x < @. A                          (built-in abbreviations)
               | block σ | val σ | fam mut @ σ | fam imm @ σ | view @ A
               | array A | array_imm @ A                        (VTy.fam, SPEC §9)
    comp   C ::= F A | A -o C | C & C | top | forall 'x < @. C | nu X. C
               | delay A | stream A | iter A A A                 (built-in abbreviations)

`VTy`/`CTy` are defined at `Ty:33`/`Ty:57`. `box @ A` is `[@] A`.

**Precedence**, loosest first:

1. `forall 'x < @.`, `all 'x < @.`, `mu X.` and `nu X.` extend as far right as possible.
2. `-o` and `=>` associate to the right.
3. `&` associates to the right.
4. `+` associates to the right.
5. `*` associates to the right.
6. Prefix formers take one atom: `U`, `F`, `ref`, `!`, `imm @`, `mut @`, `box @`, `delay`,
   `stream`, `block`, `val`, `fam m @`, `view @`, `array`, `array_imm @`; `iter` takes three.
   Their lifetime argument is also an atom.

For example, `S -o F (A + S) & F 1` is `S -o ((F (A + S)) & (F 1))`, and `imm 'a Nat * Nat`
is `(imm 'a Nat) * Nat`. `F A * B` is a sort error: write `F (A * B)`. Sorts are checked after
parsing.

**Built-in abbreviations.** Each is a Lean `abbrev` or `def`, expanded before checking:

| written | expands to | Lean |
|---|---|---|
| `A => B` | `U (A -o F B)` | `VTy.lolli`, `Ty:107` |
| `all 'x < @. A` | `U (forall 'x < @. F A)` | `VTy.all`, `Ty:110` |
| `block σ` | `σ.refTy`: `ref A` at a leaf, `*` at a node | `Bl:52` |
| `val σ` | `σ.valTy`: `A` at a leaf, `*` at a node | `Bl:57` |
| `fam m @ σ` | `σ.famTy M @`: `m @ A` at each leaf, `*` at a node | `BB:111` |
| `view @b A` | `Imm̲ @b A` | `VTy.immReborrow`, `Ty:1064` |
| `array A` | `[ref A]`: the owned array, the family of its cells | `VTy.fam`, SPEC §9 |
| `array_imm @a A` | `[imm @a A]`: the family of an array's leaf views | `VTy.fam`, SPEC §9 |
| `delay A` | `nu X. F (A + U X) & F 1` | `CTy.delay`, `Ty:1042` |
| `stream A` | `nu X. F (A * U X) & F 1` | `CTy.stream`, `Ty:1045` |
| `iter A R R'` | `nu X. F (A * U X + R) & F R'` | `CTy.iter`, `Ty:1049` |

`=>` is BoLo's arrow read call-by-value, and it is the type of every constant. `all` is BoLo's
`∀` read the same way, and it is the type of every borrow callback and fold algebra.

**Restrictions**, checked on every type:

- A type variable `X` must be bound by an enclosing `mu`. It must not occur under `U`, that is,
  anywhere inside a computation type. `rename`, `subst` and `Cl` treat `U C` as a leaf
  (`Ty:157`, `Ty:179`, `Ty:303`), so a variable there is never substituted.
- `mu X. A` must be closed (`Cl 0`, `Ty:298`), and `X` must not occur under `mut` (`NoMut`,
  `Ty:486`). These are `roll`'s premises (`Fu:174`).
- `Name` refers to an earlier `type` declaration. Abbreviations are not recursive.
- In `nu X. C` (SPEC §7, `CTy.nu`, `Ty:73`), `X` is a computation-type variable that occurs only as
  `U X`, the rest of the codata; it is the type variable `0` of `C`'s value types. `C` must be
  positive (`CTy.NuOk`, `Ty:1022`): a `&` of observation trees, each an `F A` or a `&` of them,
  with `U X` in each `A` only under `*` and `+`. `U X` may not occur inside an inner `U`.
<!-- ANCHOR_END: types -->

## 5. Shapes and fold shapes

<!-- ANCHOR: shapes -->
    shape σ ::= leaf A | node σ σ | Name                       (Shape, Bl:40)

`Name` refers to an earlier `shape` declaration.

A fold constant's `F` argument (`fold_imm[F, …]`) is written as a type in which `X` is the
recursive position. It is decoded to an `FShape` (`FI:32`) by **one canonical decoding**, `dec`:

| `T` | `dec T` |
|---|---|
| `T` with no `X` | `leaf T` (a maximal closed subtree) |
| `ref X` | `refX` |
| `X` | `varX` |
| `A * B` (containing `X`) | `tensor (dec A) (dec B)` |
| `A + B` (containing `X`) | `sum (dec A) (dec B)` |
| anything else containing `X` | error: not in `FShape` |

The decoding has to be fixed because the erasure depends on it: `leaf (1 + 1)` and
`sum (leaf 1) (leaf 1)` have the same `FShape.ty` but different `foldImmV`/`travK` terms
(`FI:112`). `dec` takes maximal leaves, which is the form the library uses (`clistF`, `CL:46`;
`natF`, `Fo:487`). Since `FShape.ty (dec T) = T`, the type `mu X. T` written elsewhere matches
the fold's `mu F.ty` exactly. `dec T = varX` (the body `X` alone) fails `FShape.Guarded`
(`FI:64`) and is rejected.
<!-- ANCHOR_END: shapes -->

## 6. Terms

<!-- ANCHOR: terms -->
There are two categories. A **value-judged expression** `V` is checked at a value type `A`
(judgment `val A`). A **computation** `M` is checked at a computation type `C` (judgment
`comp C`). Which category a position takes is fixed by the grammar.

A value-judged expression is not necessarily a syntactic value. `ofRet` (`Fu:171`) reads a
computation of `F A` as a value-judged expression of `A`, and `lolliE` (`Fu:164`) applies a
function inside one. `alloc[Nat] n` is therefore a value-judged expression.

**A-normal form.** Computation-level application `M x` and `force x` take **variables only**
(`app`, `force`: `Fu:73–79`). To apply to anything else, bind it first, `y <- return V; M y`,
or use the call-by-value forms `V W` and `V [@]` at value level.

Mode: **S** synthesizes, **C** checks only, **S/C** synthesizes when its parts do.

### 6.1 Value-judged expressions

| form | erasure | rule | mode |
|---|---|---|---|
| `x` | `var i` | `var` `Fu:51` | S |
| `()` | `()` | `unitI` `Fu:52` | S |
| `(V, W)` | `pair` | `tensorI` `Fu:53` | S/C |
| `inl V` / `inr V` | `inj₁` / `inj₂` | `sumI₁` / `sumI₂` `Fu:56,58` | C |
| `thunk M`, `M : F A` | `λ_. M` (dead binder) | `thunkF` `Fu:61` | S/C |
| `thunkv N`, `N : C ≠ F _`, `N` a literal λ | `N` | `thunkV` `Fu:64` | S/C |
| `!thunk M` | `λ_. M` | `bangThunkF` `Fu:115` | S/C |
| `!thunkv N` | `N` | `bangThunkV` `Fu:119` | S/C |
| `unbang V` | `V` | `bangE` `Fu:123` | S |
| `boxed[@] V` | `V` | `boxI` `Fu:129` | S/C |
| `unbox V` | `V` | `boxE` `Fu:131` | S |
| `(V :> @a)` at `imm @b A` | `V` | `immSub` `Fu:132` | S |
| `(V :> @a)` at `mut @b A` | `V` | `mutSub` `Fu:134` | S |
| `roll V` | `V` | `roll` `Fu:174` | C |
| `unroll V` | `V` | `unroll` `Fu:177` | S |
| `run M`, `M : F A` | `M` | `ofRet` `Fu:171` | S/C |
| `V W`, `V : A => B` | `app V W` | `lolliE` `Fu:164` | S |
| `V [@]`, `V : all 'x < @b. A` | `app V ()` | `allEV` `Fu:168` | S |
| `(V : A)` | `V` | none (ascription) | S |
| constant (section 8) | its `Expr` | its rule | S |
| derived form (section 9) | its `Expr` | its theorem | S |
| `name`, `name[A, …]` (a `def`) | the `def`'s erasure | its body, re-checked (section 10) | S |

### 6.2 Computations

| form | erasure | rule | mode |
|---|---|---|---|
| `return V` | `V` | `ret` `Fu:67` | S/C |
| `x <- M; N` | `(λx. N) M` (`bindE`, `FI:107`) | `bind` `Fu:69` | S/C |
| `x : A <- M; N` | the same, `M` checked at `F A` | `bind` `Fu:69` | S/C |
| `linear x <- M; N`, `linear x : A <- M; N` | the same; `x` is not dropped implicitly (§7) | `bind` `Fu:69` | S/C |
| `force x` | `x ()` at `F A`, else `x` | `force` `Fu:73` | S |
| `fun (x : A) -> M` | `λx. M` | `lam` `Fu:75` | S/C |
| `M x` | `app M x` | `app` `Fu:77` | S |
| `<M, N>` | `withPair M N` (`Co:190`) | `withI` `Fu:81` | S/C |
| `M.1` / `M.2` | `app M (inj₁ ())` / `app M (inj₂ ())` | `proj₁` / `proj₂` `Fu:84,86` | S |
| `<>` | `()` | `topI` `Fu:89` | S |
| `let () = V; M` | `seq V M` | `unitE` `Fu:90` | S/C |
| `let (x, y) = V; M` | `letpair V M` | `tensorE` `Fu:93` | S/C |
| `case V { inl x -> M \| inr y -> N }` | `case V M N` | `sumE` `Fu:97` | S/C |
| `absurd V` | `case V () ()` (`absurdE`, `Co:322`) | `zeroE` `Fu:103` | C |
| `Fun 'x < @. M` | `λ_. M` (dead binder) | `allI` `Fu:106` | S/C |
| `M [@]` | `app M ()` | `allE` `Fu:112` | S |
| `nu_in M` / `nu_out M` | `M` | `nuIn` / `nuOut` `Fu:209,211` | S/C / S |
| `(M : C)` | `M` | none (ascription) | S |

`delay_in`/`stream_in` and `delay_out`/`stream_out` are other spellings of `nu_in` and `nu_out`.
`nu_out M` needs `M` at a `nu` type and has its unrolling. `nu_in M` checked against `nu X. C`
checks `M` at the unrolling; it synthesizes when `M`'s type is the unrolling of a `nu` type whose
thunk occurs in it.

`[@]` takes any lifetime, not only a variable. Its premise is `Δ ⊨ @ ⊏ @b`, where `@b` is the
`∀`'s bound. The result is `C[@/'x]` (`CTy.instLife`, `Ty:1199`).

### 6.3 Binders and de Bruijn indices

The checker assigns indices by the slot layout each rule prescribes:

| form | slots added in front of `Γ` | Lean |
|---|---|---|
| `x <- M; N`, `fun (x : A) -> M`, a `case` arm | `x` live | `Fu:70,75,99` |
| `let (x, y) = V; M` | `y` (index 0), then `x` (index 1), both live | `Fu:95` |
| `thunk M`, `!thunk M` | one dead `1` | `Fu:61,116` |
| `Fun 'x < @. M` | one dead slot | `Fu:109` |
| `<M, N>` | two dead slots, `u : 1` and `s : 1 + 1` | `withCtx`, `Co:194` |
| `thunkv N`, `!thunkv N` | none | `Fu:64,119` |

This layout is why `thunk` and `thunkv` are two keywords: they shift the body's indices
differently.

### 6.4 `thunkv`'s literal-λ restriction

`thunkV` types the term `.val (.lam N)` (`Fu:64`), so the body of `thunkv`/`!thunkv` must be a
computation whose erasure is a λ. That means one of `fun …`, `Fun …`, `<M, N>`, or
`nu_in`/`nu_out` (or their other spellings)/ascription wrapped around one of these. A computation
of type `F A` uses `thunk` instead.

These are rejected: `thunkv (force t)` (erases to `t`), `thunkv (M x)`, `thunkv M.1`,
`thunkv <>` (erases to `()`), and `thunkv (x <- M; N)`. To thunk one of them, eta-expand it
into a λ at its type. For example, a `U (delay A)` from `f : U (S -o delay A)` and `s : S`
(`d_thunkFS`, `Core/DelayPrograms.lean:122`):

    thunkv (delay_in < (delay_out (force f s)).1, (delay_out (force f s)).2 >)

### 6.5 Precedence and scoping

- **Binding forms** extend as far right as possible. These are `x <- M; N`, `x : A <- M; N`,
  `let … = V; M`, `fun`, `Fun`, `thunk`, `thunkv`, `!thunk` and `!thunkv`. The extent ends
  at the enclosing `)`, `}` or `>`, at the `|` before the next `case` arm, or at the `,` between
  `<M, N>`'s components. So inside a `case` arm or a `<,>` component, a chain of `x <- …;`
  belongs to that arm or component. `;` belongs to a binding form; there is no free-standing
  sequencing `M; N` (write `u <- M; let () = u; N`).
- **Spines.** An atom followed by suffixes associates left: argument atoms, `.1`, `.2`,
  `[@]`. So `force f s .1` is `((force f) s).1`.
- **`force x` is an atom**, because it takes only a variable. `force f s` is `(force f) s`.
- **Other prefix keywords take a whole spine**: `return`, `roll`, `unroll`, `inl`, `inr`,
  `unbang`, `unbox`, `boxed[@]`, `run`, `nu_in`, `nu_out` (and `delay_in`, `delay_out`,
  `stream_in`, `stream_out`), `absurd`. So `return f x` is `return (f x)`, and `roll inr n` is `roll (inr n)`. On the
  other hand, `unbang nat_copy ['y] b` is `unbang (nat_copy ['y] b)`, which is ill-typed; write
  `(unbang nat_copy) ['y] b`. Likewise write `(delay_out (force d)).1`.
- `case V { … }` delimits its arms with braces. Ascriptions `( … : T)` and `( … :> @)` must be
  parenthesized.
- A binding form used as a head or an operand must be parenthesized: `(fun (x : A) -> M) y`.
<!-- ANCHOR_END: terms -->

## 7. Linearity

<!-- ANCHOR: linearity -->
Contexts are position-preserving lists of slots with a liveness bit (`Cx:11`). `Core` splits them
with `Ctx.SplitP`, `Ctx.DeadP` and `Ctx.SoloP` (`Core/Persistent.lean`, SPEC §10), which extend the
paper's `Ctx.Split`/`Dead`/`Solo` with one case each for **persistent** slots. A type is persistent
when it holds no resource: `1`, `0`, `unk`, `!A`, and `*`, `+`, `box @` and `mu` over persistent
types (`VTy.persistent`). It follows that:

- **Persistent variables are copied and dropped implicitly.** A split may send a persistent live
  slot to both sides, and a dead-context rule or a variable leaf may drop one.
  `copy_bang[A]`/`forget_bang[A]` (`Fu:125,127`) remain, to make it explicit.
- **Every other variable is used exactly once.** `imm @ A` has `copy[@, A]` and
  `forget_imm[@, A]`; `mut @ A` has `forget_mut[@, A]`; `ref A`, `U C` and `box @ A` over a
  non-persistent `A` have no forget. `U C` is not persistent, because a thunk holds its closure's
  resource.
- **Every `case` arm consumes the same non-persistent live variables.** `sumE` gives both arms the same
  `Γb` (`Fu:97`), so a variable live in `Γb` is consumed by each arm or by neither.
- **Each `<M, N>` component consumes everything the pair consumes.** `withI` gives both
  components the whole `Γ` (`Fu:81`). This is not contraction, because only one component
  ever runs: `< (delay_out (force f s)).1, (delay_out (force f s)).2 >` uses `f` and `s` once
  in each component.
- **Apart from persistent slots, the only discarding forms of the core are `<>` and `absurd V`.**
  `topI` holds at any `Γ` (`Fu:89`), and `zeroE` absorbs every slot that `V` does not use
  (`Fu:103`). Section 11 describes how the checker handles this.
- **Implicit destructors** (SPEC §12). A variable bound by `x <- M; N`, `let (x, y) = V; M`, a
  `case` arm or `fun`, whose type has a destructor (`HasDtor`, `Core/Dtor.lean`) and is not
  persistent, need not be consumed in the source. On each path that does not consume it, the
  checker inserts its destructor `dtorE A x` immediately before the path's terminal computation,
  most recently bound variable first. The erasure contains the call, so the core term still uses
  the variable exactly once. Borrows are dropped by `forget`. `ref A` is dropped by `free` followed
  by the destructor of `A`, a fold-class `mu` by `fold_own`, `U (C & F 1)` by `close` (`.2`), and
  `U (nu X. C & F R)` (`delay`, `stream`, `iter A R₀ R`) with `R` closed and droppable by `close`
  followed by the destructor of the residual `R`. `U C` otherwise has no destructor, so an unused thunk is an error.
  The same holds for a `case` whose arms consume different variables: arms that differ in a variable
  with a destructor are balanced by dropping it in the arm that does not use it. Any other
  difference is an error. `linear x <- M; N` opts `x` out, and then `N` must consume it.
- **Constants and `def`s consume nothing.** They are typed at a dead context.
<!-- ANCHOR_END: linearity -->

## 8. Constants

<!-- ANCHOR: constants -->
Each constant is one `CDerives` constructor at a dead context. The brackets give every
argument of the rule, so the checker never searches. A binder argument `'x` is numbered as in
section 3; it is the `∀` binder in the callback's type, and its rule's premise
`Δ.find? x = none` holds by that numbering (the checker still checks it). `dom` is `⊓Δ` at the
constant.

| constant | type | rule | side conditions beyond `Ctx.Dead` |
|---|---|---|---|
| `alloc[A]` | `A => ref A` | `alloc` `Fu:137` | none |
| `free[A]` | `ref A => A` | `free` `Fu:139` | none |
| `swap[A, B]` | `ref A => B => ref B * A` | `swap` `Fu:141`, `Ty:1395` | none |
| `copy[@a, A]` | `imm @a A => imm @a A * imm @a A` | `copy` `Fu:142`, `Ty:1398` | none |
| `copy_bang[A]` | `!A => !A * !A` | `copyBang` `Fu:125` | none |
| `forget_imm[@a, A]` | `imm @a A => 1` | `forgetImm` `Fu:143` | none |
| `forget_mut[@a, A]` | `mut @a A => 1` | `forgetMut` `Fu:144` | none |
| `forget_unk` | `unk => 1` | `forgetUnk` `Fu:145` | none |
| `forget_bang[A]` | `!A => 1` | `forgetBang` `Fu:127` | none |
| `withbor1['x, A, B]` | `ref A => (all 'x < dom. imm 'x A => box 'x B) => ref A * B` | `withbor1` `Fu:146`, `Ty:1411` | `x` fresh; `VScoped Δ A`; `'x ∉ FV(A), FV(B)` |
| `withbor2['x, @b, A, B]` | `ref A => (all 'x < dom. mut 'x A => box 'x B) => ref A * B` | `withbor2` `Fu:149`, `Ty:1416` | `x` fresh; `Δ ⊨ @b` and `Δ ⊢ A ⊐ @b` (the `∃ b` witness); `'x ∉ FV(A), FV(B)` |
| `withbor3[@a, 'x, A, B]` | `mut @a A => (all 'x < dom. mut 'x A => box 'x B) => mut @a A * B` | `withbor3` `Fu:153`, `Ty:1421` | `x` fresh; `'x ∉ FV(A), FV(B)` |
| `withload[@a, 'x, A, B]` | `imm @a A => (all 'x < dom. view 'x A => box 'x B) => B` | `withload` `Fu:156`, `Ty:1426` | `x` fresh; `'x ∉ FV(A), FV(B)` |
| `withswap[@a, A, B]` | `mut @a A => (A => A * B) => mut @a A * B` | `withswap` `Fu:159`, `Ty:1431` | none |
| `fold_imm[F, 'y, @c, R]` | `!(all 'y < top. A_R => R) => !(all 'y < @c. imm 'y (mu X. F) => R)` | `foldImm` `Fu:184`, `FI:97,101` | `FShape.WF`, `Guarded`; `'y ∉ FV(mu X. F), FV(R)`; `∀ Δ' a, Δ' ⊢ R ⊐ a` |
| `fold_own[F, R]` | `!(A′_R => R) => !((mu X. F) => R)` | `foldOwn` `Fu:190`, `FO:36,39` | `FShape.WF`, `Guarded` |
| `fold_reuse[F, R]` | `!(A″_R => R) => !((mu X. F) => R)` | `foldReuse` `Fu:195`, `FR:85` | `FShape.WF`, `Guarded` |
| `unfold[C, S]` | `!U (S -o C'[S/X]) => !U (S -o C)` for `C = nu X. C'` | `unfoldN` `Fu:215`, `Nu:40,117` | `C` is a `nu` type (positive by §4) |
| `fixd[A, S]` | `!U (S -o F (A + S) & F 1) => !U (S -o delay A)`: `unfold[delay A, S]` | `fixD` `Fu:253` | none |
| `unfold_s[A, S]` | `!U (S -o F (A * S) & F 1) => !U (S -o stream A)`: `unfold[stream A, S]` | `unfoldS` `Fu:267` | none |

Notes on the table:

- **The fold algebra's bound is `top` whatever Δ is.** It is `LifeCtx.empty.meetOfDom`
  (`FI:97`), not `dom`. The algebra's `'y` and the fold's `'y` are the same binder, so they
  get the same number.
- `A_R = FShape.res 'y R (dec F)` (`FI:53`): `view 'y` of each leaf, with `R` at every `ref X`
  and every head `X`. `A′_R = resO R` (`FO:28`) has `R` at every recursive position.
  `A″_R = resR R` (`FR:77`) has `ref 1 * R` at each `ref X` and `R` at each head `X`. The
  programmer writes these types out in the algebra's annotation, and the checker compares them
  with the computed ones.
- The erasures are the terms of `[TR]`/the library: `alloc`/`free` are `.prim`; `swap`
  (`S2:74`); `copy` and `copy_bang` are both `copy` (`Paper/S3_Dynamics/Definitions.lean:317`);
  every `forget_*` is `forget` (`…:322`); `withbor1/2/3` are all `withbor` (`S2:129`);
  `withload` is `S2:186`; `withswap` is `…/S3_Dynamics/Definitions.lean:343`;
  `foldImmV (dec F)` is `FI:152`; `foldOwnV` is `FO:100`; `foldReuseV` is `FR:149`; `unfoldV C` is
  `Nu:117`; `fixDV A` and `unfoldSV A` are `unfoldV` at the delay and stream bodies (`Fu:232,242`).
<!-- ANCHOR_END: constants -->

## 8a. Integers

<!-- ANCHOR: integers -->
Integer literals and operations are constants (`SPEC.md` §8, `Core/Integers.lean`):

- **Literals:** `i32[n]`, `i64[n]` are the `Prim.lit` constant, typed by `CDerives.lit` at `i32`/`i64`.
  `n` is decimal or `0x`-hex and is read modulo 2^32 / 2^64.
- **Operations:** `host[op]`, typed by `CDerives.hostOp op : !(hostArg op => hostRes op)`. `op` is
  written `add32`, `div_s32`, `lt_u64`, `wrap`, `extend_s`, … (one name per `HostOp`,
  `Support/Syntax/Integers.lean`). A call is the value-level application of §6.1, e.g.
  `host[add32] (x, y)`.
- **Results:** tests return `1 + 1` with `inr ()` as true, and partial operations return
  `i32 + 1` with `inr ()` where Wasm traps.
- `i32`/`i64` are persistent (section 7), so integer variables are reused and dropped freely.
<!-- ANCHOR_END: integers -->

## 8b. Arrays

<!-- ANCHOR: arrays -->
The array constants (`SPEC.md` §9, `Core/Arrays.lean`), each one `CDerives` constructor at a
dead context, typed at `!(A => B)` like a host operation, so a call is `(unbang c) V`:

| constant | type | rule |
|---|---|---|
| `array_new[A]` | `!(i32 * !(i32 => A) => array A)` | `arrNew` |
| `array_free[A]` | `!(!(A => 1) * array A => 1)` | `arrFree` |
| `array_size[A]` | `!(array A => array A * i32)` | `arrSize` |
| `array_replace[A]` | `!(array A * (i32 * A) => array A * (A + A))` | `arrReplace` |
| `array_len[@a, A]` | `!(array_imm @a A => i32)` | `arrLen` |
| `array_get[@a, A]` | `!(array_imm @a A * i32 => imm @a A + 1)` | `arrGet` |
| `array_copy[@a, A]` | `!(array_imm @a A => array_imm @a A * array_imm @a A)` | `arrCopy` |
| `array_forget[@a, A]` | `!(array_imm @a A => 1)` | `arrForget` |

- A negative length makes the empty array; an index is compared unsigned, so a negative index
  is out of range and takes `inr`.
- `array_replace` returns the old element, or on the error branch the new one back.
- An array is borrowed in a cell: `withbor1`/`withbor2` on a `ref (array A)` lend
  `imm 'x (array A)`/`mut 'x (array A)`. `withload` at the `imm` borrow gives the family
  `view 'y (array A) = array_imm 'y A`; `withswap` at the `mut` borrow lends the array itself.
- `array A` has a destructor when `A` has one (`array_free` with `A`'s destructor), and
  `array_imm @a A` is forgettable (`array_forget`), so both are dropped implicitly (SPEC §12).
- The erasures: `array_new`, `array_get`, `array_free` are the primitives `tab`, `idx`, `drop`;
  the others are closed λ-terms (`arrLenV`, `sizeV`, `replaceV`, `copyV`, `forgetV`).
<!-- ANCHOR_END: arrays -->

## 9. Derived forms

<!-- ANCHOR: derived -->
Each form is a Lean theorem concluding a `CDerives` judgment, with its own erasure, so
`fundamentalC` covers it. None of them is a `CDerives` constructor. The checker instantiates
the theorem and discharges its hypotheses. `m` is `mut` or `imm`, and each mode is a separate
keyword because each mode is a separate theorem.

| form | type / conclusion | erasure | theorem | side conditions |
|---|---|---|---|---|
| `alloc_s[σ]` | `val σ => block σ` | `allocS σ` `Bl:77` | `d_allocS` `Bl:103` | none |
| `free_s[σ]` | `block σ => val σ` | `freeS σ` `Bl:83` | `d_freeS` `Bl:115` | none |
| `withbor_s_mut[σ, 'c, T]` | `block σ => (all 'c < dom. fam mut 'c σ => box 'c T) => block σ * T` | `withborS σ` `BB:344` | `withborSM_wf` `BB:553` | `σ.plain`, `plainV T` (`BB:47,106`); `Δ.Ok`; `'c` fresh |
| `withbor_s_imm[σ, 'c, T]` | the same with `fam imm` | `withborS σ` | `withborSI_wf` `BB:559` | the same |
| `withbor_f2_mut['c, 'a, 'b, @w, A, B, T]` | `ref A * ref B => (all 'c < dom. mut 'c A * mut 'c B => box 'c T) => (ref A * ref B) * T` | `withborF2` `Fa:67` | `withborM2_wf` `Fa:245` | `FamSide` (`Fa:141`); `Δ ⊨ @w`, `Δ ⊢ A ⊐ @w`; `Δ,'a⊏dom ⊢ B ⊐ 'a` and `⊢ T ⊐ 'a` |
| `withbor_f2_imm['c, 'a, 'b, A, B, T]` | the same with `imm` | `withborF2` | `withborI2_wf` `Fa:253` | `FamSide`; `VScoped Δ A`, `VScoped Δ B`; `B`, `T` outlive `'a` as above |
| `shorten_mut[σ, @a] V`, `V : fam mut @b σ` | `fam mut @a σ` | `shortenE σ V` `BB:339` | `shortenE_wf formerMut` `BB:447` | `σ.plain`; `Δ ⊨ @a ⊑ @b` |
| `shorten_imm[σ, @a] V` | `fam imm @a σ` | `shortenE σ V` | `shortenE_wf formerImm` `BB:447` | the same |

- `withbor_f2`'s `'a` and `'b` name its two internal borrows: the outer borrow of `x` and the
  inner borrow of `y` (`Fa:75,78`). They occur nowhere else in the program. They are numbered
  `Δ.freshVar` and `Δ.freshVar + 1`, so `FamSide.hx`, `hy` and `hxy` hold. `'c` is the
  callback's binder, numbered as in section 3. `FamSide` also requires `Δ.Ok`, that `'a`/`'b`
  are not free in `A`, `B`, `T` or the callback type, and the equation `hinst`. The checker
  decides the equation by computing `instLife`. `@w` is `withbor2`'s `∃ b` witness for `A`.
- `withbor_s` chooses its internal lifetimes inside the proof (`exists_fresh_var`, `BB:437`),
  so it takes only `'c`.
- **`shorten` is not `:>`.** `:>` is `⊑Imm`/`⊑Mut` on one borrow and erases to its operand.
  `shorten` rebuilds a family leaf by leaf and erases to a `letpair` tree.
- The value-level `let`/`case`/`seq`/`λ` (`CDerives.letpairV`, `caseV`, `seqV`, `lamV`, `eletV`,
  `Rc:49–77`) get no syntax. They are `run (…)` around the computation form, with `return` at
  the leaves, and they have the same erasure. For example, `letpairV` is
  `run (let (x, y) = V; return W)`, and `lamV` is `thunkv fun (x : A) -> return W`.
- Records and variants (`getAt`, `injAt`, `vcase`, `loadField`, `swapField`, `Rc`) are not in
  draft 1. They can be written out with the forms above.
<!-- ANCHOR_END: derived -->

## 10. Declarations

<!-- ANCHOR: declarations -->
    type Name = A
    shape Name = σ
    def name : A = V
    def name[P₁, …, Pₙ] : A = V         -- value-type parameters, macro-expanded
    extern name : A
    main : C = M

- **`type` and `shape`** are abbreviations, expanded before checking, in declaration order,
  and not recursive.
- **`def`** is a macro. Its body is a closed value-judged expression: it may mention earlier
  `def`s, constants and derived forms, but no variables or lifetimes of the use site. At each
  use, the checker substitutes the body and **re-checks it there**, at that use's Δ and at an
  all-dead context. It is numbered by section 3 relative to that Δ. For example, `nat_copy`
  used inside an algebra gets its binder number `1` (`d_natCopy1`, `CL:150`); used at top level
  it gets `0` (`d_natCopy`, `Fo:494`). A `def` is also checked once at its declaration, at
  Δ = ∅, so that errors are reported early. Consequences:
  - Each use is its own derivation, so a `def` of any type can be used any number of times.
    This is sound because the body consumes nothing.
  - Each use evaluates the body again (call by name). A body `alloc[1] ()` allocates at every
    use.
  - No Δ-weakening lemma is needed (section 12 has the alternative).
  - A body may be an application, for example `def nat_copy : … = fold_imm[…] count_alg`.
  - Type parameters `def take[A] : ref A => … = …` are substituted textually, and each use
    `take[Nat]` is re-checked. Lifetime parameters are not supported; lifetime polymorphism is
    written with `all`/`forall`.
  - `def`s are checked in order, and a `def` may not refer to itself or a later one. Recursion
    goes through `fold_*`, `fixd`, `unfold_s` or `unfold`.
- **`extern name : A`** adds a live slot of type `A` to `main`'s initial context. The last
  declared extern gets index 0. `A` must be closed (no free lifetime variables). `main` must
  consume every non-persistent extern; persistent externs (such as `!`-typed ones) may go unused.
  Externs are never dropped implicitly (§7).
- **`main : C = M`** is checked at `Δ = ∅` and `Γ =` the externs. `C` is any computation type.

What a program means:

| `main` | guarantee | Lean |
|---|---|---|
| any `C`, any externs | `SemC ∅ Γ e C`: for every substitution of the externs by values of their semantic types | `fundamentalC` `Fu:221` |
| `F 1`, no externs | runs from empty memory to `()` and empty memory | `adequacyC` `Fu:342` |
| `F A`, no externs | runs to some `v` from empty memory, given a lemma that `vC` at `A` holds no resource (such as `vC_natN`, `Core/Count.lean:60`) | `theorem32` `Fu:310`, as in `sumProg_runs` (`CL:320`) |
| `F (U (delay A))`, `F (U (stream 1))` | driven `n` times, then closed | `drive_runs_unit`/`_nat` (`Core/DelayPrograms.lean:77,90`), `take_runs` (`Core/StreamPrograms.lean:85`) |

Drivers such as `driveE n` (`Core/DelayPrograms.lean:37`) are Lean meta-level recursion on
`ℕ`. The syntax has no meta-recursion, so a driver is written out to the depth wanted.

A closed `main` is compiled and run by `bcc run`; `scripts/compile-corpus.sh` compares every
corpus `main` against the interpreter (`Backend/README.md`).
<!-- ANCHOR_END: declarations -->

## 11. Checking

**Bidirectional.** Synthesis and checking follow the mode column of section 6. The annotations
the checker cannot infer are required: `fun` binders, `Fun` bounds, every bracket argument of
constants and derived forms, and `boxed[@]`. `inl`, `inr`, `roll` and `absurd` only check, and
an ascription `(V : A)` supplies the type.

**Contexts: input/output with ⊤-slack (Hodas and Miller 1994).** The judgment is
`Δ; Γin ⊢ e ; Γout, s`. `Γout` is `Γin` with the consumed slots marked dead, and `s` is a slack
flag.

- A leaf consumes its own variables, and a constant or `def` consumes none. The consumed slots
  are the left part of the `Ctx.Split` the rule needs.
- `<>` returns `Γout = Γin` with `s = ⊤`: it may consume any of what remains. `absurd V`
  returns `V`'s output with `s = ⊤`.
- Sequential forms (`bind`, `let`, `tensorI`, `lolliE`, …) thread the context. Their slack is
  the disjunction of their parts' slack. A part's slack can absorb only slots of that part's
  own context. A variable bound in `N` of `x <- M; N` can be absorbed by `N`'s slack, never by
  `M`'s.
- `case` arms and `<M, N>` components each start from the same input. Their consumed sets must
  be equal. The exception is an arm with slack, which may be extended to the other arm's set
  if its own set is contained in it. If both have slack, the result keeps slack.
- When a binder's scope closes, its variable must be consumed, or be absorbed by slack in its
  scope. With implicit destructors (§7) the checker consumes it itself where it can: see §11.1.
- **Side conditions on contexts are read on the consumed context.** They are boxI's
  `CtxOutlives Δ Γ @` (`Ty:1383`), bangThunk's `Persistent Γ` (`Rl:203`), and allI's `hΓx`
  (`'x` is not free in any live slot). At such a boundary the slack is closed: the body
  consumes exactly what it used. This loses completeness but not soundness.

**Lifetimes.** Instantiation `[@]` is explicit, and so are `:>` and `shorten`. Entailments
`Δ ⊨ @a ⊏ @b`, `Δ ⊨ @a ⊑ @b` and `Δ ⊨ @a` are decided by a procedure that is proved sound
against the semantic definitions `EntailsLt`/`EntailsLe`/`Defines` (`S2:360,419,301`; see
section 12).

**Side conditions.** Every side condition is decided by a Bool function with a soundness lemma:
`Ctx.Dead`/`Solo`/`Split` (constructed directly), `Persistent`, `VOutlives`/`CtxOutlives`,
`VScoped`, `VFree`/`mentions`, `NoMut`, `Cl`, `FShape.WF`/`Guarded`, `plainV`/`Shape.plain`,
`Δ.Ok` (`okB`, `Support/Lifetimes/Terms.lean:89`), `Δ.find? x = none`, `C.isRet = false`
(`Co:93`), `FamSide.hinst` (by computation), and foldImm's `∀ Δ' a, VOutlives Δ' a R`
(section 12). The derivation's leaves are discharged by `decide` on these functions, so no
`native_decide` is used.

**Output.** A `CDerives Δ Γ e j` derivation together with its `Expr` `e`, or an error with a
source span.

### 11.1 As implemented (`Frontend/Check/`)

The checker's behaviour where it goes beyond the sections above:

- **Masks, not threading.** Each subterm yields its erasure with two masks over the context: the
  slots it uses, and the live slots it can absorb without using them (⊤-slack). The enclosing rule
  picks the split, and a proof of `CDerives` holds for every choice between the two.
- **Modes.** `nu_in` synthesizes when the body's type is the unrolling of a `nu` type whose thunk
  occurs in it (`CTy.nuThunks`).
  `unbang V` checked at `A` checks `V` at `!A`. `Fun` checked against a `forall` type takes that
  type's binder number, not `Δ.freshVar`.
- **Declarations.** A def's type arguments are elaborated at the use site, and a parametric def is
  checked only at its uses. `main`'s context is every extern in the file.
- **Drops** (§7, SPEC §12). The checker carries the set of variables owed to the current tail
  position. At a terminal computation it checks the computation, then wraps it in `dtorE A x; …`
  for each owed variable it did not use, lowest index first. The drop is one builder (`rDrop`),
  `unitE` over `lolliE` of the variable and `dtor_wf`. The head `M` of `x <- M; N` is owed the owed
  variables it mentions by name.
- **Incompleteness.** Lifetime entailment uses only the structural rules, so it misses
  distributivity (`('x \/ 'y) /\ 'z <= ('x /\ 'z) \/ ('y /\ 'z)`). The derived forms stated at
  `Ctx.Dead` (`alloc_s`, `free_s`, `withbor_s_*`, `withbor_f2_*`) cannot drop persistent slots. The
  full list is in `Frontend/README.md`.

## 12. Proof obligations for the checker

Soundness needs only the "⇒ holds" direction of each item. Completeness, meaning that a program
the rules accept is accepted, needs the converse and is desirable, not required.

1. **Lifetime entailment.** A decision procedure with `decLt Δ a b = true → Δ.EntailsLt a b`,
   and the same for `EntailsLe`. `Defines` already has one: `Life.wf` with
   `LifeCtx.defines_of_wf`. The library has only special cases: `entailsLt_of_bound`
   (`Paper/Examples/Programs.lean:119`), `entailsLt_top`, `entailsLe_refl`
   (`Paper/Examples/Derivations.lean:50,59`), `entailsLt_inner`/`entailsLe_inner` (`Fa:81,87`)
   and `entailsLe_of_meet` (`Core/FamilyPrograms.lean:414`). The procedure has to handle `dom`
   bounds, which are meets, and `⊔`.
2. **foldImm's `hR`.** A Bool `outlivesAll R` with `outlivesAll R = true → ∀ Δ' a,
   VOutlives Δ' a R`. It is true at `1`, `0`, `*`, `+`, `ref`, `!` (any payload), `X` and `mu`,
   and false at `U`, `unk`, `imm`, `mut` and `box`. `outlives_of_dataB` (`Core/Splits.lean:122`)
   is this lemma without `ref`. The converse (take `Δ' = ∅`, `a = top`) gives completeness.
3. **Deciders** for the Prop-valued side conditions `VFree`/`CFree`, `NoMut`, `Cl`,
   `FShape.WF`, `VScoped` and `VOutlives` (which uses item 1). `plainV`, `dataB` and `okB` are
   already Bool.
4. **`DecidableEq` on `VTy`/`CTy`.** It is not derived at `Ty:33`. The checker needs it to
   compare types and to decide `FamSide.hinst`.
5. **Defs, if checked once instead of at each use.** This needs Δ-weakening with a renaming of
   `LifeVar`s: `CDerives Δ Γ e j → CDerives Δ' Γ' e j[ρ]` for `Δ ⊆ Δ'` and a dead extension
   `Γ'`. Only the dead-suffix case exists (`CDerives.append_dead`, `Core/Weaken.lean:59`).
   Draft 1 re-checks at each use, which avoids this obligation. Binding `def`s explicitly in
   `main` at `!` types is the other alternative.
6. **α-equivalence, if chosen.** This needs `CDerives` (or `SemV`/`SemC`) to be invariant under
   renaming the bound `LifeVar`s of types. Draft 1 does not choose it (section 3).

## 13. Examples

Both examples follow `CL` and `Fo`. Numerals are written out (section 14).

### 13.1 A library: numerals, addition, copying, and a borrowed sum

```
type Nat  = mu X. 1 + X
type List = mu X. 1 + (ref Nat * ref X)          -- = mu X. 1 + block Node, by refTy
shape Node = node (leaf Nat) (leaf List)          -- nodeC

-- countAlgV (Fo:84): the foldImm algebra at 1 + X; A_R = 1 + Nat
def count_alg : !(all 'y < top. 1 + Nat => Nat) =
  !thunkv Fun 'y < top. return (thunkv fun (r : 1 + Nat) ->
    case r {
      inl u -> let () = u; return (roll (inl ()))
    | inr n -> return (roll (inr n))
    })

-- natCopyE (Fo:492): a fold application, as a def
def nat_copy : !(all 'y < top. imm 'y Nat => Nat) =
  fold_imm[1 + X, 'y, top, Nat] count_alg

-- freeLAlgV (Fo:94) and freeNatE (Fo:501)
def free_l_alg : !(1 + 1 => 1) =
  !thunkv fun (r : 1 + 1) -> case r { inl u -> return u | inr u -> return u }

def free_nat : Nat => 1 = unbang (fold_own[1 + X, 1] free_l_alg)

-- addAlgV and addE (CL:112,125): curried, Nat => Nat => Nat
def add_alg : !(1 + (Nat => Nat) => (Nat => Nat)) =
  !thunkv fun (r : 1 + (Nat => Nat)) ->
    case r {
      inl u -> let () = u; return (thunkv fun (m : Nat) -> return m)
    | inr f -> return (thunkv fun (m : Nat) -> return (f (roll (inr m))))
    }

def add : Nat => Nat => Nat = unbang (fold_own[1 + X, Nat => Nat] add_alg)

-- sumAlgV (CL:171): A_R = 1 + (view 'y (ref Nat) * Nat) = 1 + (imm 'y Nat * Nat)
def sum_alg : !(all 'y < top. 1 + (imm 'y Nat * Nat) => Nat) =
  !thunkv Fun 'y < top. return (thunkv fun (r : 1 + (imm 'y Nat * Nat)) ->
    case r {
      inl u -> let () = u; return (roll (inl ()))
    | inr p -> let (b, s) = p;
               n <- return ((unbang nat_copy) ['y] b);
               return (add n s)
    })

-- sumCE (CL:268)
def sum_list : !(all 'a < top. imm 'a List => Nat) =
  fold_imm[1 + (ref Nat * ref X), 'a, top, Nat] sum_alg

-- freeCAlgV and freeCE (CL:200,280): A′_R = 1 + (ref Nat * 1)
def free_list_alg : !(1 + (ref Nat * 1) => 1) =
  !thunkv fun (r : 1 + (ref Nat * 1)) ->
    case r {
      inl u -> return u
    | inr p -> let (rn, u) = p; let () = u;
               n <- return (free[Nat] rn);
               return (free_nat n)
    }

def free_list : List => 1 = unbang (fold_own[1 + (ref Nat * ref X), 1] free_list_alg)
```

How this checks:

- **Numbering.** Inside `sum_alg`'s `Fun 'y` at Δ = ∅, Δ becomes `{0 ↦ top}`. The use of
  `nat_copy` is re-checked there, so its binder gets `1`, as in `d_natCopy1`. `['y]`
  instantiates `1 := 0` with `Δ ⊨ 'y ⊏ top`, which gives `imm 'y Nat => Nat`.
- **Fold side conditions.** `fold_imm[1 + (ref Nat * ref X), 'a, …]` decodes to `clistF`.
  Wherever `sum_list` is used, its `'a` and `sum_alg`'s `'y` are binders at the same Δ, so they
  get the same number (`0` at ∅), and the algebra's type is `algTy clistF 0 Nat` as the rule
  requires. `Nat` satisfies `outlivesAll`.
- **Erasures.** `count_alg` erases to `countAlgV`, `nat_copy` to `natCopyE`, `add` to `addE`,
  `free_nat` to `freeNatE`, and `sum_alg` to `sumAlgV`. `unbang`, `return`, `roll` and `run`
  erase to their operand.

### 13.2 A borrow, with the callback's lifetime (`sumProg`, `CL:312`)

```
def nil   : List = roll (inl ())
def one   : Nat  = roll (inr (roll (inl ())))
def two   : Nat  = roll (inr one)
def three : Nat  = roll (inr two)

-- consC (CL:71): one node, allocated as one block
def cons : Nat * List => List =
  thunkv fun (p : Nat * List) -> return (roll (inr (alloc_s[Node] p)))

main : F Nat =
  l <- return (cons (one, cons (two, cons (three, nil))));
  r <- return (alloc[List] l);
  q <- return (withbor1['x, List, Nat] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x List) ->
            n <- return ((unbang sum_list) ['x] b);
            return (boxed['x] n))));
  let (r2, n) = q;
  l2 <- return (free[List] r2);
  u  <- return (free_list l2);
  let () = u;
  return n
```

How this checks:

- **The callback's type.** At `main`, Δ = ∅, so `dom = top`. `'x` in `withbor1['x, …]` and in
  `Fun 'x` are both binders at ∅, so both are `0`. The callback has
  `all 'x < top. imm 'x List => box 'x Nat` (`axWithbor1Ty`, `Ty:1411`). Its `thunkv` body is
  `Fun …`, a literal λ.
- **Inside the callback.** Δ is `{0 ↦ top}`. `sum_list` is re-checked there, so its binder,
  and `sum_alg`'s with it, is `1`, and `nat_copy` inside `sum_alg` gets `2`. `['x]` instantiates
  `sum_list` to `imm 'x List => Nat`. `boxed['x] n` needs `CtxOutlives Δ {n : Nat} 'x`: `'x` is
  defined and `Nat` outlives every lifetime. allI's `hΓx` holds because the callback consumes
  no outer variable.
- **The side conditions of `withbor1`.** `Δ.find? 0 = none` at ∅, `VScoped ∅ List`, and `'x` is
  not free in `List` or `Nat`.
- **Linearity.** Each of `l`, `r`, `q`, `r2`, `l2`, `u`, `n` and `b` is consumed exactly once.
- **Meaning.** `main : F Nat` with no externs, so it runs to a numeral from empty memory
  (`theorem32` with `vC_natN`, as in `sumProg_runs`). The erasure differs from `sumProg`'s:
  `cons` is a λ applied to a pair, where the library inlines `consC`.

## 14. Out of scope, open

- **Numerals and list literals** (`3`, `[1, 2, 3]`) are sugar and are out for now. The library
  builds them with Lean functions (`num`, `buildList`).
- **Growable buffers and strings** are library code over arrays (`SPEC.md` §9), not yet written.
  Integers (section 8a) and arrays (section 8b) are in, and the erasure target stays Paper
  `Expr`, which gained `Prim.lit`/`Prim.host` and the array primitives `tab`, `idx`, `drop`.
- **Lifetime-parametric `def`s and `extern`s** are not supported.
- **Block provenance** (`SPEC.md` §5 Open) is not enforced: `crossPack`
  (`Core/BlockPrograms.lean`) typechecks.
- **Records and variants** (`Rc`) are derived rules with no syntax in draft 1.
- **Implicit `roll`/`unroll`/`nu_*`/`boxed`/`return`/`run`**: all are explicit in
  draft 1.
- **α-equivalence of lifetime binders**: not chosen (section 12, item 6).

## Changes from draft 0

1. A-normal form is stated. `app` and `force` take variables only, and values reach them
   through binding (§6).
2. Syntax for `lolliE` (`V W`), `allEV` (`V [@]`) and `ofRet` (`run M`). `def`s may now be fold
   applications (§6.1, §10).
3. There are two thunk keywords, `thunk` and `thunkv`, and two promoted ones. The de Bruijn
   layout is given, along with `thunkv`'s literal-λ restriction and the eta workaround
   (§6.3–§6.4).
4. Linearity: implicit copy/drop only at persistent types (SPEC §10), exact use otherwise, equal
   consumption across `case` arms and `<,>` components, and `<>`/`absurd` as the only discards
   (§7).
5. Constants with complete brackets, one keyword per rule, and their side conditions. Derived
   rules are separated from constants, with their theorems and side conditions (§8–§9).
6. `FShape` has one canonical decoding (§5).
7. Ascription `(V : A)` / `(M : C)`, `x : A <- M; N`, and `boxed[@]` (§6).
8. Lifetimes gain `⊓`/`⊔`/`dom`. Names are numbered deterministically, with no α-conversion.
   `[@]` takes any lifetime (§3).
9. `X` is forbidden under `U` (§4).
10. Precedence and scoping for types and terms (§4, §6.5).
11. `main` may have any type, `extern` declarations are added, and what each shape of `main`
    guarantees is stated (§10).
12. `shape` abbreviations. `def`s are macros re-checked at each use, with value-type
    parameters. Numerals are out (§10, §14).
13. The checker section covers Hodas–Miller slack, side conditions on the consumed context,
    erasure produced by the checker, and the proof obligations (§11–§12).
14. The worked example is fixed: `all` algebras, `Fun 'y. return (thunkv fun …)`, curried
    `add`, and fold applications as `def`s. A borrow example is added (§13).
15. Integers and arrays are pending, and the erasure target is an open question (§14).
16. Implicit destructors (SPEC §12): unused variables of a type with a destructor are
    dropped by the checker at the end of each path; `linear x <- M; N` opts out (§6.2, §7, §11.1).
