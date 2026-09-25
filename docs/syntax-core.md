# Core syntax — draft 0

Status: draft for review. Nothing here is implemented.

## Purpose

A textual form of the core calculus (`SPEC.md` §3–§7), for writing the first corpus and for the
parser and checker. There is no sugar. Every term form corresponds to one `CDerives` rule, or to
one named constant of the library, and erases to one BoLo `Expr`. The checker takes a parsed
program and returns a `CDerives` derivation of its erasure, so checker soundness is by
construction.

Allowed beyond the rules: named variables (resolved to de Bruijn indices by the parser),
type abbreviations (`type`, pure substitution), top-level definitions (substituted as closed
values), and comments.

## Lexical

- Identifiers: `[a-z_][A-Za-z0-9_']*` for variables and definitions, `[A-Z][A-Za-z0-9_]*` for type
  abbreviations, `'[a-z][a-z0-9_]*` for lifetime variables.
- Keywords: listed with the forms below.
- Each Unicode symbol has an ASCII spelling: `⊗ *`, `⊕ +`, `⊸ -o`, `& &`, `⊤ top`, `∀ forall`,
  `⊏ <`, `⊑ <=`, `μ mu`, `λ fun`, `Λ Fun`.
- Comments: `--` to end of line.

## Types

    lifetime  @ ::= 'x | top                                          (top is ⊤)
    value     A ::= 1 | 0 | A * A | A + A | U C | ref A | imm @ A | mut @ A
                  | box @ A | !A | unk | mu X. A | X | Name
    comp      C ::= F A | A -o C | C & C | top | forall 'x < @. C | delay A | str A
    shape     σ ::= leaf A | node σ σ                                   (blocks, SPEC §5)

`box @ A` is `[@] A`. `Name` is a `type` abbreviation, expanded before checking. `X` must be
bound by an enclosing `mu`, and positivity (`NoMut`) is checked.

Derived type forms (abbreviations built in, pure substitution):

    block σ    ≜ refTy σ          (the family of leaf refs; SPEC §5)
    val σ      ≜ σ's ⊗-tree of leaf types

## Terms

CBPV-style. Values `V` and computations `M` are separate categories. The table gives each form
with its erasure and its rule. `x, y` are variables; `'a` is a lifetime variable.

### Values

| form | erasure | rule |
|---|---|---|
| `x` | `var i` | `var` |
| `()` | `unit` | `unitI` |
| `(V, W)` | `pair` | `tensorI` |
| `inl V` / `inr V` | `inj₁` / `inj₂` | `sumI₁` / `sumI₂` |
| `thunk M` where `M : F A` | `λ_. M` | `thunkF` |
| `thunk N` where `N : C`, `C ≠ F _` | `N` (itself a `λ`) | `thunkV` |
| `bang thunk …` | as `thunk` | `bangThunkF` / `bangThunkV` (context persistent) |
| `roll V` / `unroll V` | `V` | `roll` / `unroll` |
| `boxed V` / `unbox V` | `V` | `boxI` / `boxE` |
| `V :> imm @ A` / `V :> mut @ A` | `V` | `immSub` / `mutSub` (shorten a lifetime) |
| `unbang V` | `V` | `bangE` |
| constant `c` (below) | its `Expr` | its rule |
| `name` (top-level `def`) | its value | the derivation of the definition |

### Computations

| form | erasure | rule |
|---|---|---|
| `return V` | `V` | `ret` |
| `x <- M; N` | `(λx. N) M`-shaped | `bind` |
| `force x` | `x ()` at `F A`; `x` otherwise | `force` |
| `fun (x : A) -> M` | `λ. M` | `lam` |
| `M V` | `app` | `app` |
| `<M, N>` | as `CDerives.withI` | `withI` |
| `M.1` / `M.2` | as `proj₁` / `proj₂` | `proj₁` / `proj₂` |
| `<>` | `unit` | `topI` |
| `Fun 'x < @. M` | `λ_. M` | `allI` |
| `M ['a]` | `M ()` | `allE` |
| `let () = V; M` | `seq` | `unitE` |
| `let (x, y) = V; M` | `letpair` | `tensorE` |
| `case V { inl x -> M | inr y -> N }` | `case` | `sumE` |
| `absurd V` | `case V …` | `zeroE` |
| `delay_in M` / `delay_out M` | `M` | `delayIn` / `delayOut` |
| `str_in M` / `str_out M` | `M` | `strIn` / `strOut` |

The call-by-value derived forms `lolliE`, `allEV`, `ofRet` get no syntax. They exist only for
the embedding.

### Constants

Each is a closed value typed by one rule (types as in `Core/Fundamental.lean`):

    alloc  free  swap  copy  forget            -- borrow axioms, [TR] p. 3
    withbor1  withbor2  withbor3  withload  withswap
    copy_bang  forget_bang
    withbor_f2                                 -- family borrow (SPEC §5)
    alloc_s[σ]  free_s[σ]  withbor_s[σ]        -- blocks (SPEC §5)
    fold_imm[F, R]  fold_own[F, R]  fold_reuse[F, R]   -- SPEC §6; F is a μ body in FShape
    fixd[A, S]  unfold_s[A, S]                 -- SPEC §7

Type arguments in brackets are required where the rule is parametric in them, so the checker
never searches.

## Declarations

    type Name = A
    def name : A = V           -- closed, checked at the dead context
    main : F 1 = M             -- the program; adequacy applies

`def`s are checked in order, and a definition may use earlier ones. There is no recursion
between `def`s: recursion is `fold_*`, `fixd` or `unfold_s`.

## Checking

The checker is bidirectional.

- **Contexts** are split algorithmically: input context in, leftover out. A variable is used
  once unless its type is `!A`, or it is consumed by `copy`/`forget`.
- **Annotations are required** on `fun` binders, on `Fun` binders (bound), and on constants'
  bracketed arguments. Everything else synthesizes or checks.
- **Lifetimes**: `Δ ⊨ @a ⊑ @b` and `@a ⊏ @b` are decided by walking Δ. Instantiation `['a]` is
  explicit, and so is subsumption `:>`.
- **Side conditions** (dead context, persistence, outlives `VOutlives`/`CtxOutlives`, `NoMut`,
  `FShape` membership, `C.isRet = false`) are decided syntactically.
- **Output**: a `CDerives Δ Γ e j` derivation, or an error with a source span.

## Example

```
type Nat  = mu X. 1 + X
type List = mu X. 1 + block (node (leaf Nat) (leaf X))

-- sum a borrowed list (SPEC §6, foldImm)
def sum : !U (forall 'a < top. imm 'a List -o F Nat) =
  fold_imm[1 + block (node (leaf Nat) (leaf X)), Nat]
    (bang thunk Fun 'y < top. fun (v : 1 + (imm 'y Nat * Nat)) ->
       case v {
         inl u -> let () = u; return (roll (inl ()))
       | inr p -> let (h, acc) = p;
                  h2 <- (force nat_copy) ['y] h;
                  (force add) h2 acc
       })
```

## Open questions for review

1. Is `thunk M` versus `thunk N` (which depends on `M`'s type) acceptable as one keyword, given
   bidirectional checking, or should it be two keywords?
2. `x <- M; N` erases to an application of a `λ`. Confirm against `bind`'s actual erasure.
3. How do fold constants name `F` (an `FShape`)? As the `μ` body, with the checker verifying
   `FShape` membership?
4. Block provenance (SPEC §5 Open) is not enforced here: `crossPack` typechecks.
5. Record and variant helpers (`getAt`, `injAt`, …) are derived rules. Should they be
   constants, or left to be written out?
6. Should `delay_in`/`delay_out`/`roll`/`unroll`/`boxed` be implicit in checking mode?
   (Proposal: no, not in draft 0.)
