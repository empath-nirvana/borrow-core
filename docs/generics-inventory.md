# Generics: inventory (#477)

Every refusal, *Not provided* line of `SPEC.md`, pending corpus program and open issue that
involves generic code, each with a minimal program and its root cause in the code, grouped by
root cause. Generic functions are monomorphised templates (SPEC §15, decision 45): each fix below
is elaboration into existing core terms, with no kernel change. The entry is SPEC §31.

Status: **fixed** (with the corpus program that covers it), **stale** (no longer reproduces),
**rejected** (with a message, by design or not provided), or **decision** (needs one; options
below).

File and line numbers are at origin/main `c9304d2`, before this change.

## R1. Recursive groups were formed only from non-generic, non-library functions

`Frontend/Elab/Effects.lean:2505–2512` (`elaborate`): `recGroupsOf` took only the `def`s with no
type parameters (`.def_ _ n [] _ V _`) and not in a library, and any generic `def` that named itself
was refused outright ("`f` is generic and calls itself: a generic recursive function is not
provided"). `defineGroup` (`:2466`) refused lifetime parameters ("is recursive and takes lifetime
parameters"), and `deepCopy` (`:2243`) emitted its source and copies with no type parameters.

    include rec
    type List[A] = mu X. 1 + (A * X)
    fn map[A, B](xs: List[A], f: !(A => B)) -> List[B] =
      match unroll xs { inl u -> roll inl () | inr (x, rest) -> let y = f(x); roll inr (y, map(rest, f)) }

| item | status | program |
|---|---|---|
| SPEC §20 *Not provided*: a generic recursive function; §20, §21 *Open* | fixed | `corpus/list-generic.bc`, `rec-generic-mutual.bc` |
| A4 written with a monomorphic `map` (`corpus/async-map.bc`) | fixed | `corpus/async-map.bc` (output and counts unchanged) |
| a layer (§21) over a generic recursion | fixed | `corpus/rec-generic-layer.bc` |
| a generic recursion under `deep` | fixed | `corpus/rec-generic-deep.bc` |
| a recursive function with lifetime parameters | fixed | `corpus/rec-lifetimes.bc` |
| a recursive library function (`lib/` was excluded from groups) | fixed | `lib/list.bc` |
| members with different type parameter names | rejected (D4) | `corpus/reject/rec-generic-params.bc` |
| polymorphic recursion (a call of itself at other types) | rejected, by design | type error at the argument |

**Fix.** A group's members share one list of type parameters and one of lifetime parameters
(`RGroup.tps`, `RGroup.lives`); the generator, the layers' transformers and the copies are templates
in the types and `all 'a` in the lifetimes, made once per row and instantiated per use by §15's
machinery. Under `deep`, the machine's source is a template whose instances keep the
`__mach_src` suffix (`makeInst`), so each becomes its own machine, and a copy names the machine at
its type arguments, `g__mach[T]`. #229's spike proposed instantiating before grouping; groups are
formed before types are known, so the group is formed first and instantiated as a template, which
gives the same instances for every recursion that is not polymorphic.

A side effect of grouping library functions: a recursive template that shares its name with
another function (`map` of `lib/list.bc` and of `lib/iters.bc`) cannot be chosen among by type,
because the group is found by name before types exist. See D1.

## R2. A block with a row given to a generic callee

`Frontend/Elab/Effects.lean:1583` (`blockCall`) refused it ("`map` is generic and is given an
effectful block: not provided"). Behind the refusal, in `Frontend/Sugar.lean`: `matchC` (`:2324`)
had no case for `CTy.eff`, so no type argument could be read through a row, and a block's
synthesized type has no row (`!(i32 => i32)`), so it never matched `!U(A -o F[Σ] B)`.

    fn slow_tens() -> List[i32] with Async, Exhausted = map(one_two_three(), !{ x -> await(); x * 10 })

| item | status | program |
|---|---|---|
| SPEC §30 *Not provided*: a block given to a generic function | fixed | `corpus/async-map.bc`, `corpus/list-blocks.bc` |

**Fix.** The refusal removed; `matchC` matches `eff` layers; a closure is matched by its result
against the parameter with the row taken off (`pureArrow`) and is elaborated at the parameter's
type once that is known.

## R3. A pair as the last argument of a generic call (#135)

`Frontend/Sugar.lean:2442` (`argOf`): rebuilding the argument tuple from its components, the case
for a pair came before the case for the last component, so a last argument that was itself a pair
was taken apart again: `snd(1, (3, 4))` became `snd(1, ((3, 4), 4))`, and the checker reported "a
pair is checked against `i32`".

    fn snd[A, B](a: A, b: B) -> B = b
    main -> i32 * i32 = snd(1, (3, 4))

Status: **fixed** (`corpus/generic-pair-arg.bc`).

## R4. A core `def` with type parameters calling a template at its type variables (#136)

`Frontend/Sugar.lean:4653` (`elabDecl`, `surfDecl`): a core `def f[A]` is checked by the checker at each
use, but its body went through the typed elaboration once, where `A` is no type in scope, so the
template's instance was made at `1`.

    fn id[A](x: A) -> A = x
    def twice[A] : !(A => A) = !thunkv fun (x : A) -> return id(x)

Status: **fixed** (`corpus/generic-in-def.bc`): a core `def` with type parameters whose body names a
template is itself a template.

## R5. A nested template call whose parameters leave a type open

`Frontend/Elab/Effects.lean:631` (`liftCalls`): inside an effectful context (a `with`), a plain
call's argument calls were each bound first with no type, so `nil()` in `cons(7, nil())` lost the
type `cons`'s parameter gives it. And `genericCall` (`Frontend/Sugar.lean:4433`) typed such an argument in the first pass.

    include list
    main -> List[i32] = with on_exhausted(!{ u -> nil() }) { map(cons(7, nil()), !{ x -> x * 2 }) }

Status: **fixed** (`corpus/list-generic.bc`): a plain call is bound whole, and a template call whose
parameters do not determine all its type parameters is typed last, as an injection is.

## R6. #167 and its cases (block-result and call-type inference)

None shares a root cause with R1–R5.

| case | status | program |
|---|---|---|
| #145: a double use inside a callee reported at the call site | stale: reported at the use | `corpus/reject/double-use-in-callee.bc` |
| S5 (§17 *Open*): a call of a function with lifetime parameters whose body lends, typed `1` | stale | `corpus/text-lend-lifetime.bc`; the §17 line removed |
| S1 (§18 *Open*): a call of a function that calls a looping function | stale: `let r = borrow mut c { 'x, m -> twice(3) }` checks | — |
| #150: `internal error: a lifetime parameter` in `fields.bc` with `for` and `return` | stale: the internal error is gone | see R7 |
| `quicksort.bc`'s ascriptions on its borrow blocks | removed: not needed | `corpus/quicksort.bc` |
| §9 *Open*: slice functions called with their element type and lifetimes written | stale: both inferred | the §9 line removed |

## R7. Injections at a `let mut`, an assignment or a `return` in a loop (not generics)

`fields.bc`'s `nth_field` written with `for` and `return` (#150) now fails on what it says: `let mut
rest = inl line` needs `rest`'s type ("the loop threads `rest`, whose type is not determined:
ascribe it"), and then `rest = inr ()` and `return inl f` need theirs ("the type of `inl V` cannot
be synthesized"). The function's result type and the variable's ascribed type are known there. This
is the typed elaboration of injections at assignments and returns (`Frontend/Sugar.lean`,
`forData`), a gap of #167's kind, not of generics. Not fixed here.

## R8. Needs a kernel rule (out of scope: no kernel change)

| item | needs |
|---|---|
| `corpus/pending/box-dup.bc`: generic code boxing at a lifetime a value already boxed at it | the same-index case of `VOutlives.box` |
| `corpus/pending/dig-bang.bc`: generic code promoting a value at a `!` type | digging, `!A ⊸ !!A` |

## R9. Not generics, listed for completeness

| item | where |
|---|---|
| `data` declarations, `box` construction, constructor patterns and fold blocks (#54 stage 8, `corpus/pending/data-box-tree.bc`) | the parser stops at `data`; the spelling is decided (`docs/typed-elaboration.md` §5.3). A large surface stage of its own; generic `data` would follow §15 and §31 unchanged. |
| type parameters on an answering effect (§18 *Not provided*) | the effect side: a capability's type would be generic; a decision of the effect calculus, not of templates. |
| `Map[K, V]` (#211) | builds on R1–R5; not started. |

## Decisions

**D1. Templates of one name when one is recursive.** `include list` with `include iters` (or
`adapters`) declares two `map`s. §15 chooses among templates of one name by the arguments' types,
in the typed elaboration; the effects elaboration, which forms recursive groups and copies, runs
before it and finds functions by name. Today a call of the shared name is rejected with a message
(`corpus/reject/rec-name-clash.bc`); including both and calling neither is accepted. Options:

- (a) **Module-qualified names** (`list.map`, `iters.map`): resolution by name stays syntactic.
  Costs a namespace design for `include`.
- (b) **Resolve overloads before the effects elaboration**, by a typed pre-pass over call sites.
  Costs a second inference pass, or moving the effects elaboration after the typed one.
- (c) **Distinct names in the library** (`list_map`, …): no mechanism, and the name choice is the
  user's.

**D2. Polymorphic recursion** is not monomorphisable in general and is rejected (as a type error at
the argument). Options: keep it rejected with a dedicated message; or allow it when the set of
instances is finite (Rust's approach, bounded by a recursion limit at instantiation).

**D3. Inference into a block's body.** A type parameter that only a block's result determines
(`fold(xs, nil(), !{ (acc, x) -> cons(x, acc) })`) is not inferred; it is written (`nil[i32]()`).
Inference is first-order matching of arguments' types, with closures typed last from their
parameter's type. Options: unification over the block's synthesized result (elaborate the block
with its result open and match it); or keep writing the type.

**D4. Members of a recursive group with type parameters of other names** (`evens[A]`, `odds[B]`)
are rejected. Renaming them positionally is sound only when every call among them passes each
parameter in its own position, which is not known before types are. Options: rename positionally
and let a mismatch fail at the checker; or keep the rejection.
