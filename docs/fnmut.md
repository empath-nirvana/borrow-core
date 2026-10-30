# The closure `Clo`, Rust's `FnMut`

Issue #236, the experiment; #239 lifted it into the kernel as SPEC §22. The kernel change of §8
is made: the positivity relaxation is in `Core/`, the closure's lemmas and derived rules in
`Core/Clo.lean` and `Core/CloRules.lean`, the programs in `Core/CloPrograms.lean`, and the
library declaration is `Clo[A, B]<'c>` in `lib/clo.bc` (decision 60: the name is not Rust's).
The Lean names below are the library's (`cloT`, `cloBox`, `d_callClo`, `d_ofFn`); this document
writes the type `FnMut^c A B` as the experiment did, and SPEC §22 writes it `Clo^c A B`.

**How claims are marked.**

- **[Lean]**: a theorem in `Core/Clo.lean`, `Core/CloRules.lean` or `Core/CloPrograms.lean`. Axioms are within
  `[propext, Classical.choice, Quot.sound]`, with no `sorry`. Each program is one closed
  `CDerives` derivation; `*_runs` is its adequacy instance at every host, and `*_eval` is the
  interpreter at Wasm's host, checked by `decide`.
- **[inspection]**: read off the rules or the code, with no proof.
- **[hypothesis]**: not checked.

---

## 0. Answers

1. **The type.**

       FnMut^c A B  ≜  νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1

   a `Clo` closure is a value of `U(FnMut^c A B)`. It has two observations:
   - `call` takes an `A` and answers a `B` together with the rest of the closure;
   - `close` ends the closure.

   The bound `@c` is the lifetime the closure outlives, Rust's `dyn FnMut(A) -> B + 'c`. The
   rest each call hands back is `[@c] U(FnMut^c A B)`, the form in which a closure is stored,
   returned or lent. Introduction is coiteration: `unfold step s` packs a state `s : S` with
   `!` code `step : S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1`. The type hides `S`.

2. **Mode index or new former? Neither.** `FnMut` is an abbreviation over the codata former
   `νX. C`, as `Stream` and `Iter` are (SPEC §7). The three closure modes are three type shapes
   that already exist:
   - `FnOnce` is `U(A ⊸ F B)`;
   - `FnMut` is `ν` with a `close` observation;
   - `Fn` is `!U(A ⊸ F B)`.

   What `experiments/BorrowedClosures` anticipated as "a mode index on the codata former" is
   supplied by `ν`'s observation set: the `close` observation is what gives the closure a derived drop.
   No new former is needed, no index on `⊸`, and no new `CDerives` rule.

3. **Is it derivable?**
   - **Not in `Core` as it is [inspection].** `CTy.NuLeaf` (`Core/Types.lean`) admits only
     `F A`, `&` and `F_Σ A` in an observation tree. An observation that takes an argument,
     `A ⊸ …`, is outside it, and `cC` at a non-positive `ν` is `True`, which carries no meaning.
     There is no existential over value types.
   - **With an existential**, `FnMut^c A B ≅ ∃S. S ⊗ !U(S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1)`. That
     is a new value-type former, about 100 match arms by `CLAUDE.md`'s count.
     `BorrowedClosures`' `envShape_unlinked` refutes such a package only where `Imm̲` looks
     inside it, and here `Imm̲` gives `Unk` [Lean: `immReborrow_fnMut`], so it would not bite.
     The cost is the former.
   - **With `ν`, after two relaxations of its positivity, it is derivable [Lean].** The
     relaxations are an observation with a closed argument (`A ⊸ D`) and a boxed rest
     (`[@c] U X`). Coiteration is the existential's introduction: `unfold step s` packs
     `(S, s, step)`. This is `docs/scope-recursion.md` §3.1's route ("the `∃S` form is how
     coiteration is *proved* … not how the type is defined"). The fork's diff against `Core` is
     139 changed lines in six files (`experiments/FnMut/kernel.patch`).

4. **The relation clause, and §12.69 [Lean].** `cC_fnMut_iff`:

       𝒞⟦FnMut^c A B⟧(e) ⟺ (∀v. 𝒱⟦A⟧(v) ─⋆ wp (e π₁ v) 𝒱⟦B ⊗ [@c] U(FnMut^c A B)⟧)
                            ∧ wp (e π₂) 𝒱⟦1⟧

   It is the unrolling of the greatest fixed point (`NuRel.lean`). At the program's view the
   clause is kept whole. In the observable view it is relaxed to `True`, like every `U C`
   (`vC_obs_fnMut`). That relaxation is never spent against a `Clo` closure:
   - an `Imm` payload is read through `Imm̲`, which takes `U C` to `Unk`, the paper's clause (4)
     (`immReborrow_fnMut`, `immReborrow_fnBox`);
   - a `Mut` payload is held at the program's view.

   `obs_transfer` is unchanged in the fork. Its arm at `U C` is the one `FnMut` takes
   (`obs_transfer_fnBox`). §12.69 survives untouched. `BorrowedClosures`' stage-2 obstruction
   (`image_dom` at a closure) does not arise, because no access path keeps a closure at the
   observable view. This matches Rust: a closure behind `&` is callable only if it is `Fn`.

5. **Compatibility lemmas.** There are none for the type beyond the existing ones' new arms:
   `nuIn`, `nuOut` and `unfold` are sound at the relaxed shapes through the new cases of
   `cB_mono`, `cB_unroll` (and the rest of `NuRel.lean`), `node_ok` and `map_ok`. The rules are
   derivations, so `fundamentalC` covers them:
   - **introduction** `d_mk`/`d_mkBox`, a λ capturing any context, linear and borrowed parts
     included, as the state;
   - **elimination** `d_call`, and `d_callMut` through `Mut @a ([@c] U FnMut)`;
   - **forget** `d_close`, `d_closeBox`, and SPEC §12's `drop_derives` at `hasDtor_fnBox`;
   - **coercions** `d_fromFn` (`Fn ≤ FnMut`) and `d_once` (`FnMut ≤ FnOnce`).

6. **The kernel change** (§8): the two positivity relaxations of `νX. C` in `Core`, `FnMut` as a
   SPEC §7 instance, and §2's closure table's `FnMut` row replaced by the type. No new former, no
   new rule, no new index.

### Requirement matrix

| # | requirement | status | where |
|---|---|---|---|
| 1 | call repeatedly through a `Mut` borrow; the state persists | **[Lean]** | `d_callMut`; `counterProg`: a counter owning a cell, stored in a cell, lent, called with 1 then 2 through the borrow, closed: `4`, no cell left |
| 2 | pass a borrowed closure on, at any depth | **[Lean]** | `d_passF n` for every `n`; `passF` reborrows once (`withbor` form 3) and calls twice; `passProg 3` = `13` |
| 3 | a closure capturing a closure; closures taking closures | **[Lean]** for capture and for `!` functions taking a borrowed closure; **[Lean]** positivity only for a `Clo` closure whose argument is a closure | `nestProg` = `8`; `twiceV`, `reV`, `passF`; `fnBody_nuOk_higher` |
| 4 | store or return one, bounded by the borrows it captures | **[Lean]** | `counterProg` stores one in a cell; `retProg` returns one from a function (`15`); `logProg` captures `Mut 'x I32`, is boxed at `'w ⊏ 'x`, and writes through the borrow (`12`); `logState_not_outlives`, `fnMut_not_outlives` |
| 5 | forget/drop | **[Lean]**; the policy **[inspection]** | `hasDtor_fnMut`; `dropProg` (`0`, its cell freed by the destructor); `not_forgettable_clo` |
| 6 | `Fn ≤ FnMut ≤ FnOnce`, with refusals | **[Lean]** for the coercions and for the premises the refusals lack; the refusal of a uniform `FnOnce → FnMut` is **[inspection]** | `d_fromFn`, `fromFnProg` (`23`); `d_once`, `onceProg` (`5`); `not_persistent_fnMut`, `not_hasDtor_lolli` |

---

## 1. Three modes, three shapes

| Rust | here | copy | drop | SPEC §12 class |
|---|---|---|---|---|
| `FnOnce(A) -> B` | `U(A ⊸ F B)` | no | no: only by calling it | 3 (strictly linear) |
| `FnMut(A) -> B + 'c` | `[@c] U(FnMut^c A B)` | no | yes: `close`, which runs code | 2 (destructor) |
| `Fn(A) -> B` | `!U(A ⊸ F B)` | yes | yes: `forget` | 1 (forgettable) |

The `!` row is SPEC §2. The `FnOnce` row is the paper's `⊸`. The `FnMut` row replaces §2's
"`(env, !code)` behind a `Mut` borrow, … run by `withswap`". That row exposes the environment's
type `E`, so a function over such closures has to be written once per `E`: the copies and ports
of #233 and `docs/effect-polymorphism.md` R2a. `FnMut^c A B` names no `E`. Internally the closure
is still an environment and `!` code, `unfold step s`. A call through a borrow is still `withswap`
on the payload (`d_callMut`). What changes is that the environment is hidden by the type.

## 2. The relaxation of `νX. C`

The fork `experiments/FnMut/FnMut/Core/` is `Core`'s import closure: the 50 modules
`Core.Fundamental`, `Core.Dtor` and `Core.Steps` need, plus `Splits.lean` and `Weaken.lean`,
copied at `620c82c` with only the imports renamed. The first commit on the branch is the
verbatim copy, so the second commit's diff is the change. Two relaxations:

1. **An observation may take an argument.** `NuLeaf` admits `A ⊸ D` when `A` is closed and `D` is
   an observation tree. `cB`'s clause there is `cC`'s `⊸` clause with the argument read without
   the type-variable environment (`A` has no `X`), so the clause is monotone in the candidate
   (`cB_mono`), and one unfolding at the relation is the unrolling (`cB_unroll`).
   - `instT` passes through the arrow.
   - Coiteration's node at `A ⊸ D` is `λx. node_D wr (childA c x)`: the argument is passed on to
     the step's computation (`nodeV_arr_steps`, `node_ok`).
2. **The rest may be boxed.** `VTy.Poly` admits `[@a] B` over a polynomial `B`. The box is the
   resource condition `@ρ ⊐ α` (`[TR]` p. 6, `box`), which is monotone. Coiteration's map is the
   identity on it, because `[]I`/`[]E` are typing rules on the same term (`mapV`, `map_ok`).

Every arm that read the old trees gains its case: `cB_mono`, `cB_unroll`, `cB_step`, `cB_bind`,
`cB_iff_stacks` (`sSB` gains the argument), `cB_congr`, `cB_tyEq`, `CTyEq.nuLeaf_iff` and
`TyEq.poly_iff`. Nothing else in the fork changes:

- `fundamentalC`, `adequacyC`, the frame rules, the reborrow images and the invariants build
  unchanged;
- every previously positive body is still positive;
- `Dtor.lean`'s `HasDtor.nu` covers `FnMut` without a new case.

`experiments/FnMut/kernel.patch` is the same diff as a patch against `Core/`, plus one proof arm
in `Frontend/Check/Decide.lean` (`polyB_sound`'s `[@a]` case, which now reaches `VTy.Poly`'s new
clause; `polyB` itself is unchanged). With the patch applied to this branch,
`lake build Core Frontend Backend bcc` succeeds. The corpus was not re-run against it.

Why the box: `VOutlives` has no rule at `U C` (`fnMut_not_outlives`). `withbor`'s mutable form
needs its payload to outlive a defined lifetime, so a closure is lent only as `[@c] U(…)`. A call
hands back the rest, and the rest must be `[@c]` again. Re-boxing after the call is impossible,
because the rest's own type no longer records `@c`. Rebuilding the box from the call's inputs is
not a theorem: a call may store a shorter-lived argument in the state. So the bound belongs in
the type, at the rest's position. The step proves it by `[]I` over its next state.

## 3. The rules

`Rules.lean`. Each is a `CDerives` derivation; `fundamentalC` gives its soundness.

| rule | term | built from |
|---|---|---|
| introduction | `mkE c A B s₀ step K` (`d_mk`) | `unfoldN`, then a `withPair` of the two observations of `f s` |
| introduction, outliving `@c` | the same, when `S ⊐ @c` (`d_mkBox`) | `[]I` over `f : !U(S ⊸ FnMut)` and `s : S` |
| call | `f π₁ a : F(B ⊗ [@c] U(FnMut^c A B))` (`d_call`) | `force`, `nuOut`, `π₁`, application |
| close | `f π₂ : F 1` (`d_close`) | `nuOut`, `π₂` |
| call through `Mut` | `withswap m (λbf. bf to f. f π₁ a to (b, r). (r, b))` (`d_callMut`) | `withswap`, `[]E`, call |
| `Fn ≤ FnMut` | `mkE` at the state `!U(A ⊸ F B)`, code `fromFnStep` (`d_fromFn`) | `unfoldN`, `!` splits |
| `FnMut ≤ FnOnce` | `λa. f π₁ a to (b, r). close r; b` (`d_once`) | call, close |

Introduction keeps the unfolded code under `!` in the context. That way the packed closure's
context is `!` code and the state, and `[]I` at any lifetime the state outlives applies to it
(`d_packBox`).

## 4. The programs

Each is closed, typed at `F I32`, run by adequacy at every host and by the interpreter.

| program | file | what it shows | interpreter |
|---|---|---|---|
| `counterProg` | `Counter.lean` | a counter over an owned cell, boxed at `⊤`, stored in a cell, lent mutably at `'w`, called with `1` and `2` through the borrow, then taken back and closed | `4` |
| `passProg 3` | `Passing.lean` | the borrow handed through three functions to `passF 0`. That function reborrows it at `'v ⊏ 'w` for one call (`reV`), then calls through it twice (`twiceV`) | `13` |
| `nestProg` | `Programs.lean` | an outer closure whose state is the counter, boxed at `'x ⊏ ⊤`, doubling each answer. Closing it closes the counter | `8` |
| `retProg` | `Capture.lean` | `mkCounter : !U(I32 ⊸ F([@⊤] U FnMut))` returns a closure owning a fresh cell | `15` |
| `logProg` | `Capture.lean` | a logger whose state is the captured `Mut 'x I32`. It is boxed at `'w ⊏ 'x` and adds each argument to the log through `withswap` on the borrow. The owner reads the log after the borrow ends | `12` |
| `fromFnProg` | `Programs.lean` | `λx. x + 10 : !U(I32 ⊸ F I32)` made a `Clo` closure and called twice | `23` |
| `onceProg` | `Programs.lean` | the counter used once as `U(I32 ⊸ F I32)` | `5` |
| `dropProg` | `Programs.lean` | the counter over a cell, never called, dropped by its destructor | `0` |

Every run ends with no cell left. In `dropProg` and `onceProg` that is the destructor's `close`
freeing the closure's cell.

**Scopes.** `withbor`'s mutable form needs its payload to outlive a lifetime defined *before* the
borrow, and `[@c]` is strict (`'a ⊏ @c`). At the empty lifetime context only `⊤` is defined, so a
closure boxed at `⊤` is lent from inside one scope `'x ⊏ ⊤` (`scopeProg`). A closure that
captures a borrow at `'x` is boxed at a shorter `'w ⊏ 'x` (`logProg`). It cannot be boxed at `'x`
itself (`logState_not_outlives`). Rust's `+ 'c` is non-strict and needs neither scope. This is
BoLo's strict outlives, not a property of the closure `Clo` [inspection].

## 5. Dropping

**Choice: dropping a `Clo` closure runs its destructor, `close`.** `close` disposes of the
captured state. Owned linear captures are freed (the counter's `close` frees its cell), captured
borrows are forgotten (the logger's `close` forgets `Mut 'x I32`), and captured closures are
closed (`nestProg`).

- **Justification.** This is SPEC §12 group 2, unchanged. `HasDtor.nu` already gives every
  `U(νX. C & F R)` with a closed droppable residual the destructor "force, `nuOut`, `π₂`, then
  the residual's destructor" (`hasDtor_fnMut` is that constructor at `FnMut`'s body). So the
  checker's insertion policy (§12) drops an unused closure at the end of its scope, as it drops
  a `Ref` or a `Stream`, and the drop is placed so that it never reorders effects.
- **What it requires of captures.** The creator writes `close`, so it must be able to dispose of
  the state.
  - The closure sugar that turns `λ` over a context into `unfold` would write `close` as the
    destructors of the captures, so it requires every capture to be droppable (`HasDtor`:
    classes 1 and 2).
  - A capture without one, such as a `U(A ⊸ F B)` (`not_hasDtor_lolli`), is accepted only when
    the creator writes an explicit `close` for it.
- **A derived drop by destructor, not by `forget`.** A `Clo` closure is not `Forgettable`
  (`not_forgettable_clo`, the experiment's name): discarding it is an action, its `close`, placed by
  the checker's insertion policy so that it never reorders effects.

## 6. Relations

- **The paper's `Unk` clause.** Kept: `Imm̲ 'b (U(FnMut …)) = Unk` (`immReborrow_fnMut`). A
  closure that may hold linear references cannot be called through an `Imm` borrow (`[CONF]`
  415:9), and that is right for `FnMut`. The paper's limit is lifted the other way: through a
  `Mut` borrow the closure is callable, by `withswap`, with no change to `withswap`.
- **`ModesLabels`.** Its README's last section proposes mode-annotated arrows: lin = `FnOnce`,
  `FnMut` at the mode with weakening only, unr = `Fn`.
  - The experiment does not need annotated arrows: the modes are the three shapes of §1.
  - **`FnMut` is not at the weakening mode in `ModesLabels`' sense [inspection].** `weaken_sound` says a value
    at a weakenable mode holds no `own` cell, and a `Clo` closure can own cells: the counter
    owns one, freed by its `close`. Its weakening is a destructor, as for `Ref A` under §12, not
    the free weakening of `Mut`.
  - So `σ(m) = W` splits in two: *forgettable* (`Mut`, class 1) and *droppable by an action*
    (`FnMut`, and `Ref` since §12). The label reading is unaffected: a `Clo` closure breaks
    independence only through the borrows its state holds, and its `[@c]` bound is the label
    that licenses it.
- **`Shifts`.** The missing shift from the weakening mode to `unr` (`withborMI`, `&mut T → &T`) is not needed. An
  `Imm` view of a closure is `Unk` whatever the shift.
- **§12.69 and `obs_transfer`.** §0.4. Nothing is relaxed that was not already relaxed, and
  nothing new is kept at the observable view.
- **#233, R2a, `docs/second-class-and-system-c.md`.** R2a's "closure value" (`!` code and an
  environment lent as `Mut 'x Env`) is what `unfold` builds. Hiding `Env` behind the type closes
  the "copies per environment type" item.
  - A function over callbacks takes `Mut 'a ([@c] U(FnMut^c A B))`, with no `Env` parameter.
  - An effectful callback is `νX. (A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`, positive under the same
    relaxation (`fnEffBody_nuOk`). It is not exercised by a program [Lean for positivity only].

## 7. What is proved

- The fork with the relaxed positivity builds, and `fundamentalC` and `adequacyC` hold over it.
- `cC_fnMut_iff` (the clause), `fnMut_coind`, `vC_obs_fnMut`, `immReborrow_fnMut`,
  `immReborrow_fnBox`, `obs_transfer_fnBox`.
- `fnBody_nuOk`, `fnBody_nuOk_higher`, `fnEffBody_nuOk`.
- `hasDtor_fnMut`, `hasDtor_fnBox`, `not_forgettable_clo`, `not_persistent_fnMut`,
  `not_persistent_fnBox`, `not_hasDtor_lolli`, `fnMut_not_outlives`, `logState_not_outlives`,
  `logState_ctx_not_outlives`.
- The derived rules of §3, and `d_passF` at every depth.
- The eight programs of §4, each with `*_derives`, `*_runs` and `*_eval`.

## 8. The kernel change it implies

Made in #239 (SPEC §22), as described here, with one addition: `type` declarations take type and
lifetime parameters, so the library can declare `Clo[A, B]<'c>`. The checker's positivity
decision and the backend's eager codata thunks (`Backend/Clos/Collapse.lean`) admit the new
shapes, and the corpus programs `corpus/clo-*.bc` cover the requirements of §0.

- **SPEC §7.** Positivity (`CTy.NuOk`) gains two shapes:
  - an observation with a closed argument, `A ⊸ D`;
  - a boxed rest, `[@a] U X`.

  The relation's clause at an argument is `cC`'s `⊸` clause, and coiteration passes the
  argument to the step. The *Open* item "in the argument of an observation (`A ⊸ …`, a sink), is
  outside `NuOk`" is then closed for an argument without `X`. An argument mentioning `X` stays
  open.
- **SPEC §7 Instances.** Add `FnMut^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`. Its
  `nuIn`/`nuOut`/`unfold` are the general ones, and its destructor is §12's `HasDtor.nu`.
- **SPEC §2's closure table.** The `FnMut` row becomes `[@c] U(FnMut^c A B)`, called through
  `Mut` by `withswap`.
- **`Core/`.** `kernel.patch`: about 140 changed lines in `Types.lean`, `Relation.lean`,
  `RelationFacts.lean`, `NuRel.lean`, `Computation.lean` and `Nu.lean`, and one proof arm in
  `Frontend/Check/Decide.lean`. The whole library and `bcc` build with it. The checker's
  positivity decision (`nuLeafB`, `polyB`) would still have to admit the new shapes before the
  checker accepts an `FnMut` program. No new
  `VTy`/`CTy`/`CDerives` constructor and no new index. The baseline theorems keep their
  statements.
- **`Frontend/`.** A closure sugar: `fnmut` over a context elaborates to `unfold` with the
  captures as the state and `close` as their destructors: elaboration into existing core terms
  (`docs/decisions.md` 33).
- **Not covered by this change.** A higher-ranked argument, Rust's `FnMut(&mut T)` for every
  lifetime (§9).

## 9. Open

- **A lifetime-polymorphic argument** (`∀'a. Mut 'a T ⊸ F(B ⊗ [@c] U X)`). It needs `∀` in
  observation trees. `cB` at `∀` would change `δ` under a candidate fixed at one `δ`. Not
  attempted. Today an argument's lifetimes are fixed when the closure's type is written.
- **a `Clo` closure taking a `Clo` closure,** as a program. The type is positive
  (`fnBody_nuOk_higher`); no program exercises it.
- **Effectful calls,** as a program (§6).
- **The closure sugar and its checker rule** (§8): not built.
- **Lowering [hypothesis].** The model's `unfold step s` is a fixed-point combinator over a
  thunk. The backend should represent a `Clo` closure as R2a's defunctionalised pair: a
  pointer to the state and a code tag. A call through `Mut` is then an indirect call on the
  state in place, not a `withswap` of the whole value. Not measured.
- **A uniform `FnOnce → FnMut`** is refused by inspection only. For some `A` and `B` such a
  coercion exists: at `A = 1`, `B = 1`, a state `1 ⊕ U(1 ⊸ F 1)` calls once, then answers `()`,
  and `close` calls it if it was not called. So the refusal is about parametricity, which is not
  stated. Its mechanical part is `not_hasDtor_lolli`: a `FnOnce` cannot be dropped by a `close`
  that has no `A`.
