# Affine: owned values dropped by elaboration

**Question** (issue #43, following #23). Can an owned value (`Ref A`, a block, a list, a codata
thunk) go unused, with the elaborator inserting its destructor so the result is an ordinary
linear core program? If so, soundness comes by translation: `fundamentalC` and `adequacyC`
apply to the elaborated term, with no model change, and leak freedom holds because drops are
inserted, not skipped.

**Answer: yes, with no model change and no new invariant.** Every droppable type's destructor is
a closed `CDerives` derivation. The affine judgment `ADerives` elaborates into `CDerives` by a
translation that never inverts `CDerives`. Two programs with their frees removed run to the
same answers with no cell left.

Build: `lake build Affine`. The library imports `Core` and nothing imports it. `Paper/`,
`Support/`, `Core/`, `Frontend/`, `Backend/` and `CDerives` are unchanged. Every declaration's
axioms are within `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Dtor.lean` | `dtorE T : T ⊸ F 1`, `HasDtor` (the droppable types), `dtor_wf` (each destructor is a `CDerives` derivation), `hasDtor_of_affine`, `dtorE_imm`/`dtorE_mut` |
| `Elab.lean` | `ADerives` (`CDerives` plus `drop`, indexed by the elaborated term), `ADerives.elab`, `fundamentalA`/`adequacyA`/`runsA`, `owner_not_shared`, `drop_needs_live` |
| `Programs.lean` | `sumAff` (the i32 list sum with no frees) and `blockAff b` (a field and a block dropped in the arms that do not use them): derivations, adequacy, interpreter runs, and the leak without the drops |

## Step 1: destructors

`dtorE T` is a closed `λ` built by one structural recursion on `T`. `dtor_wf` types it at every
lifetime context and every dead context, using existing rules only:

| type | destructor | rules |
|---|---|---|
| `1`, `0`, `I32`, `I64`, `Unk`, `!A` | `forget = λx. ()` | `λ`, `Ctx.DeadP.drop` (persistent) |
| `Imm @a A`, `Mut @a A` | `forget` | the `forgetImm`/`forgetMut` constants |
| `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise | `letpair`/`case`/`[]E`, `lolliE` |
| `Ref A` | `free`, then `dtorE A` | `free`, `elet` |
| `μX. T`, `T` in `FShape` | `foldOwn (λr. dtorE (T[1/X]) r)` | `foldOwn`, promotion over a dead context |
| `U(C & F 1)`, `U(D A)`, `U(Stream A)` | `close`: force, then `π₂` | `force`, `delayOut`/`streamOut`, `proj₂` |

**Droppable** means `HasDtor T`. The forgettable types of `Core/Records.lean` (`Affine`: borrows,
`Unk`, persistent types) are droppable (`hasDtor_of_affine`). The following have no destructor:

* `U C` in general. A thunk of `F A` or of `A ⊸ C` can be disposed of only by running it, which
  has effects and may need an argument.
* `μ` outside `FShape`, for example `X` under `U`, where `foldOwn` does not apply.
* A type variable.

At `μ`, `toFShape` reads the fold's shape back from the body (`toFShape_ty : (toFShape A).ty =
A`). The algebra is the same recursion in its `alg` mode, which gives `forget` at `Ref X` and
`X`. `algE_eq` identifies it with `dtorE (T[1/X])`.

## Step 2: the elaboration

`ADerives Δ Γ e e' j`: the source `e` is affinely typed at `j`, and `e'` is its elaboration.
Every `CDerives` rule with a subderivation is repeated with `ADerives` premises. `core` embeds
any `CDerives` derivation unchanged. There is one new rule:

```
drop:  Ctx.SplitP Γ Γ₁ Γ₂    Ctx.SoloP Γ₁ i T    HasDtor T    ADerives Δ Γ₂ e e' (comp C)
       ─────────────────────────────────────────────────────────────────────────────────
       ADerives Δ Γ e (dtorE T xᵢ; e') (comp C)
```

A discard is therefore available at any computation judgment, under any former: at the end of a
scope, in one arm of a `case`, inside a `λ`, a thunk or a borrow callback. Value positions reach
it through `ofRet`.

```
ADerives.elab : ADerives Δ Γ e e' j → CDerives Δ Γ e' j
fundamentalA  : ADerives Δ Γ e e' j → SemJ Δ Γ e' j
adequacyA     : ADerives ∅ [] e e' (F 1) → e' runs from the empty memory to () and the empty memory
runsA         : the same at any result type R, the value in vP R
```

In `elab`, the `drop` case is `unitE` over `lolliE (dtor_wf …) (var …)` (`drop_derives`). Every
other case is the constructor it copies. No case inverts `CDerives` (decision 21), and
`CDerives` gains no index or rule (decision 19). The cost is one judgment that copies the
structural rules (≈ 100 lines) and a 40-line induction.

## Step 3: borrows

A value cannot be dropped while it is lent, and nothing has to be added to enforce this:

* `withbor r cb` receives the owner `r` through a context split. A split sends a live `Ref A` to
  one side only (`owner_not_shared`: `Ref A` is not persistent, so `dup` does not apply). The
  callback's context, where a `drop` inside the loan would look for `r`, has it dead, and
  `drop` needs a live solo slot (`drop_needs_live`).
* During the loan the callback holds `Imm 'x A` or `Mut 'x A`. Both are droppable, and their
  destructor is `forget` (`dtorE_imm`, `dtorE_mut`): ending a loan early deallocates nothing.
* The owner comes back in `withbor`'s result and can be dropped after the loan. `sumAff` does
  exactly this.

Beyond these checks there is no separate argument. A `drop` elaborates to a use of a linear
variable, so linearity and lifetimes rule out a drop during a loan exactly as they rule out
a `free` there, and `fundamentalC` covers the result.

## Step 4: programs

| program | source | elaboration | interpreter | without the drops |
|---|---|---|---|---|
| `sumAff` | `IntPrograms.sumListProg` with both frees removed: `… let (r′, n) = p in return n` | `r′` dropped before `return n`: `free`, then `foldOwn` over the list (`HasDtor.ref hasDtor_ilistL`) | `123`, no cell left (`sumAffE_eval`, the same answer as `sumListProg_eval`) | leaks (`sumAff_leaks`) |
| `blockAff false` | block `{a : I32, b : I32}`; the first arm moves `a` out and returns it | field `b` dropped before `return m` | `7`, no cell left (`blockAffE_eval₁`) | leaks (`blockAff_leaks`) |
| `blockAff true` | the second arm uses nothing | the whole block (`Ref I32 ⊗ Ref I32`) dropped before `return 0` | `0`, no cell left (`blockAffE_eval₂`) | leaks |

Adequacy at every host: `sumAffE_runs` and `blockAffE_runs b` each run from the empty memory to a
32-bit literal and the empty memory.

## Step 5: where drops go

**Policy: at the end of the scope, on each control path that still holds the value.** A drop is
inserted immediately before the terminal computation of every path on which a droppable slot is
still live. That terminal computation is the `return`, the tail call, or the computation the path
ends in. So:

* a value that is never used is dropped at the end of the scope that binds it;
* after a `case` or `<,>`, an arm that does not consume the value drops it, and an arm that
  consumes it does not;
* an early exit is a path's terminal computation, so it drops what the path still holds;
* several slots are dropped in reverse binding order (Rust's order).

This is the point where `CDerives` asks for a dead context (the leaf's `Ctx.DeadP`), so the rule
is also the simplest to check: the checker's leftover live droppable slots at a leaf are exactly
the drops to insert.

**Soundness does not depend on the policy.** `ADerives.drop` is admissible at every computation
judgment, and `ADerives.elab` covers every placement. Placing a drop right after the last use,
or right after the binding when there is no use, is equally sound and frees memory sooner (U3).
End of scope is chosen because it is predictable where the order is observable: a codata
`close` runs the object's close branch, and moving it earlier reorders effects.

**Surface.** The grade is implied by the type, following #23's defaults-by-type table:

| type | surface grade | written? |
|---|---|---|
| persistent | `[0,∞]` | no |
| droppable (`HasDtor`), including owned types with a destructor | `[0,1]`: may go unused; the drop is inserted | no |
| owned without a destructor (`U(F A)`, `U(A ⊸ C)`, `μ` outside `FShape`) | `[1,1]`: must be used; an unused one is a type error naming the type | no |
| any type, opted in | `[1,1]` via `linear`, for handles whose silent drop is a bug (a transaction, a lock guard with a result) | yes |

Affine is the default for owned types that have a destructor. Rust's experience is that
implicit drop is what programmers expect of owned data, and that opting out (for linear or
must-use obligations) is rare. The opt-out is the linear grade, which the core already
implements.

## What this unlocks

* **U1 (new program).** Programs that discard owned data without writing its destructor:
  `sumAff` drops a returned list after a loan, and `blockAff` drops an unused struct field (a
  partial move) and an unused block per branch. Before this, each needed an explicit
  `free`/`foldOwn` at every discard point and on every branch. `sumAff_leaks` and
  `blockAff_leaks` show the source terms leak when run as they are.
* **U2 (proof once).** Soundness and leak freedom for every placement of every drop is one
  theorem, `ADerives.elab`, plus the one destructor lemma `dtor_wf`. No drop needs a
  compatibility lemma, and neither the model, `SemJ`, nor any invariant is touched.
* **U3 (optimization).** Placement is free for the optimizer (see Step 5). Dropping at last use
  instead of end of scope shortens lifetimes and lowers peak memory, and it is sound by the same
  theorem. Not done. A persistent `μ` is dropped by traversal here; skipping the traversal is
  an optimization the lowering can make, since the value holds no cell.
* **U4 (fewer mechanisms).** Drop elaboration subsumes the forget constants at the surface:
  `forget` at `Imm`/`Mut`/`Unk`/`!A` becomes the destructor that `drop` inserts, and the user
  never writes it. Hand-written free functions for data in the fold class (`freeIE`, `freeCE`)
  are generated (`dtorE` at `μ`). In the core itself, `ADerives` is an addition, not a
  deletion. It lives beside `CDerives` and is not a new index on it.

## Not done

* **Checker.** `Frontend/Check` does not insert drops. The integration is one builder
  (`rDrop`, wrapping a `Res` in `dtorE T xᵢ; ·` over a split) and the policy at two sites:
  leftover live droppable slots at a scope's end, and arms whose usage masks differ at a `case`
  join. Completeness is not claimed (decision 21).
* **Lowering.** `Backend/Clos` already inserts deep drops for unused persistent variables
  (`wrapDrops`). The drops here are core terms (`free`, `foldOwn`, `close`), so they lower like
  any other code. A dedicated deep-free primitive for `μ` would replace the `foldOwn` traversal.
* **`Buf`/`Str`** (SPEC §9). These are opaque extern types, not `VTy` formers, so they are
  outside `HasDtor` here. Their destructors are the externs `str_free` and `buf_free`.
  `buf_free` is typed only at a persistent element type, so a `Buf` of owned elements needs a
  drain (a `pop` loop dropping each element) before it can be freed. Each would be one
  `HasDtor` case, with its destructor an extern call.
* **A syntactic elaborator** (a function from source to elaborated term following the policy).
  `ADerives` is declarative: the derivation chooses the placement, and the programs follow the
  policy by hand.
