# Grades: interval grades `[lo, hi]` over `{0, 1, ∞}`

**Question** (issue #23). `Core`'s contexts are graded in disguise: a slot's liveness bit is
`0`/`1`, a persistent slot is `ω` by type (`Ctx.SplitP.dup` is `ω = ω + ω`, `Ctx.DeadP.drop` is
`0 ≤ ω`), and promotion's `!Γ` premise is `ω · Γ`. Is an explicit grade semiring equivalent to
that, does migrating `Core` to it delete more than it adds (decision 20), and does grade `0`
give erasure?

Build: `lake build Grades`. The library imports `Core` and nothing imports it. `Paper/`,
`Support/`, `Core/`, `Frontend/`, `Backend/` and `CDerives` are unchanged. Every declaration's
axioms are within `[propext, Classical.choice, Quot.sound]` (553 declarations).

| file | contents |
|---|---|
| `Algebra.lean` | the five grades, `+`, `·`, containment order; every law by `decide` |
| `Context.lean` | graded slots, `erase`/`embed`/`scale`, profiles, `GSplit`/`GDead`/`GSolo`; the premise translations both ways |
| `Judgment.lean` | `GDerives P` (`CDerives` with graded premises, plus `lam0`/`app0`); `GDerives.toCore`, `CDerives.toGraded`, `cderives_iff_graded`, `GDerives.mono` |
| `Soundness.lean` | `fundamentalG`: every case is `Core`'s compatibility lemma, plus one drop lemma (`semC_weak`), promotion over persistent contexts, `lam0_compat`, `app0_compat` |
| `Derived.lean` | constants that become derived; the no-ω-poison instances; `embed_erase`; promotion over an `I32` capture |
| `Erasure.lean` | a capability token at grade `0` through a borrow-using function; it runs, and runs the same with any value in the token's place |

## The algebra

A grade is an interval of use counts:

| grade | interval | surface | written? |
|---|---|---|---|
| `erased` | `[0,0]` | `ghost` / `comptime` / `erased` | yes |
| `linear` | `[1,1]` | default | no |
| `affine` | `[0,1]` | implied by a forgettable type (`Imm`, `Mut`) | no |
| `relevant` | `[1,∞]` | `must_use` | occasionally |
| `unrestricted` | `[0,∞]` | implied by a persistent type | no |

`+` and `·` act on the endpoints. At the upper endpoint `1 + 1` saturates to `∞`. At the lower
endpoint it saturates to `1`, because a lower bound of two uses is still a lower bound of one.
Without that, `[1,1] + [1,1]` would be `[∞,∞]`, which is not one of the five grades. The order is
containment. Commutativity, associativity, units, annihilation, both distributive laws and
monotonicity all hold by `decide` over the five grades (`Grade.*`).

**Type conditions from the endpoints** (`Grade.ok`). A droppable grade (`lo = 0`) other than
`[0,0]` needs a forgettable type. A copyable grade (`hi = ∞`) needs a persistent type. They pass
from a sum to its summands whenever persistent types are forgettable (`ok_add`). A **profile**
fixes the three choices this leaves open: which types are droppable, which types promotion may
scale, and whether the erased-position rules are present.

* `Profile.core`: droppable = persistent, promotion at `!`-types, no erasure. This is `Core` as
  it stands.
* `Profile.graded`: droppable = forgettable (`Imm`, `Mut`, persistent), promotion at
  persistent types (which `ω · Γ`'s own type condition already implies: `promOk_graded`),
  erasure on.

**Defaults by type** (`surfaceDefault`). A slot's grade is `[0,∞]` at a persistent type, `[0,1]`
at `Imm`/`Mut`, and `[1,1]` otherwise, and it is well graded (`surfaceDefault_ok`). Only `ghost`
and `must_use` are ever written, so the annotation burden is two keywords. The Core equivalence
grades by `dflt` instead (`[0,∞]` at persistent types, `[1,1]` otherwise), because `Core` has no
affine drop.

## Step 1: equivalence

`GDerives P Δ Γ e j` is `CDerives` with each context premise graded:

* `Ctx.SplitP` becomes `GSplit P`: per slot `g = g₁ + g₂`, with the sum's type condition checked;
* `Ctx.DeadP` becomes `GDead P`: every slot droppable;
* `Ctx.SoloP` becomes `GSolo P`: one live slot, the rest droppable;
* a live binder carries a live grade, and a dead binder is at `[0,0]`;
* promotion (`bangThunkF`/`bangThunkV`) goes from `Γ` to `ω · Γ`, with `ω · Γ` well graded and
  `PromOk P Γ`.

`GCtx.erase` makes a slot live iff its grade is not `[0,0]`. `GCtx.embed` grades a Core context
by `dflt`, and `erase_embed : erase (embed Γ) = Γ`.

```
cderives_iff_graded : CDerives Δ Γ e j ↔ GDerives Profile.core Δ (embed Γ) e j
GDerives.toCore     : GDerives Profile.core Δ Γ e j → CDerives Δ (erase Γ) e j   -- any graded Γ
```

At the premises:

```
splitP_iff     : Ctx.SplitP Γ Γ₁ Γ₂ ↔ GSplit core (embed Γ) (embed Γ₁) (embed Γ₂)
deadP_iff      : Ctx.DeadP Γ ↔ GDead core (embed Γ)
soloP_iff      : Ctx.SoloP Γ i T ↔ GSolo core (embed Γ) i T
persistent_iff : Persistent Γ ↔ (ω · embed Γ = embed Γ ∧ GOk core (ω · embed Γ) ∧ PromOk core (embed Γ))
```

So `fundamentalC` transfers to `Profile.core` through `toCore` without editing `Core`. For any
profile whose droppable types hold no owned cell, it also holds directly:

```
fundamentalG : (∀ T, P.drop T → SemForget T) → GDerives P Δ Γ e j → SemJ Δ (erase Γ) e j
fundamentalGraded : GDerives Profile.graded Δ Γ e j → SemJ Δ (erase Γ) e j
```

`GDerives.mono` and `Profile.core_le_graded` turn every Core derivation into a graded one.

**Where the letter does not match.** Under one principle the promotion condition is `hi = ∞ ⇒
persistent`. Core's `!Γ` asks for more: every live slot must be at a `!`-type. The equivalence
therefore needs `Profile.core`'s `prom = !`-types as a separate condition. The one-principle
reading (`Profile.graded`) widens promotion to persistent contexts, the item SPEC §10 lists as
Open, and it is sound: `bangThunkF_compatG` is `bangThunkF_compatC` with the resource `∅` taken
from `gSepC_deadP`. `promote_int` promotes `thunk (return x)` over `x : I32`, which `Core`
cannot do (`promote_int_not_core`). Like `relevant` and the affine drop at `Imm`/`Mut`, the
widening is an extension. None of them is in the equivalence.

**The forget constants.** Three of the five constants are already derivable in `CDerives`
without their constructor, because `Unk` and `!A` are persistent: `copy : !A ⊸ !A ⊗ !A`
(`copyBang_core`), `forget : !A ⊸ 1` (`forgetBang_core`) and `forget : Unk ⊸ 1`
(`forgetUnk_core`). Under `Profile.graded`, `forget` at `Imm` and at `Mut` is also derivable. The
binder is at `[0,1]` and the body drops it (`forgetImm_graded`, `forgetMut_graded`). `Core` has
no counterpart for that drop (`affine_imm_not_core`). Its soundness is one lemma, `semC_weak`: a
dropped slot's resource has no owned cell (`semForget_forgettable`), and `wpTS_frame_noOwn`
passes such a frame through any run. `copy` at `Imm` stays a constant, because `Imm` is not
persistent.

## Step 2: measurement

Counts are taken from `Core/`, `Frontend/` and `Backend/` at `main`. Each row is costed
separately.

| change | deletes | adds | net |
|---|---|---|---|
| (a) `copy_bang`, `forget_bang`, `forget_unk` derived. Needs no grades: they are derivable in `Core` today | 3 `CDerives` constructors (5 lines), 3 compatibility lemmas (46 lines), 6 induction arms (`fundamentalC`, `Weaken`) | 3 derived lemmas (13 lines, `Derived.lean`) | **≈ −44** |
| (b) promotion premise `!Γ` replaced by `Ctx.DeadP Γ` (every live slot persistent). Needs no grades | `Persistent` (2), `gSepC_persistent` (16), `persistent_append` (3), `persistent_dead` (2) | `persistent_cbv` restated (≈ 5, same size) | **≈ −23**, and promotion is widened |
| (c) affine drop at `Imm`/`Mut`; `forget_imm`, `forget_mut` derived | 2 constructors (2), 2 compatibility lemmas (34), 4 arms | the drop lemma and its plumbing as built here (`Weak`, `gSepC_weak`, `cC_frame`, `semC_weak`, `splitP_weak_right`, `GDead.weak`/`GSolo.weak`, `semForget_forgettable`): ≈ 190 | **≈ +150** |
| (d) grades as the context coordinate: `Grade`, graded slots, `GSplit`/`GDead`/`GSolo`, `ω ·` at promotion | `SplitP`/`DeadP`/`SoloP`, their `toP` conversions and coercions (78 lines, 11 constructors) | the algebra (≈ 100 of `Algebra.lean`'s 171), slots, `erase`/`scale`, profile and type condition (≈ 55), the premises (48). One grade and one liveness premise per binder on `bind`, `lam`, `tensorE` (two), `sumE` (two), touching every such rule application: 201 `.bind`/`.tensorE`/`.sumE` sites plus the `.lam` rule sites, and every induction over `CDerives` (`fundamentalC`, `Weaken`, `Embedding`, the checker) | **> +100 before churn** |

**Verdict: not net-negative.** Grades as a context coordinate add lines (d), and the relation
never reads them. Every grade reaches the semantics only through `erase`, that is, as the
liveness bit (`fundamentalG` is stated at `erase Γ`). At the default grades a graded context is
a Core context: `erase_embed` and `embed_erase` make it a bijection. The information grades add
is the non-default annotations: `[1,∞]` (must use), and `[1,1]` or `[0,1]` at a type that would
allow more. These are checker disciplines with no semantic content. So the grade datum is a
defaulted index in the sense of decision 19.

The deletions come from the **endpoint type conditions**, and `Core` can adopt those without
grades. (a) and (b) together are ≈ −67 lines of pure deletion, and they close SPEC §10's Open
item on promotion. (c) is a U2/U4 gain (one drop lemma instead of per-constant lemmas), but it
costs more than it deletes. (b) and (c) conflict: if `DeadP` drops `Imm`, promotion needs its own
"live slots persistent" predicate back (`deadP_of_persistent`).

## Step 3: erasure

Grade `0` is `Core`'s dead slot. A variable leaf may not use it (`erased_not_solo`), a split
sends it to both sides at `[0,0]` (`erased_add`), and a dead context drops it. Two rules, present
when the profile has erasure, give it its erased positions:

* `lam0`: `Γ, x :⁰ A ⊢ M : C` gives `Γ ⊢ λ⁰x. M : Ghost A ⊸ C`;
* `app0`: `Γ ⊢ M : Ghost A ⊸ C` and `x_i : A ∈ Γ` at any grade give `Γ ⊢ M [x_i] : C`.

`Ghost A = 1 ⊕ (0 ⊗ A)` is the run-time type. It records `A` for the checker, its only value is
`inj₁ ()`, and that value holds `∅` (`ghost_empty`). The erased argument in the term is `inj₁ ()`
(`ghostV`), and the token variable does not occur. Soundness: `lam0_compat` is `lam_compatC`
after dropping the binder, since the slot is dead in `M` and the argument holds `∅`.
`app0_compat` is `cC`'s `⊸` clause at `inj₁ ()`.

The program (`Erasure.lean`). A capability `tok : Cap`, with `Cap = Ref 1` (owned, never
droppable if held), is a grade-`0` parameter of `main`. `main` passes it at grade `0` to `use`,
which passes it at grade `0` to `priv` and then runs `cImmBorrow`: allocate a cell, borrow it
immutably, load through the borrow, end the borrow, free the cell.

    main = λ⁰tok. (λ⁰t. priv [t] to u. u; cImmBorrow) [tok]      priv = λ⁰t. ()

`main_derives` types it under `Profile.graded`. `prog_runs` runs `main [inj₁ ()]` from the empty
memory to `()` and the empty memory. `prog_runs_any v` runs `main v` to the same result for
**every** value `v` in the token's place. The token is absent at run time: nothing is allocated
for it, and its value is never inspected.

Landing this in `Core` would take two rules and two compatibility lemmas (no new index); `lam0`
needs a drop of a slot at `∅`. `Core`'s `∀I` already has the shape, a dead binder at an arbitrary
type applied to `()`. Removing the argument from the lowered code is not done.

## The no-ω-poison check

* **Promotion is the only `r ·` site.** In `GDerives`, `GCtx.scale` appears only in the
  conclusions of `bangThunkF` and `bangThunkV`. No premise is scaled. Splits combine by `+`
  (`GSplit`), and `&` gives both components the same context (additive, no scaling).
* **Scaling data is a type error at the site.** Scaling a live slot of non-persistent type by
  `ω` is ill graded under every profile (`scale_nonpersistent_rejected`). Nothing is silently
  over-charged.
* **Folds, `fixD` and `unfoldS` scale no data footprint.** `foldImm`, `foldOwn`, `foldReuse`,
  `fixD` and `unfoldS` are constants at a droppable context. Their types separate rate from
  usage: `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`. The `!` (persistent, holds `∅`) is on the
  code, and the data is a `⊸` argument used once per call. The default grading puts `[0,∞]` only
  at persistent types (`embed_copyable`). By `cderives_iff_graded`, every `Core` program (every
  fold, `fixD` and `unfoldS` program included) is therefore a graded derivation whose data slots
  are `[1,1]`. Two instances, checked: in the delay driver, the step `U(S ⊸ D A)` and the state
  `S = Ref 1` are both `[1,1]` (`fs_graded`). In the fold program `progOpen` over the boxed
  list, the fold is at `[0,∞]` and the list's free function at `[1,1]` (`progOpen_graded`).

## What this unlocks

* **U1 (new program).** Erased parameters: a capability token checked at the type level and
  absent at run time (`prog_runs_any`). Promotion over persistent captures (`promote_int`: a
  `!` thunk over an `I32`), which `Core`'s `!Γ` rejects.
* **U2 (proof once).** One drop lemma (`semC_weak`) covers every forgettable type, where `Core`
  has one compatibility lemma per `forget` constant. One promotion lemma covers every persistent
  context.
* **U3 (optimization).** An erased argument is a constant holding `∅` and is never inspected, so
  a lowering may omit it. Not done.
* **U4 (fewer mechanisms).** Three constants (`copy_bang`, `forget_bang`, `forget_unk`) are
  redundant in `Core` today, and the promotion premise can be `Ctx.DeadP`: ≈ −67 lines, with no
  grades needed. `forget_imm`/`forget_mut` become derivable under affine drops, at a net cost.

## Not done

* Migrating `Core`. The measurement recommends (a) and (b) as a spec entry, with grades kept as
  surface annotations (`ghost`, `must_use`) that elaborate to liveness bits and the erased-position
  rules.
* A graded checker, and `must_use` enforcement beyond `GDead`'s `lo = 0` condition.
* Erased arguments removed by the lowering.
