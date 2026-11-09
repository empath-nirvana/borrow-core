# #808 — codata observations that take borrowed arguments (`∀` leaves of `ν`)

Issue #808. Blocks #769 (Fs): `File` should be a protocol object whose `read` takes `&mut Buf` and
whose `write` takes `&Buf`.

Kernel target: `CTy.NuLeaf` (`Core/Types.lean`) admits an observation `∀'x ⊏ @b. D` over an observation
tree `D`, so an observation can take a lifetime-quantified borrowed argument (`∀'x. Mut 'x A ⊸ D`,
`∀'x. Imm 'x A ⊸ D`, and in general an argument type that mentions the bound lifetimes). `cB` gains
`cC`'s `∀` clause. `cB_mono`, `cB_unroll`, `cC_nu_iff`, `node_ok` and `unfold_compatX` are re-proved.
`fundamentalC`, `adequacyC`, `adequacyD` and `resourceSafety` keep their statements. A `ν` object whose
observations take `Mut 'x Buf` and `Imm 'x Buf` derives in `CDerives`, is lent a buffer, gives it back,
and runs.

Scratch checks: `~/repos/scratch-archive/808/Scratch808.lean`. It is compiled in this worktree with
`lake env lean`, and every result's axioms are `[propext, Classical.choice, Quot.sound]`.

## 1. Why `NuLeaf` refuses borrowed arguments today

**Finding: closed arguments are not the obstacle.** `A.Cl 0` says that no *type variable* is free in
`A` (`VTy.Cl`, `Core/Types.lean`). Lifetimes do not count. Free lifetimes are already allowed in an
argument, and `Mut 'x Buf ⊸ F(I32 ⊗ U X)` with `'x` free is an observation tree today (Check 1). The
obstacle is that `NuLeaf` has no `.all` case: `∀'x ⊏ ⊤. Mut 'x Buf ⊸ F(U X)` is not an observation
tree (Check 1). `cB` makes it worse by answering `True` at `.all`. A borrowed argument is lent per
call, so its lifetime must be quantified at the observation. An argument at a fixed outer lifetime
(`Clo`'s `cloBody_nuOk_higher`) ties every call of the object to one lend.

**Reading the argument "without η" costs nothing.** At a `Cl 0` type the environment is never read:
`vCE (some η) b A = vC b A` (`vCE_cl0_env`, Check 2, from `vCE_congr_occ`). `cB`'s docstring line,
"the argument read without `η` (its type is closed)", describes an equality, not a restriction.

**What `Cl 0` is for: keeping `X` out of a negative position.** The proof step that uses it is
`cB_mono`'s `⊸` case (`Core/NuRel.lean`). That case passes the argument's proof `hv` through
unchanged. If the argument were read at the candidate, the case would need
`vCE (nuEnv C R') A ⊢ vCE (nuEnv C R) A` for `R ⊆ R'`, which is antitone. At `A = U X` that fails:
`uX_not_antitone` (Check 3) gives `⊥ ⊆ ⊤` with `vCE (nuEnv C ⊤) (U X) v` true and `vCE (nuEnv C ⊥) (U X) v`
false. The condition is essential for `X` in an argument (a method that takes another object of
the same `ν` type), because `nuF_mono`, and with it `nuRel_out`/`nuRel_roll`, rests on `cB_mono`.
That `cB_mono` itself fails with `η` at the argument is not derived (I have shown only that the
step it takes is unavailable). Either way it does not bear on #808: `Mut 'x Buf` and `Imm 'x Buf`
are `Cl 0`, and **#808 keeps `A.Cl 0`.**

## 2. The new definitions

### 2.1 `NuLeaf`, `instT`, and binder freshness (`Core/Types.lean`)

```lean
def NuLeaf : CTy → Prop
  | .ret A => A.Poly
  | .amp C D => NuLeaf C ∧ NuLeaf D
  | .eff n i q A B fin rc C => EffLeaf (.eff n i q A B fin rc C)
  | .arr A D => A.Cl 0 ∧ NuLeaf D
  | .all _ _ D => NuLeaf D                       -- new
  | _ => False

def instT (S : VTy) : CTy → CTy
  | .ret A => .ret (VTy.inst S A)
  | .amp C D => .amp (instT S C) (instT S D)
  | .eff n i q A B fin rc C => .eff n i q A B fin rc (instT S C)
  | .arr A C => .arr A (instT S C)
  | .all x b C => .all x b (instT S C)           -- new
  | C => C

/-- `x` is bound by a `∀` of an observation tree. -/
def LeafBinds (x : LifeVar) : CTy → Prop
  | .amp C D => LeafBinds x C ∨ LeafBinds x D
  | .arr _ D => LeafBinds x D
  | .all y _ D => y = x ∨ LeafBinds x D
  | _ => False

/-- The shape of a positive body (read by `cC`; invariant under `CTyEq`). -/
def NuShape : CTy → Prop
  | .amp C D => NuLeaf C ∧ NuLeaf D
  | _ => False

/-- **Positivity**: the shape, and no leaf binder free in the body (so `instT` under a `∀` leaf
does not capture). -/
def NuOk (C : CTy) : Prop := C.NuShape ∧ ∀ x, C.LeafBinds x → ¬ CFree x C
```

The argument may mention the bound lifetimes: `∀'x ⊏ @b. Mut 'x A ⊸ D` is `.all x b (.arr (.mut (.var x) A) D)`,
and `.mut (.var x) A` is `Cl 0` whenever `A` is.

**Why freshness is needed.** `instT` puts `U(νX. C)` under the leaf's `∀'x`. If `'x` is also free in
`C`, for instance `C = (∀'x. F(U X)) & F(Imm 'x 1)`, the substitution captures it: the unrolling reads
the rest at `α`, while `νX. C` reads it at `δ('x)`. `cB_unroll` uses freshness at exactly one step
(Check 4). I have not shown in Lean that `cC_nu_iff` fails without it; that obstruction is not
verified. Written types are fresh by construction: `elabC` names a binder `E.Δn.freshVar`, and the
body's free lifetimes are in `E.Δn`.

**Why `NuShape` is split out.** `cC`'s `nu` clause is guarded by its body's positivity, and
`cC_tyEq_aux` needs that guard to be `CTyEq`-invariant (`CTyEq.nuOk_iff`, `Core/RelationFacts.lean`).
`CTyEq` relates `∀` binders semantically, so a `CTyEq` partner can rename a leaf binder onto a free
variable. Freshness is syntactic and is not invariant. The guard in `cC` therefore becomes
`C.NuShape`, and the rules (`nuIn`, `nuOut`, `unfoldN`) keep `hC : C.NuOk` and get freshness through
it. This changes one clause of `cC` at `ν`: the guard is weakened from `NuOk` to `NuShape`. That is a
statement change at the `ν`/`cB` level only (option D1 in §9).

### 2.2 `cB` at a `∀` leaf (`Core/Relation.lean`)

`cB` copies `cC`'s `∀` clause:

```lean
  | η, .all x c D, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cB η D ls (δ.extend x α) (.app e (.val .unit))) ρ
```

and keeps `cC`'s `⊸` clause at an argument that mentions bound lifetimes. Unchanged:

```lean
  | η, .arr A D, ls, δ, e => fun ρ =>
      ∀ v, (vCE none true A ls δ v ─⋆ cB η D ls δ (.app e (.val v))) ρ
```

Here `δ` is already `δ[x ↦ α]` under the `∀`, so `Mut 'x Buf` is read at `α`, exactly as `cC` reads
`∀'x ⊏ c. Mut 'x A ⊸ C`.

**The rest under a `∀` is read at the candidate, which does not depend on `δ`.** `nuP R` ignores the
lifetime substitution (`vCE … (.tvar n) … = tEnvP η n …`). So `CPred` stays at a fixed `δ`, as its
docstring says, and the `∀` changes only the `δ` at which the leaf's other types are read. The
docstring of `CPred` ("`νX. C` binds no lifetime, so its unfolding never changes `δ`") becomes "the
candidate is read at no lifetime; a `∀` leaf extends `δ` for the leaf's own types only".

Checks run (Check 4, prototype `cB2`/`instT2`/`NuLeaf2` beside the library):

- `cB2_mono`: the `∀` case is the `⊸` case with a pure antecedent. Proved.
- `cB2_unroll`: proved for `.ret`, `.amp`, `.arr` and `.all` with the candidate at `δ₀` and the tree
  read at `δ` agreeing on `CFree C` (`vCE_nuEnv_at`, from `cC_congr` and `vCE_nuEnv`). At `.all` the
  agreement passes to `δ[x ↦ α]` by `¬ CFree x C`. The effect leaf is excluded in the prototype by
  `EffFree`; its library case is today's proof with `vCE_nuEnv_at` in place of `vCE_nuEnv`.
- `node_all_ok` (Check 5): proved, the `unfold` side at a `∀` leaf over today's trees. The node term is
  `⊸`'s with argument `()` (`nodeV (.arr .unit D)`, since `Λ` is `λ_`). The candidate at `δ` equals the
  candidate at `δ[x ↦ α]` when `x ∉ VFree S` (`candN_congr`, from `vC_congr`), and then today's
  `node_ok` at `δ[x ↦ α]` closes it, the effect leaf included.
- `vCE_poly_ty` (Check 6): proved. At a polynomial type, the environment's *type* for `X` is never
  read, only its candidate. It is the route for `cB_tyEq` (§3).

## 3. Results to re-prove, file by file

Only `ν`/`cB`-level statements change. Each item is marked (S) where its statement changes and (P)
where only its proof does.

**`Core/Types.lean`.** `NuLeaf`, `instT`, `LeafBinds`, `NuShape`, `NuOk` (§2.1). Every proof of
`NuOk` for a body without `∀` leaves gains a trivial freshness component, because `LeafBinds` is
`False` on such a body: `cloBody_nuOk`, `cloBody_nuOk_higher`, `cloEffBody_nuOk` (`Clo.lean`),
`tickC_nuOk` (`EffPrograms.lean`), `delayBody_nuOk` and the other instance bodies (P; the statements
are unchanged because they say `NuOk`).

**`Core/Relation.lean`.** `cB` gains its `.all` clause. `cC`'s `nu` guard becomes `C.NuShape` (S, D1).

**`Core/NuRel.lean`.**
- `cB_mono`: gains a `.all` case (P).
- `nuF_mono`, `nuRel_out`, `nuRel_roll`, `cC_nu_eq`, `cC_nu_unfold`: hypothesis `NuShape` (S: weaker).
- `vCE_nuEnv_at`: new.
- `cB_unroll` (S): generalised to the candidate at `δ₀`, the tree at `δ` agreeing on `CFree C`, and
  leaf binders not free in `C`. Today's statement is the instance `δ₀ = δ`.
- `effRetE_unroll`: the same generalisation (S).
- `effTab_instT`, `CTy.divAt_instT` (`DivWp.lean`): gain a `.all` case (P).
- `cC_nu_iff`: keeps `hC : C.NuOk` and uses its freshness (P).

**`Core/RelationFacts.lean`.**
- `cB_congr`: gains a `.all` case. `EnvAgree` passes to `δᵢ[x ↦ α]` pointwise (P).
- `cB_tyEq` (S: its environment hypothesis). At `.all` it needs `EnvEq η η' (δ[x ↦ α]) (δ'[x' ↦ α])`.
  For `nuEnv` that is `TyEq (U(νX. C)) (δ[x ↦ α]) (U(νX. C')) (δ'[x' ↦ α])`, and it can fail when `x'`
  is free in `C'`. The route: by `vCE_poly_ty` (with `effRetE`, `cB` lifted to trees), `cB` at a
  `NuLeaf` tree is unchanged when the environment's type for `X` is replaced by `1`. `TyEq 1 _ 1 _`
  holds at every pair of substitutions, so `cB_tyEq` runs at the replaced environments with
  `EnvEq` at all pairs. This needs two new lemmas (`cB_nuEnv_ty`, `effRetE_nuEnv_ty`).
- `cC_tyEq_aux`'s `nu` case: uses `CTyEq.nuShape_iff` in place of `nuOk_iff` (P).
- `CTyEq.nuLeaf_iff`: gains a `.all` case from the semantic `∀` clause of `CTyEq` (P).
- `CTyEq.nuOk_iff`: replaced by `CTyEq.nuShape_iff`.

**`Core/Computation.lean`.**
- `sSB`: gains `sS`'s `.all` clause (S: definition).
- `cB_iff_stacks`, `cB_step`, `cB_bind`: gain `.all` cases, copied from `cC_iff_stacks`, `cC_step`
  and `cC_bind` (P).
- `sS`'s `nu` clause and `cC_iff_stacks` at `nu`: guard `NuShape` (P).

**`Core/Nu.lean`.**
- `nodeV`: gains `.all x b D => nodeV (.arr .unit D)`'s term over `nodeV D`.
- `nodeV_closed`, `nodeV_all_steps`: new cases or lemmas.
- `candN_congr`: new.
- `node_ok` (S): hypothesis `∀ x, D.LeafBinds x → ¬ VFree x S`. Its `.all` case is `node_all_ok`.
- `candN_post` (S): the same hypothesis on `C`.
- `unfold_compatX` (S): the same hypothesis.
- `nuIn_compatX`, `nuOut_compatX`: unchanged.

**`Core/Fundamental.lean` and the other copies of the rules.** `unfoldN` gains the premise
`hS : ∀ x, C.LeafBinds x → ¬ VFree x S`, which is decidable. The copies are `CDerivesAt`
(`Tied.lean`), `CDerivesP` (`PinDerives.lean`), `TDerivesAt`/`TDerivesP` (`Frontend/Check/TDerives.lean`)
and their erasure lemmas. Each existing use of `unfoldN` (78 mentions) discharges it with
`fun _ h => h.elim` at a body without `∀` leaves. `fundamentalC`, `adequacyC`, `adequacyD`,
`resourceSafety`, `fundamentalC_pin` and `adequacyC_pin` keep their statements.

**`Core/DelayApprox.lean`, `Core/DivReify.lean`.** These unfold `cB` at fixed bodies with no `∀`.
They are checked to still elaborate (P).

**Observable view and consume.** `vC_obs_clo`, `immReborrow_clo` and `obs_transfer_cloBox` read
`U` as `True` at `b = false` and do not look at the body. `Consumable.nu` takes
`(amp C (.ret R)).NuOk` and runs `close` (`π₂`) through `nuOut`, which gets freshness from `hC`. No
statement changes. The implicit `close` of a body with `∀` leaves is covered by the same proof. The
new program in §4 uses it (P).

**`Frontend/Check/Decide.lean`.** `nuLeafB` gains `.all`. `nuOkB` gains freshness through
`cfreeB`, plus `leafBindsB`. `nuLeafB_sound/complete`, `nuOkB_sound/complete` extend (P). The
checker's `unfold[C, S]` decides `hS` with `vfreeB`.

**`Frontend/Check/Elab.lean`.** The `nu` error message names `forall 'x < @b.` leaves.

**`Backend2/Convert.lean`.** `LCTy` erases `∀` (`ofC`), and `nodeAt` reads the kernel type through
`stripAll`. Whether an `allE` applied to an `unfold`-made observation (not an `allI`) lowers to the
erased call is not checked. It is risk R4.

**Programs, new file `Core/NuBorrowPrograms.lean`.** The closed `fileRead` of §4.3 (narrowed, as
§4.3 records).

**SPEC.** §7's positivity paragraph and §22's "Positivity"/"Relation"/"Coiteration" paragraphs gain
the `∀` leaf and the freshness premise. §22's "Baseline" paragraph is repeated for #808.

**Stretch track (`si-782`, `Core/TreeSemC.lean`).** `SCmp.nu` is generic over a monotone body
`Φ`. The mirror is a body built from `SCmp.all c (fun α => …)` with the candidate outside the
`fun α`. It needs `SCmp.all_le` (pointwise monotonicity, not on the branch) and the same freshness
at the typed interpretation of the body. Not built here.

## 4. The hardest case, kept in

**The case.** The object is used inside a lend of the buffer, and it outlives the lend. Its `read`
takes `Mut 'x Buf`, and the rest it returns must not hold `'x`.

### 4.1 The type

```
File_c ≜ νX. (∀'x ⊏ ⊤. Mut 'x Buf ⊸ F(I32 ⊗ [@c] U X))
           & ((∀'x ⊏ ⊤. Imm 'x Buf ⊸ F([@c] U X)) & F 1)
```

The rest is boxed at `@c`, as `Clo^c` boxes it. **This is a change to the protocol in #769's
comment** (`read : &mut Buf ⊸ F(n ⊗ X)`). `U` has no outlives rule (`VOutlivesR` has no `thunk`
case, and SPEC §22's `clo_not_outlives`), so an unboxed rest can never be returned out of a lend
callback. The lend callback answers `['y] B` (`axWithbor2Ty`), and `[]I` needs `CtxOutlives`. With
`[@c] U X` and `'c` outside the lend, `Δ, 'y ⊏ ⊓Δ ⊢ [@c] U File_c ⊐ 'y` holds by the box rule
(`Δ ⊨ 'y ⊑ @c`). See D2 in §9.

### 4.2 Where typing stops the rest from capturing `'x`

1. **Scoping.** `X` stands for `U(νX. C)`, which is formed outside the leaf's `∀'x`. The freshness
   part of `NuOk` gives `'x ∉ CFree C`, so `[@c] U X` cannot mention `'x`, and `'c ≠ 'x`. Nothing in
   a leaf's result type can say "the rest depends on this call's borrow".
2. **Instantiation.** `allE` at the lend's `'y` gives `D.instLife x (var y)`. The rest's type
   `U(νX. C)` has no free `'x`, so it is unchanged up to `CTyEq`. Risk R3 covers renaming of an inner
   binder.
3. **Leaving the lend.** `withbor2 buf (Λ'y. λm. …)` needs the callback's answer at `['y] B` with
   `¬ VFree 'y B` (`hfree₂`). `B = I32 ⊗ [@c] U File_c`, and `[]I` needs `CtxOutlives Δ' Γ 'y` over
   the rest's slot. A body that returned the rest boxed at the borrow,
   `∀'x. Mut 'x Buf ⊸ F([@x] U X)`, is admitted by `NuOk` (`'x` is bound, not free). After `allE` its
   rest is `[@y] U File`, and that cannot leave the lend: `B` may not mention `'y`, and the unboxed
   `U File` does not outlive `'y`. That object is usable only inside the lend, which is sound.

### 4.3 How the relation proves it

No new borrow reasoning is added. The method call is part of the lend's callback, and `withbor2`'s
compatibility lemma is already proved for every callback of its type. What #808 must supply is that
the method is the computation its type says, at every `α`. That is `cB`'s `∀` clause, `cC`'s
own. At `α ⊏ ⊤` the result is read at `δ[x ↦ α]`: `I32 ⊗ [@c] (nuP R)` is `atLife δ c (box γ …)`
with `γ = δ(c)`, independent of `α` because `c ≠ x`. The rest is in the candidate `R`, which is
read at no lifetime. That `R`-membership does not depend on `α` is the relational form of "the
rest does not capture `'x`". The `[@c]` box then puts the rest's resources in `Res_γ`, and the
existing `withbor2` proof takes the lent cell back at the lend's end.

**Done-when programs** (closed `CDerives` derivations, `adequacyC` at every host, and interpreter
runs). Each is listed with its hardest part.

- `fileRead`: `File_c` built by `unfold` over the state `Ref I32`. `read` adds the state to the
  buffer's cell and `write` stores the buffer into the state. A buffer `Ref I32` is lent `mut` by
  `withbor2` to `read` and given back, then lent `imm` by `withbor1` to `write`, then `close` runs and
  the buffer is freed. The answer reads both. Hardest part: the rest crossing the `withbor2`
  boundary as `[@c] U File_c`.
- `fileTwice`: two reads in one lend (the rest called again inside it), then one after it.
- `fileConsumed`: the object closed by its implicit consume (`Consumable.nu`).

**What is built (narrowed).** The kernel holds one closed program, `fileRead`
(`Core/NuBorrowPrograms.lean`). It is a closed `CDerives` derivation `d_fileReadProg` through
`unfold`, `withbor2` (the `mut` lend, the rest crossing it as `[⊤] U File^⊤`) and `withbor1` (the
`imm` lend), then `close` and `free`, with `adequacyC` at it (`fileReadProg_runs`) and an
interpreter run that reads every step's answer (`fileReadOut_eval`, `(1, 12, 5, 5)`). The object's
bound is `⊤`. Its `read` exchanges the buffer's and the state's contents through the `Mut 'x I32`
(the buffer takes the state's value), and its `write` loads the buffer through the `Imm 'x I32` and
stores it into the state, answering the state's old value plus the loaded one. The state is
replaced by the loaded value, not added to. `fileTwice` and `fileConsumed` are not derived in the
kernel. All three run, with the content arithmetic, as `corpus/nu-file-read.bc`,
`corpus/nu-file-twice.bc` and `corpus/nu-file-consumed.bc`.

## 5. The surface and the checker

No new judgment, no new elaboration, no sugar.

- **Types.** `nu X. (forall 'x < top. mut 'x Buf -o F (i32 * box 'c U X)) & …` already parses and
  elaborates: `elabC`'s `.all` names the binder `E.Δn.freshVar`. Only `nuOkB` refuses it today, so
  extending `nuLeafB`/`nuOkB` (§3) is the checker change.
- **A call with `&mut buf`** is the existing lend block plus the existing lifetime instantiation:

  ```
  borrow mut buf { 'w, m -> file_read(f, m) }
  fn file_read<'a, 'c>(f: box 'c File<'c>, b: mut 'a Buf) -> i32 * box 'c File<'c> =
    g <- return (unbox f); (nu_out (force g)).1['a] b
  ```

  `.inst` (`Checker.lean`, `rAllE`) is the kernel's `allE`. A call site infers `'a` as any call of a
  lifetime-polymorphic `fn` does (`clo-counter.bc`'s `twice(m)`). The library functions belong to
  #769, not to this unit. The corpus program for #808 writes the `inst` directly.
- **One typing judgment.** The new premise on `unfoldN` is a premise of the existing rule in every
  copy. `scripts/check-judgments.sh` is unaffected.

## 6. Risks, ranked

| # | risk | check | estimate |
|---|---|---|---|
| R1 | `cB_tyEq` at `.all`: a `CTyEq` partner's binder is not fresh, so `EnvEq` fails under the extension | `vCE_poly_ty` proved (Check 6). The lift to `cB`/`effRetE` and the reworked `cC_tyEq_aux` are not checked. | medium |
| R2 | The guard change `NuOk → NuShape` in `cC` ripples into lemmas that destructure the guard (`Computation.lean` `sS`, `cB_iff_stacks` at `nu`, `Inversions.lean` `unroll_amp`) | grep only. Each is a projection `hC.1`. Not checked. | low |
| R3 | `instLife` (capture-avoiding `applyLSub`) renames an inner leaf binder when the instantiated lifetime is that binder's name, so the rest's type differs syntactically from `U(νX. C)` and the checker's `B` does not match | not checked. `lsubCaptures` renames when the range mentions the binder, even if the domain variable is not free. Written types use `Δ.freshVar` at both the binder and the lend, so a clash needs a nested `∀` in a leaf. | medium for the checker, none for soundness |
| R4 | Backend2 lowers `allE` on an `unfold`-made observation | not checked. `LCTy` erases `∀` and `allIOf` matches only a syntactic `allI`. | medium |
| R5 | `node_ok` with nested `∀` (`∀ ⊸ ∀`, `∀` under `⊸`): `node_all_ok` was checked only over today's trees | Check 5 covers one `∀` over any of today's trees, the effect leaf included. Nesting is the same candidate rewrite inside the induction. Not checked. | low |
| R6 | `unfoldN`'s new premise breaks existing derivations (78 mentions) | not checked. Each discharge is `fun _ h => h.elim`. | low (volume only) |
| R7 | `adequacyD`, or the effect relation at an effect leaf under `∀` (`effTab` at `δ[x ↦ α]` with operation types mentioning `'x`) | Check 5 covers `node_ok` at an effect leaf under `∀` through today's lemma. The relation's case is not checked separately. | low |

**Size.** Core: about 450–600 lines changed or added (`Types` 40, `Relation` 10, `NuRel` 70,
`RelationFacts` 120, `Computation` 70, `Nu` 70, rule copies and call sites 100). Programs: 300–450
(`CloPrograms.lean` is 893 for seven). Frontend: 80. Backend2: 0–80 (R4). SPEC: 40. That is about
1,000–1,300 lines in all.

## 7. NOT in this unit

- A second `ν` former, or a separate "object" former.
- A new judgment, a new judgment index, or a new `CDerives` constructor. (`unfoldN` gains a
  premise; `nuIn` and `nuOut` keep theirs.)
- An elaborator workaround, such as threading the buffer through the state or handing an owned
  buffer back (#769's D10 (b)).
- Special-casing `File`, `Buf`, `Mut` or `Imm` in `NuLeaf`, `cB` or the checker. The leaf is
  `∀'x ⊏ @b. D` for every tree `D`, and the argument is any `Cl 0` type.
- Weakening `fundamentalC`, or a hypothesis on it, on `adequacyC`, on `adequacyD` or on
  `resourceSafety`.
- `X` in an argument (removing `Cl 0`).
- `File`, `lib/` functions, or #769's effect.

**Tempting shortcuts (each a STOP).**

- Making `cB` answer `True` at `.all` and leaving `NuLeaf` closed.
- Proving `cB_unroll` only at `δ₀ = δ` and assuming the extension away.
- Putting freshness on the `CTyEq` partner by a hypothesis on `cC_tyEq`.
- Admitting only `∀` leaves whose argument is literally `Mut 'x _` or `Imm 'x _`.

## 8. Kill criterion and fallback

**Stop and report** if any of these happens:

1. Any of `fundamentalC`, `adequacyC`, `adequacyD`, `resourceSafety` or `fundamentalC_pin` needs a
   changed statement or a new hypothesis.
2. R1's route fails. That is: `cB` at a `NuLeaf` tree depends on the environment's type for `X` in a
   way `vCE_poly_ty` does not lift over, and `cC_tyEq_aux` cannot be closed without freshness of the
   partner.
3. The freshness premise refuses a type that `elabC` produces from a written `nu`, and the checker
   cannot decide it.
4. Core work exceeds about 1,200 lines (twice the estimate).

**Fallback (a restriction the checker decides).** A `∀` leaf must be `∀'x ⊏ @b. A ⊸ D` with `'x` not
free in `D`. The borrow lifetime may occur in the argument only, never in the answer.
`cB_unroll`'s `∀` case then reads `D` at `δ` by `cC_congr` on `D`, so the extension never reaches the
rest's type. Freshness is still needed for `instT`, but `cB_tyEq`'s `∀` case also reduces to
`cC_congr`. It still admits `read`/`write`/`feed`. It refuses methods whose answer borrows from the
argument (`∀'x. Imm 'x Buf ⊸ F(Imm 'x I32 ⊗ …)`).

## 9. Design choices for the user

- **D1. Where freshness lives.**
  - (a) Recommended: inside `NuOk`, with `cC`'s guard weakened to `NuShape`. Only `unfoldN` gains a
    premise.
  - (b) As premises of `nuIn`, `nuOut` and `unfoldN`. `cC` is unchanged, but there are about 260 more
    call-site edits.
  - (c) A capture-avoiding `instT` that renames leaf binders, as `applyLSub` does. No premise is
    added, but `instT` needs a size measure, and `cB_unroll` passes through `CTyEq.applyLSub`.
- **D2. The rest's box.** Change #769's `File` to `[@c] U X` results, the `Clo` pattern (§4.1).
  The alternative, an outlives rule for `U`, is unsound in general because a thunk captures
  resources at any lifetime. It is not proposed.
- **D3. The method quantifier's bound.** `∀'x ⊏ ⊤` lets any lend call the method. `∀'x ⊏ @c` ties
  calls to borrows inside the object's own bound. Both are admitted. The choice is #769's.
