# ProbeD1: R1 and `binder0`'s monotonicity — the design

This unit takes the four things CHECKPOINT's "What remains for tier 2" lists at `binder0`, the
placement with the most proved:

1. **R1**: the thaw at a slot of `μ` or `fam` type outside a `Mut` or `Imm` payload, and with it the
   `U` side of statement 0 at every context. The route is the brief's, as `BINDER.md` §5.4 and
   `GAP.md` §4 give it: W reads `μ` and `fam` itself, and the thaw at such a slot is by induction on
   the data.
2. **`binder0`'s own monotonicity**: `MonoV`, `MonoG`, `MonoOwnG`, not derived since statement 0.
3. **The three obligations the freeze-binder unit left**: `RetainedPay` at every row that
   introduces a `Mut` or `Imm` value, at every payload type, the read-outs through a view and the
   slice elements included; `KeepsT` at the share, in the form `RelendJ` consumes; `OuterBelowTop`
   at every lend, the 6.64 and 6.65 lends of the arising set included.
4. **Statement 0 and OQ-8 reconsidered** at the revised relation.

The statements are in `ProbeD1/R1.lean`: definitions and `def … : Prop` only, no proofs. It is
imported by `ProbeD1.lean`, and `lake build ProbeD1` builds it with no warning. The proof files are
named in §5, and the build's outcome is §8. One definition outside `R1.lean` changes, in ProbeD1's
draft arising set: `LendMutI` and `LendImmI` (`Binder.lean`) gain the consequence `α < ⊤` of [TR]
6.64's and 6.65's H4 (§3.1). `outerBelowTopArises` reads the new field, and every other `ArisesI`
proof builds unchanged. Nothing in `Core/`,
`Paper/`, `Restrat/`, `GhostEnd/` or any printed definition changes. The one change to a relation is
to ProbeD1's draft relation: `vRLM` replaces `vRLJ` as the one draft relation at W, as `vRLJ`
replaced `vRLI` (§1.2). `vRLJ` stays as the statement it was, and every result proved about it stays
a result about it.

**Status words**, as in `BINDER.md` and `GAP.md`: *proved* is a theorem; *refuted* a theorem proving
the negation; *not derived* means neither, with no obstruction verified; *not attempted* means no
proof was tried; *[unchecked]* marks a claim argued in prose and not in Lean; *[checked outside the
build]* marks a step the designer checked against the built ProbeD1 in a scratch file that is not
committed, which the builder proves again in the build. Reading tags: *[read]* (I read the source),
*[relayed]*, *[unverified]*.

---

## 0. On one page

- **R1, by the brief's planned route** (§1.1). `vRLJ`'s last clause hands a slot of `μ`, `fam` or
  type-variable type to Core's `vC` whole (`BinderJ.lean:95`). A thunk inside is then read by Core's
  `U` clause and Core's `ℕ`-`∀`. That `∀` reads adjacency (`coreAllAdjacent`) and is not invariant
  under an embedding that opens the room (`coreAllNotNatural`): both proved, both about Core's `∀`.
  I have not derived the `vRLJ` thaw at a `μ` slot and have not verified that any obstruction is
  real (`NotMuSlotThawCore` stated, not attempted). The brief's route is for W to read `μ` and `fam`
  itself; the target is `Statement0UFullM`, `Statement0UFullJ`'s statement at that relation.
- **The revised relation `vRLM`** (§1.2) is `vRLJ` with Core's three clauses (`vCE`'s `tvar`, `μ`,
  `fam`, `Core/Relation.lean:143–150`) read at W's formers, and a type-variable environment threaded
  through W's formers as `vCE` threads it. It elaborates by structural recursion, mutually with
  `cRLM` [checked: `R1.lean` builds]. At a type with no `μ`, `fam` or type variable outside a
  borrow payload it is `vRLJ` (`RelMAgreesJ`). So the configurations of `BINDER.md` and `GAP.md`,
  all at such types, carry over, and so does every `vRLJ` result stated at such a type or at a
  `Mut` or `Imm` leaf. The `vRLJ` results quantified over every type or every context do not;
  §6's carry-over table lists them as not redone at `vRLM`. `[L]`'s elements become W leaves, so
  the slice rows owe what they did not owe before (§1.2, §3.2). A `ν` computation is still read
  by Core's `cC` whole: this unit does not need W to read `ν` (§1.2).
- **The thaw at every type** (§1.4) is by structural recursion on the type, the environment
  generalised (`RelendMValueE`): at `μ` by the fixed point's own induction, rolled back at each
  instantiated index; at `fam` slot by slot; at a variable by the environment's hypothesis; every
  other case is `GapRows.lean`'s, the leaves read at their closed types. Then `Statement0UFullM
  binder0`. Expected to go through.
- **`binder0`'s monotonicity meets the guard** (§2). The route at `U` reduces to carrying a
  computation along a push at an instantiated index. At `⊸` that needs an argument related at the
  pushed stack to be read back at the old one, under the old stack's guard. DESIGN §4.3 named this
  step. Made concrete: the guard's first conjunct (every cell at or above the innermost lend) is a
  box at `↓head`. So the closure `λg. return g` at `U(F 1) ⊸ F ([@'1] U(F 1))`, with `'1` read at
  `↓head`, is a `binder0` value at the stack at every instantiation [checked outside the build].
  After the own lend pushes a lend below `'1`, an argument holding the new view breaks the box. The
  configuration (`gd…`, `R1.lean`) meets `SemSM`'s whole index at the judgement the `∀I` row reads
  (`GdIndex`).
  - **It pins a scope; it is not item 2's result.** Expected: the unrestricted `MonoOwnGM`,
    `MonoGM` and `MonoVM` refuted at `binder0` (`NotMonoOwnGM0`). Two reasons put the configuration
    outside the arising set, neither yet a theorem about that set: its closure is no Core value
    (`GdNotCore`; the glue to `ArisesVI` is not written), and its index fails the record invariant
    (`GdNotRecsInsideOwn`; `RecsInsideOwnArises` is not attempted), because `MonoOwnGM` keeps the
    list across a 6.64 own lend. These are facts about our statements, not obstructions.
  - **The target is the consumer.** `MonoOwnGM`'s only consumer at `binder0` is `[allI]`, restated
    at `SemSM` (`AllIRowM`). `NotMonoOwnGM0` does not refute it. Two things are planned in Lean
    (§2.6):
    - the row itself at `gd`, at a derivable body that exercises the closure (`gdM`): expected to
      meet the conclusion there (`GdAllIHoldsAtM`), so `MonoOwnGM` was the wrong lemma at `gd`;
    - the route at a restricted domain, each live slot also a Core value (`gRLMC`, `SemSMC`,
      `MonoOwnGMC`, `AllIRowMC`). `gd` falls outside it (`GdCtxNotCore`). The attempt at `⊸` is
      expected to stop at W inside Core at a `U` argument (`WInsideCoreM`), OQ-58's question at a
      stack [unchecked]. The arising form (`MonoOwnGMA`) is stated; the arising set has no
      transition from which the `∀I` row could supply its restriction at the pushed stack.
  - The halves `binder0` carries by construction (`MonoExtM`, `MonoOwnGUFreeM`) are the `none`
    instances of statements under an environment (`MonoExtME`, `MonoOwnUFreeME`).
- **The three obligations** (§3).
  - `OuterBelowTop`: `LendMutI` and `LendImmI` now carry H4's consequence `α < ⊤`, and
    `OuterBelowTopArises` follows by induction on `ArisesI`. Every arising check then runs over
    configurations that meet `SemSM`'s index on this point.
  - `RetainedPay` row by row, at every payload type: the lend's view, the read-outs through a `Mut`
    view (`withswap`) and an `Imm` view (`withload`, `foldImm`), `∀E` at an instance with no join,
    and the transports. The route is `BINDER.md` §11's, made precise. Under the guard a leaf no
    entry lends is a cell strictly above the outermost lend (the table's second conjunct), so a
    retained cell, made outside the frozen computation [unchecked: historical]; its payload type
    reads the variables bound then, which `SubOutside` reads above every lend. Expected:
    - proved at the view, the transports, `∀E` at a variable, `⊤` or a meet, and the read-out's
      nested `Imm` leaves (their coherence record's reading, by `RecsOutside` and
      `RelAboveOfTagged`);
    - at a nested `Mut` leaf of a bound view's payload (`withswap`), reduced through the view's
      `CohS`: `TyEq T s e.T s` is positional, so the leaf's payload type reads, where it has no
      join, what the matching leaf of the entry's payload type reads (`PayLeavesOfTyEq`,
      `RetainedPayLoadMutBound`). The expected stop is the leftover, `EntryPayLeaves`: the entry's
      payload type's leaves read only external lifetimes. `StackJ` lets `e.T` read the stack's
      variables, so the index does not carry it;
    - not covered at a join (`⊔`). At `∀E`, `⟦'v ⊔ 'w⟧` external says nothing of the shorter of the
      two; in a payload type, `TyEq` pins a join only as a whole.

    The arising check of the stop is `InternalLeafArises`'s second disjunct,
    `InternalPayloadArises`'s question one level down. `InternalPayloadArises`'s own configuration
    refutes no read-out row (`ReadOutAtInternalPayload`). If the stop is reached, the variant leaf
    stated in `R1.lean` (`mutLeafP`, `immLeafP`) has its two costs checked in Lean (`ThawLeafP`,
    `VwPayLeaves`). Each read-out row's added hypotheses are planned as met at a one-entry stack
    (`RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet`). Every line of §3.2's table is
    [unchecked] until its row is stated and proved at `vRLM`.
  - **The slice rows are not covered at W**, separately from `RetainedPay`. A slice borrow's
    callback runs at its own lend's pushed stack, where no family of two or more elements meets the
    guard (`SliceGuardFails`), so the callback's clause says nothing about the run. The missing
    object is a stack entry lending a range of places. `RetainedPaySliceRow` holds vacuously at
    every count and is not counted toward `RetainedPay` at the rows.
  - `KeepsT` at the share: `ShareKeepsT` is stated in the form `RelendJ` consumes. It follows from
    `ResumeKeepsT` (the two worlds' tags), `RelAboveOfTagged` and the bridge `ExtKeepsTInst`. Its
    premise `FramesKept` is what statement 2's resume composite owes, so the item is reduced, not
    discharged. `RelFramesNotEnded` shows that the frames the premise names are not ghost-ended;
    `ShareKeepsTMet` meets the premise at a ghost-ended entry re-opened at a moved lifetime.
- **Statement 0 and OQ-8** (§4). Expected status at `binder0` at `vRLM`:
  - the facts beside monotonicity (`Statement0MBesideMono0`): the shared lemmas at the revised
    futures (`FutPartI`; `NilSoundRetM` through `VRLMDataE`), `ForceRowM`, the callbacks and
    `Statement0UFullM`, to prove;
  - the three unrestricted monotonicity statements refuted at `gd` (`MonoUnrestrictedRefuted0`): a
    fact about those statements, not `binder0`'s status;
  - statement 0 read at its consumers (`Statement0MAtConsumers0`, with `AllIRowM .binder0` and
    `MonoExtM .binder0`): not derived, the open item being `AllIRowM .binder0`.

  `KeepsT` at the share is reduced, not discharged, and `RetainedPay` at the read-outs stops at
  `EntryPayLeaves` if as expected. `cbpv` and `binder` still owe `BINDER.md` §5.6's list. OQ-8
  stays undecided unless a refutation passes DESIGN §11.

---

## 1. Item 1 — R1: W reads `μ` and `fam` itself

### 1.1 Why the route reads `μ` and `fam` at W

- **What `vRLJ` does at `μ` and `fam`.** Its last clause is `| σ, δ, A, αs, ls, v => vC true A ls
  (extS δ σ αs) v` (`BinderJ.lean:95`) [read]. At `μX. A`, `fam L` and a type variable the slot is
  read by Core's `vCE` whole: the least fixed point over Core's clauses (`Core/Relation.lean:144`),
  a thunk inside at Core's `U` clause (`:127`, `∀ ls', Ext ls ls' ρ → cC C ls' δ (forceE C (.val v))
  ρ`), whose `∀` is Core's `ℕ`-`∀` (`:161`).
- **What is proved about Core's `∀`, and what is not.** Core's `∀` reads adjacency: it holds at a
  cell adjacent to `⊤` (`coreAllAdjacent`) and fails once an embedding opens the room
  (`coreAllNotNatural`). Both are proved (`GAP.md` §3c), and both are about Core's `∀` under an
  embedding. The `vRLJ` thaw at a `μ` slot is a different statement. `GAP.md` §4 states its
  expected failure at the configuration `MuSlotIndex` (`NotMuSlotThawCore`), not attempted. I have
  not derived the `vRLJ` thaw at a `μ` slot and have not verified that any obstruction is real.
  Typing reaches a `μ` slot inside a lend (`ThawFreeScope`, stated, not attempted).
- **So this unit takes the brief's planned route.** W reads `μ` and `fam` itself, and the target is
  `Statement0UFullJ`'s statement at that relation, `Statement0UFullM`. A `U` inside a `μ` is then
  W's `U` clause, which reads every cut below the stack's cut by construction (`wU_allPosJ`, one
  direction). `Statement0UFullJ` at `vRLJ` is not attempted.

### 1.2 The revised relation `vRLM`

The block, verbatim from `R1.lean`:

```lean
structure WEnt where
  ty : VTy
  P : Val → WProp

def wEnv : Option (Nat → WEnt) → Nat → WEnt
  | none => fun n => ⟨.tvar n, fun _ _ => False⟩
  | some η => η

def wEnvP : Option (Nat → WEnt) → Nat → Val → WProp
  | none, _, _ => fun _ => False
  | some η, n, v => (η n).P v

def wClose : Option (Nat → WEnt) → VTy → VTy
  | none, A => A
  | some η, A => A.subst (fun n => (η n).ty)

mutual
def vRLM (p : Placement) :
    Option (Nat → WEnt) → LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | _, σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLM p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendJ δ σ (fun δ' αs' ls' => cRLM p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  | η, σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLM p η σ δ A αs ls v₁ ⋆ vRLM p η σ δ B αs ls v₂
  | η, σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLM p η σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLM p η σ δ B αs ls v₂)
  | η, σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLM p η σ δ A αs ls v ρ
  | η, σ, δ, .box a A, αs, ls, v =>
      atLife (extS δ σ αs) a fun α => box α (vRLM p η σ δ A αs ls v)
  | η, σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLM p η σ δ A αs ls v'
  | η, σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a (wClose η T)) ls (extS δ σ αs) v ρ ∧
        CohS σ αs (extS δ σ αs) (.mut a (wClose η T)) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) (wClose η T) v
  | η, σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a (wClose η T)) ls (extS δ σ αs) v ρ ∧
        CohS σ αs (extS δ σ αs) (.imm a (wClose η T)) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) (wClose η T) v
  | η, _, _, .tvar n, _, _, v => wEnvP η n v
  | η, σ, δ, .mu A, αs, ls, v => fun ρ => VTy.NoMut 0 A ∧ (wClose η (.mu A)).Cl 0 ∧
      ∀ P : Val → WProp,
        (∀ v' ρ', vRLM p (some (VTy.scons ⟨wClose η (.mu A), P⟩ (wEnv η))) σ δ A αs ls v' ρ' →
          P v' ρ') → P v ρ
  | η, σ, δ, .fam L, αs, ls, v => ex fun ℓ => ex fun c =>
      ⌜v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31⌝ ⋆
        sepRange (fun m => vRLM p η σ δ L αs ls (.loc m)) ℓ c.toNat
  | _, σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ _ A => A
def cRLM (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  …   -- cRLJ's clauses verbatim, the answers at `vRLM p none`, effRetJ → effRetM
end
```

`gSepRLM`, `gRLM` and `SemSM` are `gSepRLJ`, `gRLJ` and `SemSJ` with `vRLM p none` and `cRLM`.

**Clause by clause.**

| type | Core's `vCE` | `vRLJ` | `vRLM` |
|---|---|---|---|
| `U C` | `∀ ls', Ext → cC` | `RelendJ` (binder0) / `RelendU` | `vRLJ`'s, the body at `cRLM`; reads no environment |
| `⊗`, `⊕`, `!`, `[@a]`, `Ref` | componentwise, environment threaded | componentwise at `vRLJ` | componentwise, environment threaded |
| `Mut a T`, `Imm a T` | Core's leaf, payload at `η` | `vC` ∧ `CohS` ∧ `RetainedPay` at `T` | the same at `wClose η T` |
| `tvar n` | `tEnvP η n` | `vC` (empty) | `wEnvP η n` |
| `μX. A` | `NoMut 0 A ∧ Cl ∧ ⋂{P ∣ A[P/X] ⊆ P}` over `(b, ls, v)` | `vC` whole | `NoMut 0 A ∧ Cl ∧ ⋂{P ∣ A[P/X] ⊆ P}` over `v`, at W's clauses |
| `[L]` | `sepRange` of `vCE L` | `vC` whole | `sepRange` of `vRLM L` |
| data leaves | Core's | `vC` | `vC` |

**Design points.**
- **The candidate is a predicate on the value at the `μ`'s index** (`P : Val → WProp`). Core's is
  joint over the mode and the list (`Bool → List SRec → Val → WProp`) because Core's `Imm` clause
  reads its payload at the observable mode and the shorter list `ls₀`. In `vRLM` the variable occurs
  at W positions only through formers that keep the index (`⊗`, `⊕`, `!`, `[@a]`, `Ref`, `[L]`, a
  nested `μ`): never under `U` (`VTy.subst` leaves `U C` alone, `Core/Types.lean:238`), never in a
  `Mut` payload (`NoMut`), and in an `Imm` payload only through the leaf's closed type. A
  consequence: a statement that moves a `μ` value to another index (another list, another stack,
  Core's joint candidate) is an induction on the data whose hypothesis is on the environment, as
  the thaw's is (`EnvThaws`). §2.4 and §4.1 state those (`MonoExtME`, `MonoOwnUFreeME`, `VRLMDataE`).
- **A leaf reads its type closed by the environment** (`wClose`, Core's `tClose`). At an `Imm`
  payload that mentions `X` the payload is read by Core at `T[μX. A/X]`, Core's `μ` at the
  observable view. That is what `vRLJ` does at every `Imm` payload: the payload is Core's, handled
  by `TyEq` at a bound place and by `PayExt` at a retained one (`GAP.md` §2.3). R1 is about `μ` and
  `fam` *slots*, outside a payload, which is the exclusion `ThawFreeK` leaves.
- **`[L]`'s elements are W leaves, and the slice rows' obligations change with it.** A
  `[Mut a A]` slot (a slice, `VTy.sliceMut`) now reads `CohS` and `RetainedPay` at each element,
  which `vRLJ` (Core's `fam`) did not. The thaw needs it at a `fam` slot: an element at a lent place
  is a view (`CohS`), and one at a retained place reads external lifetimes (`RetainedPay`).
  - **What changes.** Under `vRLJ` the family a slice row hands its callback (`sliceBorrowM`,
    `sliceBorrowI`, their `U` forms), and the families the element operations take and give
    (`sliceGetM`, `sliceSplitM`, `sliceReplaceM`, `sliceSwapM`, `sliceLenM`, `arrGet`, …), were
    read by Core's `fam` and owed neither conjunct. Under `vRLM` each element owes both.
  - **Why neither is owed in practice today.** Inside a lend, no slice argument of two elements
    meets W's guard.
    - At an own-lend push (`SliceGuardFails`, stated, cheap): the table's second conjunct puts
      every top-level cell at a place no entry lends strictly above the outermost lend, the
      elements are cells at the own lend's lifetime, and one entry lends one place.
    - Without a push, the table's first conjunct puts every cell at or above the innermost lend,
      and the elements, made fresh below it, are not.

    A slice borrow's callback runs at its own lend's pushed stack wherever the row is used, the
    empty stack included. So a slice borrow at a family of two or more elements is outside W at
    `vRLJ` and at `vRLM` alike, at every stack: the callback's clause is vacuous under the guard,
    and nothing is known of its run. This is a gap in W's coverage of a typed row, not a
    `RetainedPay` result. `RetainedPaySliceRow` holds vacuously at every count: at two or more
    elements by `SliceGuardFails`; at one element, a cell at the own lend's lifetime at a place no
    entry lends fails the table's second conjunct, and at the own lend's place `RetainedPay` is
    vacuous (`innerAt`). It is not counted toward item 3. The element operations at the empty stack
    owe no more at `vRLM` than at `vRLJ`: the guard reads nothing, and `RetainedPay` is vacuous
    (`cutOf [] = none`).
  - **The missing object** is a stack entry lending a range of places. With it the elements are
    bound: `RetainedPay` is vacuous there, and `CohS` reads the range entry. Recorded in §3.2, §6
    and Unresolved, status *not attempted*.
  - **Neither program uses a slice** [read]. `genSelf`'s term (`Targets/I/Programs.lean:199`,
    with `lendCell` `:82`, `dupFlag` `:63`, `readThrough` `:68`) uses `alloc'`, `withborUE dFlag`
    at a `Ref Flag`, `withswap`, `forget` and `free'`, and no array or slice constant or `fam`
    type. `reconB′`'s term is not built; its shape (DESIGN.md §1, §9.2) uses `withbor` (1) on a
    `Ref Flag` and `withload` at `Flag`.
- **One relation.** `vRLM p none` is W's relation; `gRLM` and `SemSM` read only `none`. The
  environment is the relation's own fixed-point bookkeeping, as Core's `vCE η` is `vC`'s: no clause
  reaches another stack or index by a new means, and no relation is defined beside it. `vRLM`
  replaces `vRLJ` as the one draft relation, the step `BINDER.md` §11.4 took from `vRLI` to `vRLJ`.
- **`ν` is still Core's.** `cRLM`'s `ν` clause hands the computation to Core's `cC` whole, as
  `cRLJ`'s does, so a value a `ν` unfolding gives is read by Core's relation, Core's `U` and
  `ℕ`-`∀` inside: the shape R1 removes at `μ`, left at `ν`. The thaw and `Statement0UFullM` do not
  need it, since W's `U` clause composes instantiations without looking inside its computation
  type, and neither program uses `ν` [read: `genSelf`'s term, `Targets/I/Programs.lean:199`, a
  handler over a lend, no `ν` former; `reconB′`'s shape, DESIGN §1, §9.2]. Whether W should read
  `ν` itself is open for the rows of statements 1–4 (Unresolved).
- **Agreement with `vRLJ`** (`RelMAgreesJ`): at a type with no `μ`, `fam` or type variable outside
  a `Mut` or `Imm` payload, computation types included (`VMuFree`, `CMuFree`; neither looks inside
  a payload, and `CMuFree` counts `ν` as free, `ν` being Core's at both relations),
  `vRLM p none = vRLJ p` and `cRLM p = cRLJ p`. The `Mut` leaf is `rfl` [checked outside the build],
  since `wClose none T = T`; the rest is structural.
  - **What carries over.** The configurations of `BINDER.md` and `GAP.md` (`k`, `q2`, `adjIndex`,
    and `MuSlotIndex`'s closure at `U(adjC)`) and this unit's `gd` configuration are at `VMuFree`
    types. Their refutations and witnesses transfer. So does every `vRLJ` result stated at a
    `VMuFree` type or at one `Mut` or `Imm` leaf, where both relations read Core's leaf with `CohS`
    and `RetainedPay` (`relendJ_mutK`, `relendJ_immK`).
  - **What does not.** The `vRLJ` results quantified over every type or every context (the thaw,
    `ThawInstJ`, the four `U` rows, `wU_allPosJ` at a general `C`) do not transfer. They are redone
    by §1's statements or listed as not redone (§6's carry-over table).

### 1.3 The statements (`R1.lean` §1)

| statement | says |
|---|---|
| `RelMAgreesJ` | `vRLM p none = vRLJ p` at `VMuFree` types, `cRLM p = cRLJ p` at `CMuFree` ones |
| `VRLMMonoAt` | monotone in a variable's candidate where the type has `NoMut` at it (`vCE_mono_at`'s analog) |
| `VRLMRoll` | the body, its variable read at the `μ` itself, is the `μ` (`vC_roll`'s analog) |
| `VRLMUnroll` | the unroll equation at a closed `μ` (`vC_mu_iff`'s analog); optional |
| `EnvThaws η ηf δ σ αs ls` | the environment's types do not depend on the index, and each candidate thaws to the family's |
| `RelendMValueE` | the thaw of a value at every type under a thawing environment |
| `RelendMValue` | the thaw at every type, `η = ηf = none` (`RelendJValueK` without `ThawFreeK`) |
| `CtxRelendableAtM`, `CtxRelendsAllM` | the context's thaw, at every context |
| `ThawInstM` | a `U` value instantiated is a `U` value at the instantiation |
| `ThunkFRowM` … `BangThunkVRowM` | the four `U` rows at `SemSM`, at every context |
| `Statement0UFullM` | their conjunction: `Statement0UFullJ`'s statement at `vRLM` |
| `MuAdjNotVRLM` | `GAP.md` §4's `μ` slot: its closure is no `vRLM` value; optional |
| `MuSlotArises A` | template of the arising check for a counterexample at a `μ` slot |

The two that carry the route:

```lean
def EnvThaws (η : Option (Nat → WEnt)) (ηf : LSub → List Life → List SRec → Option (Nat → WEnt))
    (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) : Prop :=
  (∀ δ' αs' ls' n, (wEnv (ηf δ' αs' ls') n).ty = (wEnv η n).ty) ∧
  ∀ n v ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → wEnvP η n v ρ →
    RelendJ δ σ (fun δ' αs' ls' => wEnvP (ηf δ' αs' ls') n v) αs ls ρ

def RelendMValueE : Prop :=
  ∀ (A : VTy) (η : Option (Nat → WEnt))
    (ηf : LSub → List Life → List SRec → Option (Nat → WEnt))
    (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    EnvThaws η ηf δ σ αs ls → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLM .binder0 η σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLM .binder0 (ηf δ' αs' ls') σ δ' A αs' ls' v) αs ls ρ
```

`EnvThaws` is the induction's hypothesis on the free variables. It is satisfiable: at
`η = ηf _ _ _ = none` both conjuncts hold (`.tvar n`'s type on both sides; `wEnvP none` is
`False`), which is how `RelendMValue` is its corollary.

### 1.4 The route

**The fixed point's facts.**
- `VRLMMonoAt`: by structural recursion on the type, `vCE_mono_at`'s proof (`Core/RelMu.lean:245`)
  at W's clauses. A leaf reads only the entries' types, which agree. At a nested `μ` the
  closure condition is weakened under the antecedent, as there.
- `VRLMRoll`: `vC_roll`'s argument (`Core/RelMu.lean:349`). For `P` closed under the body, the `μ`
  is inside `P` by its own definition, so the body at the `μ` is inside the body at `P`
  (`VRLMMonoAt` at `0`), which is inside `P`.
- `VRLMUnroll` (optional): needs `vRLM`'s substitution lemma, `vCE_subst`'s analog
  (`Core/RelMu.lean:141`). Not read by the thaw. Attempt after §1's other items, and only if a row
  needs `roll`/`unroll` at W.

**`RelendMValueE`, by structural recursion on `A`.** Each case is `GapRows.lean`'s
`relendJ_valueK` case unless named.

| case | proof |
|---|---|
| `U C` | `vRLM` at `U` reads no environment; `relendJ_thunk`'s proof (`BinderRows.lean:956`) at `vRLM`: `instComp`, `ext_inst_comp`, `keepsSComp` |
| `⊗`, `⊕`, `!`, `Ref` | `relendJ_sep`, `relendJ_mono`, `relendJ_emp`, `compS_reassoc`, the guard at parts (`tabAtS_left/right`, `placeViewsL_left/right`) |
| `[@a]` | `vwSW_outlives_inst`, `extS_inst`, `Inst.interp_sub` |
| `Mut a T`, `Imm a T` | the leaf is `vRLJ`'s at `wClose η T` (`rfl`); `relendJ_mutK`, `relendJ_immK` (`GapRows.lean:212`, `:268`) at that type; the conclusion's type is the same by `EnvThaws`' first conjunct (`wClose_congr`) |
| data leaves | `relendJ_emp` |
| `tvar n` | `EnvThaws`' second conjunct |
| `μX. A` | below |
| `[L]` | `relendJ_sepRange`: `sepRange`'s induction on the count with `relendJ_sep` and `relendJ_emp`, each element by the case at `L` |

**The `μ` case.** From `vRLM η (μX. A)` at the old index, its fixed point at the candidate
```
P' := fun v ρ => vRLM η σ δ (.mu A) αs ls v ρ ∧
        (TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
          RelendJ δ σ (fun δ' αs' ls' => vRLM (ηf δ' αs' ls') σ δ' (.mu A) αs' ls' v) αs ls ρ)
```
Its closure under the body at `η₁ := some (VTy.scons ⟨wClose η (μX. A), P'⟩ (wEnv η))`:
- the first conjunct by `VRLMMonoAt` at `0` (from `P'` to its first conjunct) and `VRLMRoll`;
- the second by the induction hypothesis at the body `A`, at `η₁` and
  `ηf₁ δ' αs' ls' := some (VTy.scons ⟨wClose (ηf δ' αs' ls') (μX. A),
  vRLM (ηf δ' αs' ls') σ δ' (.mu A) αs' ls'⟩ (wEnv (ηf δ' αs' ls')))`. `EnvThaws η₁ ηf₁` holds:
  at `0` the types agree by `EnvThaws η ηf`'s first conjunct, and the candidate thaws by `P'`'s
  second conjunct; at `n + 1` it is `EnvThaws η ηf`. Then `relendJ_mono` with `VRLMRoll` at each
  instantiated index (`η := ηf δ' αs' ls'`; its `NoMut` is the `μ` clause's, its `Cl` by the types'
  agreement) turns the body at `ηf₁` into the `μ` at `ηf`.

The induction is on the data: the fixed point's least-ness is what makes `P'` contain the value.
No fuel and no step index.

**The corollaries.**
- `RelendMValue`: `RelendMValueE` at `none`, `fun _ _ _ => none`.
- `relendM_gSep`, `CtxRelendsAllM .binder0`: `relendJ_gSepK`'s proof with `RelendMValue` at every
  slot (no `CtxThawFreeK`).
- `ThawInstM .binder0`: the `U` case.
- The four rows: `thunkF_U_of_thawJ` and `thunkV_U_of_thawJ` (`GapRows.lean:443`, `:470`) at
  `SemSM`, with `guardInst`, `StackOK.inst`, `outerBelowTop_inst`, `stackJInst`, `subDom_inst`,
  `instModels`, `subOutsideInst` as there; `gSepRLJ_persistent` and `gRLJ_dead_cons` at `vRLM`.
  Then `Statement0UFullM .binder0`.
- `MuAdjNotVRLM` (optional, cheap): `muAdjTy = μX. U(adjC)` does not mention `X`, so the `U`
  clause at `U(adjC)` is a candidate closed under the body; a `vRLM` value at `muAdjTy` is one at
  `U(adjC)`, which `adj_not_wU` (`GapRoom.lean:266`) excludes through `RelMAgreesJ`. It shows what
  R1 buys at `GAP.md` §4's configuration: W's `μ` excludes the closure Core's admits by adjacency.

### 1.5 Success, failure, the arising check

- **Success**: `RelMAgreesJ`, `VRLMMonoAt`, `VRLMRoll`, `RelendMValueE`, and `Statement0UFullM
  .binder0` proved. R1 is then closed: the thaw has no guarantee gap left at `binder0`, and the
  `U` rows hold at every context.
- **Failure, of the route**: a case of `RelendMValueE` that does not close. The report names the
  case and the lemma it needs. The likeliest is `VRLMRoll`'s monotonicity at a nested `μ`; Core's
  `vCE_mono_at` is the template.
- **Failure, by a counterexample**: a refutation of `RelendMValue` at a slot of `μ` or `fam` type.
  It counts against the route only with DESIGN §11's check: `MuSlotArises A` at the slot's type and
  the closed derivable program whose run reaches the configuration, exhibited. Otherwise it is a
  fact about our statement.
- None of these is a failure of type (a), (b) or (d). `vRLM` adds no guard beside `TW`, no
  relation family and no quantifier.

---

## 2. Item 2 — `binder0`'s monotonicity

### 2.1 What statement 0 owes, at `vRLM`

Statement 0's `MonoV`, `MonoG` and `MonoOwnG` (`Statement0.lean:103–135`) are stated at W₀ (`vRL`,
`Fut`, `TabAtS`). At the revised relation they read the revised futures (`FutI`, `Binder.lean`), the
revised own lend (`OwnPushI`) and the revised index. In `R1.lean` §2:

```lean
def InsertedFresh (δ : LSub) (ls : List SRec) (αs αs' : List Life) : Prop :=
  RecsOutside αs' ls ∧ ∀ a ∈ αs', a ∉ αs → SubFresh δ a

def MonoVM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    Ext ls ls' ρ → KeepsT ls ls' ρ → FutI δ ρ (σ, αs) (σ', αs') → InsertedFresh δ ls' αs αs' →
    FutAvoidsV A σ σ' → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM p none σ δ A αs ls v ρ → vRLM p none σ' δ A αs' ls' v ρ

def MonoOwnGM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM p σ δ αs ls Γ γ ρ → gRLM p (e :: σ) δ (a :: αs) ls Γ γ ρ
```

`MonoGM` is `MonoVM` at contexts, `MonoG`'s shape. `MonoOwnGMOfMonoGM` and `MonoGMOfMonoVM` are the
instance lemmas (`monoOwnG_of_monoG`, `monoG_of_monoV` at `vRLM`). `MonoGMOfMonoVM` takes the
context's future slot by slot, so it reads a revised future at the whole resource as one at each
slot's part: `FutPartI` (`R1.lean` §4), `FutPart` at `FutI`. W₀'s `FutPart` is about `Fut` and does
not give it. `FutPartI`'s proof is `FutPart`'s, with `FutOKI.placesFree` at a part: a cell of a
part at any depth is one of the whole at any depth, `CellU.CompR` keeping an `imm` cell's witness
[unchecked].

`MonoOwnGM` is a lemma, not a row. At `binder0` its only consumer is `[allI]`: the `∀` clause's
own-lend conjunct asks the body at the pushed stack, and the row carries its context there (DESIGN
§4.3; `Statement0.lean`'s `MonoOwnG` docstring). At `cbpv` the `∀` clause pushes nothing, and the
consumers are the `U` rows with an own lend. §2.6 states the row at `SemSM` (`AllIRowM`) and makes it
item 2's target at `binder0`.

**The hypotheses beside W₀'s, and who supplies each.** Each is a hypothesis of our statement,
needed by the revised relation.

| hypothesis | why the revised relation needs it | supplied at |
|---|---|---|
| `KeepsT ls ls' ρ` | `RelendJ`'s extension asks it; `Ext` alone does not compose through `ι.recs` (`not_extInst`) | `[let]`: `wpTS` keeps the list's members, so `KeepsT` holds trivially; the own push and a handler: `ls' = ls` (`keepsT_refl`); the share: §3.3, reduced to statement 2's resume composite, not discharged |
| `InsertedFresh δ ls' αs αs'` | `RelendJ` asks `RecsOutside` at the new vector; a retained leaf's `RetainedPay` at a cut the future moves needs the inserted lifetimes below the reading | the own push: the `∀` clause's own-lend conjunct gives `RecsOutside (α :: αs') ls'` and `SubFresh δ α`; a handler: no insertion |
| `OuterBelowTop`, `RecsOutside`, `SubOutside`, `PlaceViewsL` | `SemSJ`'s index | the rows' index |
| `RecsOutside (a :: αs) ls`, `SubFresh δ a` (`MonoOwnGM`) | as above | the `∀` clause's own-lend conjunct |

Adding hypotheses makes the statement weaker. A refutation of the weaker statement refutes the
stronger, so §2.3's configuration is at the statements as written here.

### 2.2 The route, and the step it meets

- **At `U`.** Let `σ'` be a future of `σ` at the value's resource. The inserted entries' places hold
  no cell of it (`FutOKI.placesFree`), so the split's views of `σ` are `σ'`'s with the inserted
  flags off, and the retained part stays. An instantiation `ι'` of `σ'` at its cut is, at an
  insertion below the outermost lend, an instantiation of `σ` (one `Restrat.Emb` at one cut). The
  body is owed at `σ'` at the instantiated index; the hypothesis gives it at `σ` there. So `MonoV`
  at `U` reduces to carrying a computation along the instantiated future, which is again a fresh
  push at an index of the same kind. That is `MonoC binder0` (`Statement0.lean:136`), which DESIGN
  §4.3 named as `binder0`'s need.
- **At `F`.** `wpTS_mono` with `MonoV` at the answer, once the push is fresh at the answer's
  resource [unchecked: a value related at an index sits above every lifetime fresh below the index].
- **At `⊸`.** At `binder0` the clause is at the stack itself: `∀ v, vRLM σ A v ─⋆ guardPV σ (cRLM σ C
  (e v))`. Carried to the pushed stack `e :: σ`, it is asked at an argument related at `e :: σ`,
  under `e :: σ`'s guard. To use the clause at `σ` that argument must be related at `σ`, under `σ`'s
  guard. An argument whose `U` component holds the pushed lend's view is not: the view is below
  `σ`'s innermost lend, which `σ`'s table excludes (`TabAtS`'s first conjunct) and which `σ`'s `U`
  clause cannot retain (`stratS`). The clause at `σ` says nothing about it. DESIGN §4.3: "at `⊸` the
  old clause is read under the old stack's stronger guard".
- **Whether that is a gap in the proof or in the statement** is what §2.3's configuration decides
  for `MonoOwnGM`, and §2.6's test at `gd` for its consumer.

### 2.3 The guard-dependent closure

**The mechanism.** `TabAtS σ αs ρ`'s first conjunct is `ρ.InStratum (↓a)` at the innermost lend
`a`: every cell of a guarded resource is at or above `a`, so strictly above `↓a`. That is the box
`[@'1]` when `'1` is read at `↓a`. So
```
f = λg. return g    at    U(F 1) ⊸ F ([@'1] U(F 1)),    '1 ↦ ↓a
```
is a `binder0` value at the stack. Its `U` clause asks the body at every instantiation `ι` of the
stack, where `'1` is read at `ι(↓a)`. Since `ι` is strictly monotone (`Inst.life1_lt_iff`),
`ι(↓a) ≤ ↓(ι a)`, so the box at `'1` follows from the table at `ι a` [checked outside the build:
the `U` clause at `gdσ`, every instantiation, from `TabAtS`'s first conjunct, `wpTS_lolli` and
`wpTS_val`]. The own lend of a callback type `∀'2 ⊏ '1. Imm '2 1 ⊸ F 1` pushes a lend at a
lifetime below `'1`. At the pushed stack an argument `g` of `U(F 1)` may hold that lend's view, and
`return g` boxed at `'1` then needs the view above `'1`, which it is not.

**What the closure is not.**
- **Not derivable by the direct derivation at its type.** The box rule asks the context to outlive
  `'1` (`boxI`, `CtxOutlives`, `Core/Fundamental.lean:139`, `Core/Types.lean:1858`), and `U(F 1)`
  outlives nothing (`VOutlivesR` has no `thunk` constructor, `Core/Types.lean:1730`) [read].
- **No Core value** (`GdNotCore`, stated; cheap, in `R1Mono.lean`). At the reading `gdδ`, the empty
  resource and every list, `vC true gdTy ls gdδ gdF ∅` fails. At the empty resource every list
  extends every list, so Core's `U` clause is asked at `gdls`. The argument `gdG` over `gdY`'s
  cell at `4` is a Core value at `U(F 1)` (`wpTS_load_I`'s run). `return gdG` boxed at `'1 ↦ 3`
  then fails at the run's end, by `GdNotPushed`'s step 4 at `σ = []`.
- **Not made by a typable program** [unchecked]. `fundamentalC` gives a derivable closed term's
  answer as a Core value at its run's end resource. `GdNotCore` covers the empty resource, and the
  composition with `RunEnd`'s run is not written.

**The configuration** (`R1.lean` §2):

| object | value |
|---|---|
| `gdσ`, `gdαs` | one 6.65 entry `gdX` (place `10`, variable `'0`, payload `1`) at `2` |
| `gdδ` | `'0 ↦ 2`, then `'1 ↦ 3` (`↓2`): the outer `∀'0`'s own lend binds `'0`, as at `GdReached` |
| `gdΔ` | `'0 ⊏ ⊤, '1 ⊏ '0` (`mΔ`) |
| `gdls` | `[(gdRec, 4)]`: the 6.64 record of the pushed lend's view, at its frame lifetime |
| `gdΓ`, `gdγ` | one live slot `f : gdTy = U(U(F 1) ⊸ F([@'1] U(F 1)))`, `gdF = λg. return g` |
| `gdCy` | `∀'2 ⊏ '1. Imm '2 1 ⊸ F 1`; its own lend pushes `gdY` (place `11`, variable `'2`, payload `1`, kind `imm ()`) at `4` |
| `gdG` | `λ_. load ℓ₁₁`, a thunk of `F 1` that reads its view ([TR] 6.144) |

```lean
def GdIndex : Prop :=
  StackOK gdσ gdαs ∧ OuterBelowTop gdαs ∧ RecsOutside gdαs gdls ∧ SubOutside gdσ gdαs gdδ ∧
    OwnPushI gdδ gdCy PMap.empty (gdσ, gdαs) gdY (lifeN 4) ∧ gdδ.find? gdY.x = none ∧
    CtxFresh gdY.x gdΓ ∧ RecsOutside (lifeN 4 :: gdαs) gdls ∧ SubFresh gdδ (lifeN 4) ∧
    TabAtS gdσ gdαs PMap.empty ∧ PlaceViewsL (extS gdδ gdσ gdαs) gdσ gdαs gdls PMap.empty ∧
    BindersLow gdΓ gdCy ∧ Scoped gdΔ gdΓ gdCy ∧ StackJ gdσ gdαs gdδ gdΔ gdΓ gdCy ∧
    SubDom gdδ gdΔ ∧ gdΔ.Models (extS gdδ gdσ gdαs)
def GdRelated : Prop := gRLM .binder0 gdσ gdδ gdαs gdls gdΓ gdγ PMap.empty
def GdNotPushed : Prop :=
  ¬ gRLM .binder0 (gdY :: gdσ) gdδ (lifeN 4 :: gdαs) gdls gdΓ gdγ PMap.empty
def NotMonoOwnGM0 : Prop := ¬ MonoOwnGM .binder0
def GdNotCore : Prop := ∀ ls : List SRec, ¬ vC true gdTy ls gdδ gdF PMap.empty
def GdArises : Prop :=
  ∃ c : Cfg, ArisesI c ∧ c.σ = gdσ ∧ c.αs = gdαs ∧ c.ls = gdls ∧ ArisesVI c gdF gdTy
def GdNotRecsInsideOwn : Prop := ¬ RecsInsideOwn gdσ gdαs gdls
def GdIdxArises : Prop := ∃ c : Cfg, ArisesI c ∧ c.σ = gdσ ∧ c.αs = gdαs ∧ c.ls = gdls
def GdIdxNotArisesOf : Prop := RecsInsideOwnArises → ¬ GdIdxArises
```

**What `GdIndex` covers.** It meets every hypothesis of `MonoOwnGM`, and what the consumer has
beside them: `SemSM`'s index at the judgement `gdΔ; gdΓ ⊢ Λ. M : gdCy`, which the `∀I` row at
`binder0` reads when it carries its context across the own lend. The arithmetic, to be proved in
`R1Mono.lean` (step 1):
- `OuterBelowTop [2]`, `StackOK`, the chain `[4, 2]`;
- `SubFresh gdδ 4` (`4` below `3` and `2`), `LtLife ('1 at 3) 4`;
- `gdΔ.Models`: `'0 ↦ 2 ⊏ ⊤`, and `'1 ↦ 3 ⊏ ⟦'0⟧ = 2`;
- `StackJ`: `gdX`'s variable `'0` is `gdΔ`'s, its payload `1` closed;
- `SubDom`: `'0` and `'1` are both `gdΔ`'s;
- `Scoped` and `BindersLow`: `gdTy` and `gdCy` read only `'1`, and bind only `'2`, no `NsVar`.

Three facts hold vacuously:
- `RecsOutside`, the record being shorter-lived than both lends;
- `SubOutside`, nothing being bound before `'0`. This is as at `GdReached`, whose reading also
  binds `'0` first [unchecked: `GdReached` is optional and not built];
- the table and views, at the empty resource.

The list holds `gdRec` so that the pushed view sits in a tagged `TW` world (a 6.64 cell needs its
frame). The binding `'0 ↦ 2` is shadowed by the stack's reading (`extS` binds `'0` at `2`
too). So `GdRelated`'s `U` clause, checked outside the build at `gdδ = {'1 ↦ 3}`, reads the same
lifetimes, and it is not re-checked.

**What `GdIndex` does not cover: the record invariant.** `gdRec` sits at `4`, at or below the
outermost lend `2`, and `gdσ`'s one entry is a 6.65 entry, whose lineage holds no record. So
`RecsInsideOwn gdσ gdαs gdls` fails (`GdNotRecsInsideOwn`, stated, cheap), and with
`RecsInsideOwnArises` (`Binder.lean`, stated, not attempted) no configuration of the arising set
has `gd`'s index (`GdIdxNotArisesOf`). The record is there because `MonoOwnGM` keeps the list across
the push, as the `∀` clause's own-lend conjunct does at `binder0` (`ExtQ false`), while a 6.64 lend
extends it with its record (`CallbackExtImmM`'s `ls'`). `SemSM`'s index does not carry
`RecsInsideOwn`, so `gd` meets it.

A 6.65-callback variant needs no record before the push: at `∀'2 ⊏ '1. Mut '2 1 ⊸ F 1` the own lend
pushes a 6.65 entry, whose view has no frame, so the list is empty and `RecsInsideOwn` holds
vacuously. Its `GdNotPushed` reads the view through a `Mut` read-out (6.66's `withswap`) in place of
6.144's load. It is not built [unchecked].

**The proofs, step by step** (in `R1Mono.lean`).
1. `GdIndex`: the arithmetic above; `OwnPushI` from `OwnOKI`'s fields at `∅` and `ViewAt` at
   `Imm '2 1`.
2. `GdRelated`: the `U` clause at `∅` with the split `([false], ∅, ∅)` (`vwSW_false`,
   `placeViewsL_empty`, `stratS_empty`). At each instantiation the handed views are `∅`
   (`vwSW_false_inv`). The `⊸` clause is at the stack itself (`ExtQ false`, `FutQI false`), with
   `wpTS_lolli` and `wpTS_val`. `atLife` reads `'1 ↦ ι 3` (`extS_inst`, `Inst.find?_sub`). The box
   comes from the table's first conjunct at `ι 2`, since `ι 3 ≤ ↓(ι 2)` by `Inst.life1_lt_iff`
   (`ResU.InStratum.mono`).
3. `gdG` related at the pushed stack at the view `gdView = ℓ₁₁ ↦ imm({4}, (), ∅)`. The split holds
   the view (`[true, false]`). At each instantiation the body loads through the handed view
   (`wpTS_load_I`'s run, `Core/Wp.lean:666`) and drops it into the run's garbage (`NoOwn`), as the
   answer `()` holds nothing.
4. `GdNotPushed`. Every split of `∅` is empty (`relendJ_adj_handed`'s case analysis). At the identity
   instantiation, the list `gdls` and no views, the `⊸` clause at `gdG` over `gdView` owes
   `wpTS gdls (gdF gdG)` at `gdView`. The guard holds there: `↓4`-stratum, the view at its entry's
   place, exactly at `4`. Refute it as `adj_run_fails` does (`GapRoom.lean:191`): the frame `∅`,
   the world `gdView` with `ps = [gdRec]` (`TW.alloc` then `TW.immFrame`; `Tagged` by `FrameLife`
   at `4`), the run is the `β` step to the value `gdG`. At the end part `ρ'`:
   - if `ρ'` holds a cell at `11`, `↭`'s `imm` clause makes it `imm({4}, …)` (the step `pvlUpdN`
     spends, `AgW.imm_mem_deep`), and the box at `3` fails, `4` not being above `3`;
   - if not, `ρ'` holds no borrow cell, and `gdG`'s `U` clause at `ρ'` fails at the identity, the list
     `[]` and no views. Every extension condition is vacuous at an own-only part. At the frame `∅`, in
     an own-only `TW` world (`TW.alloc` along the domain; `tw_heap_any`, `GhostEnd/Bridge.lean:105`,
     is one step of it), `load ℓ₁₁` has no step (`staleStuck_no_step`'s shape, `Core/Stale.lean:214`).
5. `NotMonoOwnGM0` from 1, 2, 4. Then `¬ MonoGM .binder0` and `¬ MonoVM .binder0` through
   `MonoOwnGMOfMonoGM` and `MonoGMOfMonoVM`: the own push is a one-step `FutI` future
   (`ownPush_futStep`'s proof with `placeFree`), `InsertedFresh` comes from the own-lend
   conjunct's two facts, and `MonoGMOfMonoVM` reads `FutPartI` (§2.1).
6. `GdNotCore`: step 4's run at `σ = []` with Core's relation, the list `gdls`.
7. `GdNotRecsInsideOwn`: `gdRec`'s tag `4 ≤ 2`, and `gdX.k = .mut`. `GdIdxNotArisesOf` from it.

`NotMonoOwnGM0`, if proved, is a refutation of ProbeD1's draft statement `MonoOwnGM` at a
configuration not shown to arise (§2.5). It pins the scope of the restriction §2.6 adds. It is not
item 2's result, and it does not refute `MonoOwnGM`'s consumer (§2.6).

### 2.4 What `binder0` carries by construction

`vRLM`'s `μ` candidate is a predicate at one index (§1.2), so moving a `μ` value to another list or
another stack is an induction on the data whose hypothesis is on the environment. The statements
are stated under an environment, and the `none` forms are their instances, as `RelendMValue` is
`RelendMValueE`'s.

```lean
def EnvExt (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls ls' : List SRec) : Prop :=
  (∀ n, (wEnv η' n).ty = (wEnv η n).ty) ∧
  ∀ n v ρ, Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → wEnvP η n v ρ → wEnvP η' n v ρ
def MonoExtME (p : Placement) : Prop := …   -- MonoExtM at η, η' under EnvExt
def EnvPush (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (e : LEnt) (a : Life) : Prop :=
  (∀ n, (wEnv η' n).ty = (wEnv η n).ty) ∧ (∀ n, ¬ VFree e.x (wEnv η n).ty) ∧
  ∀ n v ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → (∀ ψ, ¬ DeepAt ρ e.l ψ) →
    ρ.InStratum a → wEnvP η n v ρ → wEnvP η' n v ρ
def MonoOwnUFreeME (p : Placement) : Prop := …   -- one value of a UFreeM type across the push
def EnvExtNone, EnvPushNone : Prop             -- the hypotheses hold at `none`
def MonoExtMOfE, MonoOwnGUFreeMOfE : Prop       -- the `none` forms as corollaries
```

- **`MonoExtME`**, the record half (same stack, `Ext` and `KeepsT`):
  - At `U`: the split's views along `Ext` (`GhostEnd.vwS_local`; `PlaceViewsL` reads records above
    its cells, which `Ext` fixes). Every extension of `ι.recs ls'` is one of `ι.recs ls` by `ExtInstT`
    (§3.3), `Ext.trans`, `KeepsT` transitivity and `keepsS_of_keepsT`.
  - Leaves: `vC_local`; `CohS` and `RetainedPay` read no list; the type is the same by `EnvExt`'s
    first conjunct.
  - `tvar`: `EnvExt`'s second conjunct.
  - `μ`: the fixed point at the candidate `P' v ρ := vRLM η (μ) ls v ρ ∧ (Ext ls ls' ρ → KeepsT →
    TabAtS → PlaceViewsL → vRLM η' (μ) ls' v ρ)`, closed by the induction hypothesis at the body
    under the extended environments, whose `EnvExt` holds at `0` by `P'`'s second conjunct.
  - `[L]`: `sepRange`'s induction.

  Its instance at a list with the same members is what `[let]` reads.
- **`MonoOwnUFreeME`**: one value of a type that reaches no `U` (`UFreeM`, which looks inside `μ` and
  `[L]`) carried onto the own push.
  - `monoOwnV_uFree`'s proof (`Own.lean`) with the leaves' new conjuncts: `CohS` at the pushed stack
    reads the old entries, since the value's place is not the pushed one, which no cell of the
    resource holds; `RetainedPay` by `RetainedPayPush` (§3.2).
  - `μ` and `[L]` as above, under `EnvPush`.
  - `MonoOwnGUFreeMOfE` takes it slot by slot: `OwnOKI`'s fields and `placeFree` restrict to a part
    of the context's resource.
- **The hypotheses hold at `none`** (`EnvExtNone`, `EnvPushNone`): both types are `.tvar n`, which
  reads no lifetime variable, and `wEnvP none` is `False`.

These say the failure is confined to `U` slots: values with no thunk are monotone along the push,
and every value is monotone along the record order.

### 2.5 The arising check, and what the refutation does not refute

- **`GdArises`**: the closure arises at its type at a configuration of the revised arising set with
  `gd`'s stack, lifetimes and list (`ArisesVI`). Expected false and not attempted [unchecked]. A
  value arises at a type as the answer of a run of a derivable term at that type (`ArisesVI.ret`)
  or as a lend's view (`ArisesVI.view`, at `viewTy`). `gdF` is not a view. A derivable term's
  answer is a Core value (`fundamentalC`), and `gdF` is none at the empty resource (`GdNotCore`).
  The glue between `RunEnd`'s run and `wpTS`'s is not written [unchecked], and `ArisesI`'s
  direction is not established (DESIGN §11).
- **`GdArises` is stated at the whole configuration**, the list included (`c.ls = gdls`), since an
  index is part of what a refutation must show to arise.
- **The index fails a second, cheaper way.** `gd`'s list holds a record at or below the outermost
  lend that no 6.64 entry of `gdσ` owns, so `RecsInsideOwn` fails (`GdNotRecsInsideOwn`), and the
  arising set's record invariant excludes the index (`GdIdxNotArisesOf`, from `RecsInsideOwnArises`,
  stated, not attempted). It is the result of `MonoOwnGM` keeping the list across a 6.64 own push
  (§2.3). A 6.65-callback variant would avoid it, and leaves `GdNotCore`'s reason standing.
- **So `NotMonoOwnGM0` is a refutation of ProbeD1's draft statement at a configuration not shown to
  arise**: a fact about our statement, deciding nothing by itself.
- **What it does not refute.** `MonoOwnGM` is a lemma; its only consumer at `binder0` is `[allI]`
  (§2.1), restated at `SemSM` as `AllIRowM`. `NotMonoOwnGM0` does not refute `AllIRowM .binder0`.
  `gdF`'s run is benign, the identity, so a derivable body at `gdΓ` is not obviously sent wrong at
  `gd`: the row's conclusion there asks the body's run with `gdF` captured, and returning an argument
  boxed at `'1` breaks no step of a run [unchecked]. §2.6 tests the row at `gd` directly.
- **What it shows anyway.** `binder0`'s `U` clause admits a closure whose correctness rests on the
  table. No pointwise conjunct excludes it: its resource is empty, and its index is one `binder0`'s
  own clauses reach from a closed typed program (`GdReached`, optional: `Λ'0. λx. Λ'1 ⊏ '0. λf. Λ'2 ⊏
  '1. λr. …` at `∀'0 ⊏ ⊤. Mut '0 1 ⊸ ∀'1 ⊏ '0. gdTy ⊸ gdCy`, as `k_reached` reads `kC`). What
  excludes it is historical: no typable program makes it [unchecked]. A guard conjunct on values
  would be a guard beside `TW`, failure (b), and this unit adds none.
- **Where the settled reading points.** Resources are of the calculus, and counterexamples must
  arise. `MonoOwnGM` quantifies over every related context at every index, and the closure is
  related at an index where, by the reasoning above, no typable program puts it [unchecked]. So the
  statement is too wide, and the next step is the mis-statement, not a stop. §2.6 restates the fact
  at a domain the consumer can supply, and keeps `gd` as the scope pin of that added hypothesis
  (CLAUDE.md §4).
- **The failure is `binder0`'s own** (`GdNotCbpv`, optional): at `cbpv` the `U` clause owes the body
  at every future of `gdσ`, the push of `gdY` among them, so the same run excludes the closure at
  `gdσ` already. That places it under DESIGN §12.3 as a per-placement fact, not a shared reason.

### 2.6 The consumer, and the route at a restricted domain

**The target** (`R1.lean` §2):

```lean
def AllIRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSM p Δ Γ (.val (.lam M)) (.comp (.all x b C))
def AllIRowMOfMonoOwnGM : Prop := ∀ p : Placement, MonoOwnGM p → AllIRowM p
```

`AllIRowM` is `AllIRow` (`Statement1.lean`) at `SemSM`. `AllIRowMOfMonoOwnGM` is the route statement 0
planned: the `∀` clause's first conjunct from the premise at the extended reading, its own-lend
conjunct from the premise at the pushed index, the context carried there by `MonoOwnGM`, the index's
facts by `OuterBelowTopPush`, `SubOutsidePush`, the own lend's `LtLife` for `Δ.extend x b`'s models,
and the clause's `guardPV` for the table and views. At `binder0` the route is closed by
`NotMonoOwnGM0`. The row is not.

**(i) The row itself at `gd`.**

```lean
abbrev gdCyBody : CTy := .arr (.imm (.var 2) .unit) (.ret .unit)
abbrev gdM : Expr :=     -- λr. let g = f (thunk (load r)) in force g
  .lam (elet (.app (.var 2) (.lam (.app (.val (.prim .load)) (.var 1))))
    (.app (.var 0) (.val .unit)))
def GdMDerivable : Prop :=
  ProbeRules (gdΔ.extend 2 (.var 1)) (⟨.unit, false⟩ :: gdΓ) gdM (.comp gdCyBody)
def GdAllIConclAt (M : Expr) : Prop :=
  cRLM .binder0 gdσ gdδ gdCy gdαs gdls (substAll gdγ (.val (.lam M))) PMap.empty
def GdAllIHoldsAtM : Prop := GdAllIConclAt gdM
def GdAllIHoldsDerivable : Prop :=
  ∀ (S : VTy) (M : Expr),
    ProbeRules (gdΔ.extend 2 (.var 1)) (⟨S, false⟩ :: gdΓ) M (.comp gdCyBody) → GdAllIConclAt M
def GdAllIRowRefutes : Prop :=
  ∃ (S : VTy) (M : Expr),
    SemSM .binder0 (gdΔ.extend 2 (.var 1)) (⟨S, false⟩ :: gdΓ) M (.comp gdCyBody) ∧
      ¬ GdAllIConclAt M
def GdRowRefutation : Prop := GdIndex → GdRelated → GdAllIRowRefutes → ¬ AllIRowM .binder0
```

- `gdM` is the body that exercises the closure where `GdNotPushed` fails it: it hands `f` a thunk
  holding the view the own lend pushes, unboxes the answer and forces it.
- `GdMDerivable`, to prove: `load` at `Imm '2 1`, the thunk, `f` forced (`forceE` at an `⊸` type is
  the value itself) and applied, `elet`, `boxE` at the bound variable, the force. [unchecked: the
  derivation is not built.]
- `GdAllIHoldsAtM`, expected to hold, by the runs. The `∀` clause's first conjunct is at `gdσ`, where
  every argument at `Imm '2 1` is an `imm` cell strictly above the outer lend (the table's second
  conjunct), so the thunk `gdF` hands back is boxed above `3`; its second is at the pushed stack,
  where the argument may be the view at `4`. In both, `gdF` returns the thunk, the thunk loads
  ([TR] 6.144, `wpTS_load_I`), and the answer `()` holds nothing, the read cell going to the
  garbage (`NoOwn`). The box is never read by a step of the run [unchecked].
- `GdAllIHoldsDerivable`: not derived, and no route is known. A fundamental lemma reaches a captured
  value only through a relation it is in, and `gdF` at the pushed index is in neither W's
  (`GdNotPushed`) nor Core's (`GdNotCore`). I have not derived it and have not verified that any
  obstruction is real.
- `GdAllIRowRefutes`: not expected. A body meeting the premise behaves well with every `f` W relates
  at every index, and with `gdF` it receives back an argument it made, at a closed answer type
  [unchecked]. `GdRowRefutation` is cheap: `GdIndex` and `GdRelated` meet the conclusion's
  hypotheses at `gdΔ; gdΓ ⊢ Λ. M : gdCy`.
- **If `GdAllIHoldsAtM` holds**, `MonoOwnGM` was the wrong lemma at `gd`: the row's conclusion
  survives at the body that exercises the closure. **If a body refutes the row** (`GdAllIRowRefutes`
  proved), the arising check is `GdArises` with `GdIdxNotArisesOf`, as for `NotMonoOwnGM0`.

**(ii) The route at a restricted domain: each live slot also a Core value.** The restriction is
the added hypothesis, and `gd` pins its scope: without it the lemma is refuted (`NotMonoOwnGM0`),
with it `gd` is excluded (`GdCtxNotCore`).

```lean
def gSepRLMC (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then
        (fun ρ => vRLM p none σ δ s.ty αs ls v ρ ∧ vC true s.ty ls (extS δ σ αs) v ρ) ⋆
          gSepRLMC p σ δ αs ls Γ γ
      else gSepRLMC p σ δ αs ls Γ γ
def gRLMC … := ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLMC p σ δ αs ls Γ γ
def SemSMC (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  …   -- SemSM with gRLMC in place of gRLM; the conclusion cRLM's alone
def MonoOwnGMC (p : Placement) : Prop :=
  …   -- MonoOwnGM's hypotheses, gRLMC at σ → gRLMC at e :: σ
def AllIRowMC (p : Placement) : Prop := …   -- AllIRowM at SemSMC
def AllIRowMCOfMonoOwnGMC : Prop := ∀ p : Placement, MonoOwnGMC p → AllIRowMC p
def GdCtxNotCore : Prop := ¬ gRLMC .binder0 gdσ gdδ gdαs gdls gdΓ gdγ PMap.empty
abbrev gdF₀ : Val := Val.lam (.seq (.app (.var 0) (.val .unit)) (.val (Val.lam .unit)))
def GdRestrictedMet : Prop := gRLMC .binder0 gdσ gdδ gdαs gdls gdΓ [gdF₀] PMap.empty
def WInsideCoreM (p : Placement) : Prop := …   -- vRLM at a stack ⊆ vC at its reading
def CoreInsideWM (p : Placement) : Prop := …   -- vC at a stack's reading ⊆ vRLM there
```

- **Why Core's relation.** It is the kernel's, not a new family, and W's clauses are unchanged.
  `gd` is excluded by it (`GdCtxNotCore`, cheap: every split of `∅` is empty, and the one live
  slot's Core half is `GdNotCore`, the stack's reading agreeing with `gdδ` at `'1`, `gdTy`'s one
  variable, by `vC_congr`). Its Core half crosses the own push by locality: the pushed variable is
  free in no live type (`CtxFresh`), and the two readings agree elsewhere (`vC_congr`,
  `Core/RelationFacts.lean:873`; `extS_push_find`, `Own.lean:51`). So the `∀I` row can supply the
  restriction at its premise's pushed index, which the arising form cannot (below).
  `AllIRowMCOfMonoOwnGMC` is `AllIRowMOfMonoOwnGM`'s argument with that step; to prove.
- **The restriction is met with a `U` slot** (`GdRestrictedMet`, to prove): `gdF₀` forces its
  argument and answers a thunk holding nothing, boxed at `'1` above every lifetime; it is W's at
  `gdσ` (the argument's run by its `U` clause at the identity) and Core's at the reading. So
  `MonoOwnGMC`'s hypotheses hold at `gd`'s index with a `U` slot, and the statement is not vacuous
  there.
- **The attempt, along §2.2's route at `⊸`.** At a `U` slot, an argument `v` related at the pushed
  stack under its guard:
  - if `v` is related at `σ` under `σ`'s guard, the slot's W clause at `σ`, then the answer carried
    to the pushed stack (the item's own induction at the answer type);
  - if not (it holds the pushed view, or a cell at the pushed lend's lifetime), the slot's W clause
    says nothing. Its Core half gives the application Core's when `v` is Core's: the step
    `WInsideCoreM` at the argument's type. The answer is then Core's, and the conclusion asks it
    W's at the pushed stack: the step `CoreInsideWM` at the answer's type;
  - at an instantiation other than the identity, the Core half at the reading says nothing at the
    instantiated reading: Core's relation is not invariant under an instantiation that opens room
    (`coreAllNotNatural`, `GAP.md` §3c; `InstEquivLeafAll`, `Binder.lean`, stated, not derived).
- **The expected stop** is `WInsideCoreM` at a `U` argument, at the identity [unchecked]. W's `U`
  clause covers the list extensions that keep the tags and `RecsOutside`, under the guard; Core's
  asks the body at every `Ext` extension, with no guard. At `σ = []` the two steps are OQ-58's
  `NilSoundV` and `NilAgreesU` (DESIGN §6.3), whose expected outcome there is (c). I have not derived
  either and have not verified that any obstruction is real. The builder reports the step the
  attempt stops at.
- **What a stop there would mean.** Core's relation does not see the push, so restricting by it
  does not give `binder0` the monotonicity its `⊸` clause lacks. A clause that quantifies over the
  push, as `binder`'s `⊸` does over futures, sees it by construction (`GdNotCbpv`'s mechanism). That
  is DESIGN §4.3's expectation, and it decides nothing about OQ-8 without a refutation that passes
  DESIGN §11 [unchecked].
- **What the restriction would cost if adopted.** It is not adopted here; these are recorded for the
  report.
  - `SemSMC`'s conclusion is `cRLM`'s alone, so a row that binds a value (`[let]`, `⊗E`, `⊕E`)
    cannot feed its second premise, whose context the restriction asks to be Core's too. Its
    conclusion would have to carry Core's relation at the stack's reading as well: a second
    relation at the judgement, to be read against DESIGN §12.2 (b) before adoption [unchecked].
  - Arising values are Core values for terms of Core's rules (`fundamentalC`), up to the glue
    between `RunEnd`'s run and `wpTS`'s and the three spanning rules `ProbeRules` adds [unchecked].
    Whether every context a run reaches is Core's at its reading after a resume, whose reading is
    instantiated, is not known: Core's relation is not natural (`coreAllNotNatural`) [unchecked].

**(iii) The arising form.**

```lean
def CtxArisesAt (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) (Γ : Ctx VTy)
    (γ : List Val) : Prop :=
  ∃ c : Cfg, ArisesI c ∧ c.σ = σ ∧ c.αs = αs ∧ c.ls = ls ∧ c.ρ = ρ ∧ ArisesCtxI c Γ γ
def MonoOwnGMA (p : Placement) : Prop :=
  …   -- MonoOwnGM's hypotheses and CtxArisesAt σ αs ls ρ Γ γ → gRLM at e :: σ
```

`gd` is outside it by `GdIdxNotArisesOf`, and by `GdArises` expected false. Its matching restriction
of `SemSM` would add `CtxArisesAt` at the index. The `∀I` row has no transition to supply it from at
its premise's pushed index: the own push is no constructor of `ArisesI`, and no constructor of
`ArisesVI` carries a value across a lend (`RunEnd` fixes the stack, and `ArisesVI.ret`'s run starts
where its context arises) [read: `Binder.lean`'s `ArisesI` and `ArisesVI`]. That no other proof
supplies it is [unchecked]. Carrying it by a transition would be a change to ProbeD1's draft arising
set that this unit does not make. So the Core form is the one attempted.

### 2.7 Success and failure

- **The statements as written are decided in Lean.** Either `MonoOwnGM`, `MonoGM`, `MonoVM
  .binder0` are proved (not expected), or `NotMonoOwnGM0` is proved with `GdIndex` and `GdRelated`
  (expected), with `GdNotCore`, `GdNotRecsInsideOwn` and the arising check's status reported.
- **The positive targets are in Lean** (§2.6): `AllIRowM .binder0`, the row at `binder0`; the test
  at `gd` (`GdMDerivable`, `GdAllIHoldsAtM`); the restricted route (`AllIRowMCOfMonoOwnGMC`,
  `GdCtxNotCore`, `GdRestrictedMet`, then `MonoOwnGMC .binder0`, attempted, its stopping step
  reported). `AllIRowM .binder0` itself is expected not derived; the report says which step of which
  route it stops at.
- If step 4 does not close, report the step; then the positive route of §2.2 is attempted at `⊸`
  with the argument read back at `σ`, and its stopping step is reported.
- If `NotMonoOwnGM0` is proved:
  - no further positive attempt at `MonoOwnGM`, `MonoGM` or `MonoVM` as stated; the positive work
    continues at the consumer and the restricted route, as above;
  - no pointwise conjunct is added to the guard or the leaves to exclude the closure;
  - `MonoExtM` and `MonoOwnGUFreeM` are proved, through their environment forms.

  This does not settle `binder0`'s monotonicity, and the report says so in those words.
- `MonoHide` (beside the bundle) is not addressed. Hiding pushes no lend and leaves the table as it
  is, so the closure stays a value under it [unchecked]; its `F_Σ` case changes the stops' depths and
  is not derived.

---

## 3. Item 3 — the three obligations

### 3.1 `OuterBelowTop` at every lend

```lean
def OuterBelowTopPush : Prop :=
  ∀ (αs : List Life) (a : Life) (s : LSub) (c : Lifetime.Life),
    OuterBelowTop αs → LtLife s c a → OuterBelowTop (a :: αs)
def OuterBelowTopFresh : Prop :=
  ∀ (αs : List Life) (a β : Life), OuterBelowTop αs → a < β → OuterBelowTop (a :: αs)
def OuterBelowTopArises : Prop := ∀ c : Cfg, ArisesI c → OuterBelowTop c.αs
-- Binder.lean, this revision:
def LendMutI (c c' : Cfg) (e : LEnt) : Prop :=
  LendMut c c' e ∧ (∀ α ∈ c'.αs.head?, LendFresh c.ls α) ∧ ∀ α ∈ c'.αs.head?, α < ⊤
def LendImmI (c c' : Cfg) (e : LEnt) : Prop :=
  LendImm c c' e ∧ (∀ α ∈ c'.αs.head?, LendFresh c.ls α) ∧ ∀ α ∈ c'.αs.head?, α < ⊤
```

- **The rows that push at `SemSM`.** The own lend at the `∀` clause meets a bound (`OwnPushI`'s
  `LtLife`): `OuterBelowTopPush`, `ownPushBelowTop` (`BinderInst.lean:295`). Statement 2's spanning
  rows push through the callback's own lend, so they are the same case.
- **The lends of the arising set.** [TR] 6.64's proof: "Let α be some lifetime where α ⊏ β (H4)";
  6.65's: "Let α be some lifetime where α ⊏ γ ⊓ β (H4)" [read, `3764117-supplement.pdf`, the two
  proofs]. The old `LendMutI` and `LendImmI` did not record it. At the empty stack, with no borrow
  cell in the payload or the callback's resource, `α = ⊤` met them, so `ArisesI` reached
  configurations that `SemSM`'s index excludes.
  - The fields added here are H4's consequence `α < ⊤`. This is a transcription into ProbeD1's
    draft arising set: a configuration carries no reading of the bound, so the consequence is all
    that can be recorded.
  - The existing `ArisesI` proofs (`arisesInv`, `pvArises`, `placesNodupArises`) destructure the two
    as `⟨⟨…⟩, -⟩` or read `.1`, and build unchanged [checked: `lake build ProbeD1`].
- **`OuterBelowTopArises`**, by induction on `ArisesI`:
  - `nil`: the empty vector;
  - `run`: `RunEnd` fixes `αs`;
  - `part`, `hide`: `αs` unchanged;
  - `lendMut`, `lendImm`: `c'.αs = α :: c.αs` (from `LendMut`'s and `LendImm`'s existentials), and
    `OuterBelowTopFresh` at `β = ⊤` from the new field.

  Every arising check (`GdArises`, `MuSlotArises`, `InternalLeafArises`) then runs over
  configurations with `OuterBelowTop`.
- `BINDER.md` §3.2's code block reads `LendMutI` without the field; the report updates it.
- Proofs: `OuterBelowTopPush` and `OuterBelowTopFresh` two lines each (`lt_of_lt_of_le`, `le_top`,
  cases on `αs.getLast?`); `OuterBelowTopArises` an induction of six cases.

### 3.2 `RetainedPay` row by row, at every payload type

`RetainedPay σ αs s T v` (`BinderJ.lean`) asks a `Mut` or `Imm` leaf at a place no entry lends to
read its payload type at external lifetimes. It is a conjunct of the leaf, so every row whose
answer, or whose callback's argument, holds a `Mut` or `Imm` leaf owes it there, and a row that
carries a value to another index needs it carried.

**Why per row.** A configuration carries no reading substitution (`BINDER.md` §3.2, as for
`SubOutside`), and `RetainedPay` reads one. So the obligation is stated per row, at the index each
row has, at every payload type. The arising form is stated only for a leaf whose payload type reads
a variable of the stack, which every reading reads at the entry's lifetime (`InternalLeafArises`).

**The objects** (`R1.lean` §3.2):

```lean
inductive LeafPos (R : WRes) : VTy → Val → BoCa.Loc → VTy → Prop   -- a Mut or Imm position of (T, v)
  | mut … | imm … | tensorL … | tensorR … | sumL … | sumR … | bang … | box …
  | ref : R.get l₀ = some (CellU.ownOf u) → LeafPos R A u l S → LeafPos R (.ref A) (.loc l₀) l S
  | mu : (VTy.mu A).Cl 0 → LeafPos R (VTy.inst (.mu A) A) v l S → LeafPos R (.mu A) v l S
  | fam : i < c.toNat → LeafPos R L (.loc (ℓ + i)) l S → LeafPos R (.fam L) (Val.arr ℓ c) l S
def PayLeaves (σ : LStack) (αs : List Life) (s : LSub) (R : WRes) (T : VTy) (v : Val) : Prop :=
  ∀ l S, LeafPos R T v l S → RetainedPay σ αs s S (.loc l)
def PayLeavesOfPayExt : Prop :=   -- PayExt αs s T → PayLeaves σ αs s R T v
def SemIdxM (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) : Prop :=
  BindersLow Γ C ∧ Scoped Δ Γ C ∧ StackOK σ αs ∧ OuterBelowTop αs ∧ StackJ σ αs δ Δ Γ C ∧
    SubDom δ Δ ∧ Δ.Models (extS δ σ αs) ∧ RecsOutside αs ls ∧ SubOutside σ αs δ ∧
    TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ
```

`LeafPos` is a position predicate on a type and a value, Core's `MutPos` and `GPos` at both leaf
kinds with `!`; it defines no relation. `SemIdxM` abbreviates the hypotheses `SemSM` gives every row
at its conclusion's index.

**The rows' statements** (each at every payload type, except where it asks for no join; `R1.lean`
§3.2):

| statement | the row's leaf, and the facts the row has where it hands it on |
|---|---|
| `RetainedPayViewRow` | the lend's view at the pushed stack: its place is the pushed entry's |
| `RetainedPayLoadMutRow` | `withswap`'s read-out: the payload a `Mut` view's cell stores, at `T`, at the view's index; under the guard at the read-out resource, which is a part of a tagged `TW` world (the row reads the callback's `⊸` clause under the guard, inside its run) |
| `RetainedPayLoadImmRow` | `withload`'s read-out, and `foldImm`'s at each node: the payload reborrowed by `reb_α` ([TR] p. 5), at `Imm̲ 'x T`, at the own lend's pushed stack and `'x ↦ α`; under the guard there, inside the run |
| `NoJoinL`, `NoJoinV`, `NoJoinC` | a lifetime term, a type, with no `⊔` |
| `LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq` | a leaf's position, external readings and `PayLeaves` transfer along `TyEq` to a type with no join |
| `RetainedPayLoadMutBound` | `withswap`'s read-out at a bound view, reduced through the view's `CohS` to the leaves of the entry's payload type |
| `EntryPayLeaves` | the leftover: at the read-out row's index, the stored payload's leaves read at `e.T` meet `RetainedPay` |
| `RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet` | each read-out row's hypotheses met at a one-entry stack, with a leaf at a place no entry lends whose payload type reads a variable |
| `RetainedPaySliceRow` | a slice borrow's elements, cells at the own lend's lifetime, at the pushed stack; under the guard there. Vacuous at every count; not counted toward item 3 |
| `SliceGuardFails` | two such cells meet the table at no stack whose entries lend none of their places but the innermost |
| `RetainedPayInstRow` | `∀E` at an instance `b` with no join (a variable, `⊤`, a meet): the leaf the callee gives at `'x ↦ ⟦b⟧`, at `S[b/'x]` |
| `RetainedPayPush`, `RetainedPayPop`, `RetainedPayExtend` | a push fresh below the reading, the end of a lend, a binding the payload type does not read |
| `InternalLeafArises` | the arising check: a leaf at a place no entry lends whose payload type reads a stack variable, of a value arising or of an entry's payload |
| `ReadOutAtInternalPayload` | at `InternalPayloadArises`'s shape, the read-out's only leaf has payload type `1` |
| `PayLeavesAt`, `mutLeafP`, `immLeafP` | the variant leaf (stated, not adopted): a borrow leaf carrying `PayLeaves` of its payload |
| `ThawLeafP`, `VwPayLeaves` | the variant's two costs: the thaw at a bound variant leaf, and W's views carrying their payload's leaves |

**The rows, classified.** Every line is [unchecked] until its row is stated and proved at `vRLM`.
None of statements 1–4's rows is stated at `vRLM` (statement 1's `TabRelend`, proved at W₀, is a table fact, not a row).

| rows (`CDerives` constructors) | the `Mut`/`Imm` leaf | statement | expected |
|---|---|---|---|
| `withbor1`, `withbor2`, their `U` forms, the spanning rows (statement 2), the own lend at a `ViewAt` type; `withbor3`'s view if its cell sits at the own lend's place [unchecked: where `withbor` (3)'s cell sits] | the lend's view | `RetainedPayViewRow` | proved (one line: `innerAt` at the pushed head) [unchecked] |
| `withswap` (genSelf at `Flag`; every payload type) | the payload's leaves, moved out | `RetainedPayLoadMutRow`; `RetainedPayLoadMutBound`, `EntryPayLeaves` | proved at a retained view (`PayLeavesOfPayExt`) and at the nested `Imm` leaves; at a bound view with no join reduced to `EntryPayLeaves`, the expected stop; open at a join [unchecked] |
| `withload`, `withloadU`, `SpanRuleLoad` (reconB′'s `*b` at `Flag`; every payload type); `foldImm` at each node | the reborrowed payload's leaves | `RetainedPayLoadImmRow` | proved where no lifetime term of the payload type has a join [unchecked] |
| `sliceGetM`, `arrGet`, the family operations | an element of a `vRLM` family, the same place and payload type | — | by `vRLM`'s `[L]` clause, which reads each element as W's leaf [unchecked] |
| `allE`, `allEV` at an instance with no join (a variable, `⊤`, `'v ⊓ 'w`, …) | the answer's leaves at `C[b/'x]` | `RetainedPayInstRow` | to prove; at a `⊔` instance not covered (`⟦'v ⊔ 'w⟧` external says nothing of the shorter). Neither program instantiates a lifetime `∀` at a join [unchecked: `genSelf`'s derivation is not built] |
| `var`, `ret`, `bind`, `tensorE`, `sumE`, `proj₁/₂`, `bangE`, `boxE`, `boxI`, `immSub`, `mutSub` (the leaf's lifetime only), `copy` (one leaf twice), `alloc`, `free`, `swap` (a `Ref`'s content, at the same index), `arrNew`, `arrReplace`, `roll`, `unroll` (the closed payload type, `wClose`), `lolliE`, `app`, the effect rows within one index | a premise's leaf, the same place, payload type and index | — | `RetainedPay` reads only the place, the payload type and the index [unchecked] |
| the own push (`MonoOwnGUFreeM`, the callbacks), the end of a lend (`withbor`'s answer `['x] B` at the old stack), a binding (the `∀` clause), the thaw | a value carried to another index | `RetainedPayPush`, `RetainedPayPop`, `RetainedPayExtend`; `payExt_inst` (proved, `BinderRows.lean:308`) | to prove [unchecked] |
| a handler's clause reading an operation's argument | a value read at the handler's index | not stated | statement 3's index is not built |

**Not covered at W, apart from `RetainedPay`: the slice borrows.** `sliceBorrowM`, `sliceBorrowI` and
their `U` forms at a family of two or more elements are outside W at every placement and every
stack, at `vRLJ` and `vRLM` alike. The callback runs at its own lend's pushed stack, where no such
family meets the guard (`SliceGuardFails`), so its clause says nothing about the run, and the row's
conclusion has nothing at W to come from [unchecked until `SliceGuardFails` is proved]. The missing
object is a stack entry lending a range of places (§1.2).
`RetainedPaySliceRow` is stated, and it holds vacuously at every count (`R1.lean`'s docstring), so it
is not counted toward `RetainedPay` at the rows introducing a `Mut` or `Imm` value. At one element
at the own lend's place the family is the own lend's view, and the row is the one-place borrow's.

**The route: `BINDER.md` §11's, made precise.**
- **Under the guard, a leaf no entry lends is a retained cell.** The table's second conjunct puts
  every top-level cell at a place no entry lends strictly above the outermost lend
  (`GhostEnd/Stacked.lean:290`; `stratS_single_unbound`, `BinderRows.lean:749`) [read]. At a value
  Core's relation reads at a resource, every leaf `LeafPos` reaches is a top-level cell of that
  resource (Core's `Mut` and `Imm` clauses hold the cell at the leaf's place, `ptoMutS`,
  `ptoImmS`). The read-out's payload is such a value: the view's cell stores Core's relation at the
  payload type. So where a row reads a callback's clause under the guard, every leaf at a place no
  entry lends is a cell strictly above the outermost lend.
- **Such a cell was made outside the frozen computation.** Every lend inside the outermost one is
  fresh below the stack's lifetimes and the reading (`LendFresh`, `SubFresh`; H4) [read], so its
  cells are internal [unchecked: historical, a property of the run that made the cell]. Its payload
  type then reads the variables bound when it was made, which `SubOutside` reads above every lend.
- **At a retained view.** When the view's own place is unlent, its `RetainedPay` gives `PayExt` of
  its payload type, and every leaf's payload type is a part of it: `PayLeavesOfPayExt` (`VFree`
  through each former `LeafPos` crosses, `vFree_subst` at the unrolling).
- **At a nested `Imm` leaf** (`withswap`'s and `withload`'s kept leaves):
  - Core's `Imm` clause gives `CohE`: the program's payload type at the reading is `TyEq` to a record
    `r`'s type at a reading that agrees with `r`'s on it (`Coh`, `AgreeOn`).
  - At the run's world, `RelAboveOfTagged` (§3.3) puts `r`'s tag above the outermost lend: `r` is
    relevant to the read-out resource through the leaf's cell. `RecsOutside` then puts `r`'s
    reading above it.
  - So each variable at a lifetime position reads an external lifetime, when that position's
    lifetime term has no join. A join is pinned by `TyEq` only as a whole, and `PayExt` reads
    variables one by one [unchecked].
- **At a reborrow leaf of `withload`.** `reb_α` makes an `imm` cell at `α`, the own lend's lifetime.
  Under the guard at the pushed stack it is the own lend's view or the guard fails, so
  `RetainedPay` is vacuous there. The same argument makes `RetainedPaySliceRow` vacuous, at every
  count (§1.2).
- **At a nested `Mut` leaf of a bound view's payload** (`withswap` only; `withload` reborrows a
  nested `Mut` position). No record ties a `mut` cell's payload type to a reading: the cell's stored
  predicate is the payload's meaning only (`ptoMutS`). The view's leaf ties its own payload type to
  its entry's, and the route spends that.
  - **The hypotheses the case spends**: the view's `CohS` (a conjunct of `vRLM`'s `Mut` leaf at
    `l`, `innerAt σ αs l = some (e, α)`), which gives `CohKind s e (.mut a T)`, so `TyEq T s e.T s`
    at the stack's reading `s`; that `T` has no join (`NoJoinV T`); and that `T`'s free variables
    are defined at `s` (from `Scoped`, `SubDom` and `Δ.Models` at the row's index).
  - **`TyEq` is positional** (`Core/FrameRecords.lean:195`): at a nested `Mut` it asks
    `a.interp s = a'.interp s` and recurses into the payloads. So every leaf of `(T, v)` has a
    matching leaf of `(e.T, v)` at the same place, the two payload types one type at `s`
    (`LeafPosTyEq`). A variable of the leaf's payload read at an internal lifetime sits in a meet
    term (no join), whose value is then internal; the matching term of the entry's payload type, if
    its free variables are external and its bound ones are read at `⊤`, has an external value
    (`PayExtOfTyEq`). Together: `PayLeavesOfTyEq`, and `RetainedPayLoadMutBound` reduces the row at
    a bound view to the leaves of the entry's payload type.
  - **The leftover is `EntryPayLeaves`**: the stored payload's leaves, read at `e.T`, meet
    `RetainedPay`. `StackJ` lets `e.T` read `Δ`'s variables and the stack's variables, so the index
    does not carry it. **The expected stop is at this fact**, not at "no tie". I have not derived
    `EntryPayLeaves` and have not verified that any obstruction is real.
  - `ViewTypeCoincidence` (proved, `BinderRisk.lean:365`) explains why `CohS` asks for `TyEq` rather
    than the stored meaning: two types coincide in meaning at one reading and not at an
    instantiation. It does not show that nothing ties the types.
  - At a join the transfer fails: `TyEq` pins a join only as a whole, and `PayExt` reads variables
    one by one. The row at a payload type with a join is open [unchecked].
- **The arising check of that stop is `InternalLeafArises`'s second disjunct**, an entry's payload,
  which is `InternalPayloadArises`'s question one level down.
  - `InternalLeafArises`: at a configuration of the revised arising set, a leaf of an arising value,
    or of the payload an entry's cell holds, at a place no entry lends, its cell strictly above the
    outermost lend (what the guard makes of such a leaf wherever a row reads a clause), whose
    payload type reads a stack variable. Every reading reads a stack variable at its entry's
    lifetime, which is internal, so such a leaf fails `RetainedPay` at every reading. Not attempted.
    Expected false [unchecked: historical]. By H4 a cell above the outermost lend was made before it,
    when no stack variable was bound, and its payload type is fixed then: a `Mut` payload is
    invariant, and `∀E` renames a variable to a term read at the same lifetime. The entry's payload
    type, fixed when the entry was pushed, types the Ref the lend lent, whose content is typed
    syntactically, so a nested `Mut` position of `e.T` names the payload type its cell was made at
    [unchecked: historical].
  - Without the condition on the cell's lifetime the check would be too weak. A slice element stored
    in a `Ref` and lent by a later entry is a leaf of that entry's payload at a place no entry lends,
    and its element type may read a stack variable. But the cell is internal, so the guard rejects
    it at the read-out, and the row never reads it.
  - `ReadOutAtInternalPayload` (stated, one line): at `InternalPayloadArises`'s configuration,
    `x`'s payload type `Imm 'b 1` has one leaf, whose payload type `1` reads nothing. So that
    configuration, if it arises, refutes no read-out row.
  - A payload type reading an internal variable that is not a stack variable has no arising form:
    the configuration carries no reading.
- **What a stop at `EntryPayLeaves` would mean, and what is checked then.** `vRLM` reads a `Mut`
  payload by Core's `vC`, so neither the view's leaf nor the entry carries `RetainedPay` of the leaves
  inside the payload, and the read-out hands them on. The global form of the invariant `BINDER.md`
  §11 states in prose is a leaf that carries `PayLeaves` of its payload. It is stated in `R1.lean`
  as a variant clause, not adopted:

  ```lean
  def PayLeavesAt (σ : LStack) (αs : List Life) (s : LSub) (T : VTy) (v : Val) (ρ : WRes) :
      Prop :=
    ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), v = .loc l → ρ.get l = some ψ →
      PayLeaves σ αs s ψ.wit T ψ.erase
  def mutLeafP (σ : LStack) (s : LSub) (a : Lifetime.Life) (T : VTy) (αs : List Life)
      (ls : List SRec) (v : Val) : WProp := fun ρ =>
    vC true (.mut a T) ls s v ρ ∧ CohS σ αs s (.mut a T) v ρ ∧ RetainedPay σ αs s T v ∧
      PayLeavesAt σ αs s T v ρ
  def immLeafP … -- the same at `Imm`
  def VwPayLeaves : Prop :=
    ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : LEnt) (α : Life) (ρ : WRes),
      (e, α) ∈ σ.zip αs → vwEW s e true α ls ρ → PayLeavesAt σ αs s e.T (.loc e.l) ρ
  def ThawLeafP : Prop := …   -- the variant leaf at a bound place, re-established from the view
                              -- handed at an instantiation when it carries `PayLeavesAt`
  ```

  If `RetainedPayLoadMutRow` stops at `EntryPayLeaves`, the builder checks the variant's two costs
  in Lean and reports the outcome, not only the candidate:
  - **`ThawLeafP`, the thaw at a bound variant leaf.** Expected provable [unchecked]:
    `viewSlotInstOB` (`GapRows.lean:163`) for the first three conjuncts; for the fourth, the handed
    view's `PayLeavesAt` at `e.T`, `TyEq T s e.T s` moved by `tyEqInst` (`GapCover.lean:355`), and
    `PayLeavesOfTyEq` at the instantiated reading. It needs `NoJoinV T`, as the read-out does. At a
    retained variant leaf, `PayLeavesAt` moves along an instantiation as `payExt_inst` moves
    `PayExt`.
  - **`VwPayLeaves`, whether W's views carry it as they stand.** Expected refuted, at a
    configuration not shown to arise [unchecked]: `vwEW` is GhostEnd's view at the reading, whose
    cell stores any value of Core's relation at `e.T`, and Core's nested leaves carry no
    `RetainedPay`; an entry whose payload type has a nested leaf reading a stack variable, at a place
    no entry lends, is the shape. It is `EntryPayLeaves` again, at the view.
  - **So the variant needs W's views to carry `PayLeavesAt`**, a change to the draft views (`vwSL`).
    Its producer is the lend, from the lent content: the content is W's at the old stack, whose
    leaves would carry `PayLeaves` under the variant, moved by `RetainedPayPush`. Its consumers are
    `[force]`, which hands the views back as they were, and the share's re-lend, statement 2's. Both
    are [unchecked], and the change is the user's to decide after the report.

  Reading `RetainedPay` at the cell's lifetime instead of its place does not reach the stop: under
  the guard the two agree at a top-level leaf, and the stop is at one.

**The read-out rows' added hypotheses, met** (CLAUDE.md §4). Each read-out row adds the guard at
the read-out resource (or the reborrowed one), `TW W ps rs`, `Tagged W ps ls` and the part's
`ResU.CompS` into `W`: what the row has where it reads the callback's clause, under `guardPV` inside
its run. Each bundle is planned as met at a one-entry stack, with a leaf at a place no entry lends
whose payload type reads a variable, so that the conclusion is not vacuous:
- `RetainedPayLoadMutRowMet`: the stack one 6.65 entry `e` (place `20`, variable `'0`, payload
  `T = Imm 'z ([@'z] 1)`) at `2`; `δ` binds `'z ↦ 1`, external; `e`'s cell at `20` a `mut` cell at
  exactly `2` storing `loc 21`, whose witness is `21 ↦ imm({1}, (), ∅)`. The leaf is at `21`, which
  no entry lends, at lifetime `1`, strictly above the outermost lend; its payload type `[@'z] 1`
  reads `'z`. The world: `TW.empty`, `alloc`, `immFrame` at `21` with frame lifetime `1`, as
  `ShareKeepsTMet`'s (§3.3), `ls = [(p₂₁, 1)]`.
- `RetainedPayLoadImmRowMet`: the same payload behind a 6.64 entry at `2`, its `imm` cell at `20`
  holding `loc 21` with the same witness, and the entry's own frame record at `20`, at `2`, for the
  view's coherence (a second `immFrame`); the own lend at `α = 3`, below `2`, pushing an entry at a
  fresh place `22`. `reb_3` keeps the `imm` cell at `21`, and `Imm̲ 'x T` keeps `T`'s outer `Imm`,
  so the kept leaf at `21` reads `'z`.

The witnesses exercise the proved cases (a nested `Imm` leaf through its record), not the expected
stop.

**The transports' routes.** At a push onto a non-empty stack the cut is unchanged and the reading
agrees at `T`'s variables. Onto the empty stack the cut appears just above `a`, and every reading
value is above `a` (`SubFresh`), so external. A pop is the converse; at `[]` `PayExt` is vacuous
(`cutOf [] = none`). `RetainedPayInstRow`: a variable free in `S[b/'x]` is free in `S` and not
`'x`, read where the callee read it (`'x` is no stack variable), or is a variable of `b`, with `'x`
free in `S`. The callee's `RetainedPay` puts `⟦b⟧` above the cut. With no join, `⟦b⟧` is the shortest
of `b`'s variables' values, or `⊤`, so each of them is at least as long-lived, and external. At
`b = 'v ⊔ 'w`, `⟦b⟧` is the longer of the two, and the shorter may be internal. Already proved:
`retainedPay_of_bound` (`BinderRows.lean:1234`), `retainedPay_of_closed` (`:1229`), `payExt_inst`
(`:308`).

### 3.3 `KeepsT` at the share

**What the share must hand.** `RelendJ`'s extension asks, of the list a consumer hands it at an
instantiation `ι` of the stack and the retained part `ρz` (`stratS αs ρz`),
`Ext (ι.recs ls) ls' ρz ∧ KeepsT (ι.recs ls) ls' ρz`.
- `[force]` supplies it at the list itself, `ThawInstM` by the composite (`ext_inst_comp`), and
  `MonoExtM`'s consumers at a list with the same members.
- The share owes it at a resume. Statement 2 restates `OpenS` with instantiations (`BINDER.md`
  §3.7): `ι` is the share's instantiation at the ghost-ended part's cut, as an instantiation of the
  whole stack (`EmbLift`, `ShareReLendInst`), `ls` is the stop's list, `ls'` the resume's. Core's
  `contShare` quantifies over `Ext ls ls'` at the share's resource (`Core/EffDefs.lean:144`).
- The earlier `ResumeKeepsT` concluded `KeepsT ls ls' ρ` for the uninstantiated `ls`, which is not
  what the clause asks once records move. `ExtInstT` instantiates both lists, so it does not bridge
  the gap either; it is the record half's tool (§2.4).

```lean
def LineageUnique : Prop := …  -- a record lies in one frame's lineage at a TW world
def TagFixed : Prop := …       -- two lists tagged at one TW world hold a record at one tag
def KeepsTOfTagged : Prop := … -- Ext between two lists tagged at one world keeps the tags
def ExtInstT : Prop := …       -- both lists instantiated (the record half, §2.4)
def RelAbove (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ x ∈ ls, Core.Rel x.1 ρ → ∀ o ∈ αs.getLast?, o < x.2
def RelAboveOfTagged : Prop :=
  ∀ (W ρz ρr : WRes) (ps rs : List FrameRec) (ls : List SRec) (αs : List Life),
    TW W ps rs → Tagged W ps ls → ResU.CompS ρz ρr W → stratS αs ρz → RelAbove αs ls ρz
def ExtKeepsTInst : Prop :=
  ∀ (αs : List Life) (ι : Inst) (ls ls' : List SRec) (ρz : WRes),
    InstAt αs ι → stratS αs ρz → RelAbove αs ls ρz → Ext ls ls' ρz → KeepsT ls ls' ρz →
    Ext (ι.recs ls) ls' ρz ∧ KeepsT (ι.recs ls) ls' ρz
def FramesKept (W W' ρz : WRes) (ps ps' : List FrameRec) (ls : List SRec) : Prop :=
  ∀ p ∈ ps, (∃ x ∈ ls, DescR p x.1 ∧ Core.Rel x.1 ρz) →
    p ∈ ps' ∧ ∀ α, FrameLife W p α → FrameLife W' p α
def ResumeKeepsT : Prop :=
  ∀ (W W' ρz : WRes) (ps ps' rs rs' : List FrameRec) (ls ls' : List SRec),
    TW W ps rs → Tagged W ps ls → TW W' ps' rs' → Tagged W' ps' ls' →
    FramesKept W W' ρz ps ps' ls → Ext ls ls' ρz → KeepsT ls ls' ρz
def ShareKeepsT : Prop :=
  ∀ (W W' ρz ρr : WRes) (ps ps' rs rs' : List FrameRec) (ls ls' : List SRec) (αs : List Life)
    (ι : Inst),
    InstAt αs ι → stratS αs ρz → TW W ps rs → Tagged W ps ls → ResU.CompS ρz ρr W →
    TW W' ps' rs' → Tagged W' ps' ls' → FramesKept W W' ρz ps ps' ls → Ext ls ls' ρz →
    Ext (ι.recs ls) ls' ρz ∧ KeepsT (ι.recs ls) ls' ρz
def RelFramesNotEnded : Prop :=   -- a frame FramesKept names is at no lend lifetime of the stack
def ShareKeepsTMet : Prop :=      -- the premises met at a share with a ghost-ended entry
```

**Routes.**
- **`LineageUnique`**, from `TW.inv` (`TI`, `Core/Invariant.lean:2702`).
  - If `d = p`, then `p` is a proper descendant of `p'`, whose location is a `mut` cell of an escrow
    (`SubRec`), while a record proper's location is no `MutAt` (`NoMut`'s first conjunct).
  - Otherwise `d.le` is a `mut` cell of both frames' escrows. A `mut` cell composes with nothing
    (`ResU.CompS.get_right_of_ne_imm`), so the two frames' walks meet [unchecked: the walk lemma
    that two frames' escrows are disjoint is to be found or built from `xpath_unique`,
    `LinPath.functional`].
- **`TagFixed`**: `Tagged` gives frames `p`, `p'` with `DescR` and `FrameLife` at the two tags, and
  `LineageUnique` makes them one. `LeInv` gives the frame's cell in `ag(W)`, an `imm` cell, whose
  lifetime set has a member (`LSet.meet_mem`). `frameLife_eq` (`Core/Wp.lean:502`) makes both tags
  that member.
- **`KeepsTOfTagged`**: `Ext`'s `Keeps` gives a member of `ls'` with the record; `TagFixed` gives its
  tag.
- **`ExtInstT`**: `ext_inst_comp`'s argument (`BinderRows.lean:203`) with one instantiation. The
  second conjunct of `Ext` is at records above the retained part, which the instantiation fixes
  (`mem_recs_iff_of_lt`).
- **`ResumeKeepsT`**: `TagFixed`'s argument across two worlds. For `x ∈ ls` relevant to `ρz`,
  `Ext`'s `Keeps` gives `x' ∈ ls'` with `x'.1 = x.1`. The two `Tagged` give frames `p ∈ ps`, `p' ∈ ps'`
  with `DescR` and `FrameLife` at `x.2`, `x'.2`. `FramesKept` puts `p` in `ps'` at `x.2`,
  `LineageUnique` at `W'` makes `p = p'`, and `frameLife_eq` at `W'` makes `x'.2 = x.2`.
- **`RelAboveOfTagged`**: for `x ∈ ls` relevant to `ρz` through an `imm` cell `ψ` of `ρz` at `m`,
  `Tagged` gives a frame `p` with `DescR p x.1` and `FrameLife W p x.2`.
  - If `m` is `p`'s own location, `FrameLife`'s first conjunct makes every lifetime of `ag(W)`'s
    cell at `m` equal to `x.2`.
  - Otherwise `m` is a lineage location (`LinLoc`: a sub-record's location or a chain position),
    and `FrameLife`'s second conjunct makes them `⊑ x.2`.

  `ψ`'s lifetimes are among `ag(W)`'s at `m` [unchecked: the `AgW` step for a part of `W`;
  `AgW.imm_mem_deep` is the candidate], and `stratS` puts `ψ.at` strictly above the outermost lend.
  So `o < ψ.at ≤ x.2`.
- **`ExtKeepsTInst`**:
  - `KeepsT`: a member of `ι.recs ls` relevant to `ρz` is `ι.rec1 y` with `y ∈ ls`, and `y` is
    relevant too (`rel_rec1`). `RelAbove` puts `y.2` above the outermost lend, hence at or above the
    cut (`cut_le_of_lt`), so `ι.rec1 y = y`, and `KeepsT ls ls'` keeps it.
  - `Ext`'s `Keeps`: the same.
  - `Ext`'s second conjunct: a record strictly longer-lived than a cell of `ρz` is above the
    outermost lend (`lt_of_cellIn`), so it is in `ι.recs ls` exactly when in `ls`
    (`mem_recs_iff_of_lt`).
- **`ShareKeepsT`**: `ResumeKeepsT`, then `RelAboveOfTagged` at the stop's world, then
  `ExtKeepsTInst`.
- **`RelFramesNotEnded`**: a frame `p` relevant to `ρz` through `x` has `FrameLife W p x.2`
  (`Tagged` and `LineageUnique`), and `x.2` is strictly above the outermost lend
  (`RelAboveOfTagged`). Every lend lifetime of a chained stack is at or below the outermost lend.
  So `FrameLife W p α` at such an `α` would give `α = x.2` (`frameLife_eq`), a contradiction.
- **`ShareKeepsTMet`**, a concrete configuration:
  - The stack is one 6.64 entry `e` (place `20`, variable `'0`, kind `imm ()`) at `2`; its frame
    `pe` is at `2`.
  - A kept frame `pk` (place `21`) is at `1`, and `ρz` is its cell `21 ↦ imm({1}, (), ∅)`.
  - The stop's world comes from `TW.empty`, `alloc`, `immFrame` twice, with `ls = [(pe, 2), (pk, 1)]`.
  - `ι` is `shift` at the cut `1`. The resume's world re-opens `pe` at `ι 2 = 3` and keeps `pk` at
    `1`, with `ls' = ι.recs ls`.
  - `FramesKept` names `pk` only, and `Ext ls ls' ρz` holds: `pk` is kept, and no record is
    strictly longer-lived than `1`.

  It meets the premise at a share that is not the identity (`ι.life1 2 ≠ 2`).

**Status, and what stays open.**
- **The item is reduced, not discharged.** `FramesKept` is the premise statement 2's resume
  composite owes (`BINDER.md` §3.7): that the ghost end ends only the ended entries' 6.64 frames,
  and the re-lend leaves every other frame open at its frame lifetime.
- `RelFramesNotEnded` shows that the frames it names are not ghost-ended. Each ghost-ended frame is
  at its entry's lifetime, by `PlaceViewsW`'s 6.64 clause at the arising set (`pvArises`)
  [unchecked as a step of statement 2's composite, which is not built].
- Reported open in §4.
- **Fallback**: if `LineageUnique` is not derived, `TagFixed` and `ResumeKeepsT` at records proper
  (relevance at the frame's own cell, `d = p`), and the sub-record case reported with its step.

`KeepsT` is then not a restriction at lists tagged at one world. The refuted `ExtInst`'s
configuration (`not_extInst`) holds one record at two tags in the two lists, so by `TagFixed` the
two lists are not tagged at one `TW` world.

### 3.4 `ViewSlotInst` at an outermost lend at `⊤` (only if cheap)

`NotViewSlotInst : ¬ ViewSlotInst` by `not_cohEInst`'s configuration (`BinderRefute.lean`) in an
`Imm` view slot: at a cut of `⊤` a record at `⊤` is left alone while the slot's reading moves. Cheap
means: built from `not_cohEInst`'s objects and `vwEW` at one cell, under a hundred lines. Otherwise
not attempted, with that sentence. Every index the relation reads has `OuterBelowTop`, and §3.1
supplies it at every lend and every arising configuration, so nothing reads `ViewSlotInst` as
stated.

---

## 4. Item 4 — statement 0 and OQ-8 reconsidered

### 4.1 Statement 0 at `vRLM`

```lean
def VRLMData : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), A.Data →
    ∀ (ls : List SRec) (v : Val), vRLM p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v
def EnvCore (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (ls : List SRec) : Prop :=
  (∀ n, (wEnv η n).ty = (tEnv ηc n).ty) ∧ ∀ n v ρ, wEnvP η n v ρ ↔ tEnvP ηc n true ls v ρ
def VRLMDataE : Prop :=
  ∀ (p : Placement) (k : Nat) (A : VTy), VTy.DataB k A →
    ∀ (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (σ : LStack) (δ : LSub)
      (αs : List Life) (ls : List SRec) (v : Val),
      EnvCore η ηc ls → vRLM p η σ δ A αs ls v = vCE ηc true A ls (extS δ σ αs) v
def EnvCoreNone : Prop := ∀ ls : List SRec, EnvCore none none ls
def VRLMDataOfE : Prop := VRLMDataE → VRLMData
def NilSoundRetM (p : Placement) : Prop := …   -- NilSoundRet at cRLM
def FutPartI : Prop :=
  ∀ (δ : LSub) (ρz ρn ρ : WRes) (s s' : Stk), ResU.CompS ρz ρn ρ → FutI δ ρ s s' → FutI δ ρz s s'
def Statement0SharedM : Prop :=
  (∀ p : Placement, ExtPreW p) ∧ FutPartI ∧ FutAvoidsTrans ∧ OpenSFBridge ∧
    ∀ p : Placement, NilSoundRetM p
def ForceRowM (p : Placement) : Prop := …       -- ForceRow at SemSM
def CallbackExtMutM (p : Placement) : Prop := … -- CallbackExtMut at vRLM, OwnOKI, the revised index
def CallbackExtImmM (p : Placement) : Prop := … -- the same at 6.64, the list's extension keeping tags
def Statement0M (p : Placement) : Prop :=
  MonoOwnGM p ∧ MonoVM p ∧ MonoGM p ∧ CallbackExtMutM p ∧ CallbackExtImmM p ∧ ForceRowM p ∧
    Statement0UFullM p
def Statement0MBesideMono0 : Prop :=
  Statement0SharedM ∧ CallbackExtMutM .binder0 ∧ CallbackExtImmM .binder0 ∧ ForceRowM .binder0 ∧
    Statement0UFullM .binder0
def MonoUnrestrictedRefuted0 : Prop :=
  ¬ MonoOwnGM .binder0 ∧ ¬ MonoGM .binder0 ∧ ¬ MonoVM .binder0
def Statement0MAtConsumers0 : Prop :=
  Statement0MBesideMono0 ∧ MonoExtM .binder0 ∧ AllIRowM .binder0
```

- `Statement0M` is `Statement0`'s per-placement bundle at the revised relation; W₀'s `ThawRelend` is
  `ThawInstM` there, inside `Statement0UFullM` (`BINDER.md` §5.5).
- **The shared bundle reads the revised futures.** `Statement0SharedM` takes `FutPartI` in place of
  W₀'s `FutPart`, which is about `Fut`: `MonoGMOfMonoVM` needs a `FutI` future at the whole resource
  to give one at each slot's part (§2.1). W₀'s `FutReLend` is not in it. No clause of `binder0` reads
  a future (`FutQI false`), and at `cbpv` and `binder` its place at the revised `U` clause is
  `FutInst` (§4.3, item 2). `ExtPreW`, `FutAvoidsTrans` and `OpenSFBridge` are about definitions the
  revision does not change, and are proved (`statement0Shared`); `FutPartI` is to prove.
- **Three bundles at `binder0`, none of them `binder0`'s status by itself.**
  - `Statement0MBesideMono0`: the facts of statement 0 beside monotonicity.
  - `MonoUnrestrictedRefuted0`: the three unrestricted monotonicity statements' negation, a fact
    about those statements of ProbeD1. It replaces the earlier `Statement0MBinder0Status`, whose name
    read as `binder0`'s status.
  - `Statement0MAtConsumers0`: statement 0 with monotonicity read at its consumers at `binder0`,
    `AllIRowM` for `MonoOwnGM` (§2.1, §2.6) and `MonoExtM` for the rows that move a context along
    the record order (`[let]`, the end of a lend). That these are all of `MonoVM`'s and `MonoGM`'s
    consumers at `binder0` is [unchecked]; the handler's `MonoHide` at `vRLM` is not stated (§2.7).
- **`NilSoundRetM` needs `VRLMData`.** At a data type W's `μ` and Core's are least fixed points of
  one functional at the program's mode. Core's candidate is joint over the mode and the list, and
  a data body reads its variable at the mode and list it is read at (`VTy.DataB`), so the
  comparison is at one mode and one list (`EnvCore`).
  - `VRLMDataE` is by structural recursion on `DataB`. At `μ`, one direction takes W's fixed point
    at Core's `μ` as candidate (closed by the induction hypothesis, then `vC_roll`). The other takes
    Core's at the candidate `(b, ls') ↦ (b = true → ls' = ls → vRLM η (μ) ls)` (closed by the
    induction hypothesis, then `VRLMRoll`).
  - `EnvCoreNone` and `VRLMDataOfE` give `VRLMData`, and `nilSoundRet`'s proof (`Bridge.lean:133`)
    gives `NilSoundRetM`.
- `ForceRowM`: `forceRow`'s proof (`Rows0.lean:186`) with `RelendJ` at the identity, the list itself
  (`keepsT_refl`, `RecUpTo.refl`) and the views handed back as they were; the persistent slots by
  `vRL_empty_of_persistent` at `vRLM` (`μ` by its fixed point).
- `CallbackExtMutM`, `CallbackExtImmM`: `callbackExtMut_own`'s proof (`Rows0.lean:244`) at `vRLM`.
  - The `U` clause at the identity gives the `∀`.
  - Its own-lend conjunct is read at `OwnPushI` (`OwnOKI`, `LtLife`, `ViewAt` from `e.k`,
    `e.T = T`), `RecsOutside (α :: αs)` and `SubFresh δ α`; then the `⊸` clause at the pushed
    stack.
  - The hypotheses beside W₀'s are each a property of the borrow constant's real lend (`BINDER.md`
    §5.5's table), `e.T = T` being the view's `CohS`.

### 4.2 The expected status at `binder0`

| fact | statement | expected |
|---|---|---|
| shared, relation-independent | `ExtPreW`, `FutAvoidsTrans`, `OpenSFBridge` | proved (`statement0Shared`) |
| shared, the revised futures | `FutPartI` | to prove (§2.1) |
| shared, the nil slice | `NilSoundRetM` | to prove (`VRLMDataE`, `VRLMDataOfE`) |
| `[force]` | `ForceRowM` | to prove, mechanical |
| the callback at `σ·y` | `CallbackExtMutM`, `CallbackExtImmM` | to prove, mechanical |
| the thaw and the `U` rows | `Statement0UFullM` | to prove (§1) |
| monotonicity as stated | `MonoOwnGM`, `MonoVM`, `MonoGM` (`MonoUnrestrictedRefuted0`) | refuted at `gd` (§2.3), the scope pin: an index outside the record invariant, a closure no Core value, not shown to arise |
| the consumer | `AllIRowM .binder0` | not derived, the target; the test at `gd` expected to hold at `gdM` (`GdAllIHoldsAtM`) |
| the restricted route | `MonoOwnGMC`, `AllIRowMC`, `AllIRowMCOfMonoOwnGMC` | the reduction to prove; `MonoOwnGMC .binder0` attempted, expected to stop at `WInsideCoreM` at a `U` argument |
| beside | `MonoExtM`, `MonoOwnGUFreeM` | to prove (§2.4), through `MonoExtME`, `MonoOwnUFreeME` |
| the lends below `⊤` | `OuterBelowTopArises` | to prove (§3.1) |
| `RetainedPay`, other rows | §3.2's statements | the view, the transports, `∀E` at an instance with no join to prove; the read-outs: `withload` where no join, `withswap` at a retained view; at a bound view reduced to `EntryPayLeaves`, the expected stop; open at a join |
| the slice borrows | `SliceGuardFails` | not covered at W at two or more elements (§3.2), apart from `RetainedPay` |
| `KeepsT` at the share | `ShareKeepsT` | reduced to statement 2's resume composite (`FramesKept`), not discharged |

**Is `binder0` complete for statement 0's facts?** Suppose the build confirms the table. Then:
- every fact of statement 0 beside monotonicity holds at `binder0` at `vRLM`
  (`Statement0MBesideMono0`);
- the three monotonicity statements are refuted as stated, at a configuration not shown to arise
  (`MonoUnrestrictedRefuted0`). That is a fact about those statements, and `Statement0M .binder0`,
  which bundles them, is refuted as stated with it;
- statement 0 read at its consumers (`Statement0MAtConsumers0`) is not derived: `MonoExtM .binder0`
  holds, and `AllIRowM .binder0` does not follow from any lemma proved here. `NotMonoOwnGM0` does not
  refute it.

So `binder0` is not complete for statement 0's facts, and it has not failed. What remains at
`binder0`: `AllIRowM .binder0`, by the restricted route past its stopping step or by another lemma;
`RetainedPay` at the read-outs past `EntryPayLeaves`; `KeepsT` at the share's resume composite; the
slice borrows (a range entry); `MonoHide` at `vRLM`.

The same mechanism bears on statement 4's `AllRMono` at `binder0` (a `U` value made outside a borrow
used inside it) [unchecked].

### 4.3 What remains at `cbpv` and `binder`

Their `U` clause quantifies over futures, so monotonicity is by construction there (`monoV_fut` at
W₀). At `vRLM` the leaves' `CohS` and `RetainedPay` along a future and the `μ` case are to be added
[unchecked], and the `gd` closure is no value there (`GdNotCbpv`, optional). What they owe is
`BINDER.md` §5.6's list, at `vRLM`:
1. `RelendUI` in place of W₀'s `RelendU` (the re-lend as an instantiation, then the futures); the
   thaw over it, the `μ` case as §1.4's.
2. `FutInst`: an instantiation of a future is a future of an instantiation, with the higher cut at an
   insertion outside the outermost lend. `InsertedFresh` is the field §5.6 asks for. It takes the
   place W₀'s `FutReLend` had at W₀'s `U` clause, which is why `Statement0SharedM` drops
   `FutReLend` (§4.1).
3. `MonoGPart`: the context at a future of the instantiated stack, at the part above the outermost
   lend.
4. The premise at a future's names: a `StackJ` that admits a non-`NsVar` inserted name with a
   hygiene the rows can discharge, or the renaming lemma.
5. `CallbackExt*` at `cbpv` when the bound mentions the binder.
6. The revision's obligations at their rows: §3's statements apply unchanged, and the open items
   with them (`RetainedPay` at the read-outs, `KeepsT` at the share's resume composite).
7. `PVLFut` (the guard at a future), not attempted.

The slice borrows at a family of two or more elements are outside W at every placement and every
stack until a stack entry lends a range (§1.2, §3.2).

### 4.4 OQ-8: what the Lean can decide

- **The rule** (DESIGN §3): OQ-8 is decided against a placement only by a refutation of a statement
  of its `Probe` that passes DESIGN §11: the negation proved, its configuration and values arising,
  and the closed program whose execution reaches them exhibited. A placement survives only by
  `Survives`.
- **Suppose the build confirms §4.2.** Then `binder0`'s three monotonicity statements are refuted
  as stated, at a configuration not shown to arise, and the reason is `binder0`'s placement of the
  quantifier, not a definition the placements share (`GdNotCbpv`; DESIGN §12.3).
  - This does not decide OQ-8 against `binder0`.
  - `NotMonoOwnGM0` does not refute `AllIRowM .binder0`, `[allI]` restated at `SemSM`, which is the
    lemma's only consumer at `binder0`. At `gd` the row's conclusion is expected to hold at the body
    that exercises the closure (`GdAllIHoldsAtM`).
  - Whether the row, or some form of monotonicity, holds at `binder0` is not derived: the restricted
    route is attempted (`MonoOwnGMC`) and its stopping step reported, and no obstruction to either is
    verified.
- **OQ-8 stays undecided**: `cbpv` and `binder` have not been tried at the revised relation (§4.3).
  The decision the probe can still reach is DESIGN §3's. `Survives` at `cbpv` (statement 0 at the
  revised relation, statements 1–4, `GenSelfAccepted`, `ThenRow` and `ReconAccepted`) would decide
  W = `cbpv` (OQ-8 option 2), rank 0 having no placement before it.
- **`GdArises` at the whole configuration is excluded** once `RecsInsideOwnArises` is proved
  (`GdIdxNotArisesOf`). A refutation of `MonoOwnGM` that passed DESIGN §11 would need another
  configuration, such as §2.3's 6.65 variant. DESIGN §3's rule counts statement 0's facts as
  statements of `Probe`, so such a refutation would decide OQ-8 against `binder0`; the report would
  state beside it that the refuted statement is a lemma whose consumer is not refuted (§2.6). The
  choice between `cbpv` and `binder` would still wait on their statement 0.
- No failure of type (a), (b) or (d) is expected from this unit. `SemSMC` is stated, not adopted;
  adopting it would be read against (b) first (§2.6).

---

## 5. Files, order of work, the stop rule

**Files.**

| file | contents |
|---|---|
| `ProbeD1/R1.lean` | the definitions and `def … : Prop` statements of §§1–4 (this design; no proofs) |
| `ProbeD1/Binder.lean` | `LendMutI`, `LendImmI` with H4's consequence (§3.1; definitions only, this revision) |
| `ProbeD1/R1Thaw.lean` | §1: `RelMAgreesJ`, the equations, `VRLMMonoAt`, `VRLMRoll`, `relendJ_sepRange`, `RelendMValueE`, the corollaries, the rows, `Statement0UFullM .binder0`; optional `MuAdjNotVRLM`, `VRLMUnroll` |
| `ProbeD1/R1Mono.lean` | §2: `GdIndex`, `GdRelated`, `gdG` at the pushed stack, `GdNotPushed`, `NotMonoOwnGM0`, `GdNotCore`, `GdNotRecsInsideOwn`, `GdIdxNotArisesOf`, the instance lemmas (with `FutPartI`), `¬ MonoGM`, `¬ MonoVM`; the consumer and the test at `gd`: `AllIRowMOfMonoOwnGM`, `GdMDerivable`, `GdAllIHoldsAtM`, `GdRowRefutation`; the restricted route: `GdCtxNotCore`, `GdRestrictedMet`, `AllIRowMCOfMonoOwnGMC`, `MonoOwnGMC .binder0` (attempted, its stopping step reported); `EnvExtNone`, `EnvPushNone`, `MonoExtME`, `MonoOwnUFreeME`, `MonoExtMOfE`, `MonoOwnGUFreeMOfE`; optional `GdNotCbpv`, `GdReached` |
| `ProbeD1/R1Owed.lean` | §3: `OuterBelowTopPush`, `OuterBelowTopFresh`, `OuterBelowTopArises`; `LeafPos`'s lemmas, `PayLeavesOfPayExt`, `RetainedPayViewRow`, `RetainedPayInstRow`, the transports, `SliceGuardFails`, `RetainedPaySliceRow`, `ReadOutAtInternalPayload`, `LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq`, `RetainedPayLoadMutBound`, `RetainedPayLoadImmRow`, `RetainedPayLoadMutRow` (attempted, expected to stop at `EntryPayLeaves` at a bound view), `RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet`; if the stop is reached, `ThawLeafP` and `VwPayLeaves` (attempted, outcomes reported); `ExtInstT`, `LineageUnique`, `TagFixed`, `KeepsTOfTagged`, `ResumeKeepsT`, `RelAboveOfTagged`, `ExtKeepsTInst`, `ShareKeepsT`, `RelFramesNotEnded`, `ShareKeepsTMet`; optional `NotViewSlotInst` |
| `ProbeD1/R1Stmt0.lean` | §4: `EnvCoreNone`, `VRLMDataE`, `VRLMDataOfE`, `NilSoundRetM`, `FutPartI`, `ForceRowM`, `CallbackExtMutM`, `CallbackExtImmM`, `Statement0MBesideMono0`, `MonoUnrestrictedRefuted0` |
| `ProbeD1/R1AllI.lean` | §2.6, added by the build: the `∀I` row at one context from three transports of it (`allIRowMNKAt0_of`), the transports at contexts reaching no `U` and the row there (`allIRowMNKUFree0`, `allIRowMNKNil0`), `cRLM_step`, `not_subOutsideExtendAny`; the test at `gd` at a derivable body (`gdMtDerivable`, `gdAllIHoldsAtMt`) |

`FutPartI` is read by `MonoGMOfMonoVM`; build it first in `R1Stmt0.lean`, or move it to
`R1Mono.lean`.

`ExtInstT` is read by `MonoExtME`; build it first in `R1Owed.lean`, or move it to `R1Mono.lean`.
`RelAboveOfTagged` is read by both `RetainedPayLoad*Row` and `ShareKeepsT`; build it before them.

**Order of work.**
1. §1 (R1), in `R1Thaw.lean`: `RelMAgreesJ` and the defining equations; `VRLMMonoAt`, `VRLMRoll`;
   `RelendMValueE` case by case, the `μ` case last; the corollaries and the rows. Then the optional
   `MuAdjNotVRLM`.
2. §2, in `R1Mono.lean`:
   - `GdIndex` and `GdRelated` first (its `U` clause is checked outside the build);
   - then `gdG` at the pushed stack and `GdNotPushed`;
   - then `NotMonoOwnGM0` (the scope pin), `FutPartI`, the two instance lemmas, `GdNotCore`,
     `GdNotRecsInsideOwn` and `GdIdxNotArisesOf`;
   - then the consumer: `AllIRowMOfMonoOwnGM`; the test at `gd`, `GdMDerivable`, `GdAllIHoldsAtM`
     and `GdRowRefutation`;
   - then the restricted route: `GdCtxNotCore`, `GdRestrictedMet`, `AllIRowMCOfMonoOwnGMC`, and the
     attempt at `MonoOwnGMC .binder0` along §2.2's route at `⊸`, reporting the step it stops at
     (expected: `WInsideCoreM` at a `U` argument);
   - then `ExtInstT` (§3.3), `EnvExtNone`, `EnvPushNone`, `MonoExtME`, `MonoOwnUFreeME` and their
     corollaries;
   - then the optional `GdNotCbpv`.
3. §3, in `R1Owed.lean`:
   - §3.1;
   - §3.2 in the order `LeafPos`'s lemmas, `PayLeavesOfPayExt`, `RetainedPayViewRow`, the
     transports, `RetainedPayInstRow`, `SliceGuardFails`, `RetainedPaySliceRow`,
     `ReadOutAtInternalPayload`, `LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq`,
     `RetainedPayLoadMutBound`;
   - §3.3's `LineageUnique`, `TagFixed`, `RelAboveOfTagged`, `ExtKeepsTInst`, `ResumeKeepsT`,
     `ShareKeepsT`, `RelFramesNotEnded`, `ShareKeepsTMet`, `KeepsTOfTagged`;
   - then `RetainedPayLoadImmRow` and `RetainedPayLoadMutRow`, and their witnesses
     `RetainedPayLoadImmRowMet`, `RetainedPayLoadMutRowMet`;
   - if `RetainedPayLoadMutRow` stops at `EntryPayLeaves`: `ThawLeafP` and `VwPayLeaves`;
   - §3.4 only if cheap.
4. §4, in `R1Stmt0.lean`: `EnvCoreNone`, `VRLMDataE`, `VRLMDataOfE`, `NilSoundRetM`, `ForceRowM`,
   `CallbackExtMutM`, `CallbackExtImmM`, then `Statement0MBesideMono0` and
   `MonoUnrestrictedRefuted0` from the rest; `Statement0MAtConsumers0`'s status reported with
   `AllIRowM .binder0`'s.
5. Report: the build's outcome as this file's §8 (added before *Unresolved*), README, CHECKPOINT
   ("What remains for tier 2"), DESIGN §15.9. `BINDER.md` §3.2's `LendMutI` block is updated.

**The stop rule.**
- **If R1's route fails** (a case of `RelendMValueE` does not close, or a refutation at a `μ` or
  `fam` slot is found): report the case and the lemma, or the configuration with `MuSlotArises` and
  the closed program if it arises. `vRLJ` stays the draft relation, and items 2 and 3 are still
  done at `vRLJ`: their statements are §2's and §3's with `vRLJ`, `gRLJ`, `SemSJ` in place of
  `vRLM`, `gRLM`, `SemSM`. The `gd` configuration has no `μ`, so §2.3's proofs are unchanged there;
  if `vRLM` elaborates, `RelMAgreesJ` transports them either way.
- **If `NotMonoOwnGM0` is proved**: no further positive attempt at `MonoOwnGM`, `MonoGM` or `MonoVM`
  as stated; no conjunct is added to the guard or the leaves to exclude the closure. The positive
  work goes on at the consumer and the restricted route (§2.6): the test at `gd`, the reduction
  `AllIRowMCOfMonoOwnGMC`, and the attempt at `MonoOwnGMC .binder0` with its stopping step. The
  report must not read as "`binder0` is done", nor present `MonoUnrestrictedRefuted0` as
  `binder0`'s status.
- **If `GdNotPushed` does not close**: report the step, attempt §2.2's route at `⊸`, report where
  it stops.
- **If a body refutes the row at `gd`** (`GdAllIRowRefutes`): `¬ AllIRowM .binder0` by
  `GdRowRefutation`, a refutation of our statement at a configuration not shown to arise; its arising
  check is `GdArises` with `GdIdxNotArisesOf`.
- **§3.2**: if `RetainedPayLoadMutRow` (or `RetainedPayLoadImmRow` at a join) does not close,
  report the step and its arising check (`InternalLeafArises`, `ReadOutAtInternalPayload`). If it
  stops at `EntryPayLeaves`, check the variant's two costs in Lean (`ThawLeafP`, `VwPayLeaves`) and
  report their outcome. The variant itself (`mutLeafP`, `immLeafP`, W's views carrying
  `PayLeavesAt`) is stated, not adopted: it changes ProbeD1's draft relation and views, and is the
  user's to decide after the report.
- **§3.3**: if `LineageUnique` is not derived, the records-proper fallback, and the step reported.
  `ShareKeepsT` is reported as reduced to `FramesKept` in every outcome; statement 2's resume
  composite is not built here.
- **§4**: if the unit runs long, `Statement0M` is stated and the conjuncts not redone are listed as
  "not redone at `vRLM`".
- **Hard stops**: a statement provable only with a guard beside `TW` or a second relation family
  (b), or with two quantifiers (d); any edit to `Core/`, `Paper/` or a printed definition.

**The build.** Iterate with `lake build ProbeD1.<Module>`; `lake build ProbeD1` at milestones. No
`sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`; every theorem's
`#print axioms` within `[propext, Classical.choice, Quot.sound]`. An unproved step in progress is an
enumerated `sorry` in a scratch file, never committed. Work on `targets`; never push.

---

## 6. Report lists (planned; CLAUDE.md §5)

- **Printed objects read**:
  - [TR] 6.64's and 6.65's H4, quoted from the PDF (§3.1; `LendMutI`, `LendImmI`,
    `OuterBelowTopFresh`);
  - [TR] 6.144 (`wp-load-I`, the thunk `gdG`'s run);
  - [TR] 6.43 and 6.116 through `relendJ_sep` (an `imm` view handed back and split);
  - [TR] p. 5's `reb_α` (`ResU.Reb`) at `RetainedPayLoadImmRow`, and 6.66 (`withswap`) at
    `RetainedPayLoadMutRow`;
  - [TR] p. 3's lifetime interpretation (`Life.interp`: `⊓` the shorter, `⊔` the longer) at
    `RetainedPayInstRow` and `PayExtOfTyEq`.

  `μ`, `[L]` and type variables are not BoLo's: Core's clauses are `[spec §6]` and `[spec §9]`
  (`Core/Relation.lean`), and `vRLM` reads them at W's formers.
- **Printed hypotheses unspent**: as `BINDER.md` §11.6 lists, none spent here beyond the above.
- **Our hypotheses spent at each step that has a case to make** (not printed):
  - the nested `Mut` leaf: the view's `CohS` (`TyEq T s e.T s`), `NoJoinV T`, `T`'s variables
    defined at the reading (§3.2);
  - the restricted route: the slots' Core half, moved by `vC_congr` with `CtxFresh` (§2.6).
- **Uniqueness and functionality results** to use:
  - `ResU.Flat.functional`, `ResU.CompS.functional`, `ResU.CompS.get_right_of_ne_imm`,
    `LinPath.functional`, `frameLife_eq`;
  - the strict monotonicity of `Restrat.Emb` (`Inst.life1_lt_iff`);
  - `mem_recs_iff_of_lt` (a record above the cut is fixed);
  - the machine's determinism (`AStep1.deterministic`, `Core/Demonic.lean:117`) for the runs in
    `GdNotPushed`, `GdNotCore` and `GdAllIHoldsAtM`;
  - `TyEq`'s positional shape (`Core/FrameRecords.lean:195`) at `LeafPosTyEq`.
- **Printed lemmas in the run-up that are untranscribed**: none read here. [TR] 6.150 (the
  reborrow) sits beside `withload`'s read-out; its lift at a resuming table (`RebFrameR`,
  statement 2) is stated, not built, and `RetainedPayLoadImmRow` reads only `reb_α`'s resource.
- **Hypotheses added, their scope, and a witness that each is satisfiable**:
  - `KeepsT` and `InsertedFresh` at `MonoVM`, `MonoGM`, `MonoExtM`: §2.1's table names the consumer
    that supplies each; both hold at the list itself and the reflexive future.
  - `MonoOwnGM`'s hypotheses, the revised index, the own-lend conjunct's two facts, and `SemSM`'s
    index at the `∀I` row's judgement: met together at `GdIndex`.
  - `EnvThaws`, `EnvExt`, `EnvPush`, `EnvCore` at the statements under an environment: each holds at
    `none`, which is the corollaries' use (`EnvExtNone`, `EnvPushNone`, `EnvCoreNone`).
  - The guard and the world at `RetainedPayLoadMutRow` and `RetainedPayLoadImmRow`: what the row has
    where it reads the callback's clause (under `guardPV`, inside its run). Not added where a row
    reads none (`RetainedPayInstRow`, the transports). Each bundle met at a one-entry stack with a
    leaf at a place no entry lends whose payload type reads a variable
    (`RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet`, §3.2), so the conclusions are not
    vacuous.
  - **The restriction `gRLMC`** at `MonoOwnGMC`, `SemSMC`, `AllIRowMC` (each live slot also a Core
    value): its scope pinned by `gd` (`NotMonoOwnGM0` without it, `GdCtxNotCore` with it), and met at
    `gd`'s index with a `U` slot (`GdRestrictedMet`). It does not assume the lemma: its hypothesis is
    Core's relation at the slot, not W's at the pushed stack. Not adopted (§2.6's costs).
  - `CtxArisesAt` at `MonoOwnGMA`: `gd` is outside it (`GdIdxNotArisesOf`); not carried through
    `SemSM` (§2.6).
  - `NoJoinL b` at `RetainedPayInstRow`, `NoJoinV T` and `T`'s variables defined at the reading at
    `PayExtOfTyEq`, `PayLeavesOfTyEq`, `RetainedPayLoadMutBound`, `ThawLeafP`: each holds at every
    instance and payload type with no `⊔`, `genSelf`'s `Flag` among them; the join is the case not
    covered, named in Unresolved.
  - `FramesKept` at `ResumeKeepsT` and `ShareKeepsT`: statement 2's resume composite owes it, and only
    frames relevant to the retained part are named. `RelFramesNotEnded` keeps them apart from the
    ghost-ended ones, and `ShareKeepsTMet` meets it at a ghost-ended entry re-opened at a moved
    lifetime.
  - `RecsOutside αs ls'` at `MonoExtM`: holds when `ls'` has `ls`'s members, the `[let]` case.
  - `LendMutI`'s and `LendImmI`'s new field: a transcription of H4, not a hypothesis of a lemma.
- **Carry-over from `vRLJ` to `vRLM`** (§1.2):

  | `vRLJ` results | at `vRLM` |
  |---|---|
  | the configurations and witnesses of `BINDER.md` and `GAP.md` (`k`, `q2`, `adjIndex`, `adj_not_wU`, `adj_not_cRLJ`, `MuSlotIndex`'s closure), all at `VMuFree` types | carry over through `RelMAgreesJ` |
  | `relendJ_mutK`, `relendJ_immK` (one `Mut`/`Imm` leaf, every payload) | carry over: the leaf is the same at `none` |
  | the lemmas about Core's `vC`, `TyEq`, the guard, the index and the instantiation (`vC_mut_boundK`, `vC_imm_retainedK`, `cohEInstOB`, `viewSlotInstOB`, `tyEqInst`, `BinderPV*`, `BinderArise`, `BinderInst`, `GapCover`) | relation-independent: unchanged |
  | `relendJ_value`, `relendJ_valueK`, `relendJ_gSep(K)`, `ctxRelendsThawFree(K)J` (the thaw, every slot type admitted) | not carried; redone by `RelendMValueE` and `CtxRelendsAllM` (§1) |
  | `thawInstJ` (every `C`) | not carried; redone by `ThawInstM` |
  | the four `U` rows (`statement0UThawFreeJ`, `statement0UThawFreeKJ`) | not carried; redone by `Statement0UFullM` |
  | `wU_allPosJ` at a general `C` | not carried; not restated at `vRLM` (its proof reads only the `U` clause's shape, the same at `vRLM` [unchecked]) |
  | statement 0's per-placement facts (W₀ results; never redone at `vRLJ`) | `Statement0M`'s conjuncts, §4 |
  | statement 0's shared `FutReLend`, `FutPart` (W₀'s, at `Fut`) | not carried: `FutPartI` replaces `FutPart`; `FutReLend`'s place at `cbpv` and `binder` is `FutInst` (§4.3) |

---

## 7. The reviews' findings, answered

### 7.1 The first review

The findings given with the first revision, each with the place it is answered. Items 1, 4, 5 and 8
were changed again by the second review (§7.2).

1. **`RetainedPay` at full strength** (major). §3.2 states it per row, at every payload type,
   with `LeafPos`, `PayLeaves` and `SemIdxM`. The read-outs through a `Mut` and an `Imm` view
   (`withswap`, `withload`, `foldImm`) and the slice elements the `[L]` clause reaches are stated,
   with the facts each row has where it hands the leaf on (the guard, the world). The arising-level
   form is stated where a configuration can carry it (`InternalLeafArises`), and §3.2 says why it
   cannot be stated in general.
   - The route is `BINDER.md` §11's, made precise through the table's second conjunct.
   - The expected stop (a nested `Mut` leaf of a bound view's payload) is named, with its arising
     check, `InternalPayloadArises`'s question one level down. `ReadOutAtInternalPayload` shows that
     `InternalPayloadArises`'s own configuration refutes no read-out.
   - Every line of the table is [unchecked].
2. **`KeepsT` at the share** (major). §3.3 states `ShareKeepsT` in the form `RelendJ` consumes,
   with the bridge (`RelAbove`, `RelAboveOfTagged`, `ExtKeepsTInst`). The frames-kept premise
   (`FramesKept`) names only frames relevant to the retained part. `RelFramesNotEnded` keeps them
   apart from the ghost-ended frames, and `ShareKeepsTMet` meets the premise at a ghost-ended entry
   re-opened at a moved lifetime. The item is reported as reduced to statement 2's resume composite,
   not discharged (§3.3, §4.2, §4.3).
3. **`OuterBelowTop` at the lends** (minor). `LendMutI` and `LendImmI` carry H4's consequence, and
   `OuterBelowTopArises` is stated with its induction (§3.1).
4. **The slice rows' new obligation** (minor). §1.2 and §3.2 list it (`RetainedPaySliceRow`), with
   `SliceGuardFails` showing that inside a lend no slice argument of two elements meets the guard
   today. §6 and Unresolved name the missing object.
5. **`NotMonoOwnGM0`'s label and the "not Core" half** (minor). §2.3 and §2.5 label it a refutation
   of ProbeD1's draft statement at a configuration not shown to arise. `GdNotCore` is stated, with
   its proof planned as step 6. The stop rule (§2.7, §5) no longer reads as closing `binder0`.
6. **The prose obstruction at `vRLJ`** (minor). §0 and §1.1 present the change as the brief's route,
   with "I have not derived the `vRLJ` thaw at a `μ` slot and have not verified that any obstruction
   is real".
7. **The environment-generalised statements** (minor). `MonoExtME`, `MonoOwnUFreeME` and `VRLMDataE`
   are stated with their environment hypotheses. Each hypothesis holds at `none`, and each `none`
   form is a stated corollary (§2.4, §4.1).
8. **The "would need" sentence** (minor). §4.4 says that a form of monotonicity at `binder0` is not
   derived and no obstruction to one is verified. §2.6 and Unresolved state the restricted routes in
   Lean.
9. **`GdIndex` against the consumer** (minor). `GdIndex` carries `SemSM`'s index at the `∀I` row's
   judgement (`BindersLow`, `Scoped`, `StackJ`, `SubDom`, `gdΔ.Models`). `gdδ` binds `'0 ↦ 2` as at
   `GdReached` (§2.3).
10. **The slice rows in Unresolved, the programs checked** (minor). §1.2 reads both programs [read]
    and drops the [unchecked] tag. Unresolved lists the slice rows, with the missing object named.
11. **What carries over from `vRLJ`** (minor). §1.2 narrows the sentence, and §6 adds the carry-over
    table.

### 7.2 The second review

The findings given with this revision, each with the place it is answered.

1. **Item 2 ended in a refutation at a non-arising witness, with the positive work halted**
   (major). The `gd` configuration is kept as the scope pin of an added hypothesis, not as the
   result (§2.3, §2.5).
   - (a) The form the `∀I` row at `binder0` reads is stated: the row at `SemSM` (`AllIRowM`), the
     route through `MonoOwnGM` (`AllIRowMOfMonoOwnGM`), and a restricted lemma with the matching
     restriction of `SemSM`: each live slot also a Core value (`gRLMC`, `SemSMC`, `MonoOwnGMC`,
     `AllIRowMC`, `AllIRowMCOfMonoOwnGMC`). The arising form is stated too (`CtxArisesAt`,
     `MonoOwnGMA`), with why the arising set gives the row nothing to supply it from (§2.6).
   - (b) `gd` is outside the restriction (`GdCtxNotCore`, from `GdNotCore`), and the restriction is
     met at `gd`'s index with a `U` slot (`GdRestrictedMet`).
   - (c) The attempt at `MonoOwnGMC` along §2.2's route at `⊸` is planned, with the two facts it
     reads stated (`WInsideCoreM`, `CoreInsideWM`) and the expected stop named [unchecked]; the
     builder reports the step it stops at (§2.6, §5).
   - The row is tested at `gd` directly: a derivable body that exercises the closure (`gdM`,
     `GdMDerivable`), its conclusion there (`GdAllIHoldsAtM`, expected to hold), every derivable body
     (`GdAllIHoldsDerivable`, no route known), and a refuting body (`GdAllIRowRefutes`,
     `GdRowRefutation`), whose arising check is `GdArises` (§2.6).
   - `Statement0MBinder0Status` is replaced by `Statement0MBesideMono0` and
     `MonoUnrestrictedRefuted0`, the latter documented as the unrestricted statements' negation, not
     `binder0`'s status; `Statement0MAtConsumers0` reads statement 0 at its consumers (§4.1, §4.2).
2. **The nested `Mut` stop left `CohS` unspent** (minor). §3.2 routes the case through the view's
   `CohS`: `TyEq T s e.T s` is positional (`LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq`,
   `RetainedPayLoadMutBound`), `CohS` is listed among the hypotheses spent, and the expected stop is
   the leftover `EntryPayLeaves`, the entry's payload type's leaves read at the reading, not "no
   tie". `ViewTypeCoincidence` is placed as the reason `CohS` asks for `TyEq`. §0, §4.2 and §6
   follow.
3. **`RetainedPayInstRow` covered a variable only** (minor). It is restated at every instance with
   no join (`NoJoinL`: a variable, `⊤`, a meet), and the open item is narrowed to the `⊔` instance
   (§3.2, §0, Unresolved).
4. **`NotMonoOwnGM0` and the consumer** (minor). §2.5 and §4.4 say that `NotMonoOwnGM0` does not
   refute `AllIRowM .binder0`. The open route is a `def … : Prop` (`AllIRowM`, `MonoOwnGMC`,
   `AllIRowMC`, `MonoOwnGMA`), so the next unit has a Lean target (§2.6).
5. **`gd`'s index is outside the record invariant** (minor). §2.3 and §2.5 record it
   (`GdNotRecsInsideOwn`, `GdIdxNotArisesOf`) and its cause, `MonoOwnGM` keeping the list across a
   6.64 own push while `CallbackExtImmM` extends it. `GdArises` is stated at the whole
   configuration, the list included, and §2.3 notes the 6.65-callback variant that needs no record.
6. **`Statement0SharedM` read W₀'s futures** (minor). `FutPartI` is stated and put in
   `Statement0SharedM` in place of `FutPart`; `FutReLend` is dropped, no `binder0` clause reading a
   future and its place at `cbpv` and `binder` being `FutInst` (§2.1, §2.3 step 5, §4.1, §4.3, §5).
7. **`ν` not mentioned** (minor). §1.2 and Unresolved say that `cRLM` still hands `ν` to Core's
   relation, that this unit does not need otherwise, and that whether W reads `ν` is open for the
   rows of statements 1–4. `R1.lean`'s `cRLM` docstring says it too.
8. **The read-out rows' added hypotheses** (minor). Each bundle is planned as met at a one-entry
   stack with a leaf at a place no entry lends whose payload type reads a variable
   (`RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet`), from a `TW.empty`, `alloc`, `immFrame`
   world as `ShareKeepsTMet`'s (§3.2, §6).
9. **`RetainedPaySliceRow` is vacuous at every count** (minor). §1.2, §3.2 and §4.2 list the slice
   borrows at two or more elements as not covered at W, apart from item 3, with the missing
   range-lending entry; `RetainedPaySliceRow` is not counted toward `RetainedPay` at the rows, and
   its docstring says why it holds vacuously.
10. **The global invariant deferred without evidence** (minor). The variant leaf is stated in
    `R1.lean` (`PayLeavesAt`, `mutLeafP`, `immLeafP`), with its two costs (`ThawLeafP`,
    `VwPayLeaves`). If the read-out stops at `EntryPayLeaves`, the builder checks both in Lean and
    reports the outcome (§3.2, §5).

---

## 8. The build's outcome

The build is in five files beside the design's `R1.lean`: `R1Thaw.lean` (§1), `R1Mono.lean` (§2),
`R1Owed.lean` (§3), `R1Stmt0.lean` (§4) and `R1AllI.lean` (the `∀I` row, §2.6). `lake build
ProbeD1` builds them. There is no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe`
or `implemented_by`, and every theorem's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]`. Nothing in `Core/`, `Paper/`, `Restrat/`, `GhostEnd/` or
any printed definition changed. `vRLM` is the one draft relation, as designed, and `LendMutI` and
`LendImmI` carry H4's consequence, as designed (§3.1). No relation family, guard, quantifier or
step index was added.

The build states a few things beside `R1.lean`. Each is an added hypothesis, or a stated
obligation at a narrower scope:
- `StackPayAvoids x σ` (`R1Mono.lean`): the pushed variable is free in no entry's payload type.
  `MonoOwnUFreeMEA`, `MonoOwnGUFreeMA` and `MonoOwnGMCUFreeA` are `MonoOwnUFreeME`,
  `MonoOwnGUFreeM` and `MonoOwnGMC`, at contexts reaching no `U`, with it added. Every index
  `SemSM` reads gives it (`stackPayAvoids_of_stackJ`), and it holds at every stack whose entries'
  payload types are closed, `gd`'s among them.
- `RetainedPayLoadMutRowNJ` (`R1Owed.lean`): `RetainedPayLoadMutRow` at a payload type with no join
  (`NoJoinV`).
- `MonoOwnGMAt`, `CtxExtendMAt`, `CtxShadowMAt`, `SemSMNK` and `AllIRowMNKAt` (`R1AllI.lean`): the
  `∀I` row's needs at one context, and the row at the indices whose stack does not name the binder.
- `gdMt` (`R1AllI.lean`): a derivable body for the test at `gd`, in place of `gdM`, which binds the
  thunk before applying `f` to it.

### 8.1 Per statement

**§1, R1: closed at `binder0`** (`R1Thaw.lean`).
- Proved: `RelMAgreesJ` (`relMAgreesJ`), `VRLMMonoAt` (`vRLMMonoAt`), `VRLMRoll` (`vRLMRoll`).
- **`RelendMValueE`: proved** (`relendMValueE`). The proof is structural recursion on the type,
  with the environment generalised (`EnvThaws`):
  - at `μ`, the fixed point's least-ness at the candidate "a `μ` value that thaws under the
    guard". The candidate is closed under the body by the induction hypothesis at the body (at the
    environment that reads the variable at the candidate) and by `vRLM_roll` at each instantiated
    index;
  - at `[L]`, slot by slot (`relendJ_sepRange`);
  - at a variable, by `EnvThaws`;
  - every other case as in `GapRows.lean`, the leaves at their closed types.

  No fuel and no step index.
- Proved: `RelendMValue`, `CtxRelendsAllM .binder0` (`ctxRelendsAllM`), `ThawInstM .binder0`
  (`thawInstM`), and the four `U` rows (`thunkFRowM`, `thunkVRowM`, `bangThunkFRowM`,
  `bangThunkVRowM`).
- **Proved: `Statement0UFullM .binder0`** (`statement0UFullM`). The thaw and the four `U`
  introductions hold at every context.
- Proved: `MuAdjNotVRLM` (`muAdjNotVRLM`). `GAP.md` §4's `μ` slot, whose closure Core's `μ` admits
  by adjacency, is no `vRLM` value.
- Not attempted: `VRLMUnroll`, `MuSlotArises` and `NotMuSlotThawCore`. The `vRLJ` thaw at a `μ`
  slot stays not derived, and no obstruction to it was verified.

**§2, `binder0`'s monotonicity** (`R1Mono.lean`, `R1AllI.lean`).
- **The record half: proved.** `ExtInstT` (`extInstT`), `MonoExtME .binder0` (`monoExtME0`),
  `EnvExtNone`, `MonoExtMOfE`, and **`MonoExtM .binder0`** (`monoExtM0`).
- **The push at a context reaching no `U`.**
  - `MonoOwnUFreeME` and `MonoOwnGUFreeM` as stated: not derived. At the pushed stack a leaf's
    `CohS` reads the old entries' payload types at the pushed reading, and `TyEq` with them needs the
    pushed variable free in them. Neither statement carries that.
  - With it added (`StackPayAvoids`): `MonoOwnUFreeMEA` and `MonoOwnGUFreeMA` are proved at every
    placement (`monoOwnUFreeMEA`, `monoOwnGUFreeMA`). `EnvPushNone` is proved.
  - `MonoOwnGUFreeMOfE`: not attempted. `monoOwnGUFreeMA` is proved slot by slot in the same way, with
    `StackPayAvoids` added.
- Proved: `FutPartI` (`futPartI`), `MonoOwnGMOfMonoGM` (`monoOwnGMOfMonoGM`), `MonoGMOfMonoVM`
  (`monoGMOfMonoVM`).
- **The configuration `gd`.**
  - Proved: `GdIndex`, `GdRelated` and `GdNotPushed` (`gdIndex`, `gdRelated`, `gdNotPushed`).
  - After the own lend pushes `gdY`, `gdG = λ_. load ℓ₁₁` is a `binder0` value at the pushed stack
    over the view (`gdG_pushed`). `gdF` returns it boxed at `'1 ↦ 3`, and no run meets that
    postcondition (`gd_run_fails_of`). The proof uses the machine's determinism, that the memory
    does not change in a β step, the flattening of the view, and `gdG_not_U_empty`.
- **Refuted, at a configuration not shown to arise**: `MonoOwnGM .binder0` (`notMonoOwnGM0`),
  with `MonoGM .binder0` and `MonoVM .binder0` (`notMonoGM0`, `notMonoVM0`;
  `MonoUnrestrictedRefuted0`). These are facts about ProbeD1's draft statements, not `binder0`'s
  status.
  - Two facts count against `gd` arising, each a theorem about our statements: its closure is no
    Core value (`gdNotCore`), and its index fails the record invariant (`gdNotRecsInsideOwn`,
    `gdIdxNotArisesOf`). Neither is a theorem about the arising set: the glue from `GdNotCore` to
    `ArisesVI` is not written, and `RecsInsideOwnArises` was not attempted.
  - Not attempted: `GdArises` and `GdNotCbpv`. So `gd` is not shown not to arise either.
- **The consumer, `AllIRowM .binder0`: not derived. It is proved at every context whose live slots
  reach no `U`, at every index whose stack does not name the binder** (`allIRowMNKUFree0`;
  `allIRowMNKNil0` at the empty context).
  - Carrying the premise to the two places the `∀` clause asks it (`allIRowMNKAt0_of`) shows that
    the row reads three transports of its own context, not one:
    - across the own push (`MonoOwnGMAt`, `MonoOwnGM` at one context);
    - to the reading extended at the binder, for the first conjunct (`CtxExtendMAt`);
    - after the push, to the reading extended at the pushed variable, which the stack already reads
      there (`CtxShadowMAt`).
  - At a context reaching no `U` all three hold (`monoOwnGMAt_uFree`, `ctxExtendMAt_uFree`,
    `ctxShadowMAt_uFree`). There `vRLM` reads the reading only through `extS`, at the free
    variables of the slot types and of the entries' payload types (`vRLM_reading_uFree`).
  - At a `U` slot none of the three is derived. The global forms (`CtxExtendM`, `CtxShadowM`) are
    stated and not derived.
  - At an index whose stack's innermost entry is named by the binder (`StackJ`'s third kind), the
    first conjunct's premise needs `SubOutside` at the extended reading. `subOutsideExtend` gives
    it only for a binder new to the stack, and it is not kept in general
    (`not_subOutsideExtendAny`).
- `AllIRowMOfMonoOwnGM` as stated: its `binder0` instance holds vacuously (`NotMonoOwnGM0`), and it
  was not attempted at `cbpv` or `binder`. The route it names does not supply the two reading
  transports that the proof of `allIRowMNKAt0_of` uses.
- **The restricted route** (§2.6 (ii)).
  - Proved: `GdCtxNotCore` and `GdRestrictedMet` (`gdCtxNotCore`, `gdRestrictedMet`). `gd` is
    outside the restriction, and the restriction is met at `gd`'s index with a `U` slot.
  - `MonoOwnGMC .binder0`: not derived. It is proved at contexts reaching no `U`
    (`monoOwnGMCUFreeA`, with `StackPayAvoids`).
  - The step at a `U` slot was not attempted in Lean. What reading the clause shows
    [unchecked]:
    - the pushed stack's `U` clause asks for the body at every instantiation of the pushed stack;
    - the slot's Core half is at the old reading, so it applies only at the identity;
    - at another instantiation the route needs Core's relation carried along the instantiation.
      That statement at every type, `InstEquivLeafAll`, is refuted (`not_instEquivLeafAll`, at a
      configuration not shown to arise), and its `U` instance is not derived;
    - at the identity it needs `WInsideCoreM` at the argument, and Core inside W at the answer's
      computation type.
  - Not attempted: `WInsideCoreM`, `CoreInsideWM`, `AllIRowMCOfMonoOwnGMC`, and the arising form
    `MonoOwnGMA`.
- **The row at `gd`** (§2.6 (i)).
  - Proved: `GdRowRefutation` (`gdRowRefutation`).
  - `GdMDerivable`: not proved. [unchecked: read against `CDerives`, `Core/Fundamental.lean`]
    `gdM` as written has no derivation in the rule set: its application passes a thunk literal
    where `app` takes a variable. `GdAllIHoldsAtM` (at `gdM`) was not attempted.
  - **The test at a derivable body: the conclusion holds.** `gdMt` is
    `λr. let t = thunk (forget r) in let g = f t in let h = return g in force h`. It is derived from
    `CDerivesNU`'s rules, so it is in the rule set (`gdMtDerivable`, through `probeRules_of_nu`).
    At `gd`'s index the row's conclusion holds at it (`gdAllIHoldsAtMt`):
    - at both conjuncts of the `∀` clause, the own lend's pushed stack included, where the argument
      may be the pushed view;
    - the run hands `gdF` the thunk holding the argument, takes it back, forces it, and forgets the
      cell. The answer `()` holds nothing, and the cell goes to the garbage (`gdMtS_run`);
    - the run never reads `gdF`'s relation, so the box at `'1` that `GdNotPushed` turns on is never
      asked.

    So at the body that exercises the closure where `MonoOwnGM` fails, the row's conclusion
    survives. One body is evidence, not the row at `gd`.
  - Not attempted: `GdAllIHoldsDerivable` and `GdAllIRowRefutes`.

**§3, the three obligations** (`R1Owed.lean`; `retainedPayPush` is in `R1Mono.lean`).
- **`OuterBelowTop`: proved at every lend and at the arising set.** `OuterBelowTopPush`,
  `OuterBelowTopFresh` and **`OuterBelowTopArises`** (`outerBelowTopPush`, `outerBelowTopFresh`,
  `outerBelowTopArises`, by induction on `ArisesI` from `LendMutI`'s and `LendImmI`'s new field).
  `NotViewSlotInst`: not attempted.
- **`RetainedPay`, row by row.**
  - Proved:
    - `RetainedPayViewRow`, the lend's view;
    - `RetainedPayPush`, `RetainedPayPop` and `RetainedPayExtend`, the transports;
    - `RetainedPayInstRow`, `∀E` at every instance with no join;
    - `PayLeavesOfPayExt`, `LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq` and
      `RetainedPayLoadMutBound`;
    - `ReadOutAtInternalPayload` and `ThawLeafP`.
  - **`RetainedPayLoadMutRow` (`withswap`'s read-out): not derived as stated. It stops where §3.2
    expected.** At a retained view it holds at every payload type
    (`retainedPayLoadMutRow_retained`). At a payload type with no join it follows from
    `EntryPayLeaves` (`retainedPayLoadMutRowNJ_of_entry`). `EntryPayLeaves`, the entry's payload
    type's leaves, is the leftover the index does not carry. Its arising check
    (`InternalLeafArises`) was not attempted.
  - The variant leaf: `ThawLeafP` is proved (the thaw re-establishes it at a bound place).
    `VwPayLeaves` was not attempted. The variant is stated, not adopted.
  - Not attempted: `RetainedPayLoadImmRow` (`withload`, `foldImm`), `RetainedPayLoadMutRowMet` and
    `RetainedPayLoadImmRowMet`.
  - The slice rows: `SliceGuardFails` is proved. `RetainedPaySliceRow` is proved but vacuous, and
    is not counted.
- **`KeepsT` at the share: reduced.**
  - Proved outright: `ExtInstT`, `RelAboveOfTagged` (`relAboveOfTagged`) and `ExtKeepsTInst`
    (`extKeepsTInst`).
  - Proved from `LineageUnique` (a record lies in one frame's lineage at a `TW` world): `TagFixed`,
    `KeepsTOfTagged`, `ResumeKeepsT`, **`ShareKeepsT`** and `RelFramesNotEnded`
    (`tagFixed_of`, `keepsTOfTagged_of`, `resumeKeepsT_of`, `shareKeepsT_of`,
    `relFramesNotEnded_of`).
  - `LineageUnique`: not derived. The records-proper case reads `TI`'s location clauses. The
    sub-record case needs two frames' escrows to meet at no `mut` cell, which is a walk lemma on
    `ex(W)` not found among `TW.inv`'s consequences. I have not derived it and have not verified
    that any obstruction is real.
  - `ShareKeepsTMet`: not attempted. `ShareKeepsT` stays reduced to `FramesKept`, which statement 2
    supplies.

**§4, statement 0 at `vRLM`** (`R1Stmt0.lean`).
- Proved: `VRLMDataE`, `VRLMData`, `EnvCoreNone` and `VRLMDataOfE`. At a data type `vRLM` is
  Core's, the two least fixed points compared both ways.
- Proved: `NilSoundRetM` (`nilSoundRetM`) and `Statement0SharedM` (`statement0SharedM`, with
  `FutPartI`).
- Proved: `ForceRowM` at every placement (`forceRowM`), and `CallbackExtMutM` and `CallbackExtImmM`
  at `binder0` and `binder`.
- **`Statement0MBesideMono0`: proved** (`statement0MBesideMono0`). Every fact of statement 0
  beside monotonicity holds at `binder0` at `vRLM`.
- `Statement0M .binder0` as stated: refuted together with the unrestricted monotonicity statements
  it bundles (`not_statement0M_binder0`), at a configuration not shown to arise. This is not
  `binder0`'s status.
- **`Statement0MAtConsumers0 ↔ AllIRowM .binder0`: proved** (`statement0MAtConsumers0_iff`).
  Read at its consumers, statement 0 at `binder0` is exactly its `∀I` row. The row holds at
  every context reaching no `U`, at every index whose stack does not name the binder, and is not
  derived elsewhere.

### 8.2 What remains

- **The `∀I` row at `binder0`.** It is open in two places:
  - at a context with a live `U` slot, where it reads the three transports of §8.1 (`MonoOwnGMAt`,
    `CtxExtendMAt`, `CtxShadowMAt`). `MonoOwnGM` is refuted there at `gd` when unrestricted, and
    the restricted step was not attempted in Lean;
  - at an index whose stack's innermost entry is named by the binder.
- **`RetainedPay`.**
  - `EntryPayLeaves` at a bound `Mut` view.
  - `RetainedPayLoadImmRow`.
  - A join.
  - The slice rows' missing range-lending entry.
  - The `Met` witnesses.
- **`KeepsT` at the share**: `LineageUnique`, and `FramesKept` from statement 2.
- **`StackPayAvoids`**, missing from `MonoOwnUFreeME` and `MonoOwnGUFreeM` as stated.
- **`cbpv` and `binder`**: not redone at `vRLM`. Their list is `BINDER.md` §5.6's, with `FutPartI`
  in place of `FutPart`.
- Unchanged by this unit: `ν` is still read by Core's `cC`, and `ViewSlotInst` without
  `OuterBelowTop` is still not derived.

### 8.3 Report lists (CLAUDE.md §5)

- **Printed objects read**:
  - [TR] 6.64's and 6.65's H4 (`LendMutI`, `LendImmI`, `outerBelowTopArises`);
  - [TR] 6.144 (`wpTS_load_I`, `gdG`'s run in `gdG_pushed`);
  - [TR] 6.149's frame (`wpTS_frame_noOwn`, the forgotten cell in `gdMtS_run`);
  - [TR] p. 3's lifetime interpretation (`Life.interp`) at `RetainedPayInstRow` and
    `PayExtOfTyEq`.

  `μ`, `[L]` and type variables are Core's (`[spec §6]`, `[spec §9]`), read at W's formers.
- **Printed hypotheses unspent**: none spent beyond the above.
- **Uniqueness and functionality results.**
  - Used: the machine's determinism (`AStep1.deterministic` through `ARun.rest`, in
    `run_beta_val`); `ResU.CompS.functional`, `ResU.Flat.functional` and `AgW.functional`;
    `frameLife_eq` (`frameLife_unique`); `mem_recs_iff_of_lt` (`extInstT`, `extKeepsTInst`).
  - Not used: `LinPath.functional`.
- **Printed lemmas in the run-up that are untranscribed**: none read here.
- **Hypotheses added**:
  - `StackPayAvoids`, held at every index `SemSM` reads;
  - `NoJoinV` at `RetainedPayLoadMutRowNJ`, held at every payload type with no `⊔`;
  - `LineageUnique` in the `KeepsT` chain, not derived;
  - `EntryPayLeaves` at `retainedPayLoadMutRowNJ_of_entry`, not derived (the expected stop);
  - the three transports at `allIRowMNKAt0_of`, discharged at every context reaching no `U`.
- **The technique built**: no printed proof governs W's draft relation, so no printed route was
  replaced. The thaw at `μ` is the fixed point's own induction (`vCE`'s route, at W), not a step
  index.

### 8.4 What it decides

- **R1 is closed at `binder0`.** W reads `μ` and `fam` itself, and the thaw and the four `U`
  introductions hold at every context (`statement0UFullM`).
- **Statement 0 at `binder0` reduces to its `∀I` row** (`statement0MAtConsumers0_iff`). The row
  holds at contexts reaching no `U`, at indices whose stack does not name the binder
  (`allIRowMNKUFree0`). Unrestricted monotonicity is refuted at `gd`, a configuration not shown to
  arise. That refutes a lemma for the row, not the row: at `gd` the row's conclusion holds at a
  derivable body that exercises the closure (`gdAllIHoldsAtMt`). The row's remaining cases are not
  derived.
- **OQ-8 is not decided.** No refutation passed DESIGN §11, and `cbpv` and `binder` were not redone
  at `vRLM`. No failure of type (a), (b) or (d) occurred: no guard beside `TW`, no relation family
  beside W, and no second quantifier. The fallback is not triggered.

---

## Unresolved

- **The second review's major finding, after the build** (§7.2 item 1: item 2 ended in a
  refutation at a non-arising witness, and the positive work halted). The build's answer was not
  reviewed again. Each part of the fix, with its status:
  - (a) The target and the restricted forms are stated (`AllIRowM`, `MonoOwnGMC`, `SemSMC`,
    `AllIRowMC`, `AllIRowMCOfMonoOwnGMC`, `CtxArisesAt`, `MonoOwnGMA`). Built beside them:
    - the row at one context (`allIRowMNKAt0_of`), whose proof uses two reading transports the
      planned route does not supply;
    - the row at every context reaching no `U` (`allIRowMNKUFree0`).
  - (b) Done. `gd` is outside the restriction (`gdCtxNotCore`), and the restriction is met at
    `gd`'s index with a `U` slot (`gdRestrictedMet`).
  - (c) Partly done. `MonoOwnGMC` is proved at contexts reaching no `U` (`monoOwnGMCUFreeA`). The
    step at a `U` slot was not attempted in Lean; §8.1 names the stop by reading the clause
    [unchecked].
  - The test at `gd` with a derivable body: done, at a corrected body. `gdM` as written has no
    derivation in the rule set [unchecked]. `gdMt` binds the thunk first, is derived
    (`gdMtDerivable`), and the row's conclusion holds at it at `gd`'s index (`gdAllIHoldsAtMt`).
  - The rename: done. `Statement0MBinder0Status` is replaced by two statements, both proved:
    `Statement0MBesideMono0`, and `MonoUnrestrictedRefuted0`, the unrestricted statements'
    negation (not `binder0`'s status).
- **`AllIRowM .binder0`** (open; the target). This is `[allI]` at `SemSM`, `MonoOwnGM`'s only
  consumer at `binder0`. By `statement0MAtConsumers0_iff` it is all that statement 0 at `binder0`
  still owes at its consumers. It is proved at every context reaching no `U`, at every index whose
  stack does not name the binder (`allIRowMNKUFree0`). Open:
  - **at a live `U` slot**: the three transports (`MonoOwnGMAt`, `CtxExtendMAt`, `CtxShadowMAt`).
    The routes, each stated in Lean:
    - through the restriction: `MonoOwnGMC` (each live slot also a Core value), `SemSMC`,
      `AllIRowMC`. §8.1 gives the expected stop at a `U` slot [unchecked]. Adopting `SemSMC` has
      costs, to be read against DESIGN §12.2 (b) first (§2.6);
    - through the arising set: `MonoOwnGMA` with `CtxArisesAt`. Its matching restriction of
      `SemSM` needs a transition that carries a value across a lend, which `ArisesI` lacks
      [unchecked];
    - `CtxExtendMAt` and `CtxShadowMAt` at a `U` slot: `vRLM`'s `U` clause reads the whole reading
      (`SubFresh δ α`, `RelendJ`'s `ι.sub δ`), so a change of reading is not invisible there.
  - **at an index whose stack's innermost entry is named by the binder** (`StackJ`'s third kind):
    `SubOutside` at the extended reading is not given (`not_subOutsideExtendAny`).

  At `gd` the row's conclusion holds at one derivable body that exercises the closure
  (`gdAllIHoldsAtMt`). At every derivable body (`GdAllIHoldsDerivable`) it has no known route:
  `gdF` is in neither relation at the pushed index.
- **The slice borrows** (not covered at W; not attempted). `sliceBorrowM`, `sliceBorrowI` and their
  `U` forms at a family of two or more elements. The callback runs at its own lend's pushed stack,
  where no such family meets the guard (`SliceGuardFails`), at every stack and placement. The
  missing object is a stack entry lending a range of places. The elements' `CohS` would read
  against it, and their `RetainedPay` would be vacuous at its places. The element operations at the
  empty stack owe no more at `vRLM` than at `vRLJ`.
- **`RetainedPay` at the read-outs** (open).
  - At a bound `Mut` view the build stops where expected, at `EntryPayLeaves`
    (`retainedPayLoadMutRowNJ_of_entry`).
  - The variant leaf (`mutLeafP`, `immLeafP`) is stated, not adopted. Of its two costs, `ThawLeafP`
    is proved and `VwPayLeaves` was not attempted. The variant needs W's views to carry
    `PayLeavesAt`, a change to the draft views, which is the user's to decide.
  - Not attempted: `RetainedPayLoadImmRow` and the two `Met` witnesses.
- **A join** (`⊔`).
  - At `∀E` at `'v ⊔ 'w`, `⟦'v ⊔ 'w⟧` external says nothing of the shorter of the two.
  - In a payload type at the read-outs, `TyEq` pins a join only as a whole.

  `RetainedPay` is not carried there. Neither program reaches it [unchecked].
- **`ν`** (open for statements 1–4). `cRLM` hands a `ν` computation to Core's `cC` whole, so the
  values a `ν` unfolding gives are read with Core's `U` and `ℕ`-`∀` inside. This unit does not need
  W to read `ν`. Whether it should is open for the rows of statements 1–4.
- **`KeepsT` at the share** (reduced, not discharged). `ShareKeepsT` is proved from `LineageUnique`
  (`shareKeepsT_of`), which is not derived. `FramesKept` is for statement 2's resume composite to
  supply. `ShareKeepsTMet` was not attempted.
- **`StackPayAvoids`**. `MonoOwnUFreeME` and `MonoOwnGUFreeM` as stated lack it and are not derived.
  The forms with it are proved (`monoOwnUFreeMEA`, `monoOwnGUFreeMA`).
- **`InternalLeafArises`** (not attempted). It is the arising check for the stop at a read-out: its
  second disjunct is `EntryPayLeaves`'s failure at a configuration of the arising set.
- **`RecsInsideOwnArises`** (stated in `Binder.lean`, not attempted). `GdIdxNotArisesOf` reads it.
- **`cbpv` and `binder` at `vRLM`** (not redone). Their list is `BINDER.md` §5.6's, with `FutPartI`
  in place of `FutPart`.
