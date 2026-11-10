# #835: where proof ends and assertion begins, for a handler that parks `κ` across an open borrow

Kernel target: none. Design and literature investigation; it changes no Lean in the tree.

Read on branch `rule-791-kstop` (head `048686bd`), read-only. One probe was typechecked at that
commit; every result in it has axioms `[propext, Classical.choice, Quot.sound]`. The probe and the
papers read are kept in the project's scratch archive, not in this repository.

> **Status (2026-11-09).** A design note written on the pre-merge branch `rule-791-kstop`
> (`048686bd`). It is kept for its analysis of where the handler assumption sits.
> - **What landed.** Recommendation (A) landed on main through #839 as `HandlerLawN` (decision 75),
>   with `goal791N : HandlerLawN → Goal791N` in `Core/Chain/Adequacy791N.lean`. The statement on
>   main has no `InFrag` premise and types the program at `.comp (.ret .unit)`; §5.1's form is the
>   branch's.
> - **What is still open.** Shrinking the assumption to (C), `StopReadNW`, is #838's target and is
>   not done.
> - **Names not on main.** `HandlerLawNW`, `StopReadNW`, `not_kapRelFoldToR` and `stopReadNW_ret`
>   exist only in the scratch probe.
> - **Later work.** It predates #844 Tier 1 (#861) and §68 (#889).

**Frame (the user's, relayed 2026-11-06).** The kernel proves properties of the calculus, never of
programs. A scheduler, `with_timeout`, `select`, `task_group` or a stored generator is a
well-typed program and the fundamental theorem has to cover it; no per-program contract
(`SchedOKN`, `HandlerOKK`) and no per-program proof (`hs_schedOKN`) belongs in the top-level
result. Whatever makes parking `κ` across an open borrow safe lives in the typing rules: a rule
the checker checks, or, where a rule's compatibility cannot be proved with this relation, an
assertion about that rule or something smaller beneath it, in the style of `PinLaw`.

Everything not checked in Lean is marked **not verified**.

---

## 0. Summary

1. **Soundness.** No counterexample found. Every channel through which code running while `κ` is
   parked could reach the borrowed cell is closed by typing already in the tree (`Row.Suspend`'s
   payload and answer clauses, `kTy`'s linearity, `VTy.OwnFree` excluding `U`, cancellation
   through the lend frame's finaliser). The informal argument ("while `κ` is parked the borrowed
   cell is reachable only from code inside `κ`") holds of the machine for every case the brief
   lists; where the *relation* disagrees with it, the disagreement is the relation's reading of
   the world, not a behaviour of the machine. Verdict: probably sound for every `CDerives`-typed
   program whose lend rows meet `Row.Suspend`. **Not verified**: no adequacy-level proof, and the
   falsifier is programs, as for `PinLaw`.
2. **The boundary** is one fact: a `κ` captured under a lend at floor `A` is owed along
   `KW.Owed A` (`ExtP A` at its share), and a value handler reads it at `𝒱⟦U C⟧`, which is
   `KW.OwedR` (`ExtR`, no floor). `owedR_not_owed` says the orders differ; `not_owedRFoldTransfer`
   says the Mut Frame cannot produce `OwedR`; `not_kapRelFoldToR` (probe) says the pointwise
   bridge from one to the other is false. The root is that the per-run world forgets a lend the
   moment its frame is folded into the lender's share, while `ExtR` protects only keys that the
   *share* still names. Nothing else is in the way: every other producer and consumer is
   mechanical or resumes in place.
3. **The smallest useful assertion** is not a relation-level lemma over `κ`: every such lemma is
   refuted by the stuck `κ = ()` configurations already in the tree. It is a lemma quantified over
   *derivations*, beneath the three handler rules:
   `StopReadNW` (probe): a typed computation in the relation where every entry owes along
   `KW.Owed` is in the relation where the entries at one name owe along `KW.OwedR`. From it,
   `effHandleV`, `effHandleVB`, `reify` and the tail/last handlers at any entry are proved (by
   reading, not built), with no side condition on any rule. Ranked by content:
   (E) pointwise over `κ` — **refuted**; (C) `StopReadNW` — smallest sound candidate;
   (B) the three handler rules at marked operations only; (A) `HandlerLawN` as it stands, at the
   `KW` block (`HandlerLawNW`, probe); (D) `PinLaw`'s placement, the suspending lend's
   compatibility at the `ExtR` reading — larger reliance, loses the proved lend headlines, not
   recommended.
4. **Literature.** Nothing proves what we would assert at a type interpretation with stratified
   lifetimes. Affect proves typed storing and resuming of one-shot continuations (no borrows);
   Hazel, de Vilhena–Leroy and Yarrow prove, per program in Iris, exactly the informal argument
   (`isCont₁`, `Stack κ`: a parked continuation *owns* its stack and its regions, which are
   revoked from everyone else until resumption). They are provable without assertion because
   Iris is the collapsed model: every proposition is stable, and the "island" of the lend is owned
   by `κ`, not forgotten by a per-run world. The cost of that world structure for us is rebuilding
   `vN`/`cN` in Iris (the `iris-lean` fallback), not a change of order. The Rust side has no
   published proof of borrows across `.await` or of `Pin` (Jung's thesis, ch. 15: "a full
   soundness proof for Pin will thus involve reasoning about both unsafe code and coherence of
   trait implementations").
5. **Recommendation.** Replace `Goal791SchedN`/`Goal835` by plain adequacy for closed typed
   programs with their handlers inside (`Goal791N` below), the one hypothesis being the
   assertion. Land (A) now (it is `rule-791`'s `HandlerLawN` restated at `KW`; nothing refutes it,
   `handle_resume_inst` is its witness); then shrink to (C) at marked names once E10 at `OwedR`
   entries is built, keeping the per-operation mark `ub` only as the type-level carrier of
   "performed under a borrow" that decides which programs rely on the assertion. Drop the handler
   contract, the stack theorem, the `effHandleT`/`effHandleL` side conditions (R1) and
   `Row.UBOnly` as a refusal; keep `Row.UBOnly` as an inferred, always-satisfiable bookkeeping
   fact if the mark is kept at all.

---

## 1. The soundness verdict

### 1.1 What is reachable while `κ` is parked

At a stop inside a lend's callback the machine state is `K[perform n i v]`, with the lend frame
(`Const791`'s callback frame) inside `K`. The handler gets `κ = kappaC b ℓ H K` and the payload
`v`. In the relation (`erwpK`, `TabK835N`): the stop's share `ρk` holds the continuation's
resources, the payload's share `ρa` holds `v`'s; the Mut Frame folds the lent cell `mut(A, …)`
of the borrowed share into `own` in the lender's share (`extP_foldFrame`). So after the fold:

- `ρk` (what `κ` owns): the lent cell as `own` at `ℓ`, every other local of the task, every
  outer lend frame's cell. The lender's `Ref` and the callback's view are both `loc ℓ`, both
  inside `K`.
- `ρa` (what the handler is handed): the payload. `Row.Suspend` (`Core/TreeGoal791.lean:73`)
  asks `VOutlives ∅ bnd o.A`, which at a closed bound `⊤` excludes, outside a box or `!`, every
  `Imm`/`Mut` at a variable lifetime, every `U C` and `Unk`; a `[@⊤] U C` passes but holds no
  borrow cell (`CellU.InStratum ⊤` asks a cell strictly longer-lived than `⊤`). So the payload
  cannot carry the view, a closure over it, or a borrow into the lend's stratum.
- The handler's own resources, disjoint from both.

So the cell at `ℓ` is in `ρk` and only there, and the only way to reach `ρk` is to run `K`, i.e.
to resume or cancel `κ`. That is the informal argument, and the relation agrees with it
resource-wise. What the relation does *not* agree with is the world (§2).

### 1.2 The stress cases

| Case | Mechanism that closes it | Verdict | Checked |
|---|---|---|---|
| Other code takes a lend at a longer lifetime than `A` while `κ` is parked | The new lend is on another cell (separation: `ρk` is disjoint from the handler's resources). Lifetimes are ghost; a key above `A` changes nothing the machine does | Relation artifact (§2.2): `famL A P Θ` reads `Θ.above A`, so the stored family at `(ℓ, A)` is no longer `famL A P Θ′` once a key is added above `A`; `mutL` then fails at `Θ′ + (ℓ, A)` | By reading. The Lean fact is `not_extRFoldTransfer`/`not_owedRFoldTransfer`; that it is harmless for the machine is **not verified** |
| `imm` records added or dropped while parked | Records relevant to `ρk` are kept by `ExtR`'s `Keeps` at `ρk`; a record at exactly `A` cannot enter `κ` through the answer (the answer's `Imm` is at `δ('b) ≥ bnd > A`, and `immCell` asks the cell at least that long-lived); `FoldInv A` is a clause of `KW.Owed` | Artifact of the per-run world (the lender's world forgot `A`, so freshness may pick `A` again) | By reading |
| The lender's own exit | It is code inside `K`; it runs only after a resume. `vN_local` needs the result in `Res_A`, and the lent cell at `A` is not in `Res_A` (`CellU.InStratum A (.mut m) := m.β ⊐ A`, strict), so a result cannot smuggle the cell out | Sound | Lean: `vN_local`, `CellU.InStratum` |
| `κ` never resumed (parked forever, program ends) | `kTy` at `lin`/`cancel` is `U(…)`, linear: the handler state holding it must be consumed; the only consumes are resume and cancel. A program that ends with `κ` in a live slot does not type | Sound | By reading of `kTy`, `not_release_kappa` (Core) |
| The handler raises or is cancelled while holding `κ` in its context | `effLet`'s `hW : S.Cancels → Γ₂.OwnFree`, and `VTy.OwnFree` has no `.thunk` case (`Core/EffRules.lean:1086`): a context holding `κ : U(…)` cannot be left behind by an abort. `κ` must first be stored or consumed | Sound; a real case the typing already refuses | Lean: `VTy.OwnFree` |
| Cancellation of the parked `κ`, cleanup performing effects | The cancel runs `K†` from inside `K`: the lend frame's finaliser runs the owner's consume `d`, the cell is freed; the cleanup's stops are stops *under the lend* (mode `true`, `KW.Owed`) caught by the handlers around the cancelling one. A κ-keeping handler of such a stop is the same shape again (another parked `κ` under the same lend), covered by the same assertion | Sound given the assertion; no cancel-row restriction needed | By reading of `cancelOKK`, `finSched` |
| `κ` resumed twice | `q ≠ unr` on every suspending row (`Row.Suspend`), so `κ` is linear (`kTy`'s `U`, not `!`); R2 `refuses_R_clauses`; BOXED-κ's `[@d] K` is still linear | Sound | Lean (Core): `kTy`, `Row.Suspend` |
| `κ` captured under nested lends | The stop's floor is the innermost `A`; every outer lend frame is inside `K`; each outer frame re-enters at a world keeping `FoldInv` at its own floor `g ≥ A` (`KW.Owed`'s last clause). Same shape, more frames | Sound given the assertion | Lean: `kw_owed_fold`, `KW.Owed.foldInv` |
| The answer carries borrowed data into `κ` | `Row.Suspend`'s answer clause: free of `'x`, `VOutlives ∅ bnd`. So the answer's borrows live at `≥ bnd > A`, i.e. into cells whose lends enclose the handler itself, and the handler's `kTy` mentions those lifetimes through `B`, so the stored `κ` cannot leave their callbacks. No thunk answers except `[@⊤] U C`, which owns no borrow cell | Sound | By reading of `Row.Suspend`, `kTy` |
| A payload thunk closing over the view (`U(F 1)` is free of `'x`) | Excluded: `U C` has no `VOutlives` rule, so it fails `Row.Suspend`'s payload clause unless boxed at a closed lifetime, and a box at `⊤` holds no borrow cell | Sound; this is the one place a syntactic "free of `'x`" test alone would have been unsound, and the tree already uses the semantic clause | Lean: `Row.Suspend`'s docstring enumerates exactly this |

### 1.3 Verdict

Probably sound, for every program `CDerives` types with the suspending lend constants
(`Const791.OK`, `Row.Suspend` on the callback row), with any handler of `CDerives` catching the
suspending operation, including `effHandleV`, `effHandleVB`, `reify`, stored generators,
`handle_with`, an in-language `with_timeout`/`select`/`task_group` and an in-language scheduler.

**Not verified.** No Lean configuration was found or built that refutes it, and none was found
that proves it: the only Lean statements of the relevant shape (`KapRelKTyN`, `KapRelFoldToR`,
`ExtRFoldTransfer`, `OwedRFoldTransfer`) are pointwise over `κ` or over worlds, and those are
false for reasons (§2.2) that have no machine counterpart. What would falsify the verdict is what
falsifies `PinLaw` (`docs/async-capabilities.md` §4.3): a typed program using a κ-keeping handler
over a suspending lend that gets stuck, leaks, or answers outside its type on some run. The
adversarial list of `docs/async-capabilities.md` §6.2 applies with "stored generator" replaced by
each of the four program shapes above.

---

## 2. The exact boundary

### 2.1 Proved today (branch `rule-791-kstop`)

- The Kripke stop `erwpK` with the floor chosen at the stop and `FoldInv` kept
  (`SI/ErwpK.lean`); the constant-world embedding (`erwp_eq_erwpK`); the generic laws.
- The public order `ExtP` and its fold (`LocTy.ExtP.fold`, `extPFoldTransfer`,
  `extP_foldFrame`, `kw_owed_fold`): a lender's stop under a live lend at `A` is owed along
  `ExtP A`, and that order survives the Mut Frame.
- The two orders `KW.Owed` and `KW.OwedR`, `KW.Owed.owedR`, `contShareK_owedR_lo`,
  `contShareK_owedR_U`, `vN_thunk_iff_kapRelR`: an entry owing along `OwedR` hands a clause
  exactly `𝒱⟦U C⟧`'s quantifiers (E10's world step).
- The typed tables `tabNK` with per-entry orders, the Mut Frame's premises at `KW`, the list
  frames, `erwpK_handleLe_le` (a handler at `erwpK`, clause premise at every world).
- The lend headlines `constN_w2`/`w3`/`wF` at the one-world block; the `KW` block `cNW Sch`
  beside it with its laws re-proved.

### 2.2 The one step that does not go through, exactly

The clause of a κ-keeping handler receives `KapRelK … en …` with `en.wk f y ρk = x.Owed f y ρk`
(the stop's entry is under a live lend, floor `f = A`). It must read `κ` at `𝒱⟦kTy …⟧`, which is
`KapRelR`: `cN` of the resumption at every `Θ′` with `x.Θ.ExtR Θ′ ρk`, every consistent view, every
list. So the step is

    x.Owed A y ρk  ⟸  x.OwedR y ρk        for every y reached by U

and it fails at the world level: `owedR_not_owed` (a key added above `A` is an `ExtR` move at the
share `∅`, not an `ExtP A` move). It fails at the fold: `not_extRFoldTransfer`
(`Kappa835N.lean:261`) and `not_owedRFoldTransfer` (review probe): `ExtR` at the lender's share,
which holds `ℓ` as `own`, admits a key `(ℓ₂, β)` with `β ⊐ A`; `ExtR` at the borrowed share,
which holds `ℓ` as `mut` at `A`, refuses it (`CellIn ρk A` protects `Θ.above A`). And it fails at
`κ`: `not_kapRelFoldToR` (probe), from `flooredExit_inst` and `not_kapRelR_world`: the stuck
`κ = ()` meets `KapRelP α` (no `Mut 'x` answer at `β ⊐ α` exists in any public extension at `α`)
and fails `KapRelR` (`ExtR` reaches the world with the key at `β`, where `()` is stuck).

**Why the fold loses the information.** `LocTy.ExtR Θ Θ′ ρ` protects a key `(l, a)` only when
`CellIn ρ a`: the share holds a borrow cell no longer-lived than `a`. After the fold the lender's
share holds `ℓ` as `own`, so no key is protected on its account; the world `Θ` of the lender never
held `(ℓ, A)` at all (the lend's island lives only in the callback's run). The floor `A` in
`ExtP A` is exactly the island state the world has to remember on the lender's behalf; `OwedR`
has no floor. This is `scope-835-public.md` §6.1 ("the world is per run, not global") seen from
the handler's side.

**Why it is a reading, not a behaviour.** A key `(ℓ₂, β)` above `A` is another task's lend of
another cell. The borrowed run's `Mut 'x T` value fails at `Θ′ + (ℓ, A)` only because `mutL`
asks `Θ′ ℓ A = some (famL A P Θ′)` while the stored family is `famL A P Θ₀`, and
`famL a P Θ j u r := P (Θ.above a) j u r` differs as a function once `Θ′.above A ≠ Θ₀.above A`.
For a payload type with no thunk the two are extensionally equal (`vNE` at `int` ignores `Θ`);
for a payload with a `U C` inside they differ in the *set of extensions quantified over*, not in
anything the machine does. **Not verified** that the typed instances agree; this is the content
of candidate (C).

### 2.3 Is the obstruction only this mismatch?

Yes, at this relation. Checked by reading against the producer/consumer census of
`scope-835-kripke-stop.md` §2:

- Every producer meets `Owed f` (the M class mechanically, Fm/Fi/Fa through the folds).
- Every consumer but one resumes in place (`erwp_handle_tail`, `_last`, `_handleS`,
  `last_contN`), which `KW.owed_self`/`KW.owed_of_post` give at every floor.
- The one consumer that reads a stop as a *value* is `𝒱⟦U C⟧` at `kTy`: `effHandleV`,
  `effHandleVB` (boxed, still `U`), and `reify`'s loop. That is E10, and it is the mismatch above.
- The tail/last clauses whose answering function stops with `κ` in its frame (the reason for the
  §2.4 side conditions of `scope-835-qualifier.md`) are the same mismatch one frame out: the
  outer stop must owe `κ`'s resumption along the outer entry's order. If the outer entry owes
  `Owed f′`, the clause can choose `f′ = κ`'s own floor (`contShareK`'s `∃ f ≤ lo`; `κ`'s
  `KapRelK` supplies one), and `ExtP`'s clauses restrict to the sub-resource (`ExtR.mono`). So at
  an all-`Owed` reading the tail/last handlers need **no side condition** — by reading, **not
  verified**. The side conditions arise only at a *mixed* reading, where the outer entry owes
  `OwedR` and `κ` owes `Owed f`.

There is one more statement-level obstacle, not a soundness one: the relation is one mutual block,
so "the entries at `n` owe along `OwedR`" is a parameter of `cN` (`CNW835N`'s `Sch`), and `cNW S ⊆
cNW S′` fails at `⊸` (review F2). A bridge between readings has therefore to be stated at
`SemJNW` with the hypothesis and conclusion at different readings (candidate (C)), not as a
pointwise inclusion.

### 2.4 Could a different world order, value reading or restricted class move it cheaply?

| Option | What it would do | Why it does not move the boundary cheaply |
|---|---|---|
| **A global world** (the lender's world keeps `(ℓ, A)` while `κ` is parked, as Core's record list does) | Fresh lifetimes would be chosen below `A`, so no key is ever added above a parked lend | `ExtR` is *resource-relative*: a key with no borrow cell in the share is not protected whatever the world holds. One would need `U` Kripke along the world-relative `ExtA`, which the chain abandoned because a lend's exit removes a key (`vN_local` moves along `extR_of_add`; `ExtRLit791`, D4). Cost: `vN`'s `U` clause and the 12 lend exits. Not cheap |
| **`U` along `ExtP` at a floor** (`scope-835-kripke-stop.md` §5 routes 1/2) | Both sides read one floored order | `flooredExit`: a lender's later stop at the lowered floor is not readable by a handler at its own floor; route 2's floor-raising lemma is not derived. Not cheap, and it moves the problem to the lend's exit |
| **The share remembers the island** (a ghost "lent at `A`" component left in the lender's share by the fold, so `CellIn ρkL A` holds and `ExtR` protects `A`) | Mirrors Yarrow's `Stack κ` and de Vilhena–Leroy's `isCont₁`: the parked `κ` *owns* its island | A new resource kind touches `CompS`, `Valid`, `NoOwn`, `↭`, `InStratum`, every frame. It is the principled in-model analogue of the Iris solution, and the only option here that would make E10 a theorem at κ-keeping handlers over suspending lends. Not cheap; not designed |
| **Typed continuations** (a preservation-style invariant typing `K`, structure.md §5's cactus invariant) | "`κ` from typed code" becomes syntactic, so a relation lemma may quantify over typed `κ` | A different proof architecture from the logical relation; not this track |
| **A restricted class of parking handlers** (`HandlerOKK`: resume only at `KW.Owed` worlds) | Provable today (`erwpK_handleLe_le`) | It is a per-program contract, which the frame rules out. It also cannot type a `κ` stored in a `CDerives`-typed state: the state's type says `U(…)`, read at `OwedR` |

---

## 3. The smallest useful assertion

### 3.0 The form

Following `PinLaw` (`Core/PinLaw.lean`, `docs/async-capabilities.md` §4.2): a `def … : Prop`,
every quantifier over code a quantifier over `CDerives` derivations or over `SemJN(W)` of typed
terms, never pointwise over configurations, `κ` or worlds; a hypothesis of the theorems, never an
`axiom`; non-vacuous; not refuted by any configuration in the tree; listed in the trusted base
with an issue; reliance reported by the checker per site.

All statements below are over the `Sch`-parametrised block `CNW835N` (`SemJNW Sch`), with
`Sch = fun _ => True` the reading where every entry owes along `KW.Owed` and `(· ≠ n)` the reading
where the entries at `n` owe along `KW.OwedR`. Once the block is canonical (`scope-835-qualifier.md`
§5) the parameter is the per-operation mark; until then the name predicate stands in for it.
Lean text is from the probe and elaborates.

### 3.1 The candidates, ranked by content (largest first)

**(A) `HandlerLawNW` — the three handler rules, every row, at the all-`Owed` reading.**
`rule-791`'s `HandlerLawN` restated at `KW`:

```lean
structure HandlerLawNW : Prop where
  handleV  : HandleVNW  (fun _ => True)   -- HandleVN  over SemJNW
  handleVB : HandleVBNW (fun _ => True)   -- HandleVBN over SemJNW
  reify    : ReifyNW    (fun _ => True)   -- ReifyN    over SemJNW
```

Content: `effHandleV`, `effHandleVB`, `reify` wholesale, including the part E10 would prove at
entries with no lend inside. Needs: nothing else (no mark, no `Sch`, no contract, no side
condition on T/L by §2.3). Reliance: every program with a value handler or `reify`. That is worse
than `main` for ordinary programs, whose `handleV_compatC` is proved on Core's relation.

**(B) The three rules at marked operations only.** The asserted half of (A):

```lean
def HandleVNWAt (Sch : UInt32 → Prop) : Prop :=
  ∀ {Δ Γ Γ₁ Γ₂ H e S E fs n A R}, Sch n →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
    SemJNW Sch Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))) →
    n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    Row.divB (Row.ofEff n E 0 fs ++ S) = false →
    SemJNW Sch Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) →
    SemJNW Sch Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
```

(and `HandleVBNWAt`, `ReifyNW` at `Div` marked). The other half, `¬ Sch n → …`, is E10 at `OwedR`
entries (`contShareK_owedR_U` + Core's `handleV_compatC` step by step; not built). Needs: the
mark `ub` carried by `OpSig`/`CTy.eff` (R2, 309 patterns), `Row.UBOnly` on lend rows so that
unmarked entries never have a lend frame inside (inferred, never a refusal), E10 built, and either
the §2.4 side conditions on T/L or (C). Reliance: only programs that catch a marked operation in a
κ-keeping handler. Ordinary programs stay unconditional, as on `main`.

**(C) `StopReadNW` — the bridge beneath all of them.**

```lean
/-- A typed computation in the relation where every entry owes along `KW.Owed` is in the
relation where the entries at `n` owe along `KW.OwedR`, the order `𝒱⟦U C⟧` reads. -/
def StopReadNW : Prop :=
  ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (n : UInt32),
    CDerives Δ Γ e j →
    SemJNW (fun _ => True) Δ Γ e j →
    SemJNW (· ≠ n) Δ Γ e j
```

Content: exactly the one fact of §2.2, for typed computations. From it, by reading:
`effHandleV`/`effHandleVB` (apply it to the handled computation `e` at the handler's name, then
E10 is Core's step), `reify` (at `Div`), and `effHandleT`/`effHandleL` at any entry (a stop of the
answering function at an `OwedR` entry can resume `κ` anywhere, because `κ` is `OwedR` by the
bridge). So no side condition on any rule. With the mark, it is assumed only at marked `n`; at an
unmarked `n` the two readings agree on the entry and it is a theorem. Reliance as (B). Needs: the
canonical `KW` block (qualifier §5), the fundamental theorem parametrised by the reading
(`RowRd`'s `M`), E10 built.

Why it is smaller than (B): (B) = (C) + the mechanical rest of `handleV_compatC` at `erwpK`
(return clause at the outer table, tags, cancel tables); (B) also leaves T/L needing their own
clause or side conditions.

**(D) `LendFrameN` — `PinLaw`'s placement, at the lend rule.** Assert the suspending lend's
compatibility at the `OwedR` reading, over *typed* callbacks (as `LendFrame` quantifies over
`CDerivesP … M`); then every handler is proved by E10 with every entry `OwedR`. Content: the
fold at `ExtR` for typed callbacks. Needs: the lends as rules of the judgment (a `CDerivesS` like
`CDerivesP`), because `ConstN` quantifies the callback semantically and the semantic form is the
pointwise one, which junk callbacks refute (`PinLaw`'s lesson, `core_not_relend_kU`). Reliance:
every program with a suspending lend, whatever catches it; and the proved headlines
`constN_w2`/`w3`/`wF` would no longer be what adequacy uses. Not recommended: it is `main`'s R1
status on a new relation.

**(E) A relation-level lemma over `κ` — refuted.** The brief's example, "a parked `κ` captured
under a lend at floor `f` stays owed along `ExtR` once the lend is folded":

```lean
def KapRelFoldToR : Prop :=
  ∀ f C δ Θ k κ ρ, KapRelP f C δ Θ k κ ρ → KapRelR C δ Θ k κ ρ
theorem not_kapRelFoldToR : ¬ KapRelFoldToR      -- probe; from flooredExit_inst
```

The same at the world level is `owedR_not_owed`, and at the fold `not_owedRFoldTransfer`. The
refutation-free variant must restrict `κ` to continuations of typed code, which the relation
cannot say about a machine continuation; stated over the derivation of the computation that
produced `κ`, it is (C).

### 3.2 Non-refutation, configuration by configuration

Every configuration in the tree that touches this step, and why it is not an instance of (A), (B)
or (C). The test is the one `PinLaw` passed: the candidates quantify over `CDerives` derivations
and `SemJNW` of typed terms; each configuration below is pointwise over a `κ`, a world or a share.

| Configuration | What it quantifies | Instance of (A)/(B)/(C)? |
|---|---|---|
| `Kappa835N.not_kapRelKTyN`, `not_kTy_world`, `not_kTy_view` | the one-world `KapRelN` at the thunk `κ = ()` and the old `vN` | No: `()` is no `[op]` step's `κ` (`kappa_ne_unit`, `kappaC_ne_unit`, `rule-791`), and the statements are at the one-world block |
| `Kappa835N.not_extRFoldTransfer` | `LocTy`, `ExtR` at two shares | No: no program, no `κ` |
| `not_owedRFoldTransfer` (review probe) | `KW.OwedR` at two shares | No: as above |
| `LendExit835N.flooredExit`, `flooredExit_inst`, `not_kapRelR_world`, `kapRelP_floor_world` | `KapRelP`/`KapRelR` at `κ = ()` | No; they refute (E) |
| `ProbeAssert.not_kapRelFoldToR` | (E) itself | Refutes (E) only |
| `LendExit835N.owedR_not_owed` | two `KW` worlds, empty share | No |
| `LendExit835N.not_owed_post_lower`, `not_tabLe_post_lower` | `KW.Post` lowering the floor | No; the typed instance uses `KW.PostK` (equality) |
| `Public835N.not_extP_foldConfig`, `not_extP_world`, `not_kapRelP_world`, `not_kapRelP_view`, `kapRelN_not_kapRelP` | `ExtP`/`KapRelP` at `κ = ()` | No |
| `KStopSpike835N.extP_not_foldInv` | `ExtP` and `FoldInv` on worlds | No |
| `ExtF.not_extFoldTransfer` (D8) | Core's `Ext` on record lists | No |
| `ImmShape791N.coreMutImm_not_extF`(`_inst`) (#829) | Core's `Imm` shape along `extF` | No |
| `RebAgreeCex.not_rebReentryAgreeN`, `UpdN.not_mutMutMemberStep`, `Depart831N.not_unwindArgStepLoc`, `ImmRec791N.not_wlImage*`, `FdTypes.not_fdFromLifetimeTypes` | other pointwise statements | No |
| `reseal_untyped` (named in memory; not found in this tree) | by its name, an untyped configuration | Not checked here |

No configuration in the tree quantifies over derivations. **Not verified** that no *typed*
instance refutes (A)–(C): that is the soundness question of §1, answered "probably sound, not
verified".

### 3.3 Non-vacuity

- **(A), (B).** `handle_resume_inst` (`rule-791`, `HandlerLaw.lean`): the handler `resumeH`
  (`h_ret = λx. x`, one clause that receives `κ` and resumes it once) meets the conclusion over
  every handled computation at every outer row, through `erwp_handle_le`; `handleVN_resume_premises`
  and `handleVBN_resume_premises` discharge every premise at `perform (1, (0, ()))`. Restating it
  at `erwpK_handleLe_le`/`KW` is `scope-835-qualifier.md` §3.3's `handlerOKKW_resume`, not built;
  the clause resumes at its own world, which `KW.owed_self` gives at every floor. **Not verified**
  at `KW`.
- **(C).** In Lean (probe): `stopReadNW_ret` and `stopReadNW_ret_premises`: `StopReadNW`'s shape
  at `return ()`, every premise discharged, a run with no stop reading no order (`cNW_ret_iff` at
  both readings). Beyond that, by reading: (i) `StopReadNW` is a *theorem* on the lend-free
  fragment, since every producer but the lend frames is mechanical at any reading
  (`erwpK_perform` is generic over the entry's `wk`), so the fundamental lemma at the mixed table
  proves it there (not built: it is the `RowRd`-parametrised fundamental theorem);
  (ii) a witness with a stop under a live lend exists for an `int` payload, because
  `famL A (vN int) Θ` does not read `Θ` and `mutL` is then stable under a key above `A`, so the
  Mut Frame at `OwedR` goes through for that payload — **not verified**.
- **(D).** As `PinLaw`'s `LendFrame`: the straight-line borrower. Not pursued.

### 3.4 What each candidate costs and buys

| | (A) `HandlerLawNW` | (B) three rules at marked ops | (C) `StopReadNW` at marked `n` | (D) `LendFrameN` |
|---|---|---|---|---|
| Asserted content | 3 rules, all rows | 3 rules, marked rows | one bridge, marked names | the lend's fold at `ExtR`, typed callbacks |
| Build before it can be the hypothesis | `KW` block canonical (qualifier §5, units 2+5) | + mark (unit 1), E10 (unit 6) | + fundamental lemma over the reading (`RowRd`), E10 | lends as rules; re-pointing |
| Relies for | every value handler / `reify` | κ-keeping handlers of marked ops | the same | every suspending lend |
| T/L side conditions (R1) | none needed (§2.3) | needed, or inferred marks, or (C) | none | none |
| Mark needed | no | yes | yes (to shrink; not to state) | no |
| Headlines `constN_*` kept and used | yes | yes | yes | kept, not used by adequacy |
| Available | now (restate `rule-791`'s file at `KW`) | after units 1, 2, 5, 6 | after those plus the reading-parametrised fundamental lemma | no |

---

## 4. Literature map

Files: `papers/` has `dnb-icfp10`, `dnb-jfp12`, `adr-popl09`, `dvp-popl21` (Hazel),
`blaze-popl26`, `affect-popl25`, `yarrow-2607.15876`, `timany-birkedal-icfp19`,
`devilhena-leroy-call1cc`, `voigt-dynamic-wind-2025`, `schuster-all-about-that-stack-2021`,
`jung-thesis-2020`, and (one directory up) `tang-soundly-handling-linearity.pdf`. System C
(Brachthäuser, Schuster, Lee, Boruch-Gruszecki, OOPSLA 2022) was read through its artifact
pages; Osvald et al. (OOPSLA 2016) through its abstract.

| Work | What it proves | Moves our boundary? | Justifies the assertion? |
|---|---|---|---|
| **Dreyer–Neis–Birkedal** ICFP'10 / JFP'12 | Kripke worlds with public/private transitions; `K⟦τ⟧` reads public futures; with `call/cc` the two orders must be collapsed (§7.2, Lemma 10). One-shot continuations do not restore private transitions (§9.3 encodes `call/cc` from one-shot + a cell) | No. It fixes the *shape*: `κ` is a value, so the stop and `U` must read one order — which is why `OwedR` at the handler and `Owed f` at the lend cannot both be kept without an assertion | Indirectly: it says the mismatch is structural, not a missing lemma |
| **Ahmed–Dreyer–Rossberg** POPL'09 | Single-order islands, laws, populations | No | — |
| **Timany–Birkedal** ICFP'19 | Iris logical relation for `call/cc`/`throw` with higher-order state; `cont(τ)` interpreted through the evaluation-context relation; the bind rule fails, recovered as `clwp` ("the bind rule holds for `e`"); a web server storing continuations verified | **Yes, at the cost of the model**: in Iris every proposition is stable under frame-preserving updates, references are invariants, so there is no public/private order to reconcile and a stored continuation is just an owned wand. For us that is rebuilding `vN`/`cN` in Iris (`iris-lean` fallback), not changing `ExtR` | It shows the parked-`κ` step is provable in a collapsed, ownership-based model |
| **Hazel** (de Vilhena–Pottier POPL'21) | Separation logic for effect handlers; one-shot continuations as wands, affine (runtime one-shot check); bind restricted to neutral contexts; the frame goes *inside* the continuation's wand (Monotonicity/Frame), i.e. the continuation owns the frames it captured | As above (Iris). Its neutral-context restriction is about which handler a perform reaches, not about our frame (`scope-835-public.md` §7) | Program logic: per-program proofs, no type interpretation |
| **Blaze** POPL'26 | Relational logic; `unsound-bind`; one-shot via a semantic flip-bang | As Hazel | — |
| **Affect** (van Rooij–Krebbers POPL'25) | An affine type-and-effect system; one-shot continuations stored in unrestricted references (`Ref τ` as `&Cell<τ>`, `replace` not `load`); **type soundness by a logical relation in Iris**, so storing and later resuming a one-shot continuation that owns affine resources is sound for every typed program (`iter2gen`, promises) | The closest to "proves what we would assert" on the control side. No lifetimes, no borrows, no stratified world: the stored family above the key does not exist there | Yes for the `κ`-ownership half; nothing for the lend half |
| **de Vilhena–Leroy**, *You Only Get One Shot* (call/1cc, submitted) | `isCont₁ k Q` is non-persistent and *owns* the stack and resources the continuation needs: `isCont₁ k (v. P ∗ Q v) ∗ P ⊢ isCont₁ k Q`; frame and bind both hold; cooperative multithreading with stored continuations verified, the permission `R` transferred at `yield`/`fork` | As Hazel. It is the formal statement of the informal argument: while parked, the continuation's resources are owned by it and nobody else can touch them | Yes, as a program-logic fact; it is why §1's verdict is "probably sound" |
| **Yarrow** (Mathiasen–Timany–Birkedal, arXiv 2607.15876) | Regions + one-/multi-shot handlers in Iris; `Stack κ`; **EWP-Do-Once**: performing a one-shot effect "deallocated all the references that the continuation of the effect handler captures in its regions" for the handler, and gives them back on resume (temporary revocation); using a local reference of a fiber not on the current stack is UB; the handler may push or pop regions (`κ₁′` arbitrary); async scheduler verified as a program (`task`, `sched`) | As the Iris works. Its "handler may open regions longer-lived than the captured ones" is exactly the `ExtR` move the fold refuses; Yarrow allows it because regions have no stratified meaning (`scope-835-public.md` §7) | The region analogue of the informal argument, proved; unary logic, no types |
| **Tang–Hillerström–Lindley–Morris**, *Soundly Handling Linearity* POPL'24 | Control-flow linearity per operation (`A ↠^Y B`), read by `T-Seq` and `T-Handler`; syntactic soundness; the Links bug | No. It is the precedent for a per-operation type-level mark (`ub`), and §2.2's "the handler reads the signature's annotation, not the row's kind" is the argument that the mark must be type-level (§5.2 below) | — |
| **System C** (Brachthäuser et al. OOPSLA'22) and **Osvald et al.** OOPSLA'16 | Second-class capabilities; a continuation may be stored only boxed with its capture set (scheduler case study: `enqueue(q, box { () => resume(true) })` at type `() => Unit at {p, schedule}`, the queue "second-class itself and valid only within the context of the `scheduler` region"); syntactic soundness, mechanised | No. It is the discipline of our BOXED-κ (`[@d] K`, `CtxOutlives`): a parked continuation may not outlive the scope of the capabilities it captured. No linear or mutable borrows | Supports the typing side (what a stored `κ` may mention) |
| **Schuster–Brachthäuser–Ostermann**, *All About That Stack* 2021 | Regions and control effects unified; "the continuation will always be called in exactly the same region that it was based in" (scoped resumptions); Coq, progress/preservation | No. It is the *refuse parking* discipline: resume in place only (our tail/last handlers, `Restrict835`) | — |
| **Voigt–Schuster–Brachthäuser**, *Dynamic Wind for Effect Handlers* OOPSLA'25 | Resource safety under unwind/rewind with finalisers, second-class blocks; the active/open invariant | No. Relevant to effectful cleanup across suspension (our cancel rows), not to borrows | — |
| **RustBelt**, **Jung's thesis** (2020) | λRust in Iris; `Pin` is not modelled: "a full soundness proof for Pin will thus involve reasoning about both unsafe code and coherence of trait implementations" (ch. 15); "A formal look at pinning" (2018) is an informal typestate model | No published proof of borrows across `.await` or of `Pin` was found (searches: RustBelt, Iris, Oxide, 2023–2026) | `PinLaw`'s position stands: Rust's practice has no published proof either |

**Which world structure makes the parked-`κ` step provable, and at what cost.** Every work in
which it is provable (Timany–Birkedal, Hazel, Blaze, Affect, call/1cc, Yarrow) is in Iris: the
world is the global ghost state, the lend's island is a resource *owned by `κ`* (`Stack κ`,
`isCont₁`), and no proposition can be invalidated by another thread's allocation. In our terms
that is the third row of §2.4: the fold must leave the lend's island in the parked share, not
drop it from the world. Doing that inside the present model is a resource change; doing it the
papers' way is the `iris-lean` rebuild. Neither is cheap, and neither is an order change.

---

## 5. Recommendation

### 5.1 What replaces `Goal791SchedN`

Plain adequacy, handlers inside the program, no external semantic object:

```lean
/-- Every closed program typed from the suspending lend constants, with every handler it uses
inside it, steps or is final with the empty heap. -/
def Goal791N : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → (∀ c ∈ cs, c.InFrag) →
  ∀ (e₀ : Expr), CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (CTy.effOf [] .unit)) →
    OrDiverges (substAll (vals791 cs) e₀)
```

It is `BridgeN` after `FundamentalN`, and `FundamentalN` is `fundamentalN_all` with the assertion
as its one hypothesis. The scheduler `HS` becomes a corpus program typed by `effHandleV`;
`hs_schedOKN`, `SchedOKN`, `SchedOKNLeK`, `HandlerOKK`, `StackOKKW`, `Goal835`'s layer stack and
`PoolAnsN` leave the kernel's statement (they may stay as examples). `∀ n₀` is no longer a
question: the handler's name is whatever the program wrote.

### 5.2 The per-operation mark

Not needed for soundness, and not needed to *state* (A) or (C). Needed for one thing: to make
the asserted domain smaller than "every value handler", so that a program with no suspension
under a borrow caught by a κ-keeping handler keeps an unconditional proof, as it does on `main`.
That is worth having (it is `PinLaw`'s reliance reporting), and the carrier has to be
type-level: a derivation-level test ("does the handled computation's derivation contain a
suspending lend") is not compositional — a stored thunk `g : U(F_{await} 1)` whose body lends
across `await` is forced under a handler whose own derivation holds no lend, and the handler
still receives a `κ` with a lend inside. [SHL] §2.2's "the handler reads the signature's
annotation, not the row's kind" is the same point. So: keep `ub` exactly as
`scope-835-qualifier.md` §1 states it, **as a mark, never as a refusal**: `Row.UBOnly` on lend
rows and on tail/last answering rows is an inferred fact (mark every resuming operation performed
under a borrow), satisfied by construction, and no program is refused on its account.

If the user would rather not pay R2 (the kernel-type change) now, (A) needs no mark and is
available first; the mark can be added later to shrink (A) to (C).

### 5.3 R1: the tail/last side conditions

Drop them. At the all-`Owed` reading they are not needed (§2.3, the clause adopts `κ`'s floor);
at a mixed reading with (C) they are not needed either (the bridge makes `κ` `OwedR`). They were
needed only for the design that *proves* κ-keeping handlers at unmarked entries while *refusing*
them at marked ones; under the frame, refusing is out. Not verified: `handleT_compatN`/
`handleL_compatN` at `KW` are not built (qualifier R6).

### 5.4 `HandlerLawN`

Keep its shape, restate it at `KW` as `HandlerLawNW` (probe) — that is candidate (A), the interim
hypothesis of `fundamentalN_all` once the `KW` block is canonical. Then shrink it to
`StopReadNW` at marked names (C) when E10 at `OwedR` entries and the reading-parametrised
fundamental lemma are built; at that point `HandleVN`/`HandleVBN`/`ReifyN` become theorems from
(C) and `HandlerLawN` has nothing left to name. Its non-vacuity witnesses (`handle_resume_inst`,
`semJN_resumeCT`, the `kappa_*` lemmas) carry over.

### 5.5 `scope-835-qualifier.md` re-evaluated

| Section | Keep / change |
|---|---|
| §1 the qualifier | Keep as a mark (§5.2); `Row.UBOnly` becomes inferred bookkeeping, not a check that refuses |
| §2 the handler contract (`HandlerOKK`, `HandlerOKKW`, `erwpK_handle_ok`, "three ways to meet it", "anything else is refused") | Remove from the kernel's statement; the κ-keeping case at a marked operation is the assertion, not a contract |
| §2.4 the syntactic check and the T/L side conditions | Remove (§5.3) |
| §3 `Goal835` and the layer stack | Replace by `Goal791N` (§5.1) |
| §4 E10 at unmarked entries | Keep; it is what makes the mark shrink the reliance |
| §5 `Sch` out, rework in place | Keep |
| §6 carry-over, §7 what `main` sees | Keep; `main` sees only the field |
| §8 grounding | The rows marked "goes in the stack / asks the scheduler to cancel" become "typed in the program, relies on the assertion" |
| §9 R1, R4, R5, R6 | R1 resolved (drop), R4 resolved (parking at any depth, asserted), R5 moot, R6 stays (not built) |
| §10 unit plan | Units 1, 2, 4, 5, 6 stay; unit 3 becomes "restate `HandlerLawN` at `KW` as the hypothesis, prove `handlerLawNW_resume` non-vacuity"; unit 7 becomes `Goal791N` with the assertion, then the `StopReadNW` shrink |

### 5.6 What the checker says

As `assurance: PinLaw (R1 at 22:11)` today: `assurance: StopRead (handle at 34:11)` for each
κ-keeping `handle`/`reify` of a marked operation (or of any operation, under (A)); unconditional
otherwise. The trusted base lists the `def` and its issue.

### 5.7 Falsifier

Programs, as for `PinLaw` (`docs/async-capabilities.md` §6): the eleven R1 corpus programs
re-typed with the suspending constants, plus one each of a stored generator over a borrowing
source, an in-language `with_timeout`/`select` over a borrowing future, a `task_group` whose tasks
lend their own locals across `await`, an in-language scheduler cancelling a parked task whose
cleanup performs IO, and nested lends with a parked innermost stop. Each must run to `()` at the
empty memory under the runtime's dangling-use detection, if the machine has one (§6.1 there says
it does not; that remains the gap).

---

## 6. Not verified, and bookkeeping

**Not verified** (by reading only, no Lean):
- the soundness verdict of §1 as a whole; each row of §1.2 marked "by reading";
- E10 at `OwedR` entries at the reworked `cN` (qualifier §4, R7);
- the tail/last handlers at `KW` with no side condition (§2.3, R6);
- that (A), (B) or (C) has no typed refuting instance (= §1);
- (C) as a theorem on the lend-free fragment, and its stop-under-lend witness at an `int` payload;
- `handlerOKKW_resume`/`handle_resume_inst` at `KW` (qualifier §3.3);
- the Lean-side cost claims of §2.4.

**Checked in Lean** (probe, axioms `[propext, Classical.choice, Quot.sound]`):
`not_kapRelFoldToR`; `HandlerLawNW`, `HandleVNW`, `HandleVBNW`, `ReifyNW`, `HandleVNWAt`,
`StopReadNW` elaborate; `stopReadNW_ret`, `stopReadNW_ret_premises`.

**Unspent printed hypotheses:** none (no printed proof is transcribed here).
**Uniqueness or functionality results unused:** none needed.
**Untranscribed in the run-up:** E10 at `KW`; `handleT_compatN`/`handleL_compatN` at `KW`; the
reading-parametrised fundamental lemma.

Files: this note; the probe and the papers are in the scratch archive (see the header).
