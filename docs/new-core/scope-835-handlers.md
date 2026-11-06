# #835 (L4): our handler and row conditions against *Soundly Handling Linearity*

Branch `rule-791-l4` (from 9ba78899). The design source is Tang, Hillerström, Lindley and Morris,
*Soundly Handling Linearity*, PACMPL 8 (POPL 2024), article 54, DOI 10.1145/3632896, arXiv
2307.09383v2, read in full (the copy is `~/repos/scratch-archive/rule791/tang-soundly-handling-linearity.pdf`).
Its calculi are F◦eff (§3) and Q◦eff (§5); its handlers are deep (§3), with shallow ones in §6.
Its proof is syntactic (progress, subject reduction, Theorems 3.2–3.4) plus a linearity-aware
semantics (Fig. 7, Definition 3.5, Theorem 3.6), and it has no borrows. We take its
classification, not its lemmas.

Kernel target: the L4 entries of `scope-831-interface.md` (E12 first, then E3, E5–E10, E14, W9)
at the chain, and the `FundamentalN` compatibility lemmas for the effect and handler rules they
make mechanical. This document comes first: it fixes what each of our conditions is in the
paper's terms, so a port that changes one can be checked against it.

## 1. The paper's classification

- **Value linearity** (§2.1; Fig. 2, `K-Fun`, `K-Forall`, `S-Lin`, `S-Type`): a value type is
  linear `◦` or unlimited `•`, with `Type• ≤ Type◦`.
- **Control-flow linearity** (§2.2): how many times control may enter a local context. It is
  tracked per operation, `A ↠^Y B` (Fig. 1), and is the linearity of that operation's
  continuation. It is lifted to presence and row kinds (Fig. 2, `K-Present`, `K-ExtendRow`), with
  the reversed order `Row◦ ≤ Row•` (`S-Pres`, `S-Row`). `Δ ⊢ R : ◦` means every operation of `R` is
  control-flow linear (§3.2, Fig. 3).
- **`T-Seq`** (Fig. 4): `let^Y x ← M in N` asks `Δ ⊢ Γ₂ : Y` and `Δ ⊢ R : Y`. At `Y = ◦`, `N` may
  use linear variables and every operation `M` performs must be `◦`; at `Y = •`, `N`'s context is
  unlimited. `T-SeqSub` (§3.2, with the trivial row subtyping of Fig. 5) lets `M` and `N` run at
  rows `R₁, R₂ ⩽ R` and reads `R₁ : Y`. Q◦eff's `Q-Seq` (Fig. 9) reads `Γ₂ ⪯ R₁` per binding.
- **`T-Handler`** (Fig. 4): a deep handler's context is unlimited, `Δ ⊢ Γ : •` (Theorem 3.4.3),
  and the clause of `ℓᵢ : Aᵢ ↠^{Yᵢ} Bᵢ` gets `rᵢ : Bᵢ →^{Yᵢ} D`: a linear resumption at `◦`, an
  unlimited one at `•`. The handler reads the signature's annotation, not the row's kind, so
  `Row◦ ≤ Row•` does not let a `◦` operation be handled multi-shot (§2.2, last paragraph; §3.2).
- **Theorem 3.4.2** (unlimited continuations are unlimited): the context of a `•` operation's
  continuation splits off an unlimited part that is all it uses.
- **Linear safety** (Definition 3.5, Theorem 3.6): no tagged linear value inside an unlimited
  value, a `•` continuation, or a handler; reduction preserves the multiset of linear values.
- **Shallow handlers** (§6, `T-ShallowHandler`): a shallow handler may hold linear variables, at
  `Δ ⊢ Γ : Y` and `Δ ⊢ R : Y`, because outer handlers may capture it in the continuations of the
  unhandled operations `R`.
- **Related work** (§7): `finally`, `dynamic-wind`, RAII as unwind protection, outside the
  calculus; λURAL(𝒞)'s point between linear and unrestricted, which discards; one-shot handlers
  checked at run time.

## 2. Our conditions, one by one

Each row says **matches** (the paper's condition, in our terms) or **differs** (with the reason).

### 2.1 The qualifier of an operation (`Qual`, `Core/Types.lean`; SPEC §19 *Kinds of operation*)

| Ours | Paper | Verdict |
|---|---|---|
| `lin` (must resume): `κ : U((B ⊸ F_Σ R) & ⊤)`, resumed exactly once (`kTy`, `Core/EffRules.lean`) | `A ↠◦ B`, `r : B →◦ D` (Fig. 4 `T-Handler`) | **matches** |
| `unr` (unrestricted): `κ : !U((B ⊸ F_Σ R) & F_Σ 1)`, any number of times, its captures persistent (`lam_bang_persistent`); at the relation the share of an `unr` stop is empty (`contShareN`'s first conjunct, `SI/ErwpN.lean`) | `A ↠• B`, `r : B →• D`; Theorem 3.4.2 | **matches**; our empty share is Theorem 3.4.2 read semantically |
| `cancel` (cancellable): `κ : U((B ⊸ F_Σ R) & cancelTy Σ F)`, a linear `κ` resumed once or cancelled; the cancel unwinds `κ`'s frames, each finaliser running (SPEC §19, §27) | none. The closest is λURAL(𝒞)'s point between linear and unrestricted (§7), which discards | **differs**: a third point. A cancel is not a discard: it is `κ`'s consume, with computational content (its finalisers run, and may perform effects at the cancel row `F`). The paper's two points cannot say "used at most once, and if not resumed then unwound" |
| abortive (`B = 0`, `q ≠ lin`, `OpSig.abort`): the machine cancels in place (`[unwind]`/`[finalise]`), the clause gets no `κ` | `Fail : ∀a. () ↠• a` (§1, §2) | **differs** in what the continuation may hold: the paper's `Fail` is `•`, so its continuation holds no linear value; ours unwinds the continuation, so it may hold owned values whose finalisers consume them (`[then]`) |
| the handler reads the operation's qualifier from the term (`qs`, `capTag`; `hq` of `erwp_handle`) | the handler reads the signature's annotation, not the row's kind (§2.2, §3.2) | **matches** |

### 2.2 The handler-clause conditions (SPEC §19 *Laws* item 4, §25; `Core/Inversions.lean`)

| Ours | Paper | Verdict |
|---|---|---|
| R1: a clause may not consume `κ` (`forget κ` has no derivation, `not_release_kappa`) | `◦` resumption is linear (Lemma A.3: a linear variable appears exactly once) | **matches** at `lin`; at `cancel` it is our third point (the consume is the cancel branch, not a discard) |
| R2: a clause may not resume `κ` twice (`refuses_R_clauses`, `not_der_at08`) | Lemma A.3, `r : B →◦ D` | **matches** at `lin`; at `cancel` the same reading of a linear `κ` |
| R3: a must-resume `κ` may not be cancelled (`kTy`'s `⊤` branch) | `◦` continuations are entered exactly once (§2.2) | **matches** |
| R4: a cancellable `κ` may not be cancelled and then resumed (the `&` of `kTy` is additive) | none | **differs**: only the third point has a cancel branch. Additivity is what makes "resume or cancel" one use |
| the handler's own context is dead or persistent (`hd : Ctx.DeadP Γ₁`, `effHandleV`/`VB`/`T`/`L`) | `Δ ⊢ Γ : •`, Theorem 3.4.3 | **matches** (our handlers are deep, `hndE` reinstalls the handler in `κ`) |
| BOXED-κ (`effHandleVB`, SPEC §28): `κ : [@d] K`, the handled computation's context outliving `@d` (`CtxOutlives`) and every non-abortive answer type outliving `@d` (`Row.AnsOutlives`) | none (no lifetimes) | **differs**: a refinement of control-flow linearity by stratum. The paper classifies a continuation by *whether* it holds a linear value; BOXED-κ also bounds *which* lifetimes its share lives in. The stop lemma (`stop_sem`, E12) is the semantic fact: every stop's share is in `Res_{δ(d)}` |

### 2.3 Sequencing (`effLet`, `effThen`, `effThenDiv`; SPEC §19, §24, §27)

| Ours | Paper | Verdict |
|---|---|---|
| `effLet`'s `hU : S.Unr → Ctx.Banged Γ₂` | `T-Seq`, `Y = •`: `Δ ⊢ Γ₂ : •` | **matches** |
| `effLet` with no `unr` and no cancelling operation: no condition on `Γ₂` | `T-Seq`, `Y = ◦`: every operation `◦`, `Γ₂` any | **matches** |
| `effLet`'s `hW : S.Cancels → Γ₂.OwnFree` | none | **differs**: at a row with a cancellable or abortive operation, `N`'s context may hold borrows but no owned cell. A cancel passing the frame leaves `Γ₂` behind (`ent_plain`); borrows end with their lends, which unwind, but an owned cell left behind would leak. `[then]` is the rule that owns across a cancel |
| `effThen`'s `hU : S.UnrD → Ctx.Banged Γ₂`, `UnrD` reading `unr` at the top and at every depth of the cancel rows | `T-SeqSub` (§3.2) reads `R₁ : Y`, `M`'s row only | **differs** in the row read: ours reads `Σ` and its cancel rows, not `Σ_M`, because the finaliser `D` (which holds `Γ₂`) also runs inside the cancel runs below it, whose operations are recorded in `Σ` by `hfin`/`ThenLe` |
| `effThen`'s finaliser `D`, `hfin`/`ThenLe`, `hP`, `hSD`, `effThenDiv`'s `hcap` | §7's unwind protection (`finally`, `dynamic-wind`), outside the calculus | **differs**: an extension. The shape of `hU` beside a frame that outer handlers may capture is `T-ShallowHandler`'s (§6: `Δ ⊢ Γ : Y`, `Δ ⊢ R : Y`) |
| `effSub` (`RowLe`, `OpSig.LeF`: the same signature, `Sig`, the cancel row may grow) | Fig. 5 trivial subtyping (same labels, same signatures) | **matches** for the signature; **differs** in letting a capturable entry's cancel row grow, which the paper has no counterpart of |

### 2.4 The rows a borrow callback may stop at

The question "which operations may capture a context holding a borrow" is, in the paper's terms,
"which operations may have a context with a linear value in their continuation". The paper's
answer is the `◦` ones, by `T-Seq` at `Y = ◦`. A borrow (`Mut @a A`) is a linear value, so the
paper would admit exactly `Δ ⊢ R : ◦` around it.

| Ours | Paper | Verdict |
|---|---|---|
| `Row.Unwind` (§19, `Core/EffBorrow.lean`): every operation abortive and named, its argument closed data. No operation captures the callback's context: each unwinds it in place, ending the lend | `R : ◦` | **differs** both ways. It admits operations the paper would refuse (abortive ones, `•`-like), because an abort is an unwind that runs the lend's finaliser `d`; it refuses the ones the paper would admit (`◦`), because a resumable stop under a borrow needs the lend to survive suspension (the location kept in place, SPEC §29) |
| `Row.ResumeO` (§29, `Core/PinDerives.lean`): every operation resumes (none abortive), none `unr`, empty cancel row, answer `1`, closed-data argument | `R : ◦` | **matches** in `q ≠ unr` (no multi-shot capture of a borrow), with `cancel` admitted as our third point; **differs** in the data clauses (argument and answer free of the lend's lifetime), which have no counterpart because the paper has no lifetimes |
| `Row.ResumeOC` (§29a): `Row.ResumeO`, or a cancellable wait, or its abortive cancel target; no `Div` | `R : ◦` | **differs**: it adds one abortive operation (the cancel target), read as `Row.Unwind`'s reason |
| `Row.Suspend` (chain, `Core/TreeGoal791.lean`): every operation named and not `unr`; payload and answer free of `'x` and outliving `@bnd`; a capturable operation's cancel row meets `CTy.SuspendC` | `R : ◦` | **matches** in `q ≠ unr`: "a continuation resumed twice would lend twice" is the paper's soundness bug (§1, §2.2) at a borrow. **Differs**: abortive and cancellable operations are admitted (unwind, our third point); the lifetime clauses have no counterpart |
| `CTy.SuspendC`: each layer of a cancel row not `unr`, its payload and answer as `Row.Suspend`'s, recursively | `K-ExtendRow` (Fig. 2): a row's linearity is that of each of its labels | **matches** in shape (the condition is lifted through every operation that may run while the lend is live, as the paper lifts it through every label); **differs** in that our cancel rows are rows the paper does not have |

### 2.5 Summary

**Matches** (8): `lin` as `◦`; `unr` as `•` (and its empty share as Theorem 3.4.2); the handler
reading the operation's qualifier; R1–R3 at `lin`; the handler's context dead (Theorem 3.4.3);
`effLet`'s `hU` and its unconstrained `◦` case (`T-Seq`); `RowLe`'s signatures (Fig. 5); the
borrow rows' `q ≠ unr` (`Row.ResumeO`, `Row.Suspend`, `CTy.SuspendC`) as `R : ◦`.

**Differs** (each for one of three reasons):
1. **The third point, `cancel`, and abortive operations that unwind.** A continuation not
   resumed is unwound, its finalisers running. This is what R4, `effLet`'s `hW`, `[then]`'s
   finaliser, `effThen`'s `UnrD`, `RowLe`'s growing cancel rows and `Row.Unwind`'s admission of
   aborts all follow from. The paper has two points and no unwinding (§7 lists unwind protection
   as related, not in its calculi).
2. **Lifetimes.** BOXED-κ's `@d`, `Row.ResumeO`'s and `Row.Suspend`'s data clauses. The paper has
   no borrows and no strata.
3. **Suspension under a borrow.** `Row.Unwind` refuses resumable operations the paper would
   admit; that is the location-stability question (SPEC §29, #791), not a linearity one.

**What we take from the paper's design** for L4: the qualifier is read off the operation, never
the row's kind (so `RowLe` keeps `Sig`); a deep handler's context is persistent; an `unr` stop's
share is empty and an `unr` row forces the continuation's context to be persistent; the borrow
rows exclude `unr`. None of the L4 entries changes these; E12 is the stratum refinement of
§2.2's last row, and its proof (§3) is semantic, as the paper's Theorem 3.6 is not.

## 3. The plan for L4

In the order the brief fixes, each a chain lemma under Core's name and shape:

1. **E12, `stop_sem` at `erwp`.** Core's proof (`Core/EffBoxed.lean`): `wpG` carries `↭` from a
   run's start to its end, `↭` keeps `Res_α` (`ResU.updV_inStratum`), so a run started in `Res_α`
   ends in `Res_α` (`wpG_inStratum`); the share is a `●`-factor of the end resource; across a
   resumption the next run starts at the share and the answer. The chain carries `↭` as
   `UpdVN Φ k` in `rwpG`'s `EndOKG`, whose `imm` clause is Core's and whose `mut` clause keeps each
   cell's lifetime (`MutStep`'s `ψ.at = ψ'.at`). So the steps are: `UpdN` keeps `Res_α`;
   `rwpG_inStratum`; `opTableNS α T` (Core's `opTableS`); `erwp_stratify` by induction on the index
   (Core's `ewp_stratify` by `ewp_ind`); `stop_semN` at `SemJN` from `vN_outlives` and the context's
   fold of it (Core's `gSepC_outlives`).
2. **E3**: `RowLe S S′ → OpTabN.Le (tabN …S…) (tabN …S′…)`, then `sub_compatN`.
3. **E5–E7**: `tabN`'s `CtxClosed` at a context with no handler and no catcher, `cancelOKN` at the
   empty context, a raise's introduction; then `perform_compatN`, `raise_compatN`.
4. **W9, E8, E9, E10, E14** as far as the run gets, each with its rule.

E13 (a `Div` row is a row of the table) means Core's `hSd : Row.divB S = false` premise of
`stop_sem`, which Core needs only to pass from `cwp` to `ewp`, has no use on the chain.

## 4. Outcome

Each entry is a chain lemma under Core's name with `N`, following Core's printed proof.

| Entry | Built | File | Core's proof it follows |
|---|---|---|---|
| E12 | `UpdVN.inStratum`, `rwpG_inStratum`, `opTableNS`, `erwpS_erwp`, `erwp_stratify`, `gN_outlives`, `tabN_ansIn`, `SemCSN`, `stop_semN` | `Core/Chain/Stop835N.lean` | `ResU.updV_inStratum`, `wpG_inStratum`, `opTableS`, `ewp_stratify`, `gSepC_outlives`, `Row.ansIn_of_ansOutlives`, `stop_sem` |
| E12's handler | `erwp_handleS` | `Core/Chain/HandleS835N.lean` | `ewp_handleS` |
| E3 | `tabN_effOf_find`, `finN_eq_ite`, `cancelTabN_le`, `cancelOblN_le`, `finN_mono`, `tabN_le_of_rowLe`, `erwp_rowLe` | `Core/Chain/Eff835N.lean` | `Row.tab_find`, `finObl_eq`, `cancelObl_le`, `finObl_mono`, `effWp_sub` |
| E5 | `erwp_bind_pure_frame`, `tabN_ctxClosed` | `Eff835N`, `Loop835N` | `ewp_bind_pure_frame`, `plain_cancel₀` |
| E6 | `erwp_perform_here`, `cancelOblN_start`, `entN_start` | `Eff835N` | `ewp_perform_here`, `cancelObl_start`, `ent_start` |
| E7 | `erwp_raise_here`, `vN_noOwn_of_ownFree` | `Eff835N` | `ewp_raise_here`, `vC_noOwn_of_ownFree` |
| E8 | `cancelOblN_frame`, `cancelOblN_plain₀`, `tabN_plainCancel`, `cancelOblN_frame_consume`, `entN_plain`, `erwp_frame_plain` | `Core/Chain/Frame835N.lean` | `cancel_frame`, `plain_cancel₀`, `Row.tab_plainCancel`, `cancel_frame_consume`, `ent_plain`, `ewp_frame_plain` |
| W9 | `erwp_val_post` | `Frame835N` | `wpTS_val_post` |
| E14 | `erwp_iterateC` | `Core/Chain/Loop835N.lean` | `cwp_iterate`'s *next* and *close* (`cwp_closePath`) |
| E9 | not built | — | `ewp_frame_then_or` |
| E10 | not built | — | `ewp_handle_vals`, `vC_kTy_of_kapRel` |

**Rules ported**: `effSub` (`sub_compatN`), `effPerform` (`perform_compatN`), `effRaise`
(`raise_compatN`), in `Eff835N`. Each is Core's proof step for step.

**Rules not ported, and what each waits on**:
- `effLet`, `effThen`, `effThenDiv`, `effAwait` and the four handlers split their context
  (`gN_split`, interface G1 with G12), which is L1's. `effLet` is then `erwp_frame_plain` with
  `entN_plain`, as Core's `let_compatC` is `ewp_frame_plain` with `ent_plain`.
- `effThen`/`effThenDiv` also need E9: a finaliser frame whose finaliser performs and raises,
  with the cancel rows composed (`ThenLe`, `PendLe`). The chain's `erwp_ubind` covers a finaliser
  that never stops (`FinOK`).
- `effHandleV`/`effHandleVB` need E10's reading of a clause at `vN`. A clause's `κ` is at
  `kTy Σ R q B F`, a thunk; `vN` of a thunk asks the computation at every world along `ExtR` from
  the thunk's resource and at every view consistent with it. A stop of the handled run owes its
  continuation (`KapRelN`) at that run's view, and along `extF` on the record list only. So the
  clause cannot be applied to `κ` by Core's step. Not derived; obstruction not verified. This is
  the `ExtR` part of interface entry F10 (and §3.2's risk 2, a computation moved along the world).
  `effHandleVB` has every other piece: `stop_semN` and `erwp_handleS`.
- `effHandleT`/`effHandleL` give the clauses no `κ` (the handler's own code resumes it), so they
  avoid that step; they need G1, Core's `ewp_handle_tail`/`ewp_handle_last` at `erwp`
  (`erwp_frame_plain` around the clause's run with `κ` as the frame) and, at each clause, the
  payload's consistency with the view (`rwpG_consistentXV`). Not built here.
- `iterate` needs `erwp_iterateC` with an invariant read at the index (the state's `vN` lowers
  with the loop), the step's `vN` applied at the loop's world (`LocTy.extR_refl`) and K5. Not
  built here. `divFuel` needs E11's instances at the index. Not built here.

**Unspent hypotheses**: Core's `stop_sem` premise `Row.divB S = false` is not a premise of
`stop_semN` (E13). No other printed premise was dropped.

**Restated declarations**: none. Every lemma is new; no existing statement was changed.

## 5. Part 2 (`rule-791-l4b`)

`scope-831-interface.md` §10 has the detail.

| Entry or rule | Built | File | Core's proof it follows |
|---|---|---|---|
| E10 | not derived; obstruction not verified (§10.1 there) | — | `vC_kTy_of_kapRel` |
| E11's fuel instances | `erwp_pureSteps`, `erwp_kappaC_resume_in`, `erwp_hnd_tick`, `fuel_tick_zeroN`, `fuel_tick_succN`, `fuel_totalN` | `Core/Chain/Fuel835N.lean` | `ewp_pureSteps`, `ewp_kappaC_resume_in`, `hnd_tick`, `fuel_tick_zero`, `fuel_tick_succ`, `fuel_total` |
| `divFuel` | `divFuel_compatN` | `Fuel835N` | `divFuel_compatX` |
| `effAwait` | `await_compatN`, over `let_compatN_persist` and `erwp_idxLe` | `Core/Chain/Let835N.lean` | `await_compatC` |
| `effLet` | `let_compatN_ansC` (with `hAns`), `let_compatN_persist` (a persistent bound type); `let_compatN` not derived | `Let835N` | `let_compatC` |
| E9, E10's tail and last instances, `effThen`, `effThenDiv`, `iterate`, the four handlers | not built | — | — |

The step that stops `effLet` is chain-only: `N`'s judgment is read at the run's view, and an
answer a stop is resumed at may be inconsistent with it (`tabN`'s `PB` does not read the view).
In the paper's terms it is neither value nor control-flow linearity: it is the borrow side
(§2.4), the view being where a `Mut` cell's lend is read.
