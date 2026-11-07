# #835: what a Kripke stop for `erwp` costs

This is a cost map for one change: a stop (`contShareN`, `KapRelN`) owes its continuation at every
`ExtP`-later world, with the tables and posts read at that world. This is Dreyer, Neis & Birkedal's
`K⟦τ⟧` (JFP 2012, Fig. 6), which `scope-835-public.md` §8 names as the step E10, `effHandleV`,
`effHandleVB` and `reify` wait on. This document measures the change; `erwp` is not changed.

The Lean was a spike, `Core/Chain/KStopSpike835N.lean`, with local copies of the new definitions;
it is deleted (`git show c3669cec:Core/Chain/KStopSpike835N.lean`), and its configuration
`extP_not_foldInv` is in `ConfigsKW835N.lean` (`Public835N`), over `LocTy.FoldInv`.
§6 has the verdict. The definitions are now a module, `Core/Chain/SI/ErwpK.lean`, with the stop's
floor and `FoldInv` kept (§1's two additions) and the generic laws; `scope-835-restriction.md` §6
lists what it holds.

## 1. The new definitions

All of them were in the spike `KStopSpike835N.lean`, indexed by a world type `ι`.

```lean
structure OpEntK (ι : Type) where
  q : Qual
  abort : Bool
  PA  : Nat → List SRec → Val → WProp
  PB  : ι → Nat → List SRec → Val → WProp                 -- answer at the resumption world
  fin : Option (ι → Nat → List SRec → Expr → WProp)       -- cancel obligation there
  wc  : List SRec → List SRec → WRes → Prop               -- unchanged: the list order
  wk  : ι → WRes → Prop                                   -- new: the worlds the continuation is owed at

abbrev ContK  ι := ι → Nat → List SRec → Expr → WProp
abbrev TableK ι := Nat → List SRec → Expr → ContK ι → WProp

def contShareK en k ls K Ψ : WProp := fun ρ =>
  (en.q = .unr → ρ = ∅) ∧
  ∀ y, en.wk y ρ → ∀ ls', en.wc ls ls' ρ →
    (∀ k' < k, ∀ w, (en.PB y k' ls' w ─⋆ Ψ y k' ls' (K.plug w)) ρ) ∧
    (en.q ≠ .lin → cancelOKK en y k ls' K ρ)

def erwpK (V : ι → ι → Prop) (Φ : ι → LocFam) (Tb : ι → TableK ι) (Q : ι → PostN) :
    ι → Nat → List SRec → Expr → WProp
  | x, n, ls, e => rwpG (Φ x)
      (fun k ls t => (∃ v, t = v.1 ∧ ∃ y, V x y ∧ Q y k ls v) ∨
                     Tb x k ls t (fun y k' ls' e' => if k' < n then erwpK … y k' ls' e' else False))
      n ls e
```

**How the parts are indexed.**
- The location family `Φ x`, the table `Tb x` and the post `Q y` are all read at a world.
- A stop at world `x` owes `erwpK … y` at every `y` its entry's `wk` allows. This is (a) of
  `scope-835-public.md` §8.
- A value is in `Q y` at a world `y` with `V x y`. This is (c): the post is read at an
  existentially chosen later world, as in DNB's Lemma 3 and ADR's `E`.
- `rwpG`, and every lemma at `rwpG` (the heap, `↭`, `TWNC`, `rwpG_M_frameG`), is unchanged. A run
  between stops never changes its world.

**The typed instance.** Take `ι` to be `(Θ, c, lo)`: a location typing, a view and a floor. This is
(b). Then:
- `Φ (Θ, c, lo) = Θ.view c`;
- the posts and the table read `vN` at `Θ` and the answers are `ConsistentX c`;
- a row entry's `wk y ρ` is `Θ.ExtP f y.Θ ρ`, plus the view clause, at the stop's floor `f`.

**The constant-world embedding exists, and it is proved.**
- `erwp_eq_erwpK`: `erwp Φ Tb Q n ls e = erwpK (fun _ _ => True) (fun _ => Φ) (fun _ => liftTb Tb) (fun _ => Q) () n ls e`, where `liftTb Tb k ls t Ψ = Tb k ls t (Ψ ())`.
- `opTableK_liftTab` and `erwp_opTableN_eq_erwpK`: `erwp Φ (opTableN T) Q` is `erwpK` at `Unit`
  at `opTableK (liftTab T)`. Here `liftTab` gives each entry `wk := True`, `PB` constant and `fin`
  constant.

So every existing statement about `erwp` is, word for word, a statement about `erwpK` at
`ι = Unit`. If `erwp` is redefined as that instance, or kept with the equation, no existing
statement changes.

**What the embedding does not give.** The typed layer has to move to a non-trivial `ι`. E10 needs
`cN`'s stops to be Kripke at the typed world, so `cN` is redefined through `erwpK` at
`(Θ, c, lo)`, and the typed compatibility lemmas are re-proved against that `cN`. Their old
statements stay true, but they are statements about the old `cN`.

### Two additions the spike found

The brief's three items are (a), (b) and (c). The spike shows the stop needs two more:

1. **The stop chooses its floor.**
   - The Mut Frame's lender owes its stops only along `ExtP` at the lend's floor `A`
     (`extPFoldTransfer`, and §4 below). That is a smaller set of worlds than `ExtP` at the
     lender's floor `lo > A`.
   - So the lender's table, which `cN` fixes at `lo`, must accept stops at any floor `f ≤ lo`.
   - In the typed instance an entry's `wk` therefore becomes `∃ f ≤ lo, …` taken at the stop. In
     the generic definition this is one more existential in `contShareK`. At `Unit` it is
     trivial.
   - What follows for consumers: a handler gets `κ` owed at an unknown floor `f ≤ lo`. E10 needs
     `f` to be the handler's floor. That holds exactly when no lend is live at the stop, which is
     the #835 fallback (only the scheduler catches operations performed under a live lend).
2. **Under a live lend at `A`, the order keeps `FoldInv A`.**
   - `FoldInv A` means: `A` is fresh, and no `imm` record is lent at `A`.
   - `ExtP.fold` needs `FoldInv A` at the stop's world. The frame's induction re-enters at the
     resumption world, so it needs `FoldInv A` there too.
   - `ExtP` at `A` does not keep it: a key at `A` itself is a public move at floor `A`
     (`extP_not_foldInv`, a configuration checked in Lean).
   - So under a live lend the lender's `wk` is `ExtP A x y ρ ∧ FoldInv A y`. Under nested lends
     the stop's floor is the innermost lend's, so `KW.Owed` keeps `FoldInv` at every floor at or
     above the stop's (`scope-835-mframes.md` §3).
   - In [DNB] terms, the lender's island still holds `A`, so no other island may claim it.

## 2. Producers and consumers

**Method.**
- A *producer* is a theorem whose proof builds a stop's continuation obligation. In the source that
  is a `fun ls' he =>` or `intro ls' he` inside a stop, a call to an `erwp_perform` lemma, or a
  `KapRelN` in its statement.
- A *consumer* opens a stop (`⟨K, m, i, v, en, hp⟩`, `hcont`, or `KapRelN` in its proof) without
  building one.
- Scope: `Core/Chain/*.lean` and `Core/Chain/SI/*.lean`, excluding this spike. 474 theorems there
  mention `erwp`, `rwpG` or `KapRelN`.
- The `Tree*` files use `erwpT`, a separate relation, and are untouched.
- "On path" is a name-level dependency closure from the theorems whose statements mention
  `SemJN`, `cN` or `_compatN`. It is a heuristic.

**Classes.**
- **M (mechanical):** the existing proof with a world binder added. The premises are read at every
  world the stop allows, and the steps use `ExtP`'s laws (`refl`, `trans`, `mono`, `ExtP.extR`).
  `erwpK_perform` is the template for these.
- **Fm (needs `ExtP.fold`):** a `mut` lend frame, whose inner run is at `Φ.set ℓ A F`. The spike's
  `erwpK_M_frame` and `extP_foldFrame` are the template. Each also needs the `FoldInv` clause and
  the stop's floor.
- **Fi (needs an `imm` analogue of `ExtP.fold`):** `imm` frames and reborrows. The inner world adds
  an `imm` record at `A` (`Θ.addImm`) or a reborrow's record at `β`. The analogue,
  `ExtP A Θ Θ′ ρo → ExtP A (Θ.addImm r) (Θ′.addImm r) ρi` at the frame's shares, is not proved.
  Its ingredients exist: `extP_addImm`, `extR_addImm` and `extF_fold`'s share argument. I classify
  it with the fold lemmas, not as new reasoning, but it is unbuilt.
- **Fa (needs a share-transfer lemma):** anti-frames. The world is unchanged, but the stop's share
  folds a `mut` cell back into `own`. The step is `ExtP` at the outer share giving `ExtP` at the
  inner share whenever the inner share's borrow cells are dominated (`CellIn` inner `a` →
  `CellIn` outer `a`), which is `extF_fold`'s shape. Small; not proved.
- **V (verbatim):** a concrete program (`*_ok` in the `*Prog` files and in `Hardest791N`), or a
  configuration lemma about the present `KapRelN`. These live at `erwp` itself, which is the
  constant-world instance, so they survive unchanged and are not on the path to E10.
- **N (new reasoning) / unclear:** no producer. The one new-reasoning item is in the lend rules'
  posts (§5), which construct no stop.

**Totals: 110 producers.**

| Class | All | On path |
|---|---|---|
| M | 55 | 31 |
| Fm | 13 | 11 |
| Fi | 12 | 7 |
| Fa | 4 | 4 |
| V | 26 | 0 |
| N | 0 | 0 |
| unclear | 0 | 0 |

**Per file** (`Core/Chain/` prefix dropped):

| File | Classes | Producers |
|---|---|---|
| Cancel791N | Fm 1, M 4 | `erwp_M_frame_cancelRunCR` (Fm); `erwp_cancelRun_claimX` `erwp_claimX` `erwp_ubind_cancelRunCR` `erwp_ubindClaimRT` |
| Eff835N | M 2 | `erwp_perform_here` `perform_compatN` |
| FamCancel836N | Fm 2 | `erwp_M_frameCRR` `erwp_M_frame_cancelRunCRR` |
| FamImm836N | Fi 1 | `erwp_I_frameRR` |
| FamStop836N | Fm 1 | `erwp_M_frameRR` |
| Field791N | M 2 | `erwp_frameGR` `erwp_frame_cancelRunGR` |
| Frame835N | M 2 | `cancelOblN_frame` `erwp_frame_plain` |
| Fuel835N | M 1 | `fuel_totalN` |
| HandleS835N | M 1 | `erwp_handleS_le` |
| HandleT835N | M 3 | `erwp_frame_plain_or` `erwp_consistentPA` `KapRelN.extF` |
| Hardest791N | M 1, V 3 | `erwp_cancelTabN_ctx`; V: `fieldBody_ok` `erwp_parkAt` `erwp_spawnThen` |
| Iter835N | M 1 | `erwp_iterateCI` |
| Kappa835N | V 3 | `kapRelN_world` `not_kTy_world` `kapRelN_view` |
| Lend791N | Fm 1 | `erwp_M_frameCR` |
| Let835N | M 2 | `erwp_consistentAns` `erwp_idxLe` |
| Loop835N | M 1 | `erwp_iterateC` |
| PoolN | V 1 | `poolAnsN_park` |
| Public835N | V 1 | `kapRelN_not_kapRelP` |
| Reborrow791N | Fm 2, Fa 2 | `erwp_M_frameCRG` `erwp_M_frame_cancelRunCRG`; `erwp_M_antiFrameCR` `erwp_M_antiFrame_cancelRunCR` |
| SI/AntiCancelN | Fm 1, Fa 1, M 1 | `erwp_M_frameTF`; `erwp_M_antiFrameC`; `erwpG_frameT` |
| SI/AntiCancelProg | V 1 | `lend_okCΦ` |
| SI/AntiStopN | Fm 1, Fa 1, M 1 | `erwp_M_frameF`; `erwp_M_antiFrame`; `erwpG_frame` |
| SI/BindN | M 2 | `erwp_bind` `erwp_perform` |
| SI/CaptureE | M 2 | `cerwp_perform` `cerwp_of_erwp` |
| SI/CaptureGen | M 1 | `cerwp_gen` |
| SI/CaptureScope | M 1 | `cerwp_scopeK` |
| SI/CaptureScopeM | M 2 | `cerwp_bindK` `cerwp_scopeM` |
| SI/CrossProgM | V 1 | `childM_ok` |
| SI/DeepRebProg | V 1 | `itemBody_ok` |
| SI/Erwp0 | V 1 | `erwp0_perform` |
| SI/FinCancelN | M 3 | `erwp_cfin_run` `erwp_ubind_cancelRunF` `erwp_ubindClaimF` |
| SI/FinCancelProg | V 2 | `lend_okCC` `dC_okCl` |
| SI/FinPerformN | M 2 | `erwp_frameL` `erwp_ubindRaiseF` |
| SI/HandleN | M 2 | `erwp_ccatch` `erwp_handle_le` |
| SI/HandlerLendAll | V 2 | `lendResumeU_ok` `erwp_clLendU` |
| SI/HandlerLendProg | V 3 | `lendH_ok` `lendResume_ok` `erwp_clLend` |
| SI/ILendCancelProg | V 1 | `lendI_okC` |
| SI/ILendProg | V 1 | `lendI_ok` |
| SI/IStopCancelN | Fi 2 | `erwp_I_frame_cancelRun` `erwp_I_frameT` |
| SI/IStopF | Fi 1 | `erwp_I_frameF` |
| SI/IStopN | Fi 1 | `erwp_I_frame` |
| SI/IStopRaiseN | Fi 1 | `erwp_I_frameR` |
| SI/LendCancelProg | M 2, V 1 | `erwp_performG` `erwp_cancelTabR_ctx`; V: `lend_okC` |
| SI/LendProg | V 1 | `lend_ok` |
| SI/LoopN | M 2 | `erwp_bind_le` `erwp_iterate` |
| SI/RaiseFinProg | V 1 | `dC_ok` |
| SI/RebAcrossC | Fi 1 | `erwp_reborrow` |
| SI/RebCancelC | Fi 2 | `erwp_reborrow_cancelRun` `erwp_reborrowT` |
| SI/RebCancelProg | V 1 | `rebBodyC_ok` |
| SI/RebProg | V 1 | `rebBody_ok` |
| SI/RebRaiseC | Fi 2 | `erwp_rebGen_cancelRun` `erwp_rebGen` |
| SI/RebStopD | Fi 1 | `erwp_reborrowDeep` |
| SI/StopCancelN | Fm 2 | `erwp_M_frame_cancelRun` `erwp_M_frameT` |
| SI/StopFrameN | Fm 1 | `erwp_M_frame` |
| SI/StopRaiseN | Fm 1, M 1 | `erwp_M_frameR`; `erwp_ubindRaise` |
| SI/TabLeN | M 3 | `opTableN_le` `erwp_ccatchLe` `erwp_handleLe` |
| SI/UbindGN | M 2 | `cancelOblN_ubind` `erwp_ubind` |
| SI/UbindN | M 2 | `erwp_ubind_cancelRun` `erwp_ubindClaim` |
| Stop835N | M 1 | `erwp_stratify` |
| Then835N | M 5 | `cfin_cancelN` `cfin_runN` `then_cancelN` `seq_raise_runN` `erwp_frame_then` |

**Raise-only (3):** `erwp_raise_here`, `lendRC_ok` and `lendR_ok`. They build only abortive stops,
which owe no continuation and read no world, so they are unchanged.

**Why the M class is mechanical.**
- *Same-world pass-through* (bind, `ubind`, the plain frames, loops, cancel runs, `opTableN_le`,
  `erwp_stratify`). The inner and outer stops are at the same world and the same entry. The
  induction hypothesis is applied at the resumption world `y` rather than at `x`, so every
  premise about the context (`hcont` and similar) must hold at every world. At `Unit` that is the
  old statement. At the typed world it comes from the fundamental lemma at every world, plus `gN`
  being monotone along `ExtP ⊆ ExtR` (`vN_extR`, restricted to the context's part of the share).
- *Handlers* (`erwp_handle_le`, `erwp_handleLe`, `erwp_handleS_le`, `erwp_ccatch*`,
  `fuel_totalN`). A clause's stop owes at the worlds the outer entry allows. Inside, `κ` is
  resumed at such a world, which must be one the handled entry allows. That needs three things,
  all from `ExtP`'s laws:
  - the outer order at the clause's share restricted to `κ`'s share;
  - the outer order included in the inner one for the forwarded rows (`hTin` makes them the same
    entry);
  - `ExtP.trans`, for the induction hypothesis at `y`.

  The clause premise `hop` is read at every world.
- *`erwp_consistentAns` / `erwp_consistentPA`.* Their statements name the run's view `c`. At the
  typed world the view is part of the world, so `ConsistentX c` becomes the view of the world the
  post is read at. The proof is the same induction.

**Consumers: 18** (theorems that open a stop and build none).

| File | n | Theorems |
|---|---|---|
| FamCancel836N | 2 | `erwp_opTableR_le` `erwp_opTableN_R` |
| FamImm836N | 1 | `erwp_tieEntryR` |
| HandleL835N | 2 | `last_contN` `erwp_handle_last` |
| HandleS835N | 1 | `erwp_handleS` |
| HandleT835N | 2 | `extF_trans` `erwp_handle_tail` |
| ImmLend833N | 2 | `erwp_tieEntry` `erwp_claimX_abort` |
| ImmTie791N | 1 | `not_erwp_false` |
| Kappa835N | 1 | `not_kTy_view` |
| Lend791N | 1 | `rwp_of_erwp_empty` |
| Public835N | 1 | `not_kapRelP_view` |
| SI/AntiCancelN | 2 | `erwp_frame_cancelRun` `erwp_M_antiFrame_cancelRun` |
| SI/HandleN | 1 | `erwp_handle` |
| Stop835N | 1 | `opTableNS_le` |

**Do any consumers rely on a stop at one fixed world?**
- **The handler consumers** (`erwp_handle`, `_last`, `_tail`, `erwp_handleS`, `last_contN`) resume
  `κ` at the handler's own world. `ExtP` is reflexive (`extP_refl`), so the Kripke stop gives that
  case.
- **`erwp_tieEntry` / `erwp_tieEntryR` / `erwp_claimX_abort`** change `Φ`, but at all-abortive
  tables (`hab`). Those tables owe no continuation.
- **`rwp_of_erwp_empty` / `not_erwp_false`** are at the empty table and read no stop.
- **`erwp_opTableR_le`, `erwp_opTableN_R`, `opTableNS_le`** are table inclusions. They need the
  `wk` of the included entries to be compared, which is mechanical.
- **The two configuration lemmas** (`not_kTy_view`, `not_kapRelP_view`) are *about* the
  fixed-world `KapRelN`. They stay true of it. That is their point.

No consumer needs a stop owed at exactly one world. Each one reads the stop's world through
reflexivity.

## 3. Lemmas that use only `erwp`'s generic laws

346 of the 474 theorems neither build nor open a stop. 28 of them have typed statements (`cN`,
`vN`, `gN`, `tabN` or `Θ.view`). There are also 83 `*_compat*` theorems at `SemJN`, spread over 25
files, with the most in `Rules834N` (22) and `Fam836N` (21).

**The generic laws at `erwpK`.**
- **Unchanged at `rwpG`:** `rwpG_bind`, `rwpG_frame`, `rwpG_garbage`, `rwpG_det`, `rwpG_here`,
  `rwpG_M_frameG`, `rwpG_le`, the heap laws, `rwp_iff_rwpG`. `rwpG` has no stops.
- **Same statement with a world binder, and the old statement at `Unit`:** `erwp_eq`,
  `erwp_unfold_at`/`fold_at`, `erwp_zero`, `erwp_det`, `erwp_alloc`, `erwp_free`,
  `erwp_kappa_resume`, `erwp_garbage`, `erwp_of_rwp`, `erwp_le` (with `Down` at every world). The
  spike proves `erwpK_eq`, `erwpK_unfold_at` and `erwpK_garbage`, by the existing proofs.
- **`erwp_val`** needs `V x x` (the post's world order is reflexive).
- **`erwp_bind`, `erwp_bindR`, `erwp_mono`:**
  - The continuation premise is read at every world the stops and values reach (DNB's Lemma 3).
  - Because of (c), bind also needs `Φ y = Φ x` and `Tb y ⊆ Tb x` along `V`. The post's world
    differs from the run's only in its floor, and a table at a lower floor admits fewer stops when
    the stop chooses its floor (§1).
  - At `Unit` all of these are trivial and the old statement is recovered.

**So:**
- **Every generic-law-only lemma at the generic layer is untouched.** Its old statement is the
  `Unit` instance of the world-indexed law.
- **The typed layer is re-pointed.** The 28 typed lemmas and the 83 compatibility lemmas take the
  same steps against the world-indexed laws, at the new `cN`. Their extra premise is the context
  at every world. That is the fundamental lemma's hypothesis, generalised over `Θ`, and `gN`'s
  monotonicity along `ExtP`. The step is mechanical, but every one of those proofs has to be
  touched.

## 4. The spike (`Core/Chain/KStopSpike835N.lean`, deleted; in git history at `c3669cec`)

**Producer 1: `perform`. It works.**
- `erwpK_perform` is `erwp_perform`'s proof, with the continuation premise read at every
  `y` with `en.wk y ρk`.
- Nothing is missing.

**Producer 2: the Mut Frame across a stop. It works, with one added premise.**
- `erwpK_M_frame` is `erwp_M_frame`'s proof (the must-resume table `LendOK`) at every world:
  - the return case reads the post at the world the borrowed run chose;
  - the stop case re-enters the frame at the resumption world `y` by the induction hypothesis.
- The new premise is `OpTabK.FoldTwin Inv Ti To ℓ A`. At the shares of a fold at `ℓ` (exactly
  `extF_fold`'s), every world the lender's entry allows at the lender's share is one the borrowed
  entry allows at the borrowed share, and it satisfies `Inv`.
- **At the typed world `FoldTwin` is discharged:**
  - `extP_foldFrame`: from `Θ.Fresh A`, no `imm` record at `A`, and `ExtP A Θ Θ′` at the lender's
    share `Z/ℓ ● W″`, it gives `ExtP A (Θ + (ℓ, A)) (Θ′ + (ℓ, A))` at the borrowed share
    `ρk ⊆ Z`.
  - Its proof is `LocTy.ExtP.fold`. The fold's `hc` is discharged at these shares: a borrow cell of
    `ρk` shorter-lived than `A` is not `Z`'s cell at `ℓ`, which is at `A`, so it is a cell of
    `Z/ℓ`, and so of `ρkL`. Keys and `imm` records above `A` come from `ExtP`'s own clauses.
  - `foldTwin_wk_typed`: the world clause holds with the lender's order `ExtP A ∧ FoldInv A` and
    the borrowed order `ExtP A` between the worlds with the lend.
- **What was missing, and is now stated:**
  - `FoldInv A` at the resumption world. `ExtP A` alone does not keep it (`extP_not_foldInv`), so
    the lender's order carries it (§1, addition 2).
  - `erwp_M_frameCR`'s two further cases do not change this:
    - the cancel case reads `hcan` at the world `y`, which is a world binder on the premise;
    - the raise case owes no continuation.

**Embedding:** `erwp_eq_erwpK`, `opTableK_liftTab`, `erwp_opTableN_eq_erwpK` (§1).

All 8 results are registered in `scripts/AxiomCheck.lean`. Each one's axioms are within
`[propext, Classical.choice, Quot.sound]`.

## 5. The item that is not mechanical: posts at the lend's exit

This is (c), and it lives in the lend rules' compatibility lemmas (`withbor1/2/3(U)`,
`withload(U)`, `withbor2S`, `withborFS`, `withbor3S`, `withloadS`: 12 theorems). They build no
stop. The problem:

- After `vN_local`, the callback's result is `vN` at `Θ` at the lend's floor `α`.
- `U` at floor `α` owes fewer futures than at the lender's floor `lo > α` (`ExtP.mono` read
  backwards). So the result is not `vN` at the lender's floor.

There are two routes. Neither is derived here.

1. **An existential post floor.** The post is read at `(Θ, c, α)`, and the lender runs on at the
   lower floor.
   - Its later stops then owe only along `ExtP α`, including stops made after the lend has ended.
   - An in-program handler around the lender would get `κ` at a floor below its own, so E10 would
     not apply to it. This route keeps the relation sound but does not give E10 after a lend.
2. **Raising the floor for values whose cells lie above it.** Prove: `vN` at floor `α`, at a
   resource whose borrow cells are all at or above `lo`, implies `vN` at floor `lo`.
   - A callback's result in `Res_α` holds only the lender's cells, since the callback's own lends
     are below `α` and have exited.
   - The candidate invariant is that the run's world has no key or borrow cell strictly between
     the lend's floor and the lender's. `ExtP`'s clauses and `FoldInv` are of that kind.
   - This is new reasoning about `vN`'s `U` clause and stratified families (`famL`, D4).

**Not derived; obstruction not verified.** No configuration shows that either route fails.

## 6. Verdict and estimate

**Verdict: substantial but additive.**

The parts that are additive:
- **The definitions.** `erwpK` and the Kripke stop extend `erwp` along a world index. The
  constant-world embedding is proved (`erwp_eq_erwpK`, `erwp_opTableN_eq_erwpK`), so every
  existing statement survives verbatim as the `Unit` instance.
- **`rwpG` and everything below it** are unchanged.
- **Producers:**
  - 55 are mechanical;
  - 13 `mut` frames need `ExtP.fold`, which the spike shows works (`erwpK_M_frame`,
    `extP_foldFrame`);
  - 16 need a small transfer lemma of the same shape that is not yet proved: the `imm` fold
    analogue (12) and the anti-frame share transfer (4);
  - 26 are programs or configurations that stay at the constant world;
  - none needs new reasoning.
- **Consumers.** None relies on a stop at one fixed world.

Why it is not plumbing:
1. **The typed layer is re-pointed, not reused.** `cN` is redefined through `erwpK` at
   `(Θ, c, lo)`, with `vN`'s `U` at a floor. Every typed and compatibility lemma (111) is re-proved
   at the new `cN`. The steps are the same, and the premises are read at every world.
2. **Two additions to the stop** that the brief did not list (§1): the stop chooses its floor, and
   the lender's order under a live lend keeps `FoldInv`.
3. **One item of new reasoning (§5).** Posts across a lend's exit need either an existential floor
   (sound, but E10 is lost after a lend) or a floor-raising lemma for `vN` (not derived). This is
   where E10 for in-program handlers is decided.

**It is not a rebuild.** No definition below `erwp` changes, no existing statement changes, and the
hardest frame goes through by its existing proof plus `ExtP.fold`.

**Estimate** (one agent run ≈ 1 unit):

| Item | Units |
|---|---|
| `erwpK`, the Kripke stop, the embedding, the generic laws (`ErwpN`, `BindN`, `HandleN`, `TabLeN`, `LoopN`, `Ubind*`) at `erwpK` | 1 |
| The 13 `mut` frames, with `FoldInv` and the stop's floor | 1–2 |
| The `imm` fold analogue and anti-frame share transfer; the 16 frames | 1–2 |
| The remaining M producers on the path (31), handlers included | 1 |
| `vN`'s `U` at a floor; `vN_extR` along `ExtP`; `gN` monotone; `tabN`/`entN` at the world; the scheduler (`PoolN`, `SchedOKN`) at the Kripke stop | 1–2 |
| Re-pointing the 111 typed and compatibility lemmas | 2–3 |
| §5: the floor at a lend's exit (research; may not close) | 1–3 |
| E10, `effHandleV`, `effHandleVB`, `reify` on top | 1 |
| **Total** | **9–15** |

The spread is mostly §5. Without §5 the build is 8–12 units and comes out at the fallback's
coverage: E10 for in-program handlers whose stops have no live lend and no earlier lend exit.
