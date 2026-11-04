# Scope: the step-indexed relation over the tree world (#781)

Part of #771, row 4. SPEC §62; `structure.md` §3, §5. This doc covers layout, what is ported,
the headline statements, the open items, the slices, and what not to do. No code lands until it
is reviewed.

Source: `tree-inv` 92b6cc49, a local branch (not pushed) whose tree holds the spike library
`experiments/DtorUnwind/DtorUnwind/`, which is not on `main` (below: `TreeWp/`, `Tree/`, `SI/`).
Every headline result cited from it was checked: `#print axioms` ⊆ `[propext,
Classical.choice, Quot.sound]` (`cerwpT_adequacy`, `stepKeepsFdEsc`, `fdEsc_at_join`,
`immEnd_valid_of_fdEsc`, `escBeneathT`, `twnt_invHolds`, `contShareT_resume`, `twp_update`,
`not_stepKeepsFdEscNoUpd`, `cactusT_not_fdEsc`).

## 1. Layout

The typed world uses only the carrier, re-reading and codes, and no machine. Only five spike
files read the machine (`Step1`, `Steps`, `Final`, Core's `Steps`/`EffMachine`/`Qual`):
`Rel` (from `twp` on), `Eff`, `Cactus`, `StepCopy`, and `fdEsc_at_join` in `EscBeneath`. That
gives the split. `Support/` never imports `Core/`, so the machine half goes in `Core/`, as flat
files with a `Tree` prefix (Core has no subdirectories; it groups files by prefix: `Div*`,
`Eff*`).

| Library file | From (spike) | Contents |
|---|---|---|
| `Support/Model/Tree/Reread.lean` | `Tree/KSem.lean` (52 of 65 decls) | `TRes`, `KSem`, `LocTy`, `Cov`/`CovR`, `RC`, `RR` and lemmas, `rrRel`, the formers `vUnit vSum vImm vRef vBox` that codes read |
| `Support/Model/Tree/World/Codes.lean` | `TreeWp/Codes` | `KTy`, `interp`, `sem`, `AgreeOn`, `HoldsMut`, `RR.exists_retype`, `RR.trans_retype` |
| `…/World/World.lean`, `FlatLs.lean` | `TreeWp/World`, `FlatLs` | `TWd`, `TWd.Ext`, `RRw`, `WInv` |
| `…/World/Records.lean`, `Images.lean` | `TreeWp/Records`, `ImagesT` | `FrameRecT`, positions and lineages, `TChoice`, `canonTc`, `RecRR`, `TWNT` |
| `…/World/Inv*.lean`, `Shape*.lean`, `TInv*.lean`, `Templ`, `Coherent`, `NoOwnUnder`, `RebRR`, `SimL` | the same `TreeWp/` files | `TWNT.inv`, `templ_reread`, `mutOne`, `tcCoherent`, `noOwnUnder`, `twnt_invHolds` |
| `…/World/Recs.lean` | top of `TreeWp/Rel` (before `twp`) | `SRecT`, `rsOfT`, `TaggedT`, `SplitT`, `RecInv`, `RecsRR`, `SRecsRR` |
| `…/World/UpdX.lean`, `UpdXInv.lean` | `TreeWp/UpdX`, `UpdXInv` | `UpdX`, `recMask`, `NoneAt`, `MaskDiff`, `InvKept`, `UpdX.inv` (`UpdX.frame` retired by #806) |
| `…/World/FdEsc.lean` | `TreeWp/ImmEndEsc`, `FdEscCactus` (def only), `FdEscBranch`, `EscBeneath` (less `fdEsc_at_join`), `StepKeep` | `FdEsc`, `immEnd_valid_of_fdEsc`, `EscBeneathT`, `escBeneathT`, `fdEsc_of_points`, `fdEsc_of_updX` |
| `…/World/ExtF.lean` | `TreeWp/ExtFT` | `InDomT`, `FrzT`, `RelAtT`, `RelFT`, `extFT`, `extFT.rr` |
| `Core/StepsN.lean` | `SI/WpN`, `SI/LoopN`, `SI/RwpG`, `SI/HandleN`, `SI/Frag`, `LoopAwait` (16 decls) | `StepsN`, `Final`, `stepsN_of_steps`, `final_opPlug`, the `FinDom` step lemmas, `OrDiverges` |
| `Core/TreeWp.lean` | `TreeWp/Rel` from `twp` on | `EndT`, `twp`, every `twp_*` rule, `endT_inv` |
| `Core/TreeWpEff.lean` | `TreeWp/Eff` | `OpEntT`, `fdAt`, `contShareT`, `opTableT`, `cerwpT` and its rules |
| `Core/TreeCactus.lean` | `TreeWp/Cactus`, `fdEsc_at_join` | `CactusInvT`, `cactusT_step/extend/move/spawn/join`, `JoinPtT`, `cerwpT_adequacy`, `fdEsc_at_join` |
| `Core/TreeStepKeep.lean` | `TreeWp/StepCopy` | `StepKeepsFdEsc`, `stepKeepsFdEsc`, and its companion (§2) |

Each file gets the `[spec §62]` banner and #777's header shape (what it is, forced changes named
with their printed rows). Each also needs a line in `Support.lean`/`Core.lean`. Nothing is
imported from `experiments/`.

## 2. The port list

This was computed, not guessed. I took the transitive closure of declaration uses, from the built
spike environment (`Environment.find?`, the constants used by each type and value, restricted to
`DtorUnwind.*`). The roots are the headline results: `cerwpT_adequacy`, `cactusT_*`,
`stepKeepsFdEsc`, `fdEsc_at_join`, `immEnd_valid_of_fdEsc`, `escBeneathT`, `twnt_invHolds`,
`fdEsc_of_updX`, the `twp_*` and `cerwpT_*` rules, `contShareT_*`, `extFT*`, `UpdX.*`,
`endT_inv`, `fdAt_iff`, `TWNT.templ_reread/mutOne/tcCoherent/noOwnUnder`.

| Group | Decls needed | Already in the library |
|---|---|---|
| `TreeWp/` (40 files, 13.4k lines) | 830 of ~1230 (about 9.9k lines) | none |
| `Tree/` carrier and `Tree/Port/` | 595 | **all 595**, same names, identical types (`Expr.hash` compared between `tree-inv` and `si-781`) |
| `Tree/KSem.lean` | 52 | none: `Support/Model/Tree/Reread.lean` |
| `SI/` and `LoopAwait` | 16 (machine facts above) | none |

No chain-world declaration is in the closure: no `erwp`, `cerwp`, `crwpG`, `TW`, `TWN`, `TWNC`,
`ewp` or `ExtF` (chain). Core is reached only through the dynamics (`Core.Steps`,
`Core.EffMachine`, `Qual`). The per-file name list is in the appendix.

**Not ported:**
- `TreeWp/Ops.lean` (`TWd.graft`, fresh child, `setTy`): no headline uses it today. The
  multi-branch slice ports what it reads (graft at a resume).
- `Tree/KSem.lean`'s `KMono`, `MonoΘ`, `reread`, `kmono_*`, `vMut`, `vThunk`: these go to #782
  (landed: `Support/Model/Tree/KSem.lean`; `docs/new-core/scope-782.md`).
- `TreeWp/TInvConfig.lean` (`tit_twnt_config`): this was the non-vacuity check of
  `TWNT.InvHolds` while it was a hypothesis. `twnt_invHolds` now discharges it, so it is history.
- Every chain-world `SI/` result (`erwp`/`cerwp`/`crwpG`, `HandleN`, `CaptureScope*`,
  `CactusInv`, `ExtF`/`ExtExtF`/`LinDisj`) and every spike program (`CrossProg*`, `LendProg`,
  `RebProg`, …).

**Refutations and counterexamples: does each earn a place as a "rules out" theorem?**

| Result | Verdict | Why |
|---|---|---|
| `not_stepKeepsFdEscNoUpd`, `copy_config`, `copy_end_refused` (`StepCopy`) | **yes**, beside R1 | Rules out `twp` without `↭`: a branch ends holding a copy of another's lend. `copy_end_refused` shows that `↭` refuses the copy end there. |
| `lend_open_admitted`, `lend_open_needs_mask` (`UpdXMasks`) | **yes**, beside `UpdX` | Witnesses for departure D1: the mask admits a lend left open, and the mask is needed. |
| `cactusT_config`, `cactusT_not_fdEsc`, `config_not_joinPt` (`FdEscCactus`) | **yes**, beside R3 | Rules out the invariant without branch points: `FdEsc` fails there, and `JoinPtT` fails there. |
| `twnt_config`, `immEnd_esc_config`, `config_not_fdEsc` (`ImmEndEsc`) | **yes**, beside R3 | Rules out a join condition read only at `ℓ` (`joinFd`): the escrow's exclusive part also has to be clear. |
| `clause3_not_cov` (`Clause3`) | **yes**, beside D3 | Shows why `MutOne` is needed. |
| `resume_frame_short`, `not_rebReentryAgreeN`, `not_rebRelabelAgreeN`, `not_witSwapIWN`, `not_extFoldTransfer`, `not_fdFromLifetimeTypes` | no | Chain-world history, cited in `evidence.md`; no library relation reads them. |
| `trU_not_kmono` | no (goes to #782) | It is about semantic types along the tree. |

The companions add about 90 declarations (`Clause3`, `FdEscCactus`, `ImmEndEsc`, `StepCopy`,
`UpdXMasks`).

## 3. #774 and #782

**`TWNT` already carries what #774's canonical images give, at the tree.** `TWNT.reb` and
`TWNT.rebDeep` take the image `canonTc tc r β` / `canonDTc …`, one template per record and per
chain view, read through the world's template choice `tc`. Re-reading carries the choice
(`TcCarried`, `templAt_reread`, `templDAt_reread`, `TWNT.templ_reread`). It is coherent
(`TWNT.tcCoherent`, with `twnt_invHolds`). At `tc = tmplT K Θ` it is `TWNC`'s `Classical`
choice (`canonTc_tmplT`). What is missing at the tree is a rule over `twp` that uses the reborrow
constructors: `erwp_reborrow`/`erwp_reborrowDeep` have no tree analogue.

**#774 as planned would be thrown away.** It makes Core's chain `TW` canonical in place. Today's
Core has no rule that holds a borrow across a suspension: T1 (SPEC §19, "the checker's rule
until §62's PRs land") refuses a non-abortive operation that crosses a borrow. So no current
Core theorem needs canonical images (#774's own motivation is "shared reborrows held across a
suspension"). The rules that do need them are the new ones, and they live at the tree relation.
Once Core reads the tree world (rows 5 and 6), a canonical `TW` has no consumer. The total
relation (`structure.md` §8) keeps `TW` for derivations without the new rules, and they never
need canonical images.

**Recommendation (for the coordinator):** retire #774 as a chain-world PR. Canonical images land
with `TWNT` in this issue's slice (a). The reborrow rules across stops over `twp` (the tree
analogues of `erwp_reborrow`, `erwp_reborrowDeep`, and the Anti-Frame `erwp_withbor3` that came with them) go to row 6 with the other
compatibility rules. If #774 is kept as a number, retitle it to those rules. `Core.C` stays on
`canon-core` as evidence.

**#782.** This issue needs part of what #782 lists as its own: `RR` (re-reading) and the codes
`KTy`/`interp`. `World`, `Records` and `twp` are built on them. #782 says it depends on row 4.
**Recommendation:** re-reading and codes land here, in slice (a). #782 keeps `KMono`, the
`kmono_*` results, `vMut`/`vThunk`, and the remaining type formers. Risk: when #782 adds formers
to `KTy` (thunks, μ, ν, ∀, families), every proof here that cases on `KTy` (`ShapeT`,
`ShapeMutT`, `Records`' positions, `KTy.immReborrow`) gains cases. They are extended, not
replaced.

## 4. Headline statements

The ported names do not exist on `si-781`, so the statements cannot elaborate in the library
before the port. Below is the exact Lean text. It **elaborates against the spike's names**: a
scratch file importing `DtorUnwind.TreeWp.UpdXMasks` and `DtorUnwind.TreeWp.TInvConfig` on
`tree-inv`, checked with `lake env lean`, no errors. The same file checks `TopAdequacyT` against
`cerwpT_adequacy` and `R1_StepKeepsFdEsc` against `stepKeepsFdEsc`. In the library the file
becomes `Core/TreeHeadlines.lean`, with the namespaces of §1.

| Statement | Status |
|---|---|
| `TopAdequacyT` | proved (`topAdequacyT`, from `cerwpT_adequacy`); one branch at the top |
| `MultiBranchAdequacyT` | proved (`multiBranchAdequacyT`, `Core/TreeSched.lean`); `SchedOKT` a definition (`Core/TreeHandle.lean`). It goes through `cerwpT_adequacy` at one branch (`cactusT_step`, no other branch in `CactusInvT`); the stored continuations are carried by `KapSchedT` (and `PoolT`) in `cerwpT_schedHandle`'s induction, not as branches of `CactusInvT` (below, *The invariant is in pool form*). Changed from the draft below: the task runs at base and present frame conditions every valid frame meets, not the empty frame (the scheduler's state is in a resumed branch's frame). `PoolSchedAdequacyT` (`Core/TreePoolSched.lean`) reads `SchedOKT` at `Qout = PoolAns`, the scheduler's answers functions of one fixed state representation (`stateVal`, `poolVal`; D18); `MultiBranchAdequacyT` is the general statement. Instances: `stackProg_safe`; `progLoan_safe`, `progCancel_safe`, `progDepth3_safe` under the spawning scheduler `HS` (`Core/TreePoolSpawnProgs.lean`, D19, D20) |
| `R1_StepKeepsFdEsc` | proved (`r1_stepKeepsFdEsc`, `stepKeepsFdEsc`) |
| `R2_EndBlockedByHolder` | proved (`r2_endBlockedByHolder`, from `fdEsc_of_end_valid`) |
| `R3_JoinEndNeedsFdEsc` | proved (`r3_joinEndNeedsFdEsc`, from `fdEsc_of_end_valid`; the converse direction is `fdEsc_at_join` + `immEnd_valid_of_fdEsc`) |
| Borrow edges to ancestors, in `CactusInvT` configurations | proved as properties of `CactusInvT` (`borrowEdges_ancestors`, `lender_ancestor`, `Core/TreeSchedPool.lean`): a part of a branch at point `n` holding any cell at the location of a record proper framed at `α` has `n` inside `α`, from `CactusInvT` alone (`fd_le_of_branch`). Instances at depth 1 and 3 (`lenderEdge_depth1`, `lenderEdge_depth3`, `Core/TreeBorrowEdges.lean`) add the second branch by hand (`cactusT_spawn`). **No scheduler instance:** the stored tasks are carried by `PoolT`/`KapAtT`, not as branches of `CactusInvT`, and nothing connects the two. **Open, #789:** derive the property for `PoolT`/`KapAtT` shares |
| `R4_ExtExtFT` | proved (`r4_extExtFT`, from `ext_extFT`, `Support/Model/Tree/World/ExtExtF.lean`); `RelT`, `KeepsT`, `CellInT`, `ExtLT` defined there (Core's `Rel`, `Keeps`, `CellIn`, `Ext` over the tree carrier), the statement as below |

Names that do not exist yet anywhere: `SchedOKT`, `RelT`, `KeepsT`, `CellInT`, `ExtLT` (the last
four are defined in the text). Every other name is the spike's.

How the four rules-out theorems map onto #781's list: R1 is "a branch's step that leaves it
holding part of another branch's open lend". R2 is "resuming a stored continuation after another
branch ended a lend it still borrows": the end cannot happen while the stored branch's share is
part of the world. R3 is "a join that ends a shared lend while another branch still holds part".
R4 is "a resumption condition stricter than the world's own extension".

```lean
import DtorUnwind.TreeWp.UpdXMasks
import DtorUnwind.TreeWp.TInvConfig

/-! Headline statements of #781, at the spike's names (tree-inv 92b6cc49). -/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Headline781
open BoCa BoCa.Fig16 BoCa.Fig16.Tree BoCa.Fig16.Tree.Wp BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap hndE hndVal)

/-- The empty world at the tree `P`. -/
def w₀ (P : ParentFn) : TWd := ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩

/-! ### H0. Adequacy (the `OrDiverges` shape) -/

/-- **H0a, one branch at the top** (proved: `cerwpT_adequacy`). -/
def TopAdequacyT : Prop :=
  ∀ (P : ParentFn) (Q : TPostV) (P₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty) n (w₀ P) [] []
      P₀ (PMap.empty : TRes (WCactus.ofParent P))) →
    BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait.OrDiverges (ℍ := ℍ) P₀

/-- **H0b, any number of branches.** A closed program `hnd H e₀`: the task `e₀` at `cerwpT` at the
scheduler's table `T`, the scheduler `H = hndVal n₀ qs hr hs` meeting `SchedOKT` (its clauses at
`cerwpT` at the empty table, each `κ` read by the continuation's predicate at the tree, the
stored continuations carried by that predicate). `SchedOKT` is not defined yet: it is the
parameter here only so that the statement elaborates. -/
def MultiBranchAdequacyT
    (SchedOKT : OpTabT → UInt32 → Val → Val → Val → TPostV → TPostV → Prop) : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV) (e₀ : Expr),
    (∀ k w ls O v ρ, Qout k w ls O v ρ → ρ = PMap.empty) →
    SchedOKT T n₀ qs hr hs Qin Qout →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin (fun _ ρf => ρf = PMap.empty) n (w₀ P) [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait.OrDiverges (ℍ := ℍ) (hndE (hndVal n₀ qs hr hs) e₀)

/-! ### R1. A step keeps every other branch's open lend (proved: `stepKeepsFdEsc`) -/

abbrev R1_StepKeepsFdEsc : Prop := StepKeepsFdEsc (ℍ := ℍ)

/-! ### R2. A lend a stored branch still borrows is not ended -/

/-- **R2.** In a configuration of the cactus invariant, a branch `b` that holds part of a record
proper `p`'s lend (its flattening meets `p`'s location or the escrow's exclusive part, `¬ FdEsc`)
blocks the end of `p`: with `b` a part of the rest `Y` of the world, `ℓ ↦ own(v) ● R` does not
compose with `Y` to a valid world. So no branch resumes after `p` ended while it still borrowed. -/
def R2_EndBlockedByHolder : Prop :=
  ∀ (w : TWd) (bs : List (TBranch w.K)) (ns : List Life) (W : TRes w.K)
    (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)) (μ : Heap),
    CactusInvT w bs ns W ps ls μ →
    ∀ b ∈ bs, ∀ p ∈ ps, ¬ FdEsc p.le p.R b.1 →
    ∀ (s : TSet) (hs : p.R.InStratum s) (Y Yr X' : TRes w.K),
      ResUT.CompS (ResUT.single p.le (CellUT.immOf s p.v p.R hs)) Y W →
      ResUT.CompS b.1 Yr Y →
      ResUT.CompS (ResUT.single p.le (CellUT.ownOf p.v)) p.R X' →
      ¬ ∃ W', ResUT.CompS X' Y W' ∧ ResUT.Valid W'

/-! ### R3. A join ends a shared lend only when no other branch holds part of it -/

/-- **R3.** At a join, the joiner (the head branch) owns `p` and ends it: if the end world is valid,
the other branches' composite holds nothing of `p`'s lend (`FdEsc`). With `fdEsc_at_join`
(`JoinPtT` ⇒ `FdEsc`) and `immEnd_valid_of_fdEsc` (`FdEsc` ⇒ the end is valid), the end is valid
exactly when no other branch holds part of the lend. -/
def R3_JoinEndNeedsFdEsc : Prop :=
  ∀ (w : TWd) (ρ : TRes w.K) (O : List (FrameRecT w.K)) (others : List (TBranch w.K))
    (n₀ : Life) (ns : List Life) (W : TRes w.K) (ps : List (FrameRecT w.K))
    (ls : List (SRecT w.K)) (μ : Heap),
    CactusInvT w ((ρ, O) :: others) (n₀ :: ns) W ps ls μ →
    ∀ p ∈ O, ∀ (ρf : TRes w.K), CompAllT (others.map Prod.fst) ρf →
    ∀ (s : TSet) (hs : p.R.InStratum s) (Y X' W' : TRes w.K),
      ResUT.CompS (ResUT.single p.le (CellUT.immOf s p.v p.R hs)) Y W →
      ResUT.Le ρf Y →
      ResUT.CompS (ResUT.single p.le (CellUT.ownOf p.v)) p.R X' →
      ResUT.CompS X' Y W' → ResUT.Valid W' →
      FdEsc p.le p.R ρf

/-! ### R4. `extFT` is no stricter than the tree world's own extension -/

/-- `r` is relevant to `ρ` as `Core/FrameRecords.lean`'s `Rel` reads it: an `imm` cell of `ρ` at a
place `Coh` looks for `r`. -/
def RelT {K : WCactus} (r : FrameRecT K) (ρ : TRes K) : Prop :=
  ∃ (m : BoCa.Loc) (ψ : TCell K), ρ.get m = some ψ ∧ ψ.kind = Kind.imm ∧ RelAtT r m

/-- `Core/FrameRecords.lean`'s `Keeps` over the tree carrier. -/
def KeepsT {K : WCactus} (rs rs' : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ r ∈ rs, RelT r ρ → r ∈ rs'

/-- `Core/FrameRecords.lean`'s `CellIn` read in `K`: a borrow cell of `ρ` one of whose lifetimes is
`⊑ b` (`@ψ ⊑ b`, `@ψ` the meet of the cell's set, read at a member). -/
def CellInT {K : WCactus} (ρ : TRes K) (b : Life) : Prop :=
  ∃ (m : BoCa.Loc) (ψ : TCell K) (s : TSet), ρ.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧
    ψ.lsOf = some s ∧ ∃ y ∈ s.set, K.le y b

/-- **`Core/FrameRecords.lean`'s `Ext` over the tree carrier**: the records relevant to `ρ` kept,
and the records strictly longer-lived than a borrow cell of `ρ` exactly the same. -/
def ExtLT {K : WCactus} (ls ls' : List (SRecT K)) (ρ : TRes K) : Prop :=
  KeepsT (rsOfT ls) (rsOfT ls') ρ ∧
    ∀ b, CellInT ρ b → ∀ x : SRecT K, K.lt b x.2 → (x ∈ ls ↔ x ∈ ls')

/-- **R4, `ext_extF` over the tree.** At a share `ρ` inside a typed tree world at `ls`, every list
`ls′` at which a typed tree world holds and which `ExtLT` allows, `extFT` allows. -/
def R4_ExtExtFT : Prop :=
  ∀ (K : WCactus) (Θ Θ' : CodeTy) (tc tc' : TChoice K) (W W' ρ : TRes K)
    (ps ps' : List (FrameRecT K)) (ls ls' : List (SRecT K)),
    TWNT K Θ tc W ps (rsOfT ls) → TaggedT K W ps ls → ResUT.Le ρ W →
    TWNT K Θ' tc' W' ps' (rsOfT ls') → ExtLT ls ls' ρ → extFT ls ls' ρ

/-! ### Checks: the proved ones are the spike's theorems -/

example : TopAdequacyT (ℍ := ℍ) := fun P _ _ hQ hall => cerwpT_adequacy (ℍ := ℍ) P hQ hall
example : R1_StepKeepsFdEsc (ℍ := ℍ) := stepKeepsFdEsc

end BoCa.Fig16.Tree.Wp.Headline781
```

**What `MultiBranchAdequacyT` means, and why it is stated over a handler.** The machine is
single-threaded. Spawned tasks and stored continuations are values held by a scheduler that is a
handler in the program (`lib/async.bc`; `structure.md` §9, "under a storing scheduler … a
forwarding handler between the task and the scheduler"). So "any number of branches, any
schedule" is a statement about `hnd H e₀` for every scheduler `H` that meets its specification:
`H` chooses which stored branch to resume.

**The invariant is in pool form** (decision 74, the user's of 2026-11-03). A resume's frame condition
(`fdAt`, the join's `FdEsc`) is a fact about every other branch, so the stored branches need an
invariant over all of them. It is not `CactusInvT` over several branches. `multiBranchAdequacyT`
uses `CactusInvT` at one branch only (`cerwpT_adequacy` through `cactusT_step`, the running branch
alone). The stored continuations are values the scheduler's clauses hold, each read by
`KapSchedT` (and, held as a pool, by `PoolT`/`KapAtT`), and `cerwpT_schedHandle`'s induction on
the index carries them. The invariant over them has two parts: each stored share resumes at the
per-branch share condition `KeepRel` (D13), and every two are apart at each other's record masks
(`fdMask`, `recMask`; pairwise `FdEsc` in location form, D12), with no branch points. The
pool form is the invariant because branch points are not kept along tree extension
(`not_joinPtKeptT`), while the location form is (`fdMask_mono`), and a share holding views at
incomparable lifetimes has no point (#781 issuecomment-6612202867). The
alternative is a separate machine with a pool of branches (LinearActris's thread pool). It is not
recommended: it is a second operational semantics that the closed programs of #771's target
theorem do not run on, and a later PR would have to connect it to `hnd` or throw it away.

## 5. Open research items

| Item | Reads | Size (estimate) | Risk |
|---|---|---|---|
| **R4: tree `ext_extF`** (done, slice (c)) | `ExtLT`; `inDomT_imm_or_xex`, `CellAt.inStratum`, `desc_of_xexT`, `tag_ge_nestedT`, `not_relAt_xexT` over `LinPathT`, `DescRT`, `LinLocT`, `FrameLifeT`, `TaggedT`; `LinDisj`/`DLinDisj`/`EscEx` not ported (D11): `TWNT.exclUnique`, `desc_comparable`, `not_desc_proper`, `le_not_linLoc` take their role | about 480 lines with the examples | resolved. The lifetime clause leaves records incomparable with `b` free, and the proof never asks about one: the tag it bounds is reached from `b` by `b ⊏ z ⊑ t`, `z` a lifetime of the nested view (strata), `z ⊑ t` by `FrameLifeT` of the root `TaggedT` names, the root found by `root_unique` on one branch. |
| **`fdAt` monotone** (`TFrame.Mono (fdAt en v F O′)`; done: `fdAt_mono`, the re-reading's existence a premise, `fdJoinT_fdMono`) | `OpEntT.fd` monotone along re-reading (a table condition, to add as a premise callers discharge), and that a record list has a re-reading at every extension (from `RR.exists_retype` per escrow) | 150–300 lines | low. Needed when a resumed run is bound (`twp_bind`'s `hFm`), so by the multi-branch slice. |
| **Tree `extF_fold`/`extF_seal`** (with `FrzT.del_or`, `FrzT.of_del`, `not_frzT_single_own`, …) | `FrzT`, `InDomT` and the composition lemmas in `ExtFT` | 200–400 lines | low. Read only by the frame rules across stops (`erwp_M_frame`, `erwp_M_antiFrame` analogues), which are row 6. **Recommendation:** move them to row 6 unless the scheduler's specification reads `extFT` through a fold; the top-level scheduler holds no lend. |
| **The multi-branch scheduler** (`MultiBranchAdequacyT`; done for a scheduler at the program's top: `cerwpT_schedHandle`, `multiBranchAdequacyT`) | `[handle]` at `cerwpT` over the tree (no tree version exists: the spike's `[handle]` without `hdv` is `ewp_handle`/`erwp_handle`, over `ewp` and chain `erwp`, which `cerwpT` does not reuse); `κ` cells and cancel at the tree (`cerwp_kappaCell`, `cerwp_kappaC_resume/cancel` at chain); `SchedOKT`; `cactusT_move` at capture, `cactusT_extend` + `TWd.graft` (`Ops`) at a resume, `cactusT_spawn`/`cactusT_join`; `stepKeepsFdEsc` for every stored branch across each segment; `fdEsc_at_join` + `immEnd_valid_of_fdEsc` at a join; `contShareT_resume` at the resumer's list | 3k–5k lines | **high** |
| **T1 at the flattening-level `HoldsView`** (#806, open): a frame holding the copy only at depth, inside another view's witness. `twp_consume_view_framed` is stated at `HoldsCopy` (`ρf = Y ● v`, user's decision 2026-11-04). #789's compatibility lemmas are where a consume would need it, if a frame condition there supplies only `HoldsView` | `consume_view_world` needs `ρf ● v = ρf`; a world invariant for dropping a nested copy would be needed instead | not estimated | not checked |

**Missing from #781's open list: `[handle]` without `hdv` at the tree relation.** #771 row 4 says
it lands here. It exists only over the chain relations. Porting it means re-proving
`erwp_handle`'s induction on the index at `cerwpT` (the technique carries over; the declarations
do not).

**Riskiest step: what the scheduler's resume asks, and who supplies it.** At a resume, `fdAt`
asks the resumer's frame for the entry's `fd` at the resumed run's records. For a join, that is
`FdEsc` against every other branch. `fdEsc_at_join` derives it from `CactusInvT`'s points
(`JoinPtT`). But `twp` knows no points: they live only in `CactusInvT`. Resolved without points
and without changing `twp`, `EndT` or the rules of slice (b): the resumer's guarantee is read in
location form (`fdMask`, `fdJoinT`), and the stored branches are held in pool form (§4, *The
invariant is in pool form*). Next in risk: the invariant must carry
`FdEsc` of each branch against every other branch's open records. `stepKeepsFdEsc` keeps it
across a segment for the records the frame held at the segment's start (`p ∈ psF`). A record the
segment opens needs it established at the open: the other branches hold nothing of a location the
run held exclusively, which should follow from validity. That is not stated.

Not needed by the headline (as #781 allows): abortive stops under a live borrow and same-task
frames as instances of capture. `opTableT` admits only non-abortive entries (`en.abort =
false`), and `cerwpT`'s postcondition holds only at a value or such a stop, so a task verified at
the scheduler's table never ends at a raise or an abortive operation. Cancellation goes
through `contShareT`'s `fin` obligation, which exists.

## 6. Slices

Each slice leaves main green, is built on by the later ones, and has no assumed-fact
hypotheses (every headline premise is one callers discharge: `hQ`, the program's `cerwpT`,
`hup` of `twp_update`).

| Slice | Lands | Done when | Size |
|---|---|---|---|
| **(a) The typed tree world** (`Support/Model/Tree/Reread.lean`, `World/*`) | re-reading, codes, `TWd`, records, `TWNT` with canonical images, `twnt_invHolds`, `UpdX`/`InvKept`, `FdEsc`, `escBeneathT`, `fdEsc_of_updX`, `extFT`; companions `clause3_not_cov`, `lend_open_*`, `twnt_config`/`immEnd_esc_config`; SPEC §62 updated (the canonical-image paragraph, per the #774 ruling; conditions 21 and 23) | every listed result builds with axioms ⊆ the three | about 9–10k lines, mostly copied (the carrier names already match) |
| **(b) The relation at one branch** (`Core/StepsN`, `TreeWp`, `TreeWpEff`, `TreeCactus`, `TreeStepKeep`, `TreeHeadlines`) | `twp`, `cerwpT`, `contShareT`, `CactusInvT` and its operations, `TopAdequacyT`, R1 with `not_stepKeepsFdEscNoUpd`, R3 with `cactusT_not_fdEsc`, R2 | `TopAdequacyT`, R1, R2, R3 proved | about 2k lines ported, plus R2 and R3 |
| **(c) R4** | `ExtLT`, R4 (`Support/Model/Tree/World/ExtExtF.lean`); `LinDisj`/`DLinDisj`/`EscEx` not needed (D11) | R4 proved (done) | about 480 |
| **(d) Multi-branch adequacy** | `[handle]` at `cerwpT`, `κ` cells, `SchedOKT`, `fdAt` monotone, `Ops`' graft, `MultiBranchAdequacyT` | `MultiBranchAdequacyT` proved, `SchedOKT` a definition | 3k–5k |

#781 closes after (d). (c) and (d) are independent once (b) is in.

**Recommendation on order.** Land (a) when ready: it has no machine, and nothing later is
expected to change it. Before (b) merges, run a short feasibility spike of (d)'s scheduler clause
(capture, store, resume under the invariant). Merge (b) only once it confirms that `twp`, `EndT`
and `contShareT` survive (§5, riskiest step). If they change, (b) would be re-proved: that is
re-proof, not replacement, but it should not be paid twice. If the coordinator wants fewer PRs,
(a) and (b) together form one complete unit; (c) and (d) do not split further.

**Open for the coordinator:** #771 asks every PR to "replace or generalise something rather than
sit beside it". (a) and (b) sit beside Core's chain `TW` and total relation until row 6, as #777's
carrier sits beside the printed one. Unlike #777 (`chainEquiv`), there is no theorem relating
`TWNT` at a chain to Core's `TW`: codes are not `VTy` at a substitution. Is that acceptable?

## 7. Not doing; tempting shortcuts → stop

- Porting chain-world results (`erwp`, `cerwp`, `TWNC`, `Core.C`, `ext_extF` at `WRes`) to have
  something to merge.
- A second relation, or a pool machine beside the BoLo machine (§4).
- Adequacy proved around the invariant: `MultiBranchAdequacyT` must carry every stored branch
  through an invariant, not through a direct induction on runs that ignores them. The code goes
  through `cerwpT_adequacy` at one branch, with the stored branches carried by `KapSchedT`/`PoolT`
  in `cerwpT_schedHandle`'s induction under the pool-form invariant (§4, decision 74); dropping `KeepRel` or the pool's two-way separation would be going around it.
- Hypotheses standing in for open items: no `FdEsc`, `ExtLT ⇒ extFT`, `fdAt` monotonicity or
  `SchedOKT` property taken as a premise of a headline. `SchedOKT` is a parameter in §4 only so
  the text elaborates; landing it as a parameter is a stop.
- Proving a lemma some shorter way than the spike, or than the printed proof, without recording
  it, and new case splits beyond the spike's (the transcription rules, `borrow_lang` CLAUDE.md §1 and §6).
- A done-when shaped like a corpus: no program, test count or target program is a done-when.
  The spike programs are not ported.
- Folding `extF_fold`/`extF_seal` or the frame rules across stops into this issue to "finish the
  list": they are row 6 unless (d) reads them.

## 8. Departures from the printed BoLo text

| # | Departure | Justification | Printed technique not built |
|---|---|---|---|
| D1 | `UpdX`: row 5.27/5.33's `↭` masked at the run's own records' lent and escrow locations (`recMask`), read across the re-reading `w₀ → w′` | A lend left open at a stop turns `own` into the lend cell and hands out the escrow's views (`lend_open_admitted`). Without the mask that end is refused (`lend_open_needs_mask`). Unmasked locations read row 5.27 exactly (`updX_refl_imm`), and printed `UpdV ⇒ UpdX` (`UpdX.of_updV`) | `↭` unmasked across a lend left open (6.39's use) |
| D2 | `P̂` in `↭`'s `mut` clause read as "the same code at `ℓ`, each side read at its own world" (`InvKept`, `XInv`), not as equal predicates | A `○` composite's `P̂ ∧ Q̂` re-read is not the re-read of the composite. A flattened `mut` cell's `P̂` is its location's code (`flat_mut_inv`). At the identity re-reading the two agree (`updX_refl_mut`) | `P̂` compared as a predicate across `↭` |
| D3 | `MutOne`: one `mut` cell per location at any depth (`TWNT.mutOne`) | Makes a flattened `mut` cell a stored one. Without it, clause 3 of two covered cells is not covered (`clause3_not_cov`, also on the printed chain) | reasoning about clause 3's `P̂ ∧ Q̂` composite |
| D4 | No `ρ⁺` (row 5.33, `ρ ↭ ρ′ ● ρ⁺`, `ρ⁺∣own = ∅`); `twp` relates `ρ₀` and `ρ′` | Inherited from `crwpG` | garbage `ρ⁺` (`wpG_garbage`; the chain has `rwpG_garbage`) **#793's result** (`Core/TreeConsume.lean` on `spike-793`, 6e6ac79e; `twp` unchanged): a run may give up a copy of an `imm` view when the run itself holds another copy (`twp_consume_view_held`, and through `twp_bind`, `twp_bind_callee_consume`), and the lender may give up a spare copy before `twp_lendEnd` (`twp_lendEnd_after_consume`); it is refused when the other copy is held only outside the run, by a callee proved on its own copy (`twp_frame_callee_refused`) or a spawned task (`twp_child_refused`), from `UpdX`'s start-side `imm` clause alone. Restoring `ρ⁺` literally puts another branch's garbage in the lender's frame, which fails `twp_lendEnd`'s `hF` (`not_noneAt_view`). **Resolved by #806 (design (b), `UpdA`):** `EndT` reads `UpdA`, under which an `imm` cell may leave `⦇ρ′⦈` when the end world still holds it; the refusals above are retired, and a run may give up its copy when a callee proved on its own copy (`twp_frame_callee_consume`) or a spawned task (`twp_child_consume`) holds another, and at `HoldsCopy` (`twp_consume_view_framed`); still no `ρ⁺`. Open for #789: T1 at `HoldsView`. |
| D5 | `UpdX.frame`, a masked cross-world 6.48, proved pointwise (`flat_compR`, `xopt_comp`) | Shorter route | **6.48's ancestor technique** (a `mut` cell of the aliasable walk accounted for by its immutable ancestor) is not built in `UpdX.frame`. It exists at the tree in `Support/Model/Tree/Port/Six48.lean`, and `fdEsc_of_updX` uses it (`innermost_view`). **Recommendation:** in the port, prove `UpdX.frame` along `Port/Six48`, or record the route in its docstring. This is the pattern `borrow_lang` CLAUDE.md §1 warns about (6.59 needed the ancestor technique). **#806:** `EndT` reads `UpdA`, whose frame step `UpdA.frame` is proved along the walks (`Flat.split_factors`, then the ancestor: `AgW.mut_beneath`, `Beneath.lift`), so the technique is built on `EndT`'s path. **Retired (C-2, user's decision 2026-11-04):** `UpdX.frame`, `xopt_comp`, `xcell_compR`, deleted as unused once off `EndT`'s path; `UpdA.frame` along the walks replaces it. Restore with `git show a66b0538:Support/Model/Tree/World/UpdX.lean` lines 212–413 (see `scope-806.md`, "Retired results"). |
| D6 | `FdEsc` (nothing at `ℓ` nor at any location of `ex(R)`, at any depth) as the join's condition, from branch points | Printed 6.64 reads H24/H6 (the frame fixed for the run), which the tree does not have. `joinFd` at `ℓ` alone is not enough (`immEnd_esc_config`) | 6.64's H24/H6 route |
| D7 | Retired: branch points are not used by the scheduler, whose stored tasks are held in pool form (D12, D13; §4, decision 74). `CactusInvT` keeps its points for top-level adequacy (`cactusT_not_fdEsc`) | — | — |
| D8 | `escBeneathT` is a new derivation with its own case splits, not a port | — | Check it in review against `borrow_lang` CLAUDE.md §6: the splits are ours |
| D9 | Store types as codes `KTy`, no substitution `δ`/`AdmWf` | Ruling of condition 16 | — **Open, #790:** a `mut` payload is a code, so no closures, thunks or continuations in cells. |
| D10 | `extF`/`extFT`, the in-house extension condition R4 reads (`ext_extFT`); its use as the resume condition is retired (see D13) | In-house design (`SI/ExtF.lean`: "not a transcription") | — |
| D11 | `ext_extFT`'s `desc_of_xexT` reads the owner of an exclusive cell off `TWNT.exclUnique` (with `desc_comparable`, `not_desc_proper`, `le_not_linLoc`), not off the chain's `DLinDisj`, `EscEx` and `xpath_unique` in the root's escrow | Those results are already proved of `TWNT`, its `reread` case included; `DLinDisj`/`EscEx` would need a new `reread` case | — (the chain statements are in-house designs, not printed) |
| D12 | The scheduler's join condition in location form (`fdMask`, `recMask`, `fdJoinT`), carried by the clause's state, not branch points | Points are not kept along tree extension (spike `not_joinPtKeptT`); locations are (`fdMask_mono`) | — (not printed) |
| D13 | `contShareT`/`KapSchedT` resume at any list keeping the re-readings of the stop list's records the share reads (`KeepRel`), not at a re-reading of the whole stop list with `extFT` against it | A resume after another branch ended a record of its own that was open at the stop has no re-reading of the stop list; the share reads only its own lineage. The D10 condition implies it (`keepRel_of_extFT`, `contShareT_resume_ext`) | — (not printed) |
| D14 | Opening and ending a lend as two `twp_update` instances (`twp_lendOpen`, `twp_lendEnd`, `Core/TreeLend.lean`), not the scoped Imm Frame (6.64: open, run the body, end); the empty escrow only | A lend open across a stop is opened in one segment and ended in another (#781 slice (d), item 1). The end's condition is `FdEsc ℓ ∅` against the rest of the world, read off the frame and the run's other part; the escrow's contents and their views (`TWNT.reb`) are not covered | 6.64's scoped proof (H12–H36); reborrows of the escrow at `twp` **Open, #791:** non-empty escrows and reborrows of their contents (the empty-escrow limit is coverage, not design). |
| D15 | Cancel is a resume into the cancel branch: `contShareT` owes the unwinding `ccatch (K†[raise …])` as a continuation at a cancellable entry (`OpEntT.fin` a flag), and `KapSchedT` (which now names its scheduler `H`) offers `hnd H (κ (inj₂ ()))` at `cerwpT`, so an unwinding that performs comes back to `H`'s clause as a stored continuation | #781 issuecomment-6612871618. `cerwpT_schedHandle` proves the offering by its induction hypothesis (`twp_kappa_cancel_in`, `twp_kappaC_cancel_in`); the cancel answer is in the task's answer predicate. Kept after #793 (issuecomment-6634439429): a cancelled task may hold `own` cells (decision 73: used, not lost), `mut` cells (one holder), a copy only the frame holds, or the last copy of a view, so the cancel branch has to run. The unwinding it runs is `[then]` and the unwinding borrow forms (`withborU`, §19), which end the branch's lends; there is no per-type close (decision 73). The tree has no `withborU` rule yet (row 6): the closed programs end their lends through `ubind` finalisers in the program and `twp_lendEnd` in the proof | a separate answer predicate for cancelled tasks |
| D16 | Retired as a departure: `[handle]` at `cerwpT` for a top-level scheduler only, with no forwarding, is open coverage (#792; below) | — | — |
| D17 | `cerwpT Tb Q Fb F` carries a base frame condition: a stop hands the table the base `Fb`, not the frame condition current at the stop | A resumed task's frame condition is the base and its resumer's guarantee at its records at that resume, so a stored continuation's mask is its records' at its stop and the scheduler's interface has no mask history. `cerwpT_schedHandle` asks only that every valid frame meet the base | the frame condition at the stop handed to the table |
| D18 | A scheduler handler's state is a value `(H, pool)` and its answers are functions of it (`PoolAns Q H Inv`); `SchedOKT` is read at `Qout = PoolAns` | A deep handler has no parameter, so the pool is threaded as the answer's argument; the state carries `H` so a clause runs a new task or a stored task's cancel branch under its own handler without naming itself (a clause cannot contain the handler value it belongs to). `Inv` is the scheduler's own invariant on its pool, the empty pool meeting it. `PoolSchedAdequacyT` is tied to this one state representation (`stateVal`, `poolVal`); `MultiBranchAdequacyT` is the general statement, fixing no representation | a parameterised-handler form; the pool kept in a heap cell |
| D19 | A scheduler whose clause runs a task under itself proves `SchedOKT` through `SchedOKTLe N` (clauses asked at stops `k ≤ N`), by strong induction on `N` (`cerwpT_schedHandle_le`, `poolAns_run_le`, `schedOKT_of_le`) | A spawn clause at stop `k` needs `[handle]` for its own scheduler; the child runs at least one step below `k`, so `SchedOKTLe` below `k` suffices and no premise on the scheduler is added | a step-indexed fixpoint of the scheduler's relation |
| D20 | `enSpawn`'s payload is a thunk verified at the child table `TC` (park and cancel), from every world and list, owning nothing | `TS` cannot name itself in its own entry; `TC ⊆ TS` lifts the child by `cerwpT_table_mono`. A limit of the example scheduler `HS`: children spawn from the root only and start owning nothing. Cross-task borrows are excluded by the pool invariant itself, not only by `HS`: `PoolT`'s two-way apartness (`NoneAt (recMask Ot) b`, `NoneAt (recMask Os) a`), `PoolAnsAt`, and the `fdMask` frame and resume conditions leave no task holding part of another's lend. Resources and records handed through spawn, join, and borrows shared across tasks need a change to the pool invariant, not only a new scheduler (#795) | a spawn entry at the root's own table (nested spawn) |

Open coverage, not departures: `[handle]` at `cerwpT` for a top-level scheduler only, with no
forwarding handler between a task and its scheduler (#792, D16); borrow edges to ancestors for the
scheduler's stored shares (`PoolT`/`KapAtT`, #789).

Unspent printed hypotheses: 6.64's H24 and H6 (D6). Unused uniqueness results: none
(`RecRR.func`, `RecsRR.func`, `RR.func`, `Flat.functional`, `CompR.functional` are used).
Untranscribed printed lemmas in the run-up: row 5.33's `ρ⁺` (D4), the `P̂` part of row 5.27
across re-reading (D2, read as codes), 6.48 at the masked cross-world reading (D5).

## Appendix: declarations to port, by spike file

Computed from `tree-inv` 92b6cc49; generated names (`.rec`, `.casesOn`, `match_`) are left out.
`Tree/` carrier names are not listed: all are in the library already (§2).

`LoopAwait.lean` (1): `LoopAwait.OrDiverges`.

`SI/Frag.lean` (6): `emp`, `fd_del`, `fd_empty`, `fd_fill`, `fd_step1`, `fd_upd`.

`SI/HandleN.lean` (1): `final_opPlug`.

`SI/LoopN.lean` (1): `stepsN_of_steps`.

`SI/RwpG.lean` (2): `Final`, `final_val`.

`SI/WpN.lean` (5): `StepsN`, `StepsN.more`, `StepsN.refl`, `fd_stepsN`, `stepsN_plug_split`.

`Tree/KSem.lean` (52): `Cov`, `Cov.imm`, `Cov.mut`, `Cov.own`, `Cov.rc_refl`, `CovR`, `CovR.sng`, `ImmT.eq_of`, `KSem`, `KSem.P`, `LocTy`, `MutT.eq_of`, `PMap.del`, `PMap.del_get`, `PMap.ins`, `PMap.ins_get`, `RC`, `RC.cov`, `RC.erase`, `RC.func`, `RC.imm`, `RC.inStratum`, `RC.kind`, `RC.mut`, `RC.own`, `RC.wit`, `RR`, `RR.cov`, `RR.empty`, `RR.exists_of`, `RR.func`, `RR.get_some`, `RR.get_some'`, `RR.inStratum`, `RR.of_empty`, `RR.of_sng`, `RR.refl`, `RR.rsim`, `TCell`, `TImm`, `TMut`, `TRes`, `WCactus.Ext.le`, `WCactus.Ext.refl`, `WCactus.Ext.trans`, `WCactus.minS_minS`, `rrRel`, `vBox`, `vImm`, `vRef`, `vSum`, `vUnit`.

`TreeWp/Cactus.lean` (36): `Apart`, `Apart.rr`, `AtPoints`, `AtPoints.rr`, `CactusInvT`, `CellAboveT`, `CellAboveT.rc`, `CellUT.CompS.ls`, `CompAllT`, `CompAllT.cons`, `CompAllT.nil`, `CompAllT.reread`, `JoinPtT`, `OnBranchResT`, `OnBranchResT.compS`, `OnBranchResT.empty`, `OnBranchResT.of_compS_left`, `OnBranchResT.rr`, `OpTabT.empty`, `TBranch`, `cactusT_extend`, `cactusT_frame`, `cactusT_join`, `cactusT_move`, `cactusT_spawn`, `cactusT_step`, `cerwpT_adequacy`, `compAllT_functional`, `extLe`, `forall₂_flatten`, `forall₂_map_left`, `forall₂_zip`, `lower_emptyT`, `opTableT_empty_false`, `recInv_empty`, `winv_empty`.

`TreeWp/Clause3.lean` (0 + 15 companion): . Companions: `cellAt`, `cellAt_cov`, `clause3_not_cov`, `compAt`, `compAt_compR`, `conj_tyPred`, `empty_inStratum`, `minS_pair`, `viewAt`, `viewAt_inStratum_iff`, `Θ3`, `Θ3_one`, `τ3`, `τ3_inj₁`, `τ3_view`.

`TreeWp/Codes.lean` (29): `AgreeOn`, `AgreeOn.of_compS_left`, `AgreeOn.of_compS_right`, `AgreeOn.refl`, `AgreeOn.trans`, `AgreeOn.wit`, `CodeTy`, `HoldsMut`, `HoldsMut.deep`, `HoldsMut.of_compS_left`, `HoldsMut.of_compS_right`, `HoldsMut.rr`, `HoldsMut.top`, `KTy`, `KTy.box`, `KTy.imm`, `KTy.interp`, `KTy.mut`, `KTy.ref`, `KTy.sum`, `KTy.unit`, `RC.exists_retype`, `RC.trans_retype`, `RR.exists_retype`, `RR.exists_retype_stratum`, `RR.trans_retype`, `interp_retype`, `sem`, `sem_of`.

`TreeWp/Coherent.lean` (26): `CellAt`, `CellAt.nest`, `CellAt.not_empty`, `CellAt.of_compS_left`, `CellAt.of_compS_right`, `CellAt.of_del`, `CellAt.of_le`, `CellAt.rr_back`, `CellAt.single_inv`, `CellAt.single_own`, `CellAt.split`, `CellAt.top`, `CellAt.wit_trans`, `CellUT.CompS.kind_imm`, `LinPathT.cellAt`, `MutOne`, `MutOne.of_back`, `RC.inj_of`, `RR.inj_of`, `TWNT.mutOne`, `agW_cellAt`, `cellAt_image`, `cellAt_top_own`, `cellAt_walk_dom`, `exRT_cellAt`, `kind_mut_ne_imm`.

`TreeWp/Eff.lean` (34): `ContT`, `OpEntT`, `OpEntT.PA`, `OpEntT.PBv`, `OpEntT.abort`, `OpEntT.fd`, `OpEntT.fin`, `OpEntT.oc`, `OpEntT.q`, `OpTabT`, `RecsRR.func`, `TPostV`, `TVProp`, `TableT`, `TableT.Local`, `cerwpPostT`, `cerwpT`, `cerwpTC`, `cerwpT_eq`, `cerwpT_fold_at`, `cerwpT_kripke`, `cerwpT_perform`, `cerwpT_step`, `cerwpT_unfold_at`, `cerwpT_val`, `cerwpT_zero`, `contShareT`, `contShareT_kripke`, `contShareT_resume`, `contShareT_resume_rr`, `fdAt`, `fdAt_iff`, `opTableT`, `opTableT_local`.

`TreeWp/EscBeneath.lean` (26): `CellAt.not_own_wit`, `ChainD`, `ChainD.chain`, `ChainD.last`, `ChainD.one`, `ChainD.step`, `ChainT.depth`, `ExclUniqueT`, `ExclUniqueT.parent`, `LinPathT.append`, `LinPathT.unsnoc`, `TIT.desc_closed`, `TWNT.exclUnique`, `cellAt_imm_icp`, `cellAt_onBranch`, `cellAt_split`, `chain_view_le`, `desc_comparable`, `escBeneathT`, `fdEscOfBranch`, `fdEsc_at_join`, `fdEsc_of_points`, `innermost_view`, `xpath_del`, `xpath_le`, `xpath_linPath`.

`TreeWp/ExtFT.lean` (29): `FrzT`, `FrzT.imm`, `FrzT.inImm`, `FrzT.inMut`, `FrzT.of_compS_left`, `FrzT.rr_back`, `FrzT.rr_fwd`, `FrzT.split`, `InDomT`, `InDomT.rr_back`, `InDomT.rr_fwd`, `InDomT.top`, `InDomT.wit`, `RelAtT`, `RelAtT.rr_iff`, `RelFT`, `RelFT.of_compS_left`, `RelFT.of_compS_right`, `RelFT.rr_iff`, `SRecsRR.mem_back`, `SRecsRR.mem_fwd`, `extFT`, `extFT.rr`, `extFT.trans`, `extFT_comp`, `extFT_left`, `extFT_of_sub`, `extFT_refl`, `extFT_right`.

`TreeWp/FdEscBranch.lean` (33): `CellAboveT.compR`, `CellAboveT.compS`, `CellAboveT.wit`, `CellAt.mutAt`, `CellAt.ownAt`, `CellUT.CompR.back_kind`, `EscBeneathT`, `GPosT.box`, `GPosT.mono`, `GPosT.sumL`, `GPosT.sumR`, `NoneAt.compS`, `OnBranchResT.bigComp`, `OnBranchResT.comp`, `OnBranchResT.restrict`, `agWT_onBranch`, `agW_nonimm_beneath`, `back_kind`, `beneath_of_compS_right`, `bigCompS_back_some`, `bigComp_back_kind`, `cellAt_beneath_imm_ag`, `exRT_cellAt_kind`, `exST_lineage`, `exWT_onBranch`, `fdEsc_iff_noneAt`, `fd_esc_of_branch`, `fd_le_of_branch`, `flat_onBranch`, `hCR_kind`, `le_view_cellAt`, `mut_gposT`, `noneAt_empty`.

`TreeWp/FdEscCactus.lean` (1 + 20 companion): `FdEscOfBranchT`. Companions: `KC`, `ag_config`, `bsC`, `cactusT_config`, `cactusT_not_fdEsc`, `childRes`, `config_not_joinPt`, `cov_imm_of_wit`, `frameLife_config`, `linLoc_config`, `lsC`, `mC`, `nsC`, `parentRes`, `wC`, `αC`, `βC`, `βC_lt_αC`, `ℓC`, `ℓC_ne_mC`.

`TreeWp/FlatLs.lean` (22): `AgW.lsSim`, `CellUT.CompR.lsOf_eq`, `CellUT.CompS.lsOf_eq`, `ExW.lsSim`, `LsRSim`, `LsSim`, `RC.lsSim`, `RR.lsRSim`, `ResUT.Flat.rrLs`, `lsRSim_bigComp`, `lsRSim_comp`, `lsRSim_empty`, `lsRSim_restrict`, `lsRSim_sites`, `lsSim_compR`, `lsSim_compS`, `lsSim_compatR`, `lsSim_compatS`, `lsc`, `minS_reread`, `rlsOf`, `rlsOf_lsc`.

`TreeWp/ImagesT.lean` (32 + 1 companion): `CellUT.CompR.back_view`, `Val.inj₁_inj'`, `Val.inj₁_ne_inj₂`, `Val.inj₂_inj'`, `agW_of_valid`, `agW_source`, `back_some`, `back_view`, `bigComp_back`, `compS_get_left'`, `compS_get_right'`, `comp_get_l`, `comp_some`, `comp_some_r`, `escrow_walks`, `ex_ag_disjoint`, `frame_imm`, `frame_support`, `frame_transfer`, `frame_walks`, `hRR`, `imm_back`, `imm_fwd_l`, `imm_fwd_r`, `lift_escrow`, `lift_part`, `lift_view`, `lift_view_r`, `reb_cell`, `reb_support`, `reb_transfer_gen`, `single_ne`. Companions: `flat_empty`.

`TreeWp/ImmEndEsc.lean` (7 + 27 companion): `FdEsc`, `exST_all_imm`, `hash_of_walks`, `immEnd_hash_of_fdEsc`, `immEnd_valid_of_fdEsc`, `none_of_comp_none_left`, `none_of_comp_none_right`. Companions: `JoinReadyEscT`, `ag_lend`, `ag_view`, `canonT_view`, `config_not_fdEsc`, `emptyT_inStratum`, `escR`, `escR_del`, `escR_typed`, `flat_view`, `immEnd_esc_config`, `lendCell`, `own_inStratum`, `recE`, `recE_no_desc`, `single_compS`, `single_disjoint`, `twnt_config`, `valid_W4`, `valid_single_imm`, `valid_two_own`, `valid_view`, `viewCell`, `viewRes`, `view_cov`, `view_reb`, `view_typed`.

`TreeWp/InvBase.lean` (39): `AllICp`, `CellUT.CompR.lsOf_inv`, `CellUT.kind_of_lsOf`, `ICp`, `ICp.ls`, `ICpAt`, `ResUT.CompR.lsOf_inv`, `agW_mut`, `bigComp_mut_src`, `compR_mut_src`, `comp_mut_src`, `escrow_icp`, `exW_mut`, `frame_fwd_imm`, `icpAt_agW`, `icpAt_bigComp`, `icpAt_comp`, `icpAt_left`, `icpAt_none`, `icpAt_of_immFree`, `icpAt_right`, `icpAt_trans`, `icp_trans`, `img_cell`, `img_ls`, `img_walk`, `imm_back_full`, `imm_fwd_full_l`, `imm_fwd_full_r`, `leInv_of_reb`, `lsOf_eta`, `lsOf_of_imm`, `mutAt_image`, `mutAt_of_cell`, `mutAt_walk_dom`, `nestLife_of_icp`, `nestLife_of_maps`, `not_mutAt_top_own`, `reb_cell_ls`.

`TreeWp/InvMid.lean` (37): `CellUT.CompR.lift_full`, `DescRT.cases`, `DescRT.refl`, `DescRT.sub`, `ExIn`, `LeInvW`, `Lifts`, `Lifts.trans`, `LinPathT.inv_cons`, `LinPathT.inv_nil`, `LinPathT.last`, `LinPathT.snoc`, `LinPathT.xpath`, `NVAt`, `TI.exIn`, `TI.leInvW`, `XPath`, `XPath.cons`, `XPath.nil`, `ag_none_of_top`, `bigComp_get_of_ne_imm`, `bigComp_two`, `exIn_mut`, `exIn_of_imm`, `exIn_path`, `exIn_support`, `exR_cell`, `exR_mut_wit`, `frame_ex`, `frame_new_root'`, `lifts_left`, `lifts_right`, `lineage_of_leInv`, `not_mutAt_ex_own`, `not_mutAt_ex_own_aux`, `xpath_ex`, `xpath_unique`.

`TreeWp/InvReb.lean` (9): `chainInv_reb`, `chainInv_rebDeep`, `chain_unique_recT`, `chain_val`, `deepInv_back`, `own_del`, `reb_like_back`, `reb_like_fwd`, `reb_like_new`.

`TreeWp/InvSimple.lean` (16): `MutAtT.mono`, `MutAtT.of_compS_left`, `MutAtT.of_compS_right`, `MutAtT.of_del`, `MutAtT.of_le`, `MutAtT.split`, `TIT.of_ag`, `chainInvT_of_ag_sub`, `mut_fold_ag`, `nestLifeT_of_ag`, `not_mutAt_single_own`, `own_cell_ag`, `tit_free`, `tit_mutFold`, `tit_mutUnfold`, `tit_store`.

`TreeWp/InvUses.lean` (6): `NoOwnUnderT`, `TWNT.noOwnUnder`, `TWNT.tcCarried_exists`, `TWNT.tcCoherent`, `TWNT.used_cellAt`, `leInv_view`.

`TreeWp/NoOwnUnder.lean` (23): `OwnAt`, `OwnAt.mono`, `OwnAt.nest`, `OwnAt.of_compS_left`, `OwnAt.of_del`, `OwnAt.of_le`, `OwnAt.rr_back`, `OwnAt.top`, `OwnUnder`, `OwnUnder.of_cell`, `OwnUnder.of_compS_left`, `OwnUnder.of_compS_right`, `OwnUnder.rr_back`, `OwnUnder.split`, `compS_back`, `hSS`, `not_ownUnder_single_own`, `not_ownUnder_top_own`, `ownAt_image`, `ownAt_walk_dom`, `own_not_at_view`, `step_frame`, `top_of_frame`.

`TreeWp/Ops.lean` (0 + 1 companion): . Companions: `tyPred`.

`TreeWp/RebRR.lean` (17): `Cov.wit`, `RR.bigComp`, `RR.del`, `RR.dom`, `RR.le`, `bigCompS_le`, `cov_of_imm_wit`, `exists_forall₂_rr`, `forall₂_mem_left'`, `le_agree`, `le_cov`, `le_holdsMut`, `reb_cell_src`, `reb_cov_agree`, `reb_rr`, `reb_rr_exists`, `rr_imm_at`.

`TreeWp/Records.lean` (63 + 4 companion): `ChainT`, `ChainT.one`, `ChainT.step`, `DescRT`, `DescT`, `FrameLifeT`, `FrameRecT`, `FrameRecT.R`, `FrameRecT.T`, `FrameRecT.le`, `FrameRecT.v`, `GPosT`, `GPosT.here`, `GPosT.step`, `KTy.immReborrow`, `LinLocT`, `LinPathT`, `LinPathT.cons`, `LinPathT.cov`, `LinPathT.nil`, `MutPosT`, `MutPosT.box`, `MutPosT.mut`, `MutPosT.sumL`, `MutPosT.sumR`, `RebCellLeT`, `RebEndRecT`, `RebRecLeT`, `RecRR`, `RecRR.refl`, `RefPosT`, `RefPosT.box`, `RefPosT.ref`, `RefPosT.sumL`, `RefPosT.sumR`, `SubRecT`, `TChoice`, `TWNT`, `TWNT.alloc`, `TWNT.cov_recs`, `TWNT.empty`, `TWNT.free`, `TWNT.immEnd`, `TWNT.immFrame`, `TWNT.mutFold`, `TWNT.mutUnfold`, `TWNT.reb`, `TWNT.rebDeep`, `TWNT.rebEnd`, `TWNT.rebEndDeep`, `TWNT.reread`, `TWNT.store`, `TWNT.valid`, `TcCarried`, `TmplSpecT`, `UsedT`, `canonDTc`, `canonTc`, `forall₂_mem_right`, `interp_cov`, `relCellT`, `relResT`, `tmplT`. Companions: `canonT`, `relResT_get`, `tmplR`, `tmplT_spec`.

`TreeWp/Rel.lean` (51): `EndT`, `EndT.mono`, `MutCov.of_part`, `RecInv`, `RecInv.cov_ls`, `RecInv.cov_ps`, `RecRR.trans`, `RecsRR`, `RecsRR.refl`, `RecsRR.trans`, `SRecT`, `SRecsRR`, `SRecsRR.refl`, `SRecsRR.trans`, `SplitT`, `SplitT.left`, `SplitT.right`, `TFrame`, `TFrame.Mono`, `TPost`, `TPost.Down`, `TPost.Down.le`, `TPost.sep`, `TRProp`, `TRProp.Mono`, `TaggedT`, `cov_of_comp`, `cov_valid`, `covf_of_comp`, `covf_valid`, `endT_inv`, `forall₂_append_left`, `forall₂_trans`, `hash_of_inv`, `reassoc_in`, `reassoc_out`, `rsOfT`, `twp`, `twp_bind`, `twp_det`, `twp_extend`, `twp_frame`, `twp_frameCond`, `twp_here`, `twp_kripke`, `twp_le`, `twp_mono`, `twp_mono_le`, `twp_step`, `twp_update`, `twp_zero`.

`TreeWp/ShapeMutT.lean` (14): `FrameRecT.ext'`, `GPosT.of_chain`, `LinPathT.functional`, `LinPathT.typed`, `MutPosT.not_refPos`, `MutPosT.unique`, `SubRecT.functional`, `SubRecT.typed`, `gpos_mut_cellT`, `gpos_uniqueT`, `image_at_posT`, `image_dom_mutT`, `mut_split_denT`, `typed_image_posT`.

`TreeWp/ShapeT.lean` (11): `ChainT.own`, `ChainT.snoc`, `RefPosT.unique`, `chain_lastT`, `chain_ownT`, `chain_uniqueT`, `compS_single_ins`, `image_domT`, `le_of_compS_right`, `own_of_le`, `own_splitT`.

`TreeWp/SimL.lean` (17): `LRSim`, `LSim`, `agW_simL`, `compR_lsOfI_eq`, `compS_lsOfI_eq`, `exW_simL`, `lrsim_of_RR`, `lsMerge`, `lsim_compR`, `lsim_compatR`, `rc_lsOfI`, `rc_lsim`, `wrsim_bigCompL`, `wrsim_compL`, `wrsim_emptyL`, `wrsim_restrictL`, `wrsim_sitesL`.

`TreeWp/StepCopy.lean` (2 + 18 companion): `StepKeepsFdEsc`, `stepKeepsFdEsc`. Companions: `Qpt`, `StepKeepsFdEscNoUpd`, `cellCompS_self_of_imm`, `compS_absorb`, `compS_self_of_imm`, `copy_config`, `copy_end_refused`, `copy_inside`, `copy_not_updX`, `copy_run_keeps_fdEsc`, `finDom_of_pmap`, `flat_parentRes_at`, `flat_parentRes_imm`, `not_stepKeepsFdEscNoUpd`, `onBranch_single`, `parentRes_imm`, `top_not_le_αC`, `twp_unit_empty`.

`TreeWp/StepKeep.lean` (10): `ExDom.exST`, `ExDom.linLoc`, `LinLocT.exDom`, `LinPathT.exDom`, `TWNT.esc_valid`, `fdEsc_of_updX`, `le_not_linLoc`, `linLoc_apart`, `not_desc_proper`, `recMask_apart`.

`TreeWp/TInv.lean` (15): `ChainInvT`, `ClassT`, `CoverageT`, `DeepInvT`, `JointAtT`, `JointDeepT`, `LeInvT`, `MutAtT`, `MutAtT.nest`, `MutAtT.top`, `NestLifeT`, `NoMutT`, `RootT`, `TIT`, `TWNT.InvHolds`.

`TreeWp/TInvBase.lean` (5): `TIT.congr`, `agWT_alloc_iff`, `mutAtT_alloc_iff`, `tit_alloc`, `tit_empty`.

`TreeWp/TInvEnd.lean` (7): `end_back`, `end_fwd_imm`, `end_walks`, `le_of_compS_left`, `tit_end`, `tit_endReb`, `xpath_ex_part`.

`TreeWp/TInvFrame.lean` (2): `frame_fwd`, `tit_frame`.

`TreeWp/TInvHolds.lean` (2): `TWNT.inv`, `twnt_invHolds`.

`TreeWp/TInvReb.lean` (8): `ClassT.congr`, `cov_reb_like`, `coverage_of_icp`, `exIn_of`, `leInvW_of`, `nm_reb_like`, `tit_reb`, `tit_rebDeep`.

`TreeWp/TInvReread.lean` (24): `CellAt.holdsMut`, `ChainT.rr_fwd`, `GPosT.rr_back`, `GPosT.rr_fwd`, `LRSim.back`, `LRSim.fwd`, `LinPathT.rr_back`, `LinPathT.rr_fwd`, `MutAtT.rr_back`, `RR.own_fwd`, `RecRR.func`, `TIT.agree_recs`, `TIT.recs_cellAt`, `chain_parent`, `chain_recRR_back`, `chain_recRR_fwd`, `forall₂_mem_left`, `holdsMut_of_cellAt`, `part_rr`, `tit_reread`, `walk_agree`, `walk_back`, `walk_fwd`, `walk_holdsMut`.

`TreeWp/Templ.lean` (13): `ChainT.rr_back`, `RC.own_inv`, `RR.own_back`, `RootT.rr_back`, `TWNT.templ_reread`, `TcCoherent`, `TemplAtT`, `TemplDAtT`, `agW_rr_back`, `tcCarried_exists`, `tcCoherent_of_inj`, `templAt_reread`, `templDAt_reread`.

`TreeWp/UpdX.lean` (37): `CellUT.CompR.eq_right_of_own`, `ExDom`, `ExDom.deep`, `ExDom.rr`, `ExDom.rr_back`, `ExDom.rr_iff`, `ExDom.top`, `LsSim.xcell`, `MaskDiff`, `NoneAt`, `NoneAt.mono`, `NoneAt.of_compS_left`, `NoneAt.of_compS_right`, `NoneAt.of_false`, `NoneAt.or`, `NoneAt.rr`, `UpdX`, `UpdX.congr`, `UpdX.of_rr`, `UpdX.of_updV`, `UpdX.trans`, `UpdX.widen`, `XCell`, `XCell.trans`, `XOpt`, `XOpt.trans`, `escLocs`, `flat_lsSim_self`, `imm_eq_of`, `maskDiff_trans`, `recMask`, `recMask_append`, `recMask_rr`, `updX_refl_imm` (`UpdX.frame`, `xcell_compR`, `xopt_comp` retired by #806).

`TreeWp/UpdXInv.lean` (29): `AgW.mutIn`, `CellAt.cov`, `ExW.mutIn`, `InvKept`, `InvKept.frame`, `InvKept.mono`, `InvKept.of_agree`, `InvKept.refl`, `InvKept.trans`, `MutCov`, `MutIn`, `MutIn.bigComp`, `MutIn.comp`, `MutIn.mono`, `MutIn.restrict`, `MutKeep`, `MutUniq`, `MutUniq.of_sub`, `TCell.eq_mut`, `UpdX.inv`, `XCell.mut_right`, `XInv`, `compR_mut_side`, `flat_mut_cellAt`, `flat_mut_inv`, `mutKeep_compR`, `mutKeep_compS`, `sem_some`, `updX_refl_mut`.

`TreeWp/UpdXMasks.lean` (0 + 4 companion): . Companions: `cellAt_config`, `flat_config`, `lend_open_admitted`, `lend_open_needs_mask`.

`TreeWp/World.lean` (30): `Cov.immOf_iff`, `CovR.of_compS_left`, `CovR.of_compS_right`, `ImmT.res_toRes`, `ORel`, `ORel.optComp`, `RC.compS`, `RC.immOf_inv`, `RC.immOf_of`, `RR.compS`, `RR.orel`, `RR.split_retype`, `RRw`, `RRw.trans`, `ResUT.Flat.rr`, `ResUT.Hash.of_compS`, `ResUT.Lower.rr`, `TWd`, `TWd.Ext`, `TWd.Ext.of_compS_left`, `TWd.Ext.of_compS_right`, `TWd.Ext.refl`, `TWd.Ext.trans`, `TWd.K`, `TWd.P`, `TWd.tc`, `TWd.Θ`, `WInv`, `WInv.reread`, `WInv.valid`.

