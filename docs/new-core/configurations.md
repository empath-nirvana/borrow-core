# Configurations under `Core/Chain/`

Every Lean configuration or obstruction under `Core/Chain/`, with its headline and the current
design choice it justifies. "Historical" marks a file that justifies nothing current: a candidate
for deletion at the merge. The design the choices belong to is `chain-interpretation.md`; its
departures are cited as D1–D12 (§5 there).

A headline's remaining hypotheses are the configuration's own parameters (distinct locations,
ordered lifetimes, the clause under test). A configuration refutes a step, not a constant: none of
them refutes a run of `ConstN`.

## The chain interpretation's configurations

| File | Headline | What it shows | Justifies |
|---|---|---|---|
| `Shape791N.lean` | `perLocShape_not_reborrow` | With `Mut` read per location (`Φ ℓ = (α, 𝒱⟦A⟧ above α)`, `mutC`), a value at `ℓ_b ≠ ℓ` whose cell is at `b` and holds a `Mut @β 1`, `α < b < β`, is a value at `Φ` and not at `Φ.set ℓ α F` for any `F`: a reborrow's overwrite of `ℓ` changes the family `ℓ_b` stores | D1: the world is keyed by lend, `(ℓ, b)`, not by location |
| `PerLendShape791.lean` | `perLocShape_lend_reborrow` | The same value is a `mutL` value at the per-lend world before and after the reborrow (`Wc`, `Wc.add ℓ α F`; `Wc_fresh`) | D1: the per-lend world answers `perLocShape_not_reborrow` |
| `Shape791N.lean` | `reseal_untyped` (with `stuckV_one`, `stuckV_not_two`, `unitV_all`) | At a location `Φ` does not type, no `MutStep` takes a `Mut @a (U(F 1))` cell at index `2` to one whose predicate admits content valid only at index `1` | D1: `Mut` reads the world's key (`Θ ℓ b = some (famL …)`), and a run is at a view that types the held cell (`reseal_at_entry`) |
| `ConsistentFlat791.lean` | `flat_part_config` | Consistency over the whole flattening is not kept by the part a run returns: `ρ′ = m ↦ imm(t, (), ℓ ↦ mut(a, …))` beside `ρp = ℓ ↦ imm(s, (), ∅)` hides the `mut` cell in `⦇ρ′ ● ρp⦈` and shows it in `⦇ρ′⦈`; the zero-step run returning `ρ′` is an `erwp` run. Not built: a `TWNC` frame at which `ρ` is a run's start | D7: `ConsistentX` reads the exclusive walk |
| `ExtRLit791.lean` | `extRL_breaks_extA` (with `valid_at_empty`, `not_valid_at_lend`, `vN_eq_vUgen`) | Core's `Ext` read literally on the world (`ExtRL`: nothing added above every `b` with `CellIn ρ b`) makes `𝒱⟦U(Mut 'x 1 ⊸ F 1)⟧` valid at the empty world and not at a fresh lend's, at the thunk `()` | D4: `ExtR` asks agreement only above keys present. The application `() ℓ′` is stuck, refuted from the typed world of the two `mut` cells (`world_two`) |
| `ImmShape791N.lean` | `coreMutImm_not_extF` (instance `coreMutImm_not_extF_inst`) | A value of Core's `Mut 'x (Imm 'y 1)` (`vCE`, Core's definition) at `ls` is not one at an `ls′` with `extF ls ls′ ρ` adding a record above the cell; `Ext ls ls′` fails there | D2: `vN` reads no record list; D3: the records live in the world |
| `ImmRec791N.lean` | `not_wlImage`, `not_wlImage_vN` | No `Imm` clause over `vN`'s arguments `(A, δ, Θ, n, v, ρ)` alone gives `withload`'s step 8: the cell `ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))` is the cell of a lend recorded at `Ref 1` (`world_ref`) and of one recorded at `U (F 1)` (`world_thunk`), where the canonical image is `∅` (`canon_thunk`) | D3: `Imm`'s witness `ImmWitW` reads the world's `imm` records |
| `ImmRec791N.lean` | `immAgreeErwp_both`, `not_wlImageA`, `not_wlImageA_vN` | Every agreement read off the unchanged `erwp`'s first entry (`ImmAgreeErwp`) holds at both records of that cell at one world; with it among step 8's premises, step 8 still fails, at `vN`'s clause strengthened by any condition on the world at the cell | D3: the tie is built into the relation's entry, not read off `erwp` |
| `ImmTie791N.lean` | `not_effOf_guarded`, `immTie_guard_fails` | A guard on `cN`'s run clauses that fails at `world_ref`'s list and cell breaks `cN_effOf` (the run `()` at the post `False`, `not_erwp_false`); the tie is such a guard | D3: the tie sits at `rwp`/`rwpG`/`rwpG0`'s entry (`ImmTieL`), not on `cN` |
| `ImmTie791N.lean` | `immTieL_world_ref` | At `ΘRef`, the entry tie holds at `world_ref`'s list and fails at `world_thunk`'s | D3: the entry tie excludes `immAgreeErwp_both`'s second world |
| `Lend791N.lean` | `answer_not_inStratum` | `U(F 1)` has values outside every stratum `↓α` (`λ_. ()` holding a short `mut` cell as garbage) | `Row.Suspend`'s answer clause (`VOutlives ∅ @bnd`): the Mut Frame's `pb` premise. A configuration for the premise, not a refutation of the constant |

## Relation-level configurations (from the chain relation's construction)

These predate #791's interpretation and justify choices in the relation the interpretation reads.

| File | Headline | What it shows | Justifies |
|---|---|---|---|
| `SI/UpdN.lean` | `not_mutMutMemberStep` | `UpdMutSI` does not carry [TR] 6.48's `mut ○ mut` step at a step index: `P̂ ∧ F k` can be a member while `P̂ ∧ F k′` is none | `UpdMutN`'s clause through `PredStep` |
| `SI/ExtF.lean` | `not_extFoldTransfer` | `Ext` at the lender's share (the lent cell folded to `own`) does not give `Ext` at the borrowed continuation's share | D8: resumes under `extF`. The file's header names this result `not_ext_fold` |
| `SI/HandlerLendProg.lean` | `resume_not_ext` | A handler's lend at `xTop` puts the resume list outside `Ext` at a share holding the lent cell at `A₀` | D8 |
| `Kappa835N.lean` | `not_kapRelKTyN` (with `not_kTy_world`, `kapRelN_world`, `not_kTy_view`, `kapRelN_view`, `not_kTy_at`) | Core's `vC_kTy_of_kapRel` at the chain (`KapRelKTyN`: `KapRelN` at the stop's world, view and tables gives `vN (kTy Σ R q B F)`) is false. At the stuck `κ = ()`, answer type `Mut 'x 1`: at the empty world no answer exists, so `KapRelN` holds, and `U` reaches the world with a key, at the stop's own view and list, where `κ` is stuck (the world); at the world with the key and a view with no lifetime at the key's location, the answer is not consistent with the run's view, so `KapRelN` holds, and `U` reads `κ` at the same world and list at a view that puts the location at the key (the view). Both stuck runs are refuted from `world_two` | E10 (`scope-831-interface.md` §10.1): open; a question for the design, not a departure taken |
| `Kappa835N.lean` | `not_extRFoldTransfer` | `ExtR` at the lender's share (the lent cell folded to `own`) from `Θ` to `Θ′` does not give `ExtR` at the borrowed continuation's share (the cell `mut` at `A`) from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`: a key added above `A` | E10, route 2 (a stop's share Kripke along `ExtR`): the Mut Frame's fold does not carry it at the lend's world `Θ′ + (ℓ, A)`; D8 at the world |
| `Public835N.lean` | `extPFoldTransfer`, `not_extP_foldConfig` (with `LocTy.ExtP.fold`) | `ExtP` at the lend's floor `A` at the lender's share gives `ExtR` at the borrowed continuation's share from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`; `not_extRFoldTransfer`'s key added above `A` is not a public move at that floor | E10 (`scope-835-public.md` §5.2): the public order is carried across the Mut Frame's fold |
| `Public835N.lean` | `kapRelN_not_kapRelP` (with `not_kapRelP_world`, `not_kapRelP_view`, `extP_world`, `not_extP_world`) | The stuck `κ = ()` meets `KapRelN` at the empty world and fails the stop's obligation read along `ExtP` at every floor above the key; at the one-key world it fails it at the view putting `ℓ′` at `α` | E10 (`scope-835-public.md` §5.1, §8): the two `not_kapRelKTyN` configurations are not instances of the public reading; the relation's stop must owe the continuation at other location typings |
| `SI/RebResumeN.lean` | `resume_frame_short`, `resume_frame_not_stratumLe`, `resume_frame_not_inStratum` | A condition on the resume list reads nothing of the frame: a handler's own `mut` lend makes both of `TW`'s reborrow stratum premises fail | `TWN` reads its reborrow premises at records (`RebRecLe`, `RebEndRec`) |
| `SI/RebAgreeCex.lean` | `not_rebReentryAgreeN` | Re-entering a folded reborrow at the image chosen at its first entry fails at a resume world `TWN` reaches | `TWNC`'s canonical images: `erwp_reborrow` re-enters at `canon r β` (`canon_escrowAgree`) |
| `SI/FdTypes.lean` | `not_fdFromLifetimeTypes` | Lifetimes on continuation types do not supply the join's frame condition at `Imm 'r 1` in a single chain | the tree track's branch hypotheses (structure.md §6); nothing in the chain interpretation reads it |

## Historical

| File | Headline | Why it justifies nothing current |
|---|---|---|
| `Map831N.lean` | `extR_addImm_inst`, `imm_at_extension`, `imm_world_ne_nil` | It answers `callback_any_inst`, a configuration against the old `LocTy.above` (which kept every `imm` record), removed in 6ede48eb. At the current `above` and `Keeps` it checks that one instance is an extension holding an `Imm` value; `LocTy.extR_addImm` proves the extension at every resource in the lend's stratum. `ImmLend833N.lean` imports it for module order and uses none of its declarations |
| `ImmTie791N.lean` (part) | `ImmWit`, `ImmTie`, `immTie_agree`, `immWit_ref`, `immTie_excludes_thunk`, `immTie_ref`, `immTie_wit_excludes_thunk`, `ImmTieL.tie` | The tie over an abstract record list, before it was placed. The relation carries `ImmTieL`; the interpretation's witness is `ImmWitW`, and `withloadS_compat` reads `cohE_of_immWitW`, not `immTie_agree`; no file outside `ImmTie791N.lean` uses these. The rows above (`not_effOf_guarded`, `immTie_guard_fails`, `immTieL_world_ref`) are current; `Withload791N.lean` imports the file |

Removed earlier, kept in git: `LocalU791.lean` (`u_not_local`: `U` is not local along a lend
under `ExtA`; at 728b51d7, removed in 55b83e3f) and `LocTypeSketch.lean` (the first per-lend
sketch, from 7ac003bb; its results were moved into `SI/LocTy.lean`).

Not configurations, noted here because they are definitions nothing reads: `vThunk` and
`Covers` (`SI/MutSemN.lean`; `chain-interpretation.md` Appendix A.4).

- `Depart831N.lean`: `not_unwindArgStepLoc` / `unwindArg_inst` justify D5 (`Keeps` by lifetime) at `tabN_unwind_eq`, a step Core's proofs do not take (refactor candidate); `erwp_of_noFinal` / `cN_effOf_divB` justify reading `Div` rows at `erwp` (no coinductive `cwp`).
