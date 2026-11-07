# Configurations under `Core/Chain/`

Every Lean configuration or obstruction under `Core/Chain/`, with its headline and the current
design choice it justifies. "Historical" marks a file that justifies nothing current: a candidate
for deletion at the merge. The design the choices belong to is `chain-interpretation.md`; its
departures are cited as D1–D12 (§5 there).

The configurations that read `𝒱⟦·⟧` or `𝒞⟦·⟧` are stated at the relation at `KW` (`vN`, `cN`,
`Core/Chain/Goal791N.lean`) and live in `Core/Chain/ConfigsKW835N.lean`, each in its original
file's namespace.

A headline's remaining hypotheses are the configuration's own parameters (distinct locations,
ordered lifetimes, the clause under test). A configuration refutes a step, not a constant: none of
them refutes a run of `ConstN`.

## The chain interpretation's configurations

| File | Headline | What it shows | Justifies |
|---|---|---|---|
| `Shape791N.lean` | `perLocShape_not_reborrow` | With `Mut` read per location (`Φ ℓ = (α, 𝒱⟦A⟧ above α)`, `mutC`), a value at `ℓ_b ≠ ℓ` whose cell is at `b` and holds a `Mut @β 1`, `α < b < β`, is a value at `Φ` and not at `Φ.set ℓ α F` for any `F`: a reborrow's overwrite of `ℓ` changes the family `ℓ_b` stores | D1: the world is keyed by lend, `(ℓ, b)`, not by location |
| `PerLendShape791.lean` | `perLocShape_lend_reborrow` | The same value is a `mutL` value at the per-lend world before and after the reborrow (`Wc`, `Wc.add ℓ α F`; `Wc_fresh`) | D1: the per-lend world answers `perLocShape_not_reborrow` |
| `ConfigsKW835N.lean` (`Shape791N`) | `reseal_untyped` (with `stuckV_one`, `stuckV_not_two`, `unitV_all`) | At a location `Φ` does not type, no `MutStep` takes a `Mut @a (U(F 1))` cell at index `2` to one whose predicate admits content valid only at index `1` | D1: `Mut` reads the world's key (`Θ ℓ b = some (famL …)`), and a run is at a view that types the held cell (`reseal_at_entry`) |
| `ConsistentFlat791.lean` | `flat_part_config` | Consistency over the whole flattening is not kept by the part a run returns: `ρ′ = m ↦ imm(t, (), ℓ ↦ mut(a, …))` beside `ρp = ℓ ↦ imm(s, (), ∅)` hides the `mut` cell in `⦇ρ′ ● ρp⦈` and shows it in `⦇ρ′⦈`; the zero-step run returning `ρ′` is an `erwp` run. Not built: a `TWNC` frame at which `ρ` is a run's start | D7: `ConsistentX` reads the exclusive walk |
| `ConfigsKW835N.lean` (`ExtRLit791`) | `extRL_breaks_extA` (with `valid_at_empty`, `not_valid_at_lend`, `vN_eq_vUgen`) | Core's `Ext` read literally on the world (`ExtRL`: nothing added above every `b` with `CellIn ρ b`) makes `𝒱⟦U(Mut 'x 1 ⊸ F 1)⟧` valid at the empty world and not at a fresh lend's, at the thunk `()` | D4: `ExtR` asks agreement only above keys present. The application `() ℓ′` is stuck, refuted from the typed world of the two `mut` cells (`world_two`) |
| `ImmShape791N.lean` | `coreMutImm_not_extF` (instance `coreMutImm_not_extF_inst`) | A value of Core's `Mut 'x (Imm 'y 1)` (`vCE`, Core's definition) at `ls` is not one at an `ls′` with `extF ls ls′ ρ` adding a record above the cell; `Ext ls ls′` fails there | D2: `vN` reads no record list; D3: the records live in the world |
| `ImmRec791N.lean`, `ConfigsKW835N.lean` | `not_wlImage`, `not_wlImage_vN` | No `Imm` clause over `vN`'s arguments `(A, δ, Θ, n, v, ρ)` alone gives `withload`'s step 8: the cell `ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))` is the cell of a lend recorded at `Ref 1` (`world_ref`) and of one recorded at `U (F 1)` (`world_thunk`), where the canonical image is `∅` (`canon_thunk`) | D3: `Imm`'s witness `ImmWitW` reads the world's `imm` records |
| `ImmRec791N.lean`, `ConfigsKW835N.lean` | `immAgreeErwp_both`, `not_wlImageA`, `not_wlImageA_vN` | Every agreement read off the unchanged `erwp`'s first entry (`ImmAgreeErwp`) holds at both records of that cell at one world; with it among step 8's premises, step 8 still fails, at `vN`'s clause strengthened by any condition on the world at the cell | D3: the tie is built into the relation's entry, not read off `erwp` |
| `ImmTie791N.lean` | `not_effOf_guarded`, `immTie_guard_fails` | A guard on `cN`'s run clauses that fails at `world_ref`'s list and cell breaks `cN_effOf` (the run `()` at the post `False`, `not_erwp_false`); the tie is such a guard | D3: the tie sits at `rwp`/`rwpG`/`rwpG0`'s entry (`ImmTieL`), not on `cN` |
| `ImmTie791N.lean` | `immTieL_world_ref` | At `ΘRef`, the entry tie holds at `world_ref`'s list and fails at `world_thunk`'s | D3: the entry tie excludes `immAgreeErwp_both`'s second world |
| `ConfigsKW835N.lean` (`Lend791N`) | `answer_not_inStratum` | `U(F 1)` has values outside every stratum `↓α` (`λ_. ()` holding a short `mut` cell as garbage) | `Row.Suspend`'s answer clause (`VOutlives ∅ @bnd`): the Mut Frame's `pb` premise. A configuration for the premise, not a refutation of the constant |

## Relation-level configurations (from the chain relation's construction)

These predate #791's interpretation and justify choices in the relation the interpretation reads.

| File | Headline | What it shows | Justifies |
|---|---|---|---|
| `SI/UpdN.lean` | `not_mutMutMemberStep` | `UpdMutSI` does not carry [TR] 6.48's `mut ○ mut` step at a step index: `P̂ ∧ F k` can be a member while `P̂ ∧ F k′` is none | `UpdMutN`'s clause through `PredStep` |
| `SI/ExtF.lean` | `not_extFoldTransfer` | `Ext` at the lender's share (the lent cell folded to `own`) does not give `Ext` at the borrowed continuation's share | D8: resumes under `extF`. The file's header names this result `not_ext_fold` |
| `SI/HandlerLendProg.lean` | `resume_not_ext` | A handler's lend at `xTop` puts the resume list outside `Ext` at a share holding the lent cell at `A₀` | D8 |
| `ConfigsKW835N.lean` (`Kappa835N`) | `not_kTy_at`, `not_kTy_of_extR` (with `Θ₁`, `Θ₁_ok`) | At the stuck `κ = ()` and answer type `Mut 'x 1`, `𝒞⟦(Mut 'x 1 ⊸ F 1) & ⊤⟧` fails at the world with one key `(ℓ′, α)` at a view putting `ℓ′` at `α`: that world holds the argument `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `() (inj₁ ()) ℓ′` is stuck from the typed world of the two cells (`world_two`). So `U` at `kTy` fails at every world `ExtR` reaches it from | the configurations of `Public835N` and `LendExit835N` below read it |
| `Kappa835N.lean` | `not_extRFoldTransfer` | `ExtR` at the lender's share (the lent cell folded to `own`) from `Θ` to `Θ′` does not give `ExtR` at the borrowed continuation's share (the cell `mut` at `A`) from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`: a key added above `A` | E10, route 2 (a stop's share Kripke along `ExtR`): the Mut Frame's fold does not carry it at the lend's world `Θ′ + (ℓ, A)`; D8 at the world |
| `Public835N.lean` | `extPFoldTransfer`, `not_extP_foldConfig` (with `LocTy.ExtP.fold`) | `ExtP` at the lend's floor `A` at the lender's share gives `ExtR` at the borrowed continuation's share from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`; `not_extRFoldTransfer`'s key added above `A` is not a public move at that floor | E10 (`scope-835-public.md` §5.2): the public order is carried across the Mut Frame's fold |
| `ConfigsKW835N.lean` (`Public835N`) | `not_kapRelP_world`, `not_kapRelP_view` (with `extP_world`, `not_extP_world`, `KapRelP`) | The stuck `κ = ()` fails the stop's obligation read along `ExtP` at every floor above the key, at the empty world; at the one-key world it fails it at the view putting `ℓ′` at `α` | E10 (`scope-835-public.md` §5.1, §8): the public reading does not admit `κ = ()` |
| `ConfigsKW835N.lean` (`LendExit835N`) | `flooredExit`, `flooredExit_inst` (with `kapRelP_floor_world`, `not_bMut_extP`, `not_kapRelR_world`, `vN_thunk_iff_kapRelR`, `KapRelR`) | At the empty world and a key's lifetime `β` with `α < β ≤ lo`, the stuck `κ = ()` meets the obligation along `ExtP α` and fails `U` read along `ExtP lo`; it also fails `KapRelR`, which is `vN`'s `U` clause (`vN_thunk_iff_kapRelR`) | `scope-835-lendexit.md`: `U` reads no floor; `assert-boundary.md` §3.1 (E): a relation-level lemma over `κ` is refuted, so the assertion is over typed terms |
| `LendExit835N.lean` | `owedR_not_owed`, `not_owed_post_lower`, `not_tabLe_post_lower` | `KW.Owed` at a lend's floor owes fewer worlds than `KW.OwedR`; `KW.Owed`'s floor bound is not carried along a post that lowers the floor, and a table of such entries is not `TableK.Le` along it | the relation at `KW`: every entry owes along `KW.Owed`, posts keep the floor (`KW.PostK`) |
| `ConfigsKW835N.lean` (`Public835N`) | `extP_not_foldInv` | `ExtP` at a lend's floor `A` does not keep `LocTy.FoldInv A` (a key at `A` is a public move there) | the Kripke stop's world order (`scope-835-kripke-stop.md`) |
| `SI/RebResumeN.lean` | `resume_frame_short`, `resume_frame_not_stratumLe`, `resume_frame_not_inStratum` | A condition on the resume list reads nothing of the frame: a handler's own `mut` lend makes both of `TW`'s reborrow stratum premises fail | `TWN` reads its reborrow premises at records (`RebRecLe`, `RebEndRec`) |
| `SI/RebAgreeCex.lean` | `not_rebReentryAgreeN` | Re-entering a folded reborrow at the image chosen at its first entry fails at a resume world `TWN` reaches | `TWNC`'s canonical images: `erwp_reborrow` re-enters at `canon r β` (`canon_escrowAgree`) |
| `SI/FdTypes.lean` | `not_fdFromLifetimeTypes` | Lifetimes on continuation types do not supply the join's frame condition at `Imm 'r 1` in a single chain | the tree track's branch hypotheses (structure.md §6); nothing in the chain interpretation reads it |

## Against `HandlerLawN`

`HandlerLawN` (`Core/Chain/HandlerLawN.lean`) asserts `HandleVN`, `HandleVBN` and `ReifyN` at
`SemJN`, the relation at `KW`: each field quantifies over handlers, clauses and handled
computations in `SemJN` (typed terms), never pointwise over a `κ`, a world or a share. Every
configuration in the tree was checked against the three fields; none is an instance of a field's
premises with its conclusion failing.

| Configuration | Why it is not a counterexample to a field |
|---|---|
| `not_kTy_at`, `not_kTy_of_extR` | `𝒞⟦kTy⟧` at the thunk `κ = ()` at one world. No `[op]` step hands a clause `()` (`kappa_ne_unit`, `kappaC_ne_unit`); the failure is `() (inj₁ ())` being final (`unit_resume_final`), and the resumption of every `κ` the step hands takes a step (`kappa_resume_not_final`, `kappaC_resume_not_final`) |
| `not_kapRelP_world`, `not_kapRelP_view`, `flooredExit`, `flooredExit_inst`, `not_kapRelR_world`, `kapRelP_floor_world` | The same `κ = ()`, read along `ExtP` or `ExtR`. They refute a relation-level lemma over `κ` (`assert-boundary.md` §3.1 (E)), which `HandlerLawN` is not |
| `owedR_not_owed`, `not_owed_post_lower`, `not_tabLe_post_lower`, `extP_not_foldInv`, `not_extP_foldConfig`, `not_extRFoldTransfer`, `not_extFoldTransfer` | Orders and folds on worlds, shares or record lists; no program, no `κ`, no handler |
| `extRL_breaks_extA`, `valid_at_empty`, `not_valid_at_lend` | `ExtRL`, which the relation does not read (D4); at `ExtR` the clause is `vN` (`vN_eq_vUgen`). Its thunk is `()` |
| `reseal_untyped`, `stuckV_not_two`, `perLocShape_not_reborrow`, `flat_part_config` | A `Mut` cell's predicate under a per-location reading, and the flattening's consistency; no handler |
| `answer_not_inStratum` | A value of `U(F 1)` outside a stratum: the configuration for `Row.Suspend`'s answer premise, a typing premise of the lends |
| `not_wlImage`, `not_wlImage_vN`, `not_wlImageA`, `not_wlImageA_vN`, `immAgreeErwp_both`, `not_effOf_guarded`, `immTie_guard_fails`, `immTieL_world_ref`, `coreMutImm_not_extF` | The `Imm` clause's witness and the entry tie; no handler |
| `not_unwindArgStepLoc` | `Keeps` by location at an unwinding row's step; no handler |
| `resume_not_ext`, `resume_frame_short`, `resume_frame_not_stratumLe`, `resume_frame_not_inStratum` | Candidate readings of the resume list or of `Ext` at a handler's lend, justifying `extF` and `TWN`'s record premises; none states a handler's compatibility lemma |
| `not_mutMutMemberStep`, `not_rebReentryAgreeN`, `not_fdFromLifetimeTypes` | `↭`'s step at an index, a reborrow's re-entry image, the join's frame condition; no handler |

The fields hold at instances whose clause receives `κ`: `handle_resume_inst` proves the
conclusion of `HandleVN` and `HandleVBN` at the relation at `KW` through `erwpK_handle_leI`,
every premise inhabited (`handleVN_resume_premises`, `handleVBN_resume_premises`). `ReifyN`'s
premises are inhabited (`reifyN_premises_inst`); its conclusion is proved at no instance.

**Not verified** that no typed instance refutes a field: that is the soundness question of
`assert-boundary.md` §1.

## Retired with the one-world relation

`Kappa835N`'s `KapRelKTyN` and its refutations `not_kapRelKTyN`, `not_kTy_world`,
`kapRelN_world`, `not_kTy_view`, `kapRelN_view`, and `Public835N`'s `kapRelN_not_kapRelP` (last at
42531d67). Each is stated over `KapRelN` at the one-world table `tabN₀ (F_Σ R) δ Θ c`: Core's step
`vC_kTy_of_kapRel` read at the one-world relation, refuted at `κ = ()`. That relation is gone, and
no proof at `KW` takes that step: at `KW` a clause receives `κ` with `KapRelK` at the tables
indexed by `KW`, and the step from there to `vN`'s `U` clause is what `HandlerLawN` asserts
(`assert-boundary.md` §2.2). The configurations at `κ = ()` that read `vN`/`cN` themselves
(`not_kTy_at`, `not_kapRelP_world`, `not_kapRelR_world`, `flooredExit`) are kept, at `KW`.

## Historical

| File | Headline | Why it justifies nothing current |
|---|---|---|
| `ConfigsKW835N.lean` (`Map831N`) | `extR_addImm_inst`, `imm_at_extension`, `imm_world_ne_nil` | It answers `callback_any_inst`, a configuration against the old `LocTy.above` (which kept every `imm` record), removed in 6ede48eb. At the current `above` and `Keeps` it checks that one instance is an extension holding an `Imm` value; `LocTy.extR_addImm` proves the extension at every resource in the lend's stratum. Nothing uses its declarations |
| `ImmTie791N.lean` (part) | `ImmWit`, `ImmTie`, `immTie_agree`, `immWit_ref`, `immTie_excludes_thunk`, `immTie_ref`, `immTie_wit_excludes_thunk`, `ImmTieL.tie` | The tie over an abstract record list, before it was placed. The relation carries `ImmTieL`; the interpretation's witness is `ImmWitW`, and `withloadS_compat` reads `cohE_of_immWitW`, not `immTie_agree`; no file outside `ImmTie791N.lean` uses these. The rows above (`not_effOf_guarded`, `immTie_guard_fails`, `immTieL_world_ref`) are current; `Withload791N.lean` imports the file |

Removed earlier, kept in git: `LocalU791.lean` (`u_not_local`: `U` is not local along a lend
under `ExtA`; at 728b51d7, removed in 55b83e3f) and `LocTypeSketch.lean` (the first per-lend
sketch, from 7ac003bb; its results were moved into `SI/LocTy.lean`).

Not configurations, noted here because they are definitions nothing reads: `vThunk` and
`Covers` (`SI/MutSemN.lean`; `chain-interpretation.md` Appendix A.4).

- `ConfigsKW835N.lean` (`Depart831N`): `not_unwindArgStepLoc` / `unwindArg_inst` justify D5 (`Keeps` by lifetime), a step Core's proofs do not take (refactor candidate); `Depart831N.erwp_of_noFinal` and `cN_effOf_divB` justify reading `Div` rows at `erwpK` (no coinductive `cwp`).
