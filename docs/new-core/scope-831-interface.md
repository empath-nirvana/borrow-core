# #831 step 1: the lemma interface for `FundamentalN`

Branch `rule-791` (from 63b3dd7e). Core's `fundamentalC` (`Core/Fundamental.lean`) proves each of
`CDerives`'s 104 constructors by a compatibility lemma (`*_compatC`/`*_compatX`). Those proofs are
written against a set of relation-level lemmas. This document lists that set, gives each lemma's
counterpart at the chain (`vN`/`cN`/`gN`/`SemJN`/`erwp`), and plans the port of `FundamentalN`
(`Core/Chain/Goal791N.lean`) against it. The rule-by-rule map that precedes it is
`scope-831-map.md`; its G1–G8 and E1–E11 are cited by those names.

Kernel target: the interface of relation lemmas that `fundamentalC`'s compatibility proofs reach
for, each with its chain counterpart, so that `FundamentalN` can be ported rule by rule against it.

## 1. How the interface was found

The list comes from reading the proofs, not from guessing. Each constructor's case of
`fundamentalC` names its compatibility lemma. For each of those lemmas, every identifier in its
proof body (comments stripped) was resolved against the declarations of `Core/` (Tree files
excluded), `Paper/` and `Support/`. The walk then went into helpers that live in the rule's own
file (`countLoop_wp`, `withborUE_beta`, `ewp_frame_then`, …), but not into other rules'
compatibility lemmas; `effAwait`, which composes other rules, gets their union. Model algebra
(`ResU.CompS` laws, `pure_sep_*`, `hash_*`), substitution and closedness lemmas (`psub_*`,
`shift_*`, `closedAt`) and lifetime-interpretation facts (`interp_*`, `meetOfDomL_wf`) were
left out: they are shared between Core and the chain, and no chain counterpart is involved. The
names that remained were grouped into 83 interface entries (one entry may hold several Core
lemmas that have one chain counterpart). Then each entry was checked by hand against the chain's
declarations.

"Rules" counts the constructors whose proof reaches the lemma. Four groups of rows were adjusted
by hand where the walk could not see a dependency:
- every row outside the fragment needs its former's clause (F5, F6, F8, F9);
- the rows whose `⊸` is introduced or eliminated need the chain's `⊸` clause (F10);
- every row with a context split needs the chain's index and consistency at the split (G11, G12);
- every row that frames across a run needs V11.

Statuses:
- **same**: the chain lemma exists with the same statement shape; named.
- **departed (built)**: it exists with a different statement, and a recorded Lean configuration
  forces the difference; the configuration is named.
- **departed, no configuration**: it exists with a different statement and no configuration
  forces the difference. This is a gap to close (§2.2).
- **departed, forced by `erwp`'s definition**: the chain's `erwp` has no counterpart of Core's
  object, and a Lean lemma records why (§6.3).
- **departed, to build**: a chain lemma exists in a narrower form. The form Core's proofs read is
  missing, buildable, and departs in the way the narrower form already does.
- **missing, buildable**: says what it would be built from.
- **missing, unclear**: not derived; obstruction not verified.

The configurations named below are indexed in `configurations.md`; the design they belong to is
`chain-interpretation.md`:
`coreMutImm_not_extF` (`ImmShape791N.lean`), `not_wlImage` (`ImmRec791N.lean`),
`perLocShape_not_reborrow` and `reseal_untyped` (`Shape791N.lean`), `extRL_breaks_extA`
(`ExtRLit791.lean`, which rests on `ν` read as empty), and `flat_part_config`
(`ConsistentFlat791.lean`).

## 2. The interface

### W. `wpTS` at the empty table

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| W1 | `wpTS_val` | 6.136 | 64: `var`, `unitI`, `tensorI`, `sumI₁` … | **same** | `erwp_val` (`SI/ErwpN.lean`) |
| W2 | `wpTS_bind` | 6.135 | 22: `sumI₁`, `sumI₂`, `swap`, `arrNew` … | **same** | `erwp_bind` (`SI/BindN.lean`; its `CtxClosed` at the empty table is `empty_ctxClosed`), or `rwp_of_erwp_empty` → `rwp_bind` → `erwp_of_rwp` at a context with a handler |
| W3 | `wpTS_mono` | — | 20: `sumI₁`, `sumI₂`, `bangE`, `boxE` … | **same** | `erwp_mono` (`SI/AntiStopN.lean`), `erwp_mono_le` |
| W4 | `wpTS_bind_frame`, `wpTS_ramify` | 6.135, 6.146 | 22: `tensorI`, `arrNew`, `arrFree`, `countFold` … | **missing, buildable** | map G3: `rwp_of_erwp_empty`, `rwp_frame` (`SI/WpN.lean`), `rwp_bind`, `erwp_of_rwp`; the frame read at the run's later index needs V11 and G11 |
| W5 | `wpTS_frame_noOwn` | 6.148/6.149 | 4: `arrLen`, `arrGet`, `arrRelease`, `sliceGetM` | **same** | `erwp_garbage` (`SI/BindN.lean`) |
| W6 | `wpTS_head`, `wpTS_lolli`, `wpTS_1`, `wpTS_tensor` … | 6.137–6.140 | 43: `copyBang`, `releaseBang`, `tokMint`, `tokBurn` … | **same** | `erwp_det` (`SI/ErwpN.lean`, any `Step1Only` step): one lemma for every head step |
| W7 | `wpTS_box` | 6.147 | 1: `boxI` | **missing, buildable** | a run at the empty table from `Res_α` ends in `Res_α`: from `rwp`'s definition (the model's `↭` keeps strata) |
| W8 | `wpTS_iff_wpG`, `ewp_abortive` | — | 6: `withbor1U`, `withbor2U`, `withbor3U`, `withloadU` … | **same** | `erwp_eq`, `rwp_iff_rwpG` (`SI/RwpG.lean`): `erwp` is already the general form |
| W9 | `wpTS_val_post` | — | 5: `reify`, `effHandleV`, `effHandleVB`, `effHandleT` … | **missing, buildable** | map E9: `vN` read off a value's `cN (.ret A)`, from `erwp_unfold_at` at `.val v` |

### H. Heap steps

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| H1 | `wpTS_alloc` | 6.141 | 2: `alloc`, `tokMint` | **same** | `erwp_alloc` (`SI/HandleN.lean`) |
| H2 | `wpTS_free` | 6.142 | 4: `free`, `tokBurn`, `arrFree`, `foldOwn` | **same** | `erwp_free` (`SI/HandleN.lean`) |
| H3 | `wpTS_load` | 6.143 | 6: `swap`, `arrReplace`, `sliceReplaceM`, `sliceSwapM` … | **same** | `rwp_load` (`SI/HeapN.lean`) under `erwp_bindR` |
| H4 | `wpTS_load_I` | 6.144 | 2: `withload`, `withloadU` | **same** | `rwp_load_I` (`SI/HeapN.lean`) |
| H5 | `wpTS_store` | 6.145 | 7: `swap`, `arrNew`, `arrReplace`, `sliceReplaceM` … | **same** | `rwp_store` (`SI/HeapN.lean`) |
| H6 | `wpTS_I_forget`, `ptoImmS_ptoImm` | 6.149 | 1: `releaseImm` | **same** | `erwp_garbage` with `noOwn_of_imm` (`SI/RebAcrossC.lean`) |
| H7 | `wpTS_M_forget`, `ptoMutS_ptoMut` | 6.148 | 1: `releaseMut` | **same** | `erwp_garbage` with `noOwn_single_mut`; `dRelease_sem` (`Inst791N.lean`) is the instance at `Γ = []` |

### K. The Kripke order

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| K1 | `vC_local` | — | 19: `swap`, `iterate`, `reify`, `sliceBorrowM` … | **departed (built)** | `vN_extR` (`Goal791N.lean`), along `LocTy.ExtR` at the value's resource. Configurations: `extRL_breaks_extA` (Core's `Ext` read literally is not Kripke along `ExtA`; rests on `ν` read as empty) and `coreMutImm_not_extF` (payloads read off the list are not stable along `extF`, so the order is on the world) |
| K2 | `vC_same`, `vP_same`, `gDenC_same`, `ext_of_same` | — | 31: `tensorI`, `bind`, `unitE`, `tensorE` … | **same** | holds by definition: `vN`/`gN` read no record list; `LocTy.extR_refl` |
| K3 | `ext_add` | 6.64 | 2: `withbor1`, `withbor1U` | **departed (built)** | `LocTy.extR_addImm` (`SI/LocTy.lean`): the record goes into the world, not the list (`coreMutImm_not_extF`) |
| K4 | `ext_drop` | 6.64 | 0 (inside the Imm Frame) | **departed (built)** | `LocTy.extR_of_addImm`: Core asks `∀ r ∈ rsOf ls′, Rel r ρ → r ∈ rsOf ls` and discharges it at the Imm Frame's exit from the run (`not_rel_lineage`); the chain's statement has no such premise because `Keeps` reads relevance by lifetime. Configuration: `Depart831N.not_unwindArgStepLoc` (§6.3) |
| K5 | `ext_empty'` | — | 11: `iterate`, `reify`, `withbor1U`, `withbor2U` … | **missing, buildable** | `ExtR` at `∅` (no `CellIn`): one line; inlined in `ImmLend833N.gN_dead_any` |
| K6 | `opTable_ext` | — | 2: `withbor1U`, `sliceBorrowIU` | **same** | not needed: `entN` reads no list (`scope-831-map.md` §3.2) |

### V. Value-relation laws

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| V1 | `vC_tyEq`, `cC_tyEq` | — | 5: `allE`, `withload`, `withloadU`, `allEV` … | **missing, buildable** | map G8: `vN_tyEq`/`cN_tyEq` by Core's induction (`Core/RelationFacts.lean`); `vN_congr` covers only `δ`-agreement |
| V2 | `vC_vShape` | — | 3: `withload`, `withloadU`, `foldImm` | **same** | `vN_vShape` (`ImmImage791N.lean`), to Core's `vShape` |
| V3 | `vC_extend_of_not_free` | — | 14: `allI`, `sliceBorrowM`, `sliceBorrowI`, `withbor1` … | **same** | `vN_extend_of_not_free`, `vO_extend_of_not_free`, `gN_extend_of_not_free` |
| V4 | `vC_congr`, `vCE_congr_occ` | — | 3: `reify`, `foldImm`, `unfoldN` | **same** | `vN_congr`, `vO_congr`, `cN_congr` |
| V5 | `vC_outlives` | 6.60 | 2: `foldImm`, `effHandleVB` | **same** | `vN_outlives` |
| V6 | `vC_outlivesLe` | 6.60 | 6: `sliceBorrowM`, `sliceBorrowI`, `withbor2`, `withbor2U` … | **same** | `vN_outlivesLe` |
| V7 | `vO_obs` | — | 4: `sliceBorrowI`, `withbor1`, `withbor1U`, `sliceBorrowIU` | **same** | `vN_vO` (`ImmImage791N.lean`) |
| V8 | `vC_noOwn_of_ownFree` | — | 2: `effAwait`, `effHandleL` | **missing, buildable** | `vN` of an `OwnFree` type owns nothing: induction on `A` |
| V9 | `vP_empty_of_persistent` | spec §10 | 6: `effThen`, `effThenDiv`, `effHandleV`, `effHandleVB` … | **same** | `vN_empty_of_persistent` (`ImmLend833N.lean`) |
| V10 | `admWf_of_vScoped`, `cohE_of_coh` | — | 4: `sliceBorrowI`, `withbor1`, `withbor1U`, `sliceBorrowIU` | **departed (built)** | the Imm Frame's admissibility and `Coh` become the witness `ImmWitW` (`cohE_of_immWitW`, `Withload791N.lean`) at the world's records, with the lifetime match `⊓s ⊑ x.2`. Carrier: `coreMutImm_not_extF`, `not_wlImage` (`ImmRec791N`). The lifetime match serves `Keeps` by lifetime, configured with K4 (§6.3) |
| V11 | `vN_le` (chain only) | — | 28: `tensorI`, `bind`, `unitE`, `tensorE` … | **same** | `vN_le`, `vO_le`, `cN_le`: the index is the chain's, Core has none |

### G. The context relation

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| G1 | `gDenC_split`, `gSepC_splitP` | spec §10 | 16: `tensorI`, `bind`, `app`, `unitE` … | **missing, buildable** | `gN` along `Ctx.SplitP`: from `gN`'s definition |
| G2 | `gSepC_soloP` | spec §10 | 4: `var`, `force`, `app`, `effAwait` | **missing, buildable** | `gN` at `SoloP`: from `gN`'s definition |
| G3 | `gSepC_deadP`, `eq_empty_of_compS_empty`, `sem_const` | spec §10 | 60: `unitI`, `copyBang`, `releaseBang`, `alloc` … | **same** | `gN_deadP` (`ImmLend833N.lean`) |
| G4 | `gSepC_persistent`, `gSepC_cons_persistent`, `gDenC_persistent` | — | 7: `lamDead`, `bangThunkF`, `bangThunkV`, `effAwait` … | **missing, buildable** | a banged context owns nothing: from `vN_empty_of_persistent` |
| G5 | `gDenC_dead_cons`, `gDenC_mk`, `gDenC_iff` | — | 15: `thunkF`, `bind`, `lam`, `lamDead` … | **same** | by `gN`'s definition (a dead slot; `LiveWithin` is `SemJN`'s own premise) |
| G6 | `gDenC_local`, `gSepC_local` | — | 16: `thunkF`, `thunkV`, `lam`, `lamDead` … | **missing, buildable** | `gN` along `ExtR`: `vN_extR` slot by slot with `ExtR.left`/`.right` |
| G7 | `gSepC_outlives` | 6.62, 6.60 | 2: `boxI`, `effHandleVB` | **missing, buildable** | from `vN_outlives` folded over the context |
| G8 | `gSepC_congr` | — | 1: `allI` | **missing, buildable** | from `vN_congr` |
| G9 | `gDenC_noOwn` | — | 2: `effAwait`, `effLet` | **missing, buildable** | from V8 |
| G10 | `semV_dead_closed` | — | 5: `withbor1U`, `withbor2U`, `withbor3U`, `sliceBorrowMU` … | **same** | `gN_dead_any` (`ImmLend833N.lean`): at every world and lower index |
| G11 | `gN_le` (chain only) | — | 18: `tensorI`, `bind`, `lam`, `lamDead` … | **missing, buildable** | `gN` at a lower index, from `vN_le` |
| G12 | `consistentX` split (chain only) | — | 16: `tensorI`, `bind`, `app`, `unitE` … | **missing, buildable** | G7 of the map: `consistentX_left`/`_right` (`SI/LocTy.lean`) need `ResU.Valid ρ`, which `erwp_of_valid` (`Cancel791N.lean`) gives at a run |

### C. The computation relation

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| C1 | `cC_head` | — | 14: `thunkF`, `bind`, `lam`, `lamDead` … | **same** | `cN_head` (`Goal791N.lean`) |
| C2 | `cC_bind` | — | 6: `bind`, `unitE`, `tensorE`, `sumE` … | **missing, buildable** | `cN_bind` by induction on `C`: `erwp_bindR` at `F`/`F_Σ`, the clauses elsewhere, G6 and G11 to re-enter at the clause's world and index |
| C3 | `cC_effOf`, `cC_effOf_wp` | spec §19 | 20: `iterate`, `divFuel`, `reify`, `withbor1U` … | **same** | `cN_effOf`, at every row: no `divB` split (E13) |

### F. The formers' clauses and laws

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| F1 | `pure_sep_mk` (⊗, +, 1, 0 clauses) | — | 33: `tensorI`, `sumI₁`, `sumI₂`, `copyBang` … | **same** | `vN`'s clauses, definitionally Core's with `⋆` as `ResU.CompS` |
| F2 | `bang_app` | — | 4: `arrNew`, `arrFree`, `countFold`, `countTry` | **missing, buildable** | `!(A ⊸ B)` applied at a later world: from `vN .bang` and the `⊸` clause |
| F3 | `instLife`, `immReborrow`, `vShape_tyEq`, `six132_shape_fresh` | 6.132 | 6: `allE`, `withload`, `withloadU`, `allEV` … | **same** | syntactic or model-level: Core's lemmas used as they are (`TyEq.instLife`, `tyEq_immReb`, `six132_shape_fresh`) |
| F4 | `host_call_sound`, `vP_lit` | spec §8 | 2: `lit`, `hostOp` | **missing, buildable** | `host_call_sound` at `vN` (`hostSig` uses `int`, `⊗`, `+`, `1`, `0`); `vP_lit` is `vN .int` by definition |
| F5 | `rel_tok_intro`, `rel_cases`, `tok_not_host` | — | 2: `tokMint`, `tokBurn` | **missing, buildable** | an `opq` clause in `vN` reading `k.rel` (for `Tok`, a fresh unit cell), and its laws |
| F6 | `vP_fam_mk`, `vP_fam_split`, `vP_fam_idx`, `sepRange_pick` … | spec §9 | 22: `arrNew`, `arrFree`, `arrSize`, `arrReplace` … | **missing, buildable** | a `fam` clause in `vN`/`vO` (an indexed `sepRange` of leaves), the array steps at `erwp`, and the laws re-proved over it (`scope-831-map.md` §4) |
| F7 | `wpTS_M_frameFam`, `wpTS_I_frameFam`, `wpG_M_frameFam`, `wpG_I_frameFam` | — | 4: `sliceBorrowM`, `sliceBorrowI`, `sliceBorrowMU`, `sliceBorrowIU` | **missing, buildable** | the `n`-cell frames: list inductions over the one-cell frames (`erwp_M_frameCRG`, `erwp_I_frameC`), one key per cell |
| F8 | `vC_roll`, `vC_unfold`, `vC_immReborrow_mu_iff`, `vCE_subst` … | — | 8: `reify`, `roll`, `unroll`, `foldImm` … | **missing, buildable** | an environment argument in `vN`/`vO`, the `μ`/`tvar` clauses, Core's `RelMu` laws at the index; `withload_sized` is `withloadS_compat` with a size measure. Very high; not checked |
| F10 | `cC` .arr (the `⊸` clause) | — | 10: `bind`, `lam`, `lamDead`, `app` … | **same** (#834) | `cN .arr` is Core's plain wand at the function's own world, read at every later index and every view consistent with the composite (§8.1). The Kripke reading along `ExtR` is gone: no configuration forced it |
| F9 | `cC_nu_iff`, `nuRel_coind`, `cB_step` | spec §7 | 4: `reify`, `nuIn`, `nuOut`, `unfoldN` | **missing, unclear** | a reading of `ν` at `erwp`: a design choice first. Not derived; obstruction not verified |

### R. Frames, the reborrow theorem, the chooser, the cells

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| R1 | `wpTS_M_frameX`, `ewpTS_M_frameU` | 6.65 | 3: `withbor2`, `withbor3`, `withbor2U` | **departed (built)** | `erwp_M_frame` (`SI/StopFrameN.lean`), `erwp_M_frameR` (raises, `SI/StopRaiseN.lean`), `erwp_M_frameCR`/`CRG` (cancel runs): the lend's key in the world `Φ[ℓ ↦ (A, F)]`, not `ptoMutS ℓ α ls₀`. Configurations: `perLocShape_not_reborrow`, `reseal_untyped`, `coreMutImm_not_extF` |
| R2 | `wpTS_M_antiFrameX` | 6.66 | 4: `sliceReplaceM`, `sliceSwapM`, `withbor3`, `withswap` | **departed (built)** | `erwp_M_antiFrame` (`SI/AntiStopN.lean`) at the view: `erwp_antiFrame_view`, `reseal_at_entry` (`SI/LocTy.lean`). Configuration: `reseal_untyped` |
| R3 | `ewpTS_M_antiFrameU` | 6.66 | 1: `withbor3U` | **departed, to build** | the anti-frame across an unwinding row's raises: `erwp_M_antiFrameCR` (`Reborrow791N.lean`) at the row's guarded twin. Missing: the twin tables at a `Row.Unwind` row (every entry abortive, so no stop to guard: `tabN_unwind_abort`). Buildable from `erwp_M_antiFrameCR` and `tabN_unwind_*` |
| R4 | `wpG_M_frameX` | 6.65 | 1: `withbor3U` | **departed (built)** | `erwp_M_frameCRG`/`erwp_M_frameF`: the inner Mut Frame of 6.174 with the fold at every stop (`erwp_withbor3`, `SI/AntiStopN.lean`) |
| R5 | `wpTS_I_frameX`, `ewpTS_I_frameU`, `ptoImmS_mono` | 6.64 | 4: `sliceBorrowI`, `withbor1`, `withbor1U`, `sliceBorrowIU` | **departed (built)** | `erwp_I_frame` (`SI/IStopN.lean`), `erwp_I_frameR` (`SI/IStopRaiseN.lean`), with the record in the world (`LocTy.addImm`) and the run read at the lender's view by `erwp_tieEntry` (abortive tables only, §6.1). Carrier: `coreMutImm_not_extF` |
| R6 | `wpG_frame`, `wpG_garbage` | 6.146 | 13: `withbor1U`, `withbor2U`, `withbor3U`, `withloadU` … | **same** | `erwpG_frame` (`SI/AntiStopN.lean`), `erwp_frameL`, `rwpG_garbage` |
| R7 | `wpTS_reborrow`, `wpG_reborrow`, `wpG_bind_pure` | 6.150 | 2: `withload`, `withloadU` | **departed (built)** | `erwp_reborrow` (`SI/RebAcrossC.lean`), `erwp_rebGen`/`erwp_rebGen_cancelRun` (raises, layered cancel runs, `SI/RebRaiseC.lean`), `erwp_reborrowDeep`: at the canonical image the first entry chose. Configurations: `coreMutImm_not_extF`, `not_wlImage` (`configurations.md`) |
| R8 | `rebChooseTW_top`, `rebChooseTW_deep`, `rebChooseTW_pin`, `ptoImmO_toImm` … | 6.131, 6.134 | 3: `withload`, `withloadU`, `foldImm` | **departed (built)** | the chooser at the world: `cohE_of_immWitW`, `TI.leInvW`/`TI.exIn`, `tmpl_exists`, `relabel_vN`, `vO_transfer`, `reb_witness_choice` (`Withload791N.lean`, `ImmImage791N.lean`; `chain-interpretation.md` §6.3, `wl` steps 6–10). Configurations as R7 |
| R9 | `ptoImmS_antitone`, `ptoMutS_antitone` | 6.114, 6.118 | 2: `immSub`, `mutSub` | **same** | inside `immSub_compatN`/`mutSub_compatN` (`Goal791N.lean`) |
| R10 | `ptoImmS_dup` | 6.116 | 2: `copy`, `arrCopy` | **same** | `compS_imm_dup` (`SI/IStopN.lean`) |
| R11 | `ewp_unwind`, `ewp_box_end`, `ewp_ret_pair`, `fin_run` … | spec §19 | 6: `withbor1U`, `withbor2U`, `withbor3U`, `withloadU` … | **departed (built)** | the unwinding row's finaliser: `erwp_ubindRaise` (`SI/StopRaiseN.lean`), `fin_claimI`, `erwp_claimX_abort` (`ImmLend833N.lean`). The claim carries the view's consistency (configuration `flat_part_config`, which replaces `Covers`) |

### E. Effects, handlers and the stop lemma

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| E1 | `ewp_fold`, `ewp_unfold`, `ewp_ind` | — | 18: `iterate`, `divFuel`, `reify`, `withbor1U` … | **same** | `erwp_fold_at`, `erwp_unfold_at` (`SI/ErwpN.lean`) |
| E2 | `ewp_val`, `ewp_mono`, `ewp_step`, `effWp_step` … | — | 16: `iterate`, `divFuel`, `reify`, `withbor1U` … | **same** | `erwp_val`, `erwp_mono`, `erwp_det`, `erwp_step` (`SI/LoopN.lean`) |
| E3 | `effWp_sub`, `ewp_sub`, `finLe_iff`, `cancelObl_le` | — | 6: `effSub`, `effAwait`, `effThen`, `effThenDiv` … | **departed, to build** | `erwp_tabLe` (`SI/TabLeN.lean`) is there; `RowLe S S′ → OpTabN.Le (tabN …)` is missing, buildable (map E1) |
| E4 | `opTable_mono`, `opTable_abortive`, `tab_local`, `tab_zero` … | — | 21: `iterate`, `divFuel`, `reify`, `withbor1U` … | **same** | `opTableN_le`, `opTableN_local`, `opTableN_down`, `tabN_effOf_some`, `tab_lookupN`, `tabN_unwind_abort` |
| E5 | `ewp_bind_pure_frame` | spec §19 | 3: `effPerform`, `effAwait`, `effRaise` | **departed, to build** | `erwp_bind` with `T.CtxClosed K`: `tabN`'s `CtxClosed` at a context with no handler or catcher is missing, buildable (map E3) |
| E6 | `ewp_perform_here`, `ent_start`, `cancelObl_start` | spec §19 | 2: `effPerform`, `effAwait` | **departed, to build** | `erwp_performG` (`SI/LendCancelProg.lean`), `erwp_perform`; `cancelOKN` at the empty context (`ent_start`) missing, buildable (map E2) |
| E7 | `ewp_raise_here` | spec §19 | 2: `effAwait`, `effRaise` | **missing, buildable** | a raise's introduction at `raiseStopN`: built inline in `erwp_handle`'s proof (`SI/HandleN.lean`), to be stated (map E4) |
| E8 | `ewp_frame_plain`, `ent_plain`, `cancel_frame`, `cancel_frame_consume` … | spec §27 | 10: `iterate`, `divFuel`, `reify`, `unfoldN` … | **missing, buildable** | the frame at a row's table: owning across must-resume stops, owning nothing where the row cancels, empty at an unrestricted row; `erwpG_frame`, `erwp_frameL` are special cases (map E5) |
| E9 | `ewp_frame_then`, `ewp_frame_then_or`, `cwp_then`, `cwp_then_div` … | — | 3: `effThen`, `effThenDiv`, `effHandleL` | **departed, to build** | `erwp_ubind` (`SI/UbindGN.lean`) and its cancel/raise/claim companions are stated without unrestricted operations in `Σ_M` and at a finaliser meeting `FinOK`; Core's `hP`/`hU`/`ThenLe` form and a finaliser row holding `Div` are missing, buildable (map E6, E7) |
| E10 | `ewp_handle_vals`, `ewp_handle_valsB`, `ewp_handle_tail`, `ewp_handle_last` … | — | 4: `effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL` | **departed, to build** | `erwp_handle` (`SI/HandleN.lean`; needs no `hdv`), `erwp_kappa_*`; the clauses' reading at `vN` and the split of `tabN (ofEff n E 0 fs ++ S)` (map E8), the tail and last instances (map E11): missing, buildable |
| E11 | `ewp_kappaC_resume`, `ewp_kappaC_cancel`, `ewp_kappaCell`, `ewp_kappa_resume` … | — | 3: `divFuel`, `reify`, `effHandleVB` | **same** | `erwp_kappa_resume`, `erwp_kappaC_resume`, `erwp_kappa_cancel`, `erwp_kappaC_cancel`, `erwp_kappaCell`, `erwp_ccatch` (`SI/HandleN.lean`) |
| E12 | `stop_sem` | spec §28 | 1: `effHandleVB` | **missing, unclear** | the BOXED-κ stop lemma at `erwp` (map E10). Not derived; obstruction not verified |
| E13 | `cwp_bind`, `cwp_of_ewp`, `effWp_of_ewp`, `cwp_out` … | spec §14 | 21: `iterate`, `divFuel`, `reify`, `withbor1U` … | **departed, forced by `erwp`** | a `Div` row is a row of the table; `erwp` is step-indexed, so Core's coinductive `cwp` and its bookkeeping have no counterpart, and each `cwp` branch is the `ewp` branch's `erwp` lemma. Reason: `Depart831N.erwp_of_noFinal`; the split: `Depart831N.cN_effOf_divB` (§6.3) |
| E14 | `cwp_iterate` | spec §14 | 1: `iterate` | **departed, to build** | `erwp_iterate` (`SI/LoopN.lean`) is stated where the tick always answers *next*; the version answering in `vN nextTy` (the close branch) is missing, buildable from its induction |

### 2.1 Counts

| Status | Entries |
|---|---|
| same | 38 |
| departed (built) | 11 (K1, K3, K4, V10, R1, R2, R4, R5, R7, R8, R11) |
| departed, forced by `erwp`'s definition | 1 (E13) |
| departed, no configuration | 0 |
| departed, to build | 7 (R3, E3, E5, E6, E9, E10, E14) |
| missing, buildable | 24 |
| missing, unclear | 2 (F9 `ν`, E12 the BOXED-κ stop lemma) |
| **total** | **83** |

The chain-only entries V11, G11 and G12 are counted here. They have no Core lemma: the chain's
judgment carries a step index and a view (`SemJN`'s `n` and `c`), and Core's has neither.

### 2.2 Departed without a configuration

K4, V10's lifetime match, E13 and F10 were listed here. K4/V10 now have a configuration and E13
is forced by `erwp`'s definition (§6.3); F10 returned to Core's plain wand in #834 (§8.1). None
remain.

### 2.3 Missing, unclear

- **F9, the `ν` clause** (`cC_nu_iff`, `nuRel_coind`, `cB_step`; `nuIn`, `nuOut`, `unfoldN`,
  `reify`). A reading of `ν` at `erwp` must be chosen first (`scope-831-map.md` §4). Not derived;
  obstruction not verified.
- **E12, the BOXED-κ stop lemma `stop_sem`** at `erwp` (`effHandleVB`). Not derived; obstruction
  not verified.

### 2.4 Chain-only obligations

Core has no counterpart for these. Every rule that splits its context or frames across a run
carries them:
- **V11**: `vN_le`/`vO_le`/`cN_le` exist.
- **G11**: `gN_le`, buildable.
- **G12**: the view's consistency at the split parts. It is buildable at each run, where
  `erwp_of_valid` gives `ResU.Valid`. It is not verified at a conclusion that is not an
  `F`/`F_Σ` (map G7).

With W4 and G1, these three are the whole difference between Core's `tensorI_compatC` and its
port.

## 3. Rule coverage

Columns:
- **Frag**: from `scope-831-map.md`.
- **Map**: that map's class.
- **Interface lemmas**: the entries the rule's proof uses.
- **Still to build**: the entries among them that are missing or departed-to-build.
- **Class**:
  - *proved*: a compatibility lemma at `SemJN` exists;
  - *mechanical now*: every entry the rule uses is same or departed-and-built;
  - *mechanical once built*: every entry still to build is buildable;
  - *waits (unclear)*: an entry it uses is missing, unclear.
- **Rule-local**: what the rule proves for itself, ported with it.

`withload`/`withloadU` read `vC_tyEq` (V1) inside `withload_compatX`'s record step. On the chain,
that step is done inside `withloadS_compat`, which is proved, so V1 is not a blocker for them.

| # | Constructor | Frag | Map | Interface lemmas | Still to build | Class | Rule-local |
|---|---|---|---|---|---|---|---|
| 1 | `var` | yes | portable | W1 G2 | G2 | mechanical once built |  |
| 2 | `unitI` | yes | portable | W1 G3 | — | mechanical now |  |
| 3 | `tensorI` | yes | portable | W1 W4 K2 V11 G1 G11 G12 F1 | W4 G1 G11 G12 | mechanical once built |  |
| 4 | `sumI₁` | yes | portable | W1 W2 W3 F1 | — | mechanical now |  |
| 5 | `sumI₂` | yes | portable | W1 W2 W3 F1 | — | mechanical now |  |
| 6 | `thunkF` | yes | portable | W1 G5 G6 C1 | G6 | mechanical once built |  |
| 7 | `thunkV` | yes | portable | W1 G6 | G6 | mechanical once built |  |
| 8 | `ret` | yes | portable | — | — | mechanical now |  |
| 9 | `bind` | cut | portable | K2 V11 G1 G5 G11 G12 C1 C2 F10 | G1 G11 G12 C2 | mechanical once built |  |
| 10 | `force` | yes | portable | G2 | G2 | mechanical once built |  |
| 11 | `lam` | yes | portable | G5 G6 G11 C1 F10 | G6 G11 | mechanical once built |  |
| 12 | `lamDead` | yes | portable | G4 G5 G6 G11 C1 F10 | G4 G6 G11 | mechanical once built |  |
| 13 | `app` | cut | portable | G1 G2 G11 G12 F10 | G1 G2 G11 G12 | mechanical once built |  |
| 14 | `withI` | yes | portable | G5 C1 | — | mechanical now |  |
| 15 | `proj₁` | yes | portable | — | — | mechanical now |  |
| 16 | `proj₂` | yes | portable | — | — | mechanical now |  |
| 17 | `topI` | yes | portable | — | — | mechanical now |  |
| 18 | `unitE` | yes | portable | K2 V11 G1 G11 G12 C1 C2 F10 | G1 G11 G12 C2 | mechanical once built |  |
| 19 | `tensorE` | cut | portable | K2 V11 G1 G5 G11 G12 C1 C2 F10 | G1 G11 G12 C2 | mechanical once built |  |
| 20 | `sumE` | cut | portable | K2 V11 G1 G5 G11 G12 C1 C2 F10 | G1 G11 G12 C2 | mechanical once built |  |
| 21 | `zeroE` | cut | portable | K2 V11 G1 G11 G12 C2 F10 | G1 G11 G12 C2 | mechanical once built |  |
| 22 | `allI` | yes | proved | V3 G5 G8 C1 | — (proved with chain lemmas inline) | proved |  |
| 23 | `allE` | yes | portable | V1 F3 | V1 | mechanical once built |  |
| 24 | `bangThunkF` | yes | portable | W1 G4 G5 G6 C1 | G4 G6 | mechanical once built |  |
| 25 | `bangThunkV` | yes | portable | W1 G4 G6 | G4 G6 | mechanical once built |  |
| 26 | `bangE` | yes | portable | W3 | — | mechanical now |  |
| 27 | `copyBang` | yes | portable | W1 W6 G3 F1 | — | mechanical now |  |
| 28 | `releaseBang` | yes | portable | W1 W6 G3 | — | mechanical now |  |
| 29 | `boxI` | yes | portable | W7 G7 | W7 G7 | mechanical once built |  |
| 30 | `boxE` | yes | portable | W3 | — | mechanical now |  |
| 31 | `immSub` | yes | proved | W3 F1 R9 | — (proved with chain lemmas inline) | proved |  |
| 32 | `mutSub` | yes | proved | W3 F1 R9 | — (proved with chain lemmas inline) | proved |  |
| 33 | `alloc` | yes | portable | W1 H1 G3 F1 | — | mechanical now |  |
| 34 | `free` | yes | portable | W1 H2 G3 | — | mechanical now |  |
| 35 | `tokMint` | no | out | W1 W6 H1 G3 F5 | F5 | mechanical once built |  |
| 36 | `tokBurn` | no | out | W1 W6 H2 G3 F5 | F5 | mechanical once built |  |
| 37 | `swap` | yes | portable | W1 W2 W6 H3 H5 K1 G3 F1 | — | mechanical now |  |
| 38 | `copy` | yes | portable | W1 W6 G3 F1 R10 | — | mechanical now |  |
| 39 | `releaseImm` | yes | portable | W1 W6 H6 G3 | — | mechanical now |  |
| 40 | `releaseMut` | yes | portable | W1 W6 H7 G3 | — | mechanical now |  |
| 41 | `releaseUnk` | yes | portable | W1 W6 G3 | — | mechanical now |  |
| 42 | `lit` | yes | portable | W1 G3 F4 | F4 | mechanical once built | `vP_lit` (F4) |
| 43 | `hostOp` | yes | portable | W1 W6 G3 F4 | F4 | mechanical once built | `host_call_sound` (F4) |
| 44 | `arrNew` | no | out | W1 W2 W4 W6 H5 K2 V11 G3 F1 F2 F6 | W4 F2 F6 | mechanical once built |  |
| 45 | `arrFree` | no | out | W1 W2 W4 W6 H2 K2 V11 G3 F2 F6 | W4 F2 F6 | mechanical once built |  |
| 46 | `arrSize` | no | out | W1 W6 G3 F1 F6 | F6 | mechanical once built |  |
| 47 | `arrReplace` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 | F6 | mechanical once built |  |
| 48 | `arrLen` | no | out | W1 W5 W6 G3 F6 | F6 | mechanical once built |  |
| 49 | `arrGet` | no | out | W1 W5 W6 G3 F1 F6 | F6 | mechanical once built |  |
| 50 | `arrCopy` | no | out | W1 W6 G3 F1 F6 R10 | F6 | mechanical once built |  |
| 51 | `arrRelease` | no | out | W1 W5 W6 G3 F6 | F6 | mechanical once built |  |
| 52 | `countFold` | yes | portable | W1 W4 W6 K2 V11 G3 F1 F2 | W4 F2 | mechanical once built | `countLoop_wp` (induction on `len − i`) |
| 53 | `countTry` | yes | portable | W1 W4 W6 K2 V11 G3 F1 F2 | W4 F2 | mechanical once built | `countTryLoop_wp` |
| 54 | `boundedFix` | yes | portable | W1 G3 C1 F1 | — | mechanical now | `fixSelf_valid`, `cC_boundedFix` along `ExtR` |
| 55 | `iterate` | yes | portable | W1 K1 K5 G3 C3 E1 E2 E4 E8 E13 E14 | K5 E8 E14 | mechanical once built | `cwp_iterate` → E14 |
| 56 | `divFuel` | yes | portable | W1 G3 C3 E1 E2 E4 E8 E11 E13 | E8 | mechanical once built | `fuel_total`, `divFuel_steps`, `fuelK_frame` |
| 57 | `reify` | no | out | W1 W9 K1 K5 V4 G3 C3 F8 F9 E1 E2 E4 E8 E11 E13 | W9 K5 F8 F9 E8 | waits (unclear) | `reify_compat` |
| 58 | `sliceBorrowM` | no | out | W1 W2 W3 W4 W6 K1 K2 V3 V6 V11 G3 F1 F6 F7 | W4 F6 F7 | mechanical once built |  |
| 59 | `sliceBorrowI` | no | out | W1 W2 W3 W4 W6 K1 K2 V3 V6 V7 V10 V11 G3 F1 F6 F7 R5 | W4 F6 F7 | mechanical once built |  |
| 60 | `sliceGetM` | no | out | W1 W5 W6 G3 F6 | F6 | mechanical once built |  |
| 61 | `sliceLenM` | no | out | W1 W6 G3 F6 | F6 | mechanical once built |  |
| 62 | `sliceSplitI` | no | out | W1 W6 G3 F6 | F6 | mechanical once built |  |
| 63 | `sliceSplitM` | no | out | W1 W6 G3 F6 | F6 | mechanical once built |  |
| 64 | `sliceEmptyI` | no | out | W1 G3 F6 | F6 | mechanical once built |  |
| 65 | `sliceEmptyM` | no | out | W1 G3 F6 | F6 | mechanical once built |  |
| 66 | `arrEmpty` | no | out | W1 G3 F6 | F6 | mechanical once built |  |
| 67 | `sliceReplaceM` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 R2 | F6 | mechanical once built |  |
| 68 | `sliceSwapM` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 R2 | F6 | mechanical once built |  |
| 69 | `withbor1` | yes | proved | W1 W2 W3 W4 W6 K1 K2 K3 V3 V7 V10 V11 G3 F1 R5 | — (proved with chain lemmas inline) | proved |  |
| 70 | `withbor2` | yes | proved | W1 W2 W3 W4 W6 K1 K2 V3 V6 V11 G3 F1 R1 | — (proved with chain lemmas inline) | proved |  |
| 71 | `withbor3` | yes | portable | W1 W2 W3 W4 W6 K1 K2 V3 V11 G3 F1 R1 R2 | W4 | mechanical once built | `withbor3S_compat` (`Reborrow791N.lean`) at the empty table |
| 72 | `withload` | yes | portable | W1 W2 W3 W4 W6 H4 K1 K2 V1 V2 V3 V11 G3 F1 F3 R7 R8 | W4 (V1 is inside `withloadS_compat`) | mechanical once built | `withloadS_compat` (`Withload791N.lean`) at the empty table |
| 73 | `withswap` | yes | portable | W1 W2 W4 W6 H3 H5 K1 V11 G3 F1 R2 | W4 | mechanical once built | `withswap_compatX`'s anti-frame and reseal (as `withbor3S_compat` step 13) |
| 74 | `withbor1U` | yes | proved | W1 W4 W6 W8 K1 K2 K3 K5 K6 V3 V7 V10 V11 G3 G6 G10 C3 F1 R5 R6 R11 E1 E2 E4 E13 | — (proved with chain lemmas inline) | proved |  |
| 75 | `withbor2U` | yes | proved | W1 W4 W6 W8 K2 K5 V3 V6 V11 G3 G6 G10 C3 F1 R1 R6 R11 E1 E2 E4 E13 | — (proved with chain lemmas inline) | proved |  |
| 76 | `withbor3U` | yes | portable | W1 W4 W6 W8 K2 K5 V3 V11 G3 G6 G10 C3 F1 R3 R4 R6 R11 E1 E2 E4 E13 | W4 K5 G6 R3 | mechanical once built | `withbor3S_compat` at an unwinding row |
| 77 | `withloadU` | yes | portable | W1 W8 H4 V1 V2 V3 G3 C3 F3 R6 R7 R8 R11 E1 E2 E4 E13 | (V1 is inside `withloadS_compat`) | mechanical once built | `withloadS_compat` at an unwinding row |
| 78 | `sliceBorrowMU` | no | out | W1 W4 W6 W8 K2 K5 V3 V6 V11 G3 G6 G10 C3 F1 F6 F7 R6 R11 E1 E2 E4 E13 | W4 K5 G6 F6 F7 | mechanical once built |  |
| 79 | `sliceBorrowIU` | no | out | W1 W4 W6 W8 K1 K2 K5 K6 V3 V6 V7 V10 V11 G3 G6 G10 C3 F1 F6 F7 R5 R6 R11 E1 E2 E4 E13 | W4 K5 G6 F6 F7 | mechanical once built |  |
| 80 | `lolliE` | cut | portable | W2 W4 K1 K2 V11 G1 G5 G6 G11 G12 F10 | W4 G1 G6 G11 G12 | mechanical once built |  |
| 81 | `allEV` | yes | portable | W2 W3 V1 F3 | V1 | mechanical once built |  |
| 82 | `ofRet` | yes | portable | — | — | mechanical now |  |
| 83 | `roll` | no | out | W3 F8 | F8 | mechanical once built |  |
| 84 | `unroll` | cut | out | W3 F8 | F8 | mechanical once built |  |
| 85 | `foldImm` | no | out | W1 W2 W3 W4 W6 K1 K2 V2 V3 V4 V5 V11 G3 F3 F8 R8 | W4 F8 | mechanical once built | `foldImmV`, `travK` |
| 86 | `foldOwn` | no | out | W1 W2 W3 W4 W6 H2 K1 K2 V11 G3 F8 | W4 F8 | mechanical once built | `foldOwnV` |
| 87 | `foldReuse` | no | out | W1 W2 W3 W4 W6 H3 H5 K1 K2 V11 G3 F8 | W4 F8 | mechanical once built | `foldReuseV` |
| 88 | `foldOwnG` | no | out | W1 W2 W3 W4 W6 K1 K2 V11 G3 F3 F6 F8 | W4 F6 F8 | mechanical once built | `FoldP` traversal |
| 89 | `nuIn` | no | out | F9 | F9 | waits (unclear) |  |
| 90 | `nuOut` | cut | out | F9 | F9 | waits (unclear) |  |
| 91 | `unfoldN` | no | out | W1 W2 W3 W6 K1 V4 G3 C1 F8 F9 R6 E1 E2 E4 E8 E13 | F8 F9 E8 | waits (unclear) | `nuRel_coind` |
| 92 | `effSub` | yes | portable | C3 E3 E4 E13 | E3 | mechanical once built |  |
| 93 | `effPerform` | yes | portable | C3 E4 E5 E6 E13 | E5 E6 | mechanical once built |  |
| 94 | `effAwait` | yes | portable | W1 K2 V8 V11 G1 G2 G3 G4 G5 G6 G9 G11 G12 C1 C2 C3 F10 R6 E1 E2 E3 E4 E5 E6 E7 E8 E13 | V8 G1 G2 G4 G6 G9 G11 G12 C2 E3 E5 E6 E7 E8 | mechanical once built | composes `perform`, `raise`, `sub`, `ret`, `var`, `sumE`, `let` |
| 95 | `effRaise` | yes | portable | C3 E4 E5 E7 E13 | E5 E7 | mechanical once built |  |
| 96 | `effLet` | cut | portable | K2 G1 G4 G5 G6 G9 G11 G12 C3 R6 E1 E2 E4 E8 E13 | G1 G4 G6 G9 G11 G12 E8 | mechanical once built |  |
| 97 | `effThen` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | mechanical once built |  |
| 98 | `effThenDiv` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | mechanical once built |  |
| 99 | `effHandleV` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 F1 E1 E4 E10 E13 | W9 K5 G1 G11 G12 E10 | mechanical once built |  |
| 100 | `effHandleVB` | cut | pending | W9 K5 V5 V9 G1 G3 G7 G11 G12 C3 F1 R6 E1 E4 E10 E11 E12 E13 | W9 K5 G1 G7 G11 G12 E10 E12 | waits (unclear) |  |
| 101 | `effHandleT` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 E1 E2 E3 E4 E8 E10 E13 | W9 K5 G1 G11 G12 E3 E8 E10 | mechanical once built |  |
| 102 | `effHandleL` | cut | portable | W9 K1 K2 K5 V8 V9 G1 G3 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E10 E13 | W9 K5 V8 G1 G11 G12 E3 E8 E9 E10 | mechanical once built |  |
| 103 | `letPoly` | cut | portable | G5 C1 | — | mechanical now |  |
| 104 | `alpha` | yes | portable | V1 | V1 | mechanical once built |  |

### 3.1 Counts

| Class | yes | cut | no | total |
|---|---|---|---|---|
| proved | 7 | | | 7 |
| mechanical now | 21 | 1 | | 22 |
| mechanical once built | 29 | 13 | 28 | 70 |
| waits (unclear) | | 2 (`nuOut`, `effHandleVB`) | 3 (`nuIn`, `unfoldN`, `reify`) | 5 |

**Once the layer is built, 92 rules are mechanical** (22 now and 70 more), 7 are proved, and 5
wait on F9 or E12. On the fragment (the 73 *yes* and *cut* rows), 72 are proved or mechanical
once built, and `effHandleVB` waits on E12. "Mechanical" is a reading of Core's proofs against
the interface; it is not a build.

### 3.2 The five borrow rows #833 left

| Row | Waits on |
|---|---|
| `withbor3` | W4 (the frame beside a run at the empty table), then `withbor3S_compat`'s steps at the empty table: `erwp_withbor3` (6.174 across stops), the reseal `reseal_at_entry`. Restatement at `Δ` |
| `withbor3U` | **R3**: the anti-frame across an unwinding row's raises, `erwp_M_antiFrameCR` at the row's guarded twin. A `Row.Unwind` row's entries are all abortive (`tabN_unwind_abort`), so its twin guards no stop: only the raises' claim (`hRin`/`hRout`) and cancel obligations (`hcan`) remain. Also W4, G6, K5 (`ExtR` at `∅`, for the finaliser) |
| `withload` | W4, then `withloadS_compat`'s 13 steps (`chain-interpretation.md` §6.3) at the empty table; `erwp_reborrow` for 6.150 |
| `withloadU` | `withloadS_compat` at an unwinding row: `erwp_rebGen` for the raises. `RebClosed` at an unwinding row is `tab_rebClosed`'s base case, since the row has no cancellable entry. Not checked |
| `withswap` | W4; the anti-frame at the view (`erwp_antiFrame_view`, R2) around `rwp_load`/`rwp_store`; the reseal into the stored family at the anti-frame's return, as `withbor3S_compat`'s step 13. Not checked in detail |

These five need no new reading of the world. They need W4 (every one but `withloadU`), the twin
at an unwinding row (`withbor3U`), and the reseal (`withbor3`, `withswap`, both through
`reseal_at_entry`).

### 3.3 Core's printed case splits, kept

- `effThenDiv`: `fundamentalC` splits on `Row.divB SD` (`then_compatC` and `then_compatC_div`).
- The handlers: `ewp_handle_*` against `cwp_handle_*`.

On the chain both branches of each split are proved by the same `erwp` lemma (E13). The port
keeps the split as printed; it does not merge the branches into one proof.

## 4. Port strategy

**Option A: one statement over an abstract interface.** Define a structure with the world and
the carriers (Core: `ls`; chain: `(Θ, c, n, ls)`), the relations (`vRel`, `cRel`, `gRel`, `wp`),
the Kripke order, and the entries of §2 as fields. Restate Core's compatibility proofs over it,
then instantiate the structure at Core and at the chain. Three representative rules:
- **`tensorI`** (16 lines in Core). It uses W1, W4 twice, G1, K2 and F1. Over the interface, W4
  becomes a field whose frame condition is "stable along the run's world change". For Core that
  is `hR` (lists with the same members); for the chain it is `gN` down the index at the same `Θ`
  (G11), and the consistency of the split parts (G12) goes into the field G1. The proof is the
  same for both: **A works**.
- **`lam`** (8 lines in Core). Core's proof uses `cC_head` and `gDenC_mk` only, because Core's
  `cC .arr` is a plain wand. The chain's `⊸` is Kripke along `ExtR` and the index (F10), so the
  chain's proof has two more steps: G6 and G11 at the argument's world. An abstract `⊸` field
  would have to quantify over an order, with Core's instance taking `Eq`. That restates Core's
  printed proof with steps it does not take: **A distorts it**.
- **`withbor1U`** (75 lines in Core; proved on the chain). Core moves the list (`AddAt`, the Imm
  Frame's `fresh … ∀ ls′, AddAt ls ls′ α → …`). The chain moves the world (`addImm`), reads the run
  at the lender's view (`erwp_tieEntry`), and returns by `extR_of_addImm`. No common field
  statement covers both without designing a new abstraction: **A does not apply**.

The same holds for every departed entry (R1–R8, R11, K3, K4, V10): the 11 borrow rows and the
slice rows.

The cost of A, concretely:
1. Core's compatibility proofs (about 2,800 non-blank lines over the 104 rows) unfold `vC`/`wpTS`/`gDenC` definitionally
   (`show wpTS ls …`, `obtain ⟨…⟩ := gDenC_iff.mp hg`, taking `vC (.tensor A B)` apart). Every
   such unfolding becomes a field (a clause `iff`), and Core's file must be rewritten against the
   fields. That edits Core's printed proofs, which is the thing the port is meant to follow.
2. Two instances must be proved: Core's from existing lemmas (cheap), the chain's from the layer
   (the layer itself).
3. The fields at the departed entries need new statements general over both worlds. That is
   design work on the borrow rows, which are the rows where the chain's departures are recorded.

**Option B: a line-by-line port against chain lemmas named after Core's.** For each Core helper,
build one chain lemma with Core's shape and the chain's extra obligations folded in:
- `gN_split` returns the parts' consistency (G1 with G12);
- `erwp_bind_frame` takes the frame at every lower index (W4 with G11).

Each rule's chain proof then follows Core's line for line (`tensorI_compatN` is `tensorI_compatC`
with `gDenC_split ↦ gN_split`, `wpTS_bind_frame ↦ erwp_bind_frame`). The extra binders of `SemJN`
(`Θ`, `c`, `n`, `Θ.OK`, `ConsistentX`) are introduced and passed in the same places in every rule.
A rule's port is about the length of Core's proof plus those binders. For the 61 in-fragment
rows outside the borrow group that are not yet proved, Core's proofs come to about 1,090 lines.
The borrow rows are already ported this way (`ImmLend833N.lean`, `Reborrow791N.lean`, `Withload791N.lean`).

**Recommendation: B, with the shared steps factored as in A.** The interface is a set of chain
lemmas with Core's names and shapes (§2's "Chain counterpart" column), not a Lean structure.
Within the chain, the steps that recur across rules are stated once, as lemmas that each rule
calls:
- the context split with its consistency;
- the bind frame with its index;
- the `SemJN` introduction;
- `cN_bind`.

The second copy that A would avoid is a copy of Core's proof text, which is what the port is
meant to follow. A would save it only for the structural rows (about 45). The price is rewriting
Core's file and designing the fields at the departed entries, and the departed entries are where
the work is. Parity with `main` remains the merge bar either way.

## 5. Units

These replace the rule-group units #834–#837. They are ordered by uncertainty first (each unit
starts with its hardest case), then by the number of rules unblocked. The counts below are
cumulative, simulated from §3's table: a rule is unblocked once every entry it uses is built.

| Unit | Builds | Hardest case (first) | Rules then mechanical | Effort |
|---|---|---|---|---|
| **L1: context and bind** | G1 with G12, G2, G4, G6, G7, G8, G9, G11, K5, W4, C2 (`cN_bind`), W7, V8, F2 (`bang_app`), F4 (`host_call_sound` at `vN`) | G12 at a conclusion that is not `F`/`F_Σ` (map G7: not verified), and `cN_bind`'s `⊸` case under F10 | 25, beyond the 22 mechanical now: `var`, `tensorI`, `thunkF`, `thunkV`, `bind`, `force`, `lam`, `lamDead`, `app`, `unitE`, `tensorE`, `sumE`, `zeroE`, `bangThunkF`, `bangThunkV`, `boxI`, `lit`, `hostOp`, `countFold`, `countTry`, `lolliE`, and the borrow rows `withbor3`, `withload`, `withloadU`, `withswap` | medium |
| **L2: type equality** | V1 (`vN_tyEq`/`cN_tyEq`, Core's `Alpha.lean`/`RelationFacts.lean` induction) | the `Imm`/`Mut` clauses under `TyEq` (`ImmWitW`'s `CohE`, `mutL`'s family) | `allE`, `allEV`, `alpha` | medium (map: a third of the structural unit) |
| **L3: the unwinding anti-frame** | R3 | the twin of a `Row.Unwind` row for `erwp_M_antiFrameCR` | `withbor3U` | small to medium |
| **L4: effects and handlers** | E12 first, then E3, E5, E6, E7, E8, E9 (`erwp_ubind` with `hP`/`hU`/`ThenLe`, a `Div` finaliser row), E10 (the clauses' reading, the table split, the tail and last instances), E14, W9 | **E12** (BOXED-κ stop lemma at `erwp`): missing, unclear | 13: `iterate`, `divFuel`, `effSub`, `effPerform`, `effAwait`, `effRaise`, `effLet`, `effThen`, `effThenDiv`, `effHandleV`, `effHandleT`, `effHandleL`, and `effHandleVB` if E12 is derived | high |
| **L5: opaque types and families** | F5, F6, F7 | F7 across stops (one key per cell, the twin per layer) | 23: `tokMint`, `tokBurn`, the 8 array rows, the 11 slice rows, `sliceBorrowMU`, `sliceBorrowIU` | high (F5 small) |
| **L6: `μ`** | F8 | the environment argument in `vN`/`vO` and Core's `RelMu` laws at the index | `roll`, `unroll`, `foldImm`, `foldOwn`, `foldReuse`, `foldOwnG` | very high |
| **L7: `ν`** | F9 | the reading of `ν` at `erwp` (a design choice first) | `nuIn`, `nuOut`, `unfoldN`, `reify` | high |

`FundamentalN` on the fragment needs L1–L4. The *cut* rows need L5–L7 wherever a derivation
passes through an excluded former. L1 and L4 are independent and can run in parallel. L2 and L3
need only L1's W4/G6.

No interface departure is without a configuration: K4/V10 and E13 are settled in §6.3, and F10
returned to Core's reading in #834 (§8.1).

## 6. The concerns and the departure check

### 6.1 `erwp_tieEntry` and an inner location typing

`erwp_tieEntry` (`ImmLend833N.lean`) reads a run at a world with more `imm` records as a run at
the lender's. Its premise `hab` asks every entry of the table to be abortive. A run at a world
with extra records arises only where the world gains an `imm` record that the lender's view
lacks, which is an `imm` lend's callback. Core's proofs that do this are exactly the ones that
reach `ext_add` (K3) or the Imm Frame (R5):
- `withbor1`, at the pure row;
- `withbor1U`, at a `Row.Unwind` row, whose entries are all abortive (`Row.Unwind.abort`,
  `tabN_unwind_abort`);
- `sliceBorrowI`/`sliceBorrowIU`: the same two rows, outside the fragment.

`CDerives` has no `imm` lend at a row whose table resumes. `withbor1U` and `sliceBorrowIU`
require `S.Unwind x`, and no `Const791` lends `imm` at `Row.Suspend`: its five constructors are
`w2`, `w3`, `wF`, `wl` and `sm`, which are `mut` lends and reborrows. `withload`'s images are witnessed by the source's record, already in the
world (`chain-interpretation.md` §6.3, `wl` step 8), so it adds none. A handler's resumption inside a callback is a step of the
callback's own expression at its own world, and that world is the one its view reads.

**Verdict: no rule needs the generalisation to an inner location typing.** It would be needed by
an `imm` lend whose callback may suspend, which is not among the 104 constructors or the
constants.

### 6.2 `Keeps` by lifetime against Core's `Rel` by location

Core's `Keeps rs rs′ ρ := ∀ r ∈ rs, Rel r ρ → r ∈ rs′` (`Core/FrameRecords.lean`) reads relevance
off the location: `ρ` has an `imm` cell at `r.le` or at a chain position of `r`. The chain's
`LocTy.Keeps Θ Θ′ ρ := ∀ x ∈ Θ.imm, CellIn ρ x.2 → x ∈ Θ′.imm` reads it off the lifetime the
record was lent at.

Where the two readings meet a proof: Core uses `Keeps` through `ext_drop`, whose premise `hk` it
discharges inside the Imm Frame (`FrameRules.lean:266/302`, `EffWp.lean:283/319`) by
`not_rel_lineage`, from the run's `FrameLife`, `AgW` and `ICpAt`. Under the location reading the
chain's `extR_of_addImm` would carry that premise, and it would be discharged at the same exit of
`erwp_I_frame*`, whose run carries `TW` and the tags at its entry (`ImmTieL`, `Tagged`). By
inspection, the unpremised `extR_of_addImm` would fail under the location reading. Take
`ρ = ℓ ↦ imm({β}, …)` with `β ⊐ α`, at the record's own location: it is in `Res_α` and `Rel r ρ`
holds. That configuration is not built, and it says nothing about Core's route, which never asks
the unpremised statement.

The verdict is in §6.3.

### 6.3 The departure check (`Core/Chain/Depart831N.lean`)

**K4/V10: the departure stays, with a configuration.**

The chain has two record carriers.
- *The run's list `ls`.* Here the chain follows Core: `erwp_I_frameR`'s `hQ` is Core's `Ext` on
  lists, and its exit discharges `ext_drop`'s premise with `not_rel_lineage`, as Core's
  `ewpTS_I_frameU` does. The run does supply Core's premise here.
- *The world's records `Θ.imm`.* `vN`'s `Imm` clause reads these, and the lifetime reading of
  `Keeps` is used only here.

`LocTy.extR_of_addImm` is used at the world in three places:
1. `tabN_unwind_eq` (`ImmLend833N.lean`). This identifies the callback's table at `Θ + (p, α)`
   with the lender's at `Θ`. It moves every value of every operation's argument type in `Res_α`
   across the two worlds. A table is a function of the world and the view, with no run, so there
   is no `FrameLife`, `AgW` or `ICpAt` for `not_rel_lineage` to read.
2. and 3. The callback's result at the Imm Frame's exit, in `withbor1U_sem` and `withbor1_sem`.
   This is transported by `erwp_mono_le`, which sees the postcondition only.

Core has no counterpart of (1), because Core's table does not read the list (`Row.tab_local`,
`hS.tab_extend`). It moves a stop's argument along `Ext` inside the frame instead (`opTable_ext`
at `hQ`).

The configuration covers (1):
- `LocTy.KeepsLoc` is Core's `Keeps` on `rsOf Θ.imm`, and `LocTy.ExtRLoc` is `ExtR` with that
  record conjunct.
- `UnwindArgStepLoc` is the step `tabN_unwind_eq` takes, read by location, at every value of an
  `Imm` type at the world with the record, in `Res_α`.
- `not_unwindArgStepLoc` shows it fails.
- `unwindArg_inst` discharges every hypothesis. It uses an `OK` world with one record
  `q = (ℓ ↦ own(loc ℓ′))`, lent at `γ = 1` at type `Ref 1`, and a record `p ≠ q` at `ℓ`, lent at
  `α = 2 ⊏ γ`. The resource `ℓ ↦ imm({γ}, loc ℓ′, ℓ′ ↦ own(()))` is a value of `Imm 'y (Ref 1)`
  at `δ['y ↦ γ]` at `Θ + (p, α)`, witnessed by `q`, and it lies in `Res_α`. By location `Rel p ρ`
  holds and `p` is not in `Θ`, so `ExtRLoc` fails. By lifetime the same step holds
  (`LocTy.extR_of_addImm`).
- This configures the step, not `tabN_unwind_eq`. A configuration of the lemma itself would need
  a second `vN` built on `ExtRLoc`.

What reverting would touch, so it is not local:
- `LocTy.Keeps` and `ExtR`.
- `extR_of_addImm`: it gains `hk`.
- `extR_above`: under the location reading it needs every record relevant to `ρ ∈ Res_a` to be
  lent above `a`. Its `vN_above.mpr` uses in the `mut` lends (`ImmLend833N.lean`,
  `Cancel791N.lean`) would follow Core's `strat_fresh` instead, with the lend's lifetime chosen
  below every record.
- `vN_extR`'s `Imm` case: `ImmWitW`'s witness is a descendant `d` of a world record, and `Rel`
  at the root does not see `d`'s location.
- `tabN_unwind_eq`: it would have to be replaced by a stop-level transport inside the frame, which
  means restating `erwp_I_frameR` and `erwp_tieEntry` with a world-level `hQ`.
- `withbor1_sem`/`withbor1U_sem` and the `w2`/`w3` constants.

These carry the #833 borrow rows and `constN_*`, so the stop rule applies and the departure is
kept. V10's lifetime match stays with it. Under the lifetime reading it is what makes a witness
relevant to its cell.

**E13: forced by `erwp`'s definition.**

Core's `ewpTS` is a least fixed point. A run that ticks forever is not in it, so at a row that
holds `Div` Core takes the greatest fixed point over segments (`cwp`, `Core/DivDefs.lean`).
`erwp` at `n` constrains only the runs of fewer than `n` steps that reach a final configuration.
So a computation with no final configuration is in `erwp` at every index, at every table and
postcondition (`erwp_of_noFinal`), and there is nothing for a greatest fixed point to add.

Core's split on `Row.divB` appears in two places:
- *Between `CDerives` constructors* (`effThen` and `effThenDiv`). This is a case of the
  induction and stays as printed.
- *Inside the relation* (`effWp`'s two branches, and the handler lemmas `ewp_handle_*` against
  `cwp_handle_*`). On the chain both branches are `erwp` at the row's table (`cN_effOf_divB`, at
  either value of `Row.divB`), and the port keeps the split (§3.3).

One consequence: Core's `Closing` (a close is followed by finitely many ticks, each answered
close) is a least fixed point. `fuel_total` reads it to conclude `ewpTS` after `div_fuel`. `erwp`
states no termination, so on the chain the content of `Closing` has no counterpart. The chain
port of `divFuel` concludes `erwp`, which does not need it. That port is not done.

**Bookkeeping for this check.**
- Unspent printed hypotheses: none. No printed statement was restated.
- Unused uniqueness or functionality results: none.
- Untranscribed in the run-up: the world-level `hQ` for `erwp_I_frameR` that a revert would need,
  and the port of `divFuel` (E8, E14).

## 7. Bookkeeping

- **Unspent printed hypotheses.** This is a map only; no rule was proved. `withload`'s V1 is read
  as discharged inside `withloadS_compat` by inspection.
- **Unused uniqueness or functionality results.** None was needed.
- **Untranscribed in the run-up.** These are the entries marked missing or departed-to-build in
  §2: G1, G2, G4, G6–G9, G11, G12, W4, W7, W9, K5, C2, V1, V8, F2, F4–F9, R3, E3, E5–E10, E12,
  E14. Of these, F9 and E12 are not derived; obstruction not verified.
- No Lean was written for this step.

## 8. Built in #834 (units L1 and L2)

### 8.1 F10: `⊸` is Core's plain wand

`cN .arr A C` at `(Θ, n, ρ)` is now: at every view `c′`, every `k ≤ n`, every argument `v` with
`vN A δ Θ k v ρv` and every composite `ρ′` consistent with `c′`, `cN C δ Θ c′ k ls (e v) ρ′`. The
world is the function's own, as in Core's `cC .arr`; the index is the chain's step-indexed `−∗`,
the view the chain's `ConsistentX`. Every headline kept its statement: `constN_*` and their
`_inst` through `withbor2S_compat`, `withbor3S_compat`, `withborFS_compat`, `withloadS_compat`,
and the #833 borrow rows (`withbor1_compatN`, `withbor1U_compatN`, `withbor2_compatN`,
`withbor2U_compatN`). The proofs lost steps: each applied the wand at the world `U` had already
reached, by `ExtR` reflexivity. No configuration forces the Kripke reading.

Restated: `noEffSpine` excludes `⊸`, so `cN_extA` no longer covers it (a plain wand at `Θ` reads
its argument at `Θ`; an argument at an extension is not one at `Θ`). `cN_extA` has no caller.
`ExtRLit791.vUgen` reads the order at `U` only; `extRL_breaks_extA` stands as stated.

### 8.2 The interface (`Core/Chain/Iface834N.lean`, `Core/Chain/TyEq834N.lean`)

| ID | Chain lemma |
|---|---|
| G1/G12 | `gN_split`; `gN_splitC` (the parts consistent with the view at a valid resource) |
| G12 at a conclusion not `F`/`F_Σ` | `cN_of_valid`: a computation at a type with a reading at every spine position (`noNuSpine`, every former but `ν`; `noNuSpine_of_inFrag`) may assume its resource valid |
| G2 | `gN_soloP` |
| G4 | `gN_persistent`, `gN_cons_persistent` |
| G6 | `gN_extR` |
| G7 | `gN_outlives` |
| G8 | `gN_congr` |
| G9 | `gN_noOwn` |
| G11 | `gN_le` |
| K5 | `LocTy.extR_empty` |
| W4 | `erwp_bind_frame` (the inner run at the empty table, any outer local table; the continuation at the index the run leaves, the returned resource consistent and valid) |
| C2 | `cN_bind`, by induction on `C` with `noNuSpine C` |
| W7 | `rwp_box`, `erwp_box` |
| V8 | `vN_noOwn_of_ownFree` |
| F2 | `bang_app` (at any later world) |
| F4 | `host_call_sound` at `vN`, through `vN_iff_vP` at the first-order types |
| V1 | `vN_tyEq`, `vO_tyEq`, `cN_tyEq`, `tabN_tyEq`, `finN_tyEq`, `retN_tyEq` |

The hardest case, G12 at a conclusion that is not `F`/`F_Σ`, is `cN_of_valid`: at `⊸` the resource
is a part of the composite the wand runs from. It needs the conclusion to have a reading: `cN` at
`ν` is `False` (outside the fragment, F9), where validity cannot be assumed. The compatibility
lemmas whose proof reads it (`app`, `bind`, `unitE`, `tensorE`, `sumE`, `zeroE`) carry
`noNuSpine C`; `FundamentalN` quantifies over in-fragment judgments, which give it.

### 8.3 The rules ported (`Core/Chain/Rules834N.lean`, `Borrow834N.lean`, `Count834N.lean`)

`var_compatN`, `tensorI_compatN`, `thunkF_compatN`, `thunkV_compatN`, `force_compatN`,
`lam_compatN`, `lamDead_compatN`, `app_compatN`, `bind_compatN`, `unitE_compatN`,
`tensorE_compatN`, `sumE_compatN`, `zeroE_compatN`, `bangThunkF_compatN`, `bangThunkV_compatN`,
`boxI_compatN`, `lit_compatN`, `hostOp_compatN`, `lolliE_compatN`, `countFold_compatN`
(`countLoop_wpN`), `countTry_compatN` (`countTryLoop_wpN`), `allE_compatN`, `allEV_compatN`,
`alpha_compatN`; the borrow rows `withbor3_compatN` (the anti-frame and the Mut Frame together,
`erwp_withbor3` at the empty table), `withload_compatN` (`withload_reb` at the empty row with the
pure callback, `callback_at_imageP`), `withswap_compatN` (`erwp_M_antiFrame` at the view).

Restated: `withload_reb` takes the bound's definedness at the run's `δ` (was `∅ ⊨ @bnd`) and the
callback's run at the image as a premise (was the suspending callback's value);
`withloadS_compat` supplies `callback_at_image`, its statement unchanged.

### 8.4 Not ported

- **`withloadU`**: `erwp_rebGen` asks every entry of the table to be other than `unr`
  (`OpTabN.RebOKR.entry`); `Row.Unwind` admits an abortive `unr` operation. Not derived;
  obstruction not verified.

