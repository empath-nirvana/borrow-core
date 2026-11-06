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
| W9 | `wpTS_val_post` | — | 5: `reify`, `effHandleV`, `effHandleVB`, `effHandleT` … | **built** (#835: `erwp_val_post`) | map E9: `vN` read off a value's `cN (.ret A)`, from `erwp_unfold_at` at `.val v` |

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
| F5 | `rel_tok_intro`, `rel_cases`, `tok_not_host` | — | 2: `tokMint`, `tokBurn` | **same** (#836) | `vN`/`vO` at `opq k` read Core's `k.rel`; Core's lemmas used as they are (§9.2) |
| F6 | `vP_fam_mk`, `vP_fam_split`, `vP_fam_idx`, `sepRange_pick` … | spec §9 | 22: `arrNew`, `arrFree`, `arrSize`, `arrReplace` … | **same** (#836), but the `tab` step | `vN`/`vO` at `[L]` Core's `sepRange` clause; `vN_fam_iff`/`_mk`/`_idx`/`_split`, `noOwn_famN`; the laws re-proved over it (§9.2). The `tab` step at the index (`arrNew`) is missing, buildable |
| F7 | `wpTS_M_frameFam`, `wpTS_I_frameFam`, `wpG_M_frameFam`, `wpG_I_frameFam` | — | 4: `sliceBorrowM`, `sliceBorrowI`, `sliceBorrowMU`, `sliceBorrowIU` | **departed, to build** (#836) | `wpTS_M_frameFam` is `rwp_M_frameListN` (built). Across raises, the one-cell frame under inner claims `erwp_M_frameRR` is built; its list induction, the cancel-run counterpart and the Imm family frames are missing, buildable (§9.3) |
| F8 | `vC_roll`, `vC_unfold`, `vC_immReborrow_mu_iff`, `vCE_subst` … | — | 8: `reify`, `roll`, `unroll`, `foldImm` … | **same** (#836 L6) | `vNE`/`vOE` under a type-variable environment, `vN`/`vO` at the empty one; the `μ`/`tvar` clauses; Core's `RelMu` at the chain (`vN_mu_iff`, `vN_ind`, `vBN_subst`, `vBN_mono_at`, …); `withload_sized` is `withload_sizedN` (§13) |
| F10 | `cC` .arr (the `⊸` clause) | — | 10: `bind`, `lam`, `lamDead`, `app` … | **same** (#834) | `cN .arr` is Core's plain wand at the function's own world, read at every later index and every view consistent with the composite (§8.1). The Kripke reading along `ExtR` is gone: no configuration forced it |
| F9 | `cC_nu_iff`, `nuRel_coind`, `cB_step` | spec §7 | 4: `reify`, `nuIn`, `nuOut`, `unfoldN` | **missing, unclear** | a reading of `ν` at `erwp`: a design choice first. Not derived; obstruction not verified |

### R. Frames, the reborrow theorem, the chooser, the cells

| ID | Core lemma | [TR] | Rules | Status | Chain counterpart |
|---|---|---|---|---|---|
| R1 | `wpTS_M_frameX`, `ewpTS_M_frameU` | 6.65 | 3: `withbor2`, `withbor3`, `withbor2U` | **departed (built)** | `erwp_M_frame` (`SI/StopFrameN.lean`), `erwp_M_frameR` (raises, `SI/StopRaiseN.lean`), `erwp_M_frameCR`/`CRG` (cancel runs): the lend's key in the world `Φ[ℓ ↦ (A, F)]`, not `ptoMutS ℓ α ls₀`. Configurations: `perLocShape_not_reborrow`, `reseal_untyped`, `coreMutImm_not_extF` |
| R2 | `wpTS_M_antiFrameX` | 6.66 | 4: `sliceReplaceM`, `sliceSwapM`, `withbor3`, `withswap` | **departed (built)** | `erwp_M_antiFrame` (`SI/AntiStopN.lean`) at the view: `erwp_antiFrame_view`, `reseal_at_entry` (`SI/LocTy.lean`). Configuration: `reseal_untyped` |
| R3 | `ewpTS_M_antiFrameU` | 6.66 | 1: `withbor3U` | **departed (built)** | `erwp_M_antiFrameU` (`Unwind833N.lean`): `erwp_M_antiFrameCR` with the row's own table as its twin (`OpTabN.Twin.refl`). Every entry of a `Row.Unwind` row is abortive (`tabN_unwind_abort`), so the twin guards no stop and no cancel obligation is transferred; only the raises' claim (`hRin`/`hRout`) remains |
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
| E3 | `effWp_sub`, `ewp_sub`, `finLe_iff`, `cancelObl_le` | — | 6: `effSub`, `effAwait`, `effThen`, `effThenDiv` … | **built** (#835: `tabN_le_of_rowLe`, `erwp_rowLe`) | `erwp_tabLe` (`SI/TabLeN.lean`) is there; `RowLe S S′ → OpTabN.Le (tabN …)` is missing, buildable (map E1) |
| E4 | `opTable_mono`, `opTable_abortive`, `tab_local`, `tab_zero` … | — | 21: `iterate`, `divFuel`, `reify`, `withbor1U` … | **same** | `opTableN_le`, `opTableN_local`, `opTableN_down`, `tabN_effOf_some`, `tab_lookupN`, `tabN_unwind_abort` |
| E5 | `ewp_bind_pure_frame` | spec §19 | 3: `effPerform`, `effAwait`, `effRaise` | **built** (#835: `erwp_bind_pure_frame`, `tabN_ctxClosed`) | `erwp_bind` with `T.CtxClosed K`: `tabN`'s `CtxClosed` at a context with no handler or catcher is missing, buildable (map E3) |
| E6 | `ewp_perform_here`, `ent_start`, `cancelObl_start` | spec §19 | 2: `effPerform`, `effAwait` | **built** (#835: `erwp_perform_here`, `entN_start`) | `erwp_performG` (`SI/LendCancelProg.lean`), `erwp_perform`; `cancelOKN` at the empty context (`ent_start`) missing, buildable (map E2) |
| E7 | `ewp_raise_here` | spec §19 | 2: `effAwait`, `effRaise` | **built** (#835: `erwp_raise_here`) | a raise's introduction at `raiseStopN`: built inline in `erwp_handle`'s proof (`SI/HandleN.lean`), to be stated (map E4) |
| E8 | `ewp_frame_plain`, `ent_plain`, `cancel_frame`, `cancel_frame_consume` … | spec §27 | 10: `iterate`, `divFuel`, `reify`, `unfoldN` … | **built** (#835: `erwp_frame_plain`, `entN_plain`, `tabN_plainCancel`) | the frame at a row's table: owning across must-resume stops, owning nothing where the row cancels, empty at an unrestricted row; `erwpG_frame`, `erwp_frameL` are special cases (map E5) |
| E9 | `ewp_frame_then`, `ewp_frame_then_or`, `cwp_then`, `cwp_then_div` … | — | 3: `effThen`, `effThenDiv`, `effHandleL` | **not built** (#835 §9.4) | `erwp_ubind` (`SI/UbindGN.lean`) and its cancel/raise/claim companions are stated without unrestricted operations in `Σ_M` and at a finaliser meeting `FinOK`; Core's `hP`/`hU`/`ThenLe` form and a finaliser row holding `Div` are missing, buildable (map E6, E7) |
| E10 | `ewp_handle_vals`, `ewp_handle_valsB`, `ewp_handle_tail`, `ewp_handle_last` … | — | 4: `effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL` | **not derived** (#835 §9.1: the clauses at `vN`; the tail and last instances not built) | `erwp_handle` (`SI/HandleN.lean`; needs no `hdv`), `erwp_kappa_*`; the clauses' reading at `vN` and the split of `tabN (ofEff n E 0 fs ++ S)` (map E8), the tail and last instances (map E11): missing, buildable |
| E11 | `ewp_kappaC_resume`, `ewp_kappaC_cancel`, `ewp_kappaCell`, `ewp_kappa_resume` … | — | 3: `divFuel`, `reify`, `effHandleVB` | **same**; the fuel handler's instances built (#835: `erwp_kappaC_resume_in`, `erwp_hnd_tick`) | `erwp_kappa_resume`, `erwp_kappaC_resume`, `erwp_kappa_cancel`, `erwp_kappaC_cancel`, `erwp_kappaCell`, `erwp_ccatch` (`SI/HandleN.lean`) |
| E12 | `stop_sem` | spec §28 | 1: `effHandleVB` | **built** (#835: `stop_semN`, `erwp_handleS`) | the BOXED-κ stop lemma at `erwp` (map E10). Not derived; obstruction not verified |
| E13 | `cwp_bind`, `cwp_of_ewp`, `effWp_of_ewp`, `cwp_out` … | spec §14 | 21: `iterate`, `divFuel`, `reify`, `withbor1U` … | **departed, forced by `erwp`** | a `Div` row is a row of the table; `erwp` is step-indexed, so Core's coinductive `cwp` and its bookkeeping have no counterpart, and each `cwp` branch is the `ewp` branch's `erwp` lemma. Reason: `Depart831N.erwp_of_noFinal`; the split: `Depart831N.cN_effOf_divB` (§6.3) |
| E14 | `cwp_iterate` | spec §14 | 1: `iterate` | **built** (#835: `erwp_iterateC`) | `erwp_iterate` (`SI/LoopN.lean`) is stated where the tick always answers *next*; the version answering in `vN nextTy` (the close branch) is missing, buildable from its induction |

### 2.1 Counts

| Status | Entries |
|---|---|
| same | 40 (F5, F6 in #836) |
| departed (built) | 12 (K1, K3, K4, V10, R1, R2, R3, R4, R5, R7, R8, R11) |
| departed, forced by `erwp`'s definition | 1 (E13) |
| departed, no configuration | 0 |
| departed, to build | 7 (E3, E5, E6, E9, E10, E14, F7) |
| missing, buildable | 21 |
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
| 35 | `tokMint` | no | out | W1 W6 H1 G3 F5 | F5 | proved (#836) |  |
| 36 | `tokBurn` | no | out | W1 W6 H2 G3 F5 | F5 | proved (#836) |  |
| 37 | `swap` | yes | portable | W1 W2 W6 H3 H5 K1 G3 F1 | — | mechanical now |  |
| 38 | `copy` | yes | portable | W1 W6 G3 F1 R10 | — | mechanical now |  |
| 39 | `releaseImm` | yes | portable | W1 W6 H6 G3 | — | mechanical now |  |
| 40 | `releaseMut` | yes | portable | W1 W6 H7 G3 | — | mechanical now |  |
| 41 | `releaseUnk` | yes | portable | W1 W6 G3 | — | mechanical now |  |
| 42 | `lit` | yes | portable | W1 G3 F4 | F4 | mechanical once built | `vP_lit` (F4) |
| 43 | `hostOp` | yes | portable | W1 W6 G3 F4 | F4 | mechanical once built | `host_call_sound` (F4) |
| 44 | `arrNew` | no | out | W1 W2 W4 W6 H5 K2 V11 G3 F1 F2 F6 | W4 F2 F6 | mechanical once built |  |
| 45 | `arrFree` | no | out | W1 W2 W4 W6 H2 K2 V11 G3 F2 F6 | W4 F2 F6 | proved (#836) |  |
| 46 | `arrSize` | no | out | W1 W6 G3 F1 F6 | F6 | proved (#836) |  |
| 47 | `arrReplace` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 | F6 | proved (#836) |  |
| 48 | `arrLen` | no | out | W1 W5 W6 G3 F6 | F6 | proved (#836) |  |
| 49 | `arrGet` | no | out | W1 W5 W6 G3 F1 F6 | F6 | proved (#836) |  |
| 50 | `arrCopy` | no | out | W1 W6 G3 F1 F6 R10 | F6 | proved (#836) |  |
| 51 | `arrRelease` | no | out | W1 W5 W6 G3 F6 | F6 | proved (#836) |  |
| 52 | `countFold` | yes | portable | W1 W4 W6 K2 V11 G3 F1 F2 | W4 F2 | mechanical once built | `countLoop_wp` (induction on `len − i`) |
| 53 | `countTry` | yes | portable | W1 W4 W6 K2 V11 G3 F1 F2 | W4 F2 | mechanical once built | `countTryLoop_wp` |
| 54 | `boundedFix` | yes | portable | W1 G3 C1 F1 | — | mechanical now | `fixSelf_valid`, `cC_boundedFix` along `ExtR` |
| 55 | `iterate` | yes | portable | W1 K1 K5 G3 C3 E1 E2 E4 E8 E13 E14 | K5 E8 E14 | waits: answer consistency (§9.2) | `cwp_iterate` → E14 |
| 56 | `divFuel` | yes | portable | W1 G3 C3 E1 E2 E4 E8 E11 E13 | E8 | proved (`divFuel_compatN`) | `fuel_total`, `divFuel_steps`, `fuelK_frame` |
| 57 | `reify` | no | out | W1 W9 K1 K5 V4 G3 C3 F8 F9 E1 E2 E4 E8 E11 E13 | W9 K5 F8 F9 E8 | waits (unclear) | `reify_compat` |
| 58 | `sliceBorrowM` | no | out | W1 W2 W3 W4 W6 K1 K2 V3 V6 V11 G3 F1 F6 F7 | W4 F6 F7 | proved (#836) |  |
| 59 | `sliceBorrowI` | no | out | W1 W2 W3 W4 W6 K1 K2 V3 V6 V7 V10 V11 G3 F1 F6 F7 R5 | W4 F6 F7 | mechanical once built |  |
| 60 | `sliceGetM` | no | out | W1 W5 W6 G3 F6 | F6 | proved (#836) |  |
| 61 | `sliceLenM` | no | out | W1 W6 G3 F6 | F6 | proved (#836) |  |
| 62 | `sliceSplitI` | no | out | W1 W6 G3 F6 | F6 | proved (#836) |  |
| 63 | `sliceSplitM` | no | out | W1 W6 G3 F6 | F6 | proved (#836) |  |
| 64 | `sliceEmptyI` | no | out | W1 G3 F6 | F6 | proved (#836) |  |
| 65 | `sliceEmptyM` | no | out | W1 G3 F6 | F6 | proved (#836) |  |
| 66 | `arrEmpty` | no | out | W1 G3 F6 | F6 | proved (#836) |  |
| 67 | `sliceReplaceM` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 R2 | F6 | mechanical once built |  |
| 68 | `sliceSwapM` | no | out | W1 W2 W6 H3 H5 G3 F1 F6 R2 | F6 | mechanical once built |  |
| 69 | `withbor1` | yes | proved | W1 W2 W3 W4 W6 K1 K2 K3 V3 V7 V10 V11 G3 F1 R5 | — (proved with chain lemmas inline) | proved |  |
| 70 | `withbor2` | yes | proved | W1 W2 W3 W4 W6 K1 K2 V3 V6 V11 G3 F1 R1 | — (proved with chain lemmas inline) | proved |  |
| 71 | `withbor3` | yes | portable | W1 W2 W3 W4 W6 K1 K2 V3 V11 G3 F1 R1 R2 | W4 | mechanical once built | `withbor3S_compat` (`Reborrow791N.lean`) at the empty table |
| 72 | `withload` | yes | portable | W1 W2 W3 W4 W6 H4 K1 K2 V1 V2 V3 V11 G3 F1 F3 R7 R8 | W4 (V1 is inside `withloadS_compat`) | mechanical once built | `withloadS_compat` (`Withload791N.lean`) at the empty table |
| 73 | `withswap` | yes | portable | W1 W2 W4 W6 H3 H5 K1 V11 G3 F1 R2 | W4 | mechanical once built | `withswap_compatX`'s anti-frame and reseal (as `withbor3S_compat` step 13) |
| 74 | `withbor1U` | yes | proved | W1 W4 W6 W8 K1 K2 K3 K5 K6 V3 V7 V10 V11 G3 G6 G10 C3 F1 R5 R6 R11 E1 E2 E4 E13 | — (proved with chain lemmas inline) | proved |  |
| 75 | `withbor2U` | yes | proved | W1 W4 W6 W8 K2 K5 V3 V6 V11 G3 G6 G10 C3 F1 R1 R6 R11 E1 E2 E4 E13 | — (proved with chain lemmas inline) | proved |  |
| 76 | `withbor3U` | yes | proved | W1 W4 W6 W8 K2 K5 V3 V11 G3 G6 G10 C3 F1 R3 R4 R6 R11 E1 E2 E4 E13 | — (`withbor3U_compatN`, `Unwind833N.lean`) | proved | `withbor3S_compat`'s steps at an unwinding row |
| 77 | `withloadU` | yes | proved | W1 W8 H4 V1 V2 V3 G3 C3 F3 R6 R7 R8 R11 E1 E2 E4 E13 | — (`withloadU_compatN`, `Unwind833N.lean`) | proved | `withloadS_compat`'s steps at an unwinding row |
| 78 | `sliceBorrowMU` | no | out | W1 W4 W6 W8 K2 K5 V3 V6 V11 G3 G6 G10 C3 F1 F6 F7 R6 R11 E1 E2 E4 E13 | W4 K5 G6 F6 F7 | mechanical once built |  |
| 79 | `sliceBorrowIU` | no | out | W1 W4 W6 W8 K1 K2 K5 K6 V3 V6 V7 V10 V11 G3 G6 G10 C3 F1 F6 F7 R5 R6 R11 E1 E2 E4 E13 | W4 K5 G6 F6 F7 | mechanical once built |  |
| 80 | `lolliE` | cut | portable | W2 W4 K1 K2 V11 G1 G5 G6 G11 G12 F10 | W4 G1 G6 G11 G12 | mechanical once built |  |
| 81 | `allEV` | yes | portable | W2 W3 V1 F3 | V1 | mechanical once built |  |
| 82 | `ofRet` | yes | portable | — | — | mechanical now |  |
| 83 | `roll` | no | out | W3 F8 | F8 | proved (#836 L6) |  |
| 84 | `unroll` | cut | out | W3 F8 | F8 | proved (#836 L6) |  |
| 85 | `foldImm` | no | out | W1 W2 W3 W4 W6 K1 K2 V2 V3 V4 V5 V11 G3 F3 F8 R8 | W4 F8 | proved (#836 L6) | `foldImmV`, `travK` |
| 86 | `foldOwn` | no | out | W1 W2 W3 W4 W6 H2 K1 K2 V11 G3 F8 | W4 F8 | proved (#836 L6) | `foldOwnV` |
| 87 | `foldReuse` | no | out | W1 W2 W3 W4 W6 H3 H5 K1 K2 V11 G3 F8 | W4 F8 | proved (#836 L6) | `foldReuseV` |
| 88 | `foldOwnG` | no | out | W1 W2 W3 W4 W6 K1 K2 V11 G3 F3 F6 F8 | W4 F6 F8 | proved (#836 L6) | `FoldP` traversal |
| 89 | `nuIn` | no | out | F9 | F9 | waits (unclear) |  |
| 90 | `nuOut` | cut | out | F9 | F9 | waits (unclear) |  |
| 91 | `unfoldN` | no | out | W1 W2 W3 W6 K1 V4 G3 C1 F8 F9 R6 E1 E2 E4 E8 E13 | F8 F9 E8 | waits (unclear) | `nuRel_coind` |
| 92 | `effSub` | yes | portable | C3 E3 E4 E13 | E3 | proved (`sub_compatN`) |  |
| 93 | `effPerform` | yes | portable | C3 E4 E5 E6 E13 | E5 E6 | proved (`perform_compatN`) |  |
| 94 | `effAwait` | yes | portable | W1 K2 V8 V11 G1 G2 G3 G4 G5 G6 G9 G11 G12 C1 C2 C3 F10 R6 E1 E2 E3 E4 E5 E6 E7 E8 E13 | V8 G1 G2 G4 G6 G9 G11 G12 C2 E3 E5 E6 E7 E8 | proved (`await_compatN`) | composes `perform`, `raise`, `sub`, `ret`, `var`, `sumE`, `let` |
| 95 | `effRaise` | yes | portable | C3 E4 E5 E7 E13 | E5 E7 | proved (`raise_compatN`) |  |
| 96 | `effLet` | cut | portable | K2 G1 G4 G5 G6 G9 G11 G12 C3 R6 E1 E2 E4 E8 E13 | G1 G4 G6 G9 G11 G12 E8 | waits: answer consistency (§9.2); `let_compatN_ansC`, `let_compatN_persist` |  |
| 97 | `effThen` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | waits: answer consistency (§9.2), E9 |  |
| 98 | `effThenDiv` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | waits: answer consistency (§9.2), E9 |  |
| 99 | `effHandleV` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 F1 E1 E4 E10 E13 | W9 K5 G1 G11 G12 E10 | waits: E10 (§9.1), answer consistency |  |
| 100 | `effHandleVB` | cut | pending | W9 K5 V5 V9 G1 G3 G7 G11 G12 C3 F1 R6 E1 E4 E10 E11 E12 E13 | W9 K5 G1 G7 G11 G12 E10 E12 | waits: E10 (§9.1), answer consistency; E12 built |  |
| 101 | `effHandleT` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 E1 E2 E3 E4 E8 E10 E13 | W9 K5 G1 G11 G12 E3 E8 E10 | waits: answer consistency (§9.2), E10's tail instance |  |
| 102 | `effHandleL` | cut | portable | W9 K1 K2 K5 V8 V9 G1 G3 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E10 E13 | W9 K5 V8 G1 G11 G12 E3 E8 E9 E10 | waits: answer consistency (§9.2), E9, E10's last instance |  |
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
| `withbor3U` | proved in #833 L3: `withbor3U_compatN` (§9) |
| `withload` | W4, then `withloadS_compat`'s 13 steps (`chain-interpretation.md` §6.3) at the empty table; `erwp_reborrow` for 6.150 |
| `withloadU` | proved in #833 L3: `withloadU_compatN` (§9), with `OpTabN.RebOKR.entry` read at resumable entries only |
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
| **L3: the unwinding anti-frame** | R3 | the twin of a `Row.Unwind` row for `erwp_M_antiFrameCR` | `withbor3U` | small to medium (built, §9) |
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
  Ported in §9.

## 9. Built in #833 (unit L3)

`Core/Chain/Unwind833N.lean`; every rule at any `Δ` and a `Row.Unwind x` row.

| Entry or rule | Chain lemma |
|---|---|
| R3 | `erwp_M_antiFrameU` (Core's `ewpTS_M_antiFrameU`): `erwp_M_antiFrameCR` at `T′ = T` (`OpTabN.Twin.refl`), its `hT` and `hcan` vacuous at a table whose every entry is abortive |
| the row's tables | `tabN_unwind_lendOKCR` (the Mut Frame's table condition), `tabN_unwind_rebOKR` (the reborrow's), `tabN_unwind_rebClosed` (no cancel obligation), `tabN_unwind_extend` (the table reads neither `'x` nor its base) |
| `withbor3U` | `withbor3U_sem`, `withbor3U_compatN`: `withbor3S_compat`'s steps with the bound `Δ.meetOfDom`; the Mut Frame at the row's table (`erwp_M_frameCRG`, the callback's table the lender's by `tabN_unwind_eq_add`); the anti-frame `erwp_M_antiFrameU`; the claim consistent (`erwp_claimX_abort`); the finaliser frame at a raise (`erwp_ubindRaise`, `fin_claimMN`) |
| `withloadU` | `withloadU_sem`, `withloadU_compatN`: `withloadS_compat`'s steps; 6.150 across the row's raises (`withload_rebT`, `erwp_rebGen`); the callback at the image (`callback_at_imageU`) |
| an `unr` row | `unrRaiseRow` (`raise : 1 ↠^unr 0`), `unrRaiseRow_unwind`, `withloadU_unr_inst`: `withloadU_compatN` with every hypothesis discharged at a row whose one entry is unrestricted |

**`unr` at an unwinding row.** `OpTabN.RebOKR.entry` now reads only resumable entries
(`en.abort = false → en.q ≠ unr ∧ en.wc = extF`). `erwp_rebGen` and `erwp_rebGen_cancelRun` read
`entry` only at a stop, whose entry is resumable (`performStopN` carries `en.abort = false`); a
raise never resumes, so the reborrow is never re-entered through it. Their statements are
unchanged but for the structure. `tabN_rebOKR` discharges the guarded field as before.

**Restated.** `OpTabN.RebOKR.entry`: was `T m i = some en → en.q ≠ unr ∧ en.wc = extF`, now with
the premise `en.abort = false`. `withload_rebT` is `withload_reb` with the row's `S.Suspend x bnd`
replaced by the two facts its proof reads of the table: `hTab` (the table is `RebOKR β` at every
`β ⊏ @bnd`) and `hClo` (its cancel obligations are closed under the reborrow at every entry).
`withload_reb` keeps its statement and is `withload_rebT` with `tabN_rebOKR` and `tab_rebClosed`.

The class counts of §3.1 and the map's rows for the rules ported in #834 are as the map left them;
rows 76 and 77 are updated here.

## 10. Built in #835 (unit L4)

Branch `rule-791-l4b`. The paper mapping is `scope-835-handlers.md`. Part 1 (`rule-791-l4`) built
E3, E5–E8, W9, E12, E14 and ported `effSub`, `effPerform`, `effRaise` (`scope-835-handlers.md`
§4). Part 2 is this section.

### 10.1 E10: the clauses read at `vN`

Core's step is `vC_kTy_of_kapRel` (`Core/EffFin.lean`), which `ewp_handle_vals` applies to each
clause: `KapRel` at `ls` is Kripke along `Ext` (`∀ ls′, Ext ls ls′ ρ → …`), because the stop's
share in `opTable` is (`contShare`), and that is exactly `vC`'s `U` at `ls`. In Core one world, the
record list, indexes both the values (`vC … ls`) and the run (`ewpTS ls`), so the two quantifiers
are the same quantifier, and `hk ls′ he` closes the step.

At the chain the world is split. `vN`'s `U` quantifies the value world (`Θ′` with
`Θ.ExtR Θ′ ρ`, `Θ′.OK`), every view consistent with the thunk's resource, and every record list.
`KapRelN` fixes the run's view `Θ.view c` and its tables at `Θ` and `c`, and resumes along `extF`
on the list (D8). So `κ`'s `vN (kTy …)` asks the handled continuation at worlds, views and lists
that its stop does not owe it at. The port of Core's step would make the stop's share Kripke in
the value world as Core's is in `ls` (`contShareN` along `ExtR`), which `erwp`'s fixed view does
not express. F10's plain wand (§8.1) does not change this: it puts the clause's argument pair at the
clause's own world, which `ExtR`'s reflexivity reaches, but `κ`'s own type is `U(…)`, whose clause
still quantifies `Θ′`, the view and the list. Not derived; obstruction not verified.

`effHandleT` and `effHandleL` give the clauses no `κ` and do not need this step; they need §9.2
and the tail and last instances, which are not built.

### 10.2 Answer consistency

`SemJN` reads a judgment at a view `c` consistent with its resource (D7). A rule that runs typed
code after a computation at a row (`effLet`'s `N`, `effThen`'s `N` and `D`, `iterate`'s step on the
next state, a handler's `h_ret` on the handled value) reads that code at the run's view, from the
resource the computation returned. When the computation never stops, that resource is consistent
(`rwp_consistentXV`, as `bind_compatN` reads it). Across a stop it is the continuation's share
beside the answer it was resumed at, and `tabN`'s answers are `vN B δ Θ` at any resource:
`entN`'s `PB` does not read `c`. Core has no view, so Core's proofs have no such step.

- `erwp_consistentAns` (`Core/Chain/Let835N.lean`): a run from a consistent resource, at a table
  whose answers are consistent with `c` (`OpTabN.AnsC c`), returns consistent resources at every
  value across its resumptions.
- `let_compatN_ansC`: Core's `let_compatC`, step for step (`erwp_frame_plain`, `entN_plain`,
  `gN_noOwn`, `gN_persistent`), with one premise Core's rule does not have,
  `hAns : ∀ δ Θ c, (tabN (F_Σ B) δ Θ c).AnsC c`. `tabN_ansC_of_persistent` gives it at a row whose
  answer types are persistent.
- `let_compatN_persist`: the same proof when the bound type is persistent (the bound value owns
  nothing, so `N` starts from the frame's resource, consistent from the start). `await_compatN`
  is its instance.

`let_compatN` without `hAns` is not derived; obstruction not verified. Two routes, both outside
this unit's allowance: answers consistent with the view in `tabN`'s entries (`entN`'s `PB` read at
`c`, which makes `Goal791SchedN`'s hypothesis `SchedOKN` at `rowTabN` ask consistent answers of the
scheduler's clauses), or a side condition on the rules. The rules waiting on this are `effLet`,
`effThen`, `effThenDiv`, `iterate`, and the four handlers.

### 10.3 Rules ported

| Rule | Lemma | File | Core |
|---|---|---|---|
| `divFuel` | `divFuel_compatN` (`fuel_totalN`, `fuel_tick_zeroN`, `fuel_tick_succN`, `erwp_hnd_tick`, `erwp_kappaC_resume_in`, `erwp_pureSteps`) | `Core/Chain/Fuel835N.lean` | `divFuel_compatX` (`fuel_total`, `fuel_tick_zero`, `fuel_tick_succ`, `hnd_tick`, `ewp_kappaC_resume_in`, `ewp_pureSteps`) |
| `effAwait` | `await_compatN` (`let_compatN_persist`, `erwp_idxLe`) | `Core/Chain/Let835N.lean` | `await_compatC` |

`fuel_totalN` inducts on the index alone. Core inducts on the budget and, inside, on `cwp`'s
segment, and treats the spent budget by `Closing` (`fuel_closing`); a `Div` row is a row of the
chain's table (E13), so every tick's continuation is owed below the tick's index whether it is
answered *next* or *close*, and `Closing` has no counterpart. No typed code runs after a
resumption in `div_fuel`: an answer of `Σ` goes back into the callback's own continuation.

### 10.4 Not built

- E9 (`ewp_frame_then_or` with `ThenLe`/`PendLe`, a finaliser that performs and raises): not
  built. `effThen`/`effThenDiv` also wait on §9.2.
- E10's tail and last instances (`ewp_handle_tail`, `ewp_handle_last`): not built.
  `effHandleT`/`effHandleL` also wait on §9.2.
- `iterate`: `erwp_iterateC` (E14) with the invariant `vN St` read at the index; the step's next
  state is read at the loop's view, which §9.2 is.
- `withloadU` (#834 §8.4) is unchanged.

## 11. Unit L5: opaque types and families (#836)

### 11.1 The map

The clauses are Core's (`Core/Relation.lean`): at `opq k`, `k.rel v` (for `Tok` a location owning a
unit cell, `Opaque.rel`); at `[L]`, `v = arr(ℓ, c)`, `c < 2³¹` and `sepRange (λm. 𝒱⟦L⟧(loc m)) ℓ c`.
On the chain both go into `vN` and `vO` as they are, the leaf read at the world and index of the
family (`sepRange` is Core's, `Core/SepRange.lean`). The laws are re-proved over them: a family's
law is the leaf's, lifted by `sepRange_mono_down` (for laws read at a part of the resource:
`vN_extR`, `vN_outlives`, `vN_above`) or `sepRange_mono'`.

Each row, its Core proof, and the chain lemmas it reads (`·N` names are new in this unit):

| Row | Core proof | Chain lemmas |
|---|---|---|
| `tokMint` | `tokMint_compatX` (`Core/Tok.lean`) | `gN_deadP`, `erwp_val`, `erwp_det` (β), `erwp_alloc` (H1), `Opaque.rel_tok_intro` at the `opq` clause |
| `tokBurn` | `tokBurn_compatX` | `erwp_det` (β), `erwp_free` (H2), `Opaque.rel_cases`, `Opaque.tok_not_host` |
| `arrLen` | `arrLen_compatX` (`Core/Arrays.lean`) | `vN_fam_iff`, `noOwn_arrayImmN`, `erwp_garbage` (W5), `erwp_det` |
| `arrGet` | `arrGet_compatX` | `vN_fam_idx`, `erwp_det` at `Head.idx`, `sepRange_pick`, `noOwn` of a leaf, `erwp_garbage` |
| `arrCopy` | `arrCopy_compatX` | `sepRange_dup` with the `imm` leaf's duplication (`compS_imm_dup`, R10, and the witness `ImmWitW` kept on both halves) |
| `arrRelease` | `arrRelease_compatX` (`release_fam_compatX`) | `noOwn_famN`, `erwp_garbage` |
| `arrSize` | `arrSize_compatX` | `erwp_det`, `vN_fam_mk` |
| `arrReplace` | `arrReplace_compatX` | `erwp_det`, `erwp_bindR`, `rwp_load` (H3), `rwp_store` (H5), `sepRange_pick` |
| `arrNew` | `arrNew_compatX`, `tabFill_wp`, `wpTS_tab`, `alloc_block` (`Core/ArrayWp.lean`) | `rwp_tab`/`erwp_tab` (the `tab` step at the index: `n` of `TWNC.alloc`, a block from `finDom_block`), `tabFill_wpN` by Core's induction: `bang_app` (F2), `erwp_bind_frame` (W4), `rwp_store` |
| `arrFree` | `arrFree_compatX`, `dropFill_wp` | `erwp_det` at `Head.drop`, `erwp_free`, `bang_app`, `erwp_bind_frame` |
| `arrEmpty`, `sliceEmptyI`, `sliceEmptyM` | `famEmpty_compatX` (`Core/SliceOps.lean`) | `vN_fam_mk` at `0` |
| `sliceSplitI`, `sliceSplitM` | `famSplit_compatX` | `vN_fam_split`, `erwp_det` at `Head.split` |
| `sliceGetM` | `famGet_compatX` (`Core/Slices.lean`) | as `arrGet`, the leaf a `mut` one (`noOwn` of `mutL`) |
| `sliceLenM` | `famSize_compatX` | as `arrSize` |
| `sliceReplaceM` | `sliceReplaceM_compatX` | `erwp_M_antiFrame` at the view (R2, as `withswap_compatN`) at the leaf, `rwp_load`, `rwp_store`, `sepRange_pick` |
| `sliceSwapM` | `sliceSwapM_compatX` | the same at one leaf (`i = j`) or two (`sepRange_pick2N`) |
| `sliceBorrowM` | `sliceBorrowM_compatX`, `wpTS_M_frameFam`/`wpTS_M_frameList` (`Core/SliceFrames.lean`) | `erwp_M_frameFamN`: the list induction over the one-cell frame at the empty table (`erwp_M_frameR`, as `withbor2_compatN`), each cell its own key `Θ + (ℓᵢ, αᵢ)`, `αᵢ₊₁` fresh for the world after `ℓᵢ`; the callback reads every leaf at the innermost lifetime through `Mut`'s slack `@aδ ⊑ b` |
| `sliceBorrowI` | `sliceBorrowI_compatX`, `wpTS_I_frameFam` | `erwp_I_frameFamN`: the list induction over `erwp_I_frame` (R5), one `imm` record per cell (`LocTy.addImm`), the run read at the lender's view by `erwp_tieEntry` |
| `sliceBorrowMU` | `sliceBorrowMU_compatX` (`Core/EffBorrow.lean`), `wpG_M_frameFam` | the list induction over `erwp_M_frameR` at a `Row.Unwind` table (abortive entries), as `withbor2U_compatN` |
| `sliceBorrowIU` | `sliceBorrowIU_compatX`, `wpG_I_frameFam` | the list induction over `erwp_I_frameR`, as `withbor1U_compatN` |
| `sm` (constant) | `sliceBorrowMU_compatX` at `Row.Suspend` | the list induction over `erwp_M_frameCR` (stops, raises) and `erwp_M_frame_cancelRunCR` (layered cancel runs): each layer's table the guarded twin of the next (`tabR` at that layer's claim), `tabR_can` per layer; `withbor2S_compat`'s structure around it, `erwp_claimX`, `erwp_ubindClaimRT`, the finaliser `d : Array A ⊸ 1` |

The statements `JdgInFrag` and `Const791.InFrag` read `VTy.inFrag`; it is widened to `opq` and to
`[L]` at an in-fragment `L`. `μ`, `tvar` (L6) and `ν` (L7) stay out.

### 11.2 Built (`Core/Chain/Fam836N.lean`, `FamFrame836N.lean`, `FamStop836N.lean`)

The clauses (`Goal791N.lean`): `vN`/`vO` at `opq k` are `k.rel v ρ`; at `[L]` they are
`∃ ℓ c, v = arr(ℓ, c) ∧ c < 2³¹ ∧ sepRange (λm. 𝒱⟦L⟧(loc m)) ℓ c ρ`, the leaf at the family's
world and index. `VTy.inFrag` admits `opq` and `[L]` at an in-fragment `L`, so `JdgInFrag` and
`Const791.InFrag` do; the family rows of §3 (marked `no` there) are now in the fragment.

Laws re-proved over the two clauses, statements unchanged: `vN_down`/`vO_down`, `vN_congr`/
`vO_congr`, `vN_extR`/`vO_extR` (`sepRange_mono_down` at `ExtR`'s parts), `vN_outlives`,
`vN_outlivesLe` (`sepRange_closed`; at `Tok` the owned unit cell), `vN_vO`, `vN_vShape`/
`vO_vShape`, `vO_transfer` and `relabel_vN` (`sepRange_zip`, Core's `obs_transfer`/`relabel_obs`
family cases, with the chain's `LifeBoundOn`/`LifeBoundWit` conjuncts closed under parts),
`vN_tyEq`/`vO_tyEq`, `vN_noOwn_of_ownFree` (both copies; `Tok` is not own-free).

| Row | Chain lemma | Core proof |
|---|---|---|
| `tokMint` | `tokMint_compatN` | `tokMint_compatX` |
| `tokBurn` | `tokBurn_compatN` | `tokBurn_compatX` |
| `arrLen` | `arrLen_compatN` | `arrLen_compatX` |
| `arrGet`, `sliceGetM` | `arrGet_compatN`, `sliceGetM_compatN` (`famGet_compatN`) | `arrGet_compatX`, `famGet_compatX` |
| `arrCopy` | `arrCopy_compatN` (`vN_imm_dupN`, `sepRange_dup`) | `arrCopy_compatX` |
| `arrRelease` | `arrRelease_compatN` (`release_fam_compatN`) | `release_fam_compatX` |
| `arrSize`, `sliceLenM` | `arrSize_compatN`, `sliceLenM_compatN` (`famSize_compatN`) | `famSize_compatX` |
| `arrEmpty`, `sliceEmptyI`, `sliceEmptyM` | `arrEmpty_compatN`, `sliceEmptyI_compatN`, `sliceEmptyM_compatN` (`famEmpty_compatN`) | `famEmpty_compatX` |
| `sliceSplitI`, `sliceSplitM` | `sliceSplitI_compatN`, `sliceSplitM_compatN` (`famSplit_compatN`, `vN_fam_split`) | `famSplit_compatX` |
| `arrFree` | `arrFree_compatN` (`dropFill_wpN`) | `arrFree_compatX`, `dropFill_wp` |
| `arrReplace` | `arrReplace_compatN` | `arrReplace_compatX` |
| `sliceBorrowM` | `sliceBorrowM_compatN` (`sliceBorrowM_sem`, `rwp_M_frameListN`) | `sliceBorrowM_compatX`, `wpTS_M_frameList` |

`rwp_M_frameListN` is Core's `wpTS_M_frameList` as the list induction over `rwp_M_frame`: frame `j`
lends its leaf at `αⱼ` fresh for the world the frames before it reached, at the key `(ℓⱼ, αⱼ)`,
below the frame's rest, the payloads' stratum and the result's (Core's `aF ⊓ β′ ⊓ β`); the inner
frames' callback bound is `aR ⊓ α₁ ⊓ γH` as printed. Core's `ptoMutS_antitone` step (the outer
leaf shortened to the innermost lifetime) is `Mut`'s slack `@aδ ⊑ b` on the chain (`mutLeafN`,
`vN_mutLeaf`): the leaf keeps its cell at `αⱼ` and is read at `α ⊑ αⱼ`. The callback's result
returns frame by frame by `vN_local`.

`erwp_M_frameRR` (`FamStop836N.lean`) is `erwp_M_frameR` with the callback's raises at
`opTableR T R`, the claims of the frames nested inside it: at a `raise` the lent cell's claim joins
`R` (`R` in the lend's stratum, so the lent cell is not in it). It is the one-cell step of the
family frame across raises.

### 11.2a Built in `Core/Chain/FamCancel836N.lean`, `FamSlice836N.lean`

| Row / constant | Chain lemma | Core proof |
|---|---|---|
| `sm` (constant) | `constN_sm` (`sliceBorrowMS_compat`, `erwp_M_frameListCRN`); instance `sliceBorrowMS_inst` at `hardestRow`, finaliser `dArrFree = λa. drop (λu. (), a)` (`dArrFree_sem`) | `sliceBorrowMU_compatX` at `Row.Suspend` |
| `sliceBorrowMU` | `sliceBorrowMU_compatN` (`sliceBorrowMU_sem`, `erwp_M_frameListRN`) | `sliceBorrowMU_compatX`, `wpG_M_frameFam` |
| `sliceReplaceM` | `sliceReplaceM_compatN` (`sepRange_pickW`) | `sliceReplaceM_compatX` |

`ConstsN` now follows from `FundamentalN` (`constsN_of`, the five `constN_*`), so
`goal791Sched_of`'s second hypothesis is discharged: `goal791Sched_of_fundamental : FundamentalN →
Goal791SchedN`.

**The one-cell frame at an incoming claim.** Nesting `erwp_M_frameCR` needs the callback's raises
and cancel runs already carrying the inner frames' claims. Each declaration below is a new lemma
beside the one it restates; the originals are unchanged and keep their callers.

| Original | At an incoming claim `R` |
|---|---|
| `erwp_M_frameCR`: callback at `opTableN T`, lender at `opTableR T′ (claimR ℓ A F)` | `erwp_M_frameCRR`: callback at `opTableR T R`, lender at `opTableR T′ (claimR ℓ A F ⋆ R)`, `R` in `A`'s stratum |
| `erwp_M_frame_cancelRunCR`: `cancelTabN T` to `cancelTabR T′ (claimR …)` | `erwp_M_frame_cancelRunCRR`: `cancelTabR T R` to `cancelTabR T′ (claimR … ⋆ R)` |
| `tabN_tabR_twin` (`tabN` at the lend's world, `tabR` without it) | `tabR_tabR_twinW` (`tabR R` at one world, `tabR R′` at another, the row's types read alike) |
| `tabN_lendOKCR_C` | `tabR_lendOKCR_C` |
| `tabR_can` (`tabN` entries' cancel runs to `tabR (claimR …)`) | `tabR_canR` (`tabR R` entries' cancel runs to `tabR (claimR … ⋆ R)`, by `erwp_M_frame_cancelRunCRR`) |
| `tabR`/`finR` | unchanged: already parametric in the claim |

Beside them: `tab_lookupRW` (a `tabR` entry at every claim and world), `tabR_le` (`tabR`
monotone in its claim along `OpTabN.Le`), `tabN_tabR_le` (the callback's `tabN` below `tabR` at a
claim holding of `∅`), `performStopN_le`, `errOkN_le`, `erwp_opTableR_le`, `erwp_cancelTabR_le`,
`erwp_opTableN_R`, `erwp_cancelTabN_R`.

**The list induction** (`erwp_M_frameListCRN`, Core's `wpG_M_frameList` across stops, raises and
layered cancel runs) is `rwp_M_frameListN`'s, with `erwp_M_frameCRR` for `rwp_M_frame`. Frame `j`
lends at `αⱼ` fresh and below the frame's rest, the payloads' and result's strata and the bound.
Its callback, the run of frames `j+1 … n`, runs at `tabR (claimL A δ Θⱼ I)` at the world `Θⱼ` with
`αⱼ`'s key. `claimL A δ Θ I` is the composite claim: the cells of `I` owned again, each holding a
member of `A` at `Θ`. Frame `j`'s output `claimR ℓⱼ αⱼ Fⱼ ⋆ claimL … Θⱼ I` is moved to
`claimL … Θⱼ₋₁ (ℓⱼ :: I)` by `vN_local` (the cells are in `αⱼ`'s stratum), at every cancel depth
(`tabR_le`). The innermost callback runs at the empty claim `claimL … []`, and its own `tabN` lies
below that (`tabN_tabR_le`). `sliceBorrowMS_compat` is `withbor2S_compat`'s structure around it:
`erwp_claimX` at `claimL`, then `erwp_ubindClaimRT`, where `d : Array A ⊸ 1` takes the array
(`fin_claimArr`).

**At an unwinding row** the table reads no fresh key (`tabN_unwind_add`), so
`erwp_M_frameListRN` is the list induction over `erwp_M_frameRR` at one table. The finaliser
runs at a raise (`erwp_ubindRaise`, `fin_claimArrI`).

**`sliceReplaceM`** is `arrReplace_compatN`'s steps with `erwp_M_antiFrame` at the view at the
picked leaf (`consistentX_get` for the cell's view lifetime), as in `withswap_compatN`. The steps
inside the anti-frame are taken at the index each one costs. The family is rebuilt at the end's
index by `sepRange_pickW` (`sepRange_pick` with the rest read at a weaker predicate).

### 11.3 Not built

- **`sliceBorrowIU`, `sliceBorrowI`**: the family Imm Frame. This is the list induction over
  `erwp_I_frameR`/`erwp_I_frame`, one record per cell (`LocTy.addImm`), each leaf's `ImmWitW`
  at its record, with the run read at the lender's view by `erwp_tieEntry`. Nesting needs
  `erwp_I_frameR` at an incoming claim, as `erwp_M_frameCRR` is for the Mut Frame: the callback
  at `opTableR Tb R`, the lender at `opTableR Tb (claimI … ⋆ R)`. Not built. Not derived;
  obstruction not verified.
- **`arrNew`**: the `tab` step at the index. `rwp_tab` takes one head step to `tabFill` that
  allocates a block. It needs `alloc_block` at the chain (`n` of `TWNC.alloc` and
  `hash_compS_own`, the block from `finDom_block`) and the continuation's `rwp` from the post-step
  configuration. `rwp_head1` covers only steps to a value. After that comes `tabFill_wpN`, by
  Core's induction. Not built. Not derived; obstruction not verified.
- **`sliceSwapM`**: `sliceReplaceM_compatN`'s steps at one leaf (`i = j`) or two (two anti-frames,
  `sepRange_pick2N`). Not built. Not derived; obstruction not verified.

## 13. Unit L6: `μ` (#836)

### 13.1 Core's `μ` clause and `RelMu`

Core's relation takes a type-variable environment, `vCE : Option (Nat → TEnt) → Bool → VTy → …`
(`Core/Relation.lean`); `vC` is notation for `vCE none`. An entry `TEnt` holds the closed type the
variable stands for (`ty`, which the `Imm` clause's `CohE` reads through `tClose η A`) and a
candidate `P : Bool → List SRec → Val → WProp` over the mode and the record list. The clauses:

- a type variable reads its entry's candidate (`tEnvP`), empty at `none`;
- `μX. A` is the least fixed point `⋂{P | A[P/X] ⊆ P}`, written in `Prop` and joint over the mode
  and the list:
  `A.NoMut 0 ∧ (tClose η (μX. A)).Cl 0 ∧ ∀ P, (∀ b' ls' v' ρ', vCE (some (P · η)) b' A ls' δ v' ρ' →
  P b' ls' v' ρ') → P b ls v ρ`;
- `U C` reads no environment (`cC` has none), so a thunk is a leaf of the induction;
- `Mut`'s payload is read under `η`, and `NoMut 0` keeps `X` out of it: the `Mut` clause stores its
  predicate by an equation and is not monotone.

`Core/RelMu.lean` proves, with no [TR] number cited (the file cites spec §6):

| Core | Content |
|---|---|
| `vCE_some` | the relation reads `η` only through `tEnv` |
| `vCE_rename`, `vCE_subst` (`substEnv`) | renaming and substitution move into the environment |
| `vCE_congr_occ` | only the entries of occurring variables are read |
| `vCE_mono_at` | monotone in an entry whose variable occurs in no `Mut` payload |
| `cBody`, `vC_inst`, `cBody_mono` | one unfolding at a candidate; `A[μX. A/X]` is the body at `vC (μX. A)` |
| `vC_roll`, `vC_unfold`, `vC_mu_iff` | the unroll equation at a closed `μ` outside its `Mut` payloads |
| `vF`, `vF_vC`, `vF_mono`, `vC_ind` | the induction principle: a property closed under one unfolding of every clause holds of `vC` |
| `vC_mu_ind` | induction at one `μ` |
| `vC_immReborrow_mu_iff` | `Imm̲` at a closed `μ` is read at the reborrow of the unrolling |

`Core/RelationFacts.lean` proves the laws over the environment two ways. `vCE_congr` (with
`EnvAgree`) and `vCE_tyEq` (with `EnvEq`) are by induction on the type, generalised over the
environment with a hypothesis on its entries. `vC_local`, `vO_obs`, `vC_vShape`, `vC_outlives`,
`vC_outlivesLe`, `obs_transfer` and `relabel_obs` are by `vC_ind` at the empty environment, the
`μ` case by `vC_roll` at the unrolling.

### 13.2 The environment in `vN`

`vNE`/`vOE` (`Goal791N.lean`) are `vN`/`vO` with an environment `η : Option (Nat → TEntN)` in
front. `TEntN` is Core's `TEnt` with the candidate over the chain's arguments:
`P : Bool → LocTy → Nat → Val → WRes → Prop`, the mode (`true` for `vNE`, `false` for `vOE`), the
world, the index, the value and the resource. `tEnvN`, `tEnvPN`, `tCloseN` are Core's `tEnv`,
`tEnvP`, `tClose`. `vBN η b` is `vNE η` or `vOE η`: Core's `vCE η b`.

New clauses:
- `vNE η (tvar n)` is `tEnvPN η n true`; `vOE η (tvar n)` is `tEnvPN η n false`;
- `vNE η (μX. A)` is Core's clause, with the candidate's closure asked in both modes: `vNE` and
  `vOE` at `some (scons ⟨tCloseN η (μX. A), P⟩ (tEnvN η))` into `P true` and `P false`
  (`MuClosedN`, `vBN_mu`);
- `Imm`'s witness is read at `tCloseN η A`;
- `Mut`'s family and uniform conjunct are read at `vNE η A`.

Every other clause is the old one with `η` passed down. `cN`, `tabN`, `finN`, `retN` keep their
signatures and read `vNE none`.

**At the empty environment every statement is unchanged.**
- `vN`/`vO` are syntax for `vNE (η := none)`/`vOE (η := none)`, and `vN (ℍ := h) A …` for
  `vNE (ℍ := h) none A …`, so every existing use elaborates to the empty environment.
- At `none`, `tvar` is `False` (as before), `tCloseN none A` is `A` definitionally (so the `Imm`
  clause is the old one), and every other clause is the old one.
- `μ` was `False` and now has Core's clause.

**What changed in the signature (for the hand merge with #835 and #837).**
- `vN`/`vO` are no longer `def`s. The mutual block defines
  `vNE : (η : Option (Nat → TEntN)) → VTy → LSub → LocTy → Nat → Val → WRes → Prop` and `vOE`
  (same type); `vN`/`vO` are `syntax` with `macro_rules` after the block.
- Inside the block a section-local notation makes `vN`/`vO` read as `vNE none`/`vOE none`, so the
  text of `cN`'s, `tabN`'s, `finN`'s and `retN`'s clauses (`entN`'s callers included) is unchanged
  and merges as it is.
- `simp only [vN, …]`/`[vO, …]` become `simp only [vNE, …]`/`[vOE, …]` (`vN` is not a constant).
- A law over `vN` that matched on `.tvar`/`.mu` as `h.elim` needs the `μ` case: by `vN_ind`
  (Core's route), or generalised over the environment (§13.4).

### 13.3 The step index and unfolding

The candidate is joint over the mode, the world and the index, as Core's is joint over the mode
and the list. Every clause that reaches `X` reads it at the same world and index, so the least
fixed point is pointwise in them. The joint quantification is the one the laws use: `vN_down` and
`vN_extR` take candidates that close over lower indices and later worlds.

Unfolding costs no step: `vN_mu_iff` is the unroll equation at the same index, as `vC_mu_iff` is
Core's at the same list. The machine has no `roll`/`unroll` step (`Fundamental.lean`: "typing rules
on the same term"), so no index is spent and no later modality is needed. This is Core's answer;
nothing departs from it.

### 13.4 The laws

Core's `RelMu` at the chain (`Goal791N.lean`):

| Core | Chain |
|---|---|
| `vCE_some`, `vCE_rename`, `vCE_subst`, `vCE_congr_occ`, `vCE_mono_at` | `vBN_some`, `vBN_rename`, `vBN_subst` (`substEnvN`), `vBN_congr_occ`, `vBN_mono_at` |
| `cBody`, `vC_inst`, `cBody_mono` | `bodyN`, `vN_inst`, `bodyN_mono` |
| `vC_roll`, `vC_unfold`, `vC_mu_iff` | `vBN_roll`, `vBN_unfold`, `vBN_mu_iff`; at `vN`: `vN_roll`, `vN_unfold`, `vN_mu_iff` |
| `vF`, `vF_vC`, `vF_mono`, `vC_ind` | `vFN`, `vFN_vN`, `vFN_mono`, `vN_ind` |
| `vC_mu_ind` | `vBN_mu_ind` (at every environment), with `vBN_rollE` |
| `vC_immReborrow_mu_iff` | `vN_immReborrow_mu_iff` (`ImmImage791N.lean`) |

Each existing law is extended to the new clauses, its statement unchanged at the empty
environment.
- **Generalised over the environment, with a hypothesis on its entries** (Core's route for
  `vCE_congr`/`vCE_tyEq`). The `μ` case takes the candidate "the property at the least fixed
  point" and closes it by the law at the body and `vBN_mono_at`.
  - `vNE_down`/`vOE_down`, mutual with `cN_down`, entries `EnvDownN`. The candidate is
    "every lower index is in `P`" (`vBN_mu_down`).
  - `vNE_congr`/`vOE_congr`, entries `EnvAgreeN`.
  - `vNE_extR`/`vOE_extR`, entries `EnvExtRN`. The candidate is "in `P` at every extension"
    (`vBN_mu_extR`).
  - `vNE_outlives`/`vNE_outlivesLe`, entries in the stratum. The candidate is
    `b = true → InStratum`.
  - `vNE_tyEq`/`vOE_tyEq` (`TyEq834N.lean`), entries `EnvEqN`.
- **By `vN_ind`** (Core's route for these): `vN_vO` (`vO_obs`), `vBN_vShape` (`vC_vShape`;
  `vN_vShape`, `vO_vShape` are its two modes), `vO_transfer` (`obs_transfer`), `relabel_vN`
  (`relabel_obs`; at `μ` by `vN_immReborrow_mu_iff` and `vShape_immReborrow_mu_iff`), and
  `vN_empty_of_persistent` (`ImmLend833N.lean`, at `μ` by `persistent_inst_mu`).

The old names (`vN_down`, `vN_congr`, `vN_extR`, `vO_extR`, `vN_outlives`, `vN_outlivesLe`,
`vN_tyEq`, `vO_tyEq`) are corollaries at `none`, with their statements unchanged. Every other law
(`vN_local`, `vN_above`, `vN_inStratum_bnd`, `vN_noOwn_of_ownFree`, `vN_iff_vP`, …) builds
unchanged.

`VTy.inFrag` admits `μX. A` at an in-fragment body and every type variable, so `JdgInFrag`
and `Const791.InFrag` do too. `ν` stays out (L7).

### 13.5 The rows (`Core/Chain/Mu836N.lean`)

| Row | Chain lemma | Core proof |
|---|---|---|
| `roll` | `roll_compatN` (`vN_roll` under `erwp_mono`) | `roll_compatX` |
| `unroll` | `unroll_compatN` (`vN_unfold`) | `unroll_compatX` |
| `foldOwn` | `foldOwn_compatN` (`travO_specN`, `hOSpecN_all`, `travO_appN`, `hO_appN`) | `foldOwn_compatX`, `travO_spec`, `hOSpec_all` |
| `foldReuse` | `foldReuse_compatN` (`travR_specN`, `hRSpecN_all`, `erwp_swapN`) | `foldReuse_compatX`, `travR_spec`, `hRSpec_all`, `wpTS_swap` |
| `foldOwnG` | `foldOwnG_compatN` (`Core/Chain/FoldG836N.lean`: `trav_specN`, `arr_specN`, `step_specN`, `countLoop_invN`, `selfG_runN`, `hs_allN`, `fold_specN`, `algsOK_of_tupleN`) | `foldOwnG_compatX`, `trav_spec`, `arr_spec`, `step_spec`, `countLoop_inv`, `selfG_run`, `hs_all`, `fold_spec`, `algsOK_of_tuple` |
| `foldImm` | `foldImm_compatN` (`Core/Chain/FoldImm836N.lean`: `withload_sizedN`, `good_of_imageN`, `trav_specKN`, `pSpec_succN`, `hSpec_allN`, `alg_callN`) | `foldImm_compatX`, `withload_sized`, `good_of_image`, `trav_spec`, `pSpec_succ`, `hSpec_all`, `alg_call` |

The folds follow Core line by line: Core's terms (`foldOwnV`, `travO`, `selfO`, `hO`, and the
`R` versions) with their reductions, and Core's induction on the resource size (`dsize`) and then
the value size.
- A pure step is `erwp_det` at the same index; the Z combinator's unrolling is `erwp_pureSteps`
  over Core's `selfV_steps_in`.
- A `free`, `load` or `store` costs one step (`erwp_free`, `rwp_load`, `rwp_store`).
- Core's `wpTS_bind_frame` is `erwp_bind_frame`. Its consistency premise is met at each split from
  the whole resource's consistency and validity (`erwp_of_valid`, `consistentX_left`/`right`).
- The fold runs at one world and one view. The algebra `g` has the empty resource, so it moves to
  the world where the fold is forced (`vN_extR`), and it is read there at every index below the
  fold's. That index bound is the `N` of `HOSpecN`/`HRSpecN`.

`foldOwnG`: Core's loop invariant `ArrInv` becomes `ArrInvN`, a post read at the index, and is
closed downward (`arrInvN_down`). The loop step's frames are the exact resources Core's
reassociation produces. The array is drained by `dropFill_wpN` with `dropU_sem`. The algebras
come out of the run-time tuple at the world the fold is forced at (`bang_app`, at the empty
resource), at every index up to the tuple's.

`foldImm`: `withload_sizedN` is Core's `withload_sized` at the empty row, by `withload_reb` (the
row `[]`, the bound `⊤`). Its callback is handed the image's relation to the loaded witness. For
that, `withload_rebT` and `withload_reb` now give their callback two more premises:
- `u = v`: the view is the loaded payload's value;
- `ResU.Reb β σ χ`: the view's resource is an image of the payload's witness.

Both premises are already in scope where `withload_rebT` calls the callback (`hreb`, after the
`subst`). The three callers ignore them: `withloadS_compat`, `withload_compatN` and the unwinding
row's `withload`. `good_of_imageN` is Core's `good_of_image` with `vO_vShape`/`vN_vShape`. The
algebra is called at the run's world by `alg_callN`: `cN`'s `∀` clause at `β`, then the `⊸`
clause.

### 13.6 Restated declarations

| Declaration | Before | After |
|---|---|---|
| `vN`, `vO` | `def`s in the mutual block | syntax for `vNE (η := none)`, `vOE (η := none)`; the block defines `vNE`, `vOE` |
| `vN_down`, `vO_down`, `vN_congr`, `vO_congr`, `vN_extR`, `vO_extR`, `vN_outlives`, `vN_outlivesLe`, `vN_tyEq`, `vO_tyEq` | proved by structural recursion | the same statements, as corollaries at `none` of the `vNE`/`vOE` laws |
| `vN_vO`, `vN_vShape`, `vO_vShape`, `vO_transfer`, `relabel_vN`, `vN_empty_of_persistent` | structural recursion | the same statements, by `vN_ind` (Core's route) |
| `VTy.inFrag` | `μ` and type variables out | `μ` at an in-fragment body, every type variable in |
| `withload_rebT`, `withload_reb` | callback at `u χ Bχ`, all-`imm` `χ` | the same, plus `u = v` and `ResU.Reb β σ χ` |

`FundamentalN`'s statement reads `JdgInFrag`, so the wider `VTy.inFrag` makes it quantify over more
derivations. `goal791Sched_of_fundamental : FundamentalN → Goal791SchedN` and `constsN_of`
build unchanged in text. `Goal791SchedN` covers more programs (rows and constants with `μ`).

### 13.7 What remains

The six `μ` rows are proved at `SemJN`. `reify` and `unfoldN` also read F8, but they wait on `ν`
(F9, L7).
