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
(`ExtRLit791.lean`, at a stuck application, `world_two`), and `flat_part_config`
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
| K1 | `vC_local` | — | 19: `swap`, `iterate`, `reify`, `sliceBorrowM` … | **departed (built)** | `vN_extR` (`Goal791N.lean`), along `LocTy.ExtR` at the value's resource. Configurations: `extRL_breaks_extA` (Core's `Ext` read literally is not Kripke along `ExtA`; at a stuck application from a typed world of two `mut` cells, #837) and `coreMutImm_not_extF` (payloads read off the list are not stable along `extF`, so the order is on the world) |
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
| F8 | `vC_roll`, `vC_unfold`, `vC_immReborrow_mu_iff`, `vCE_subst` … | — | 8: `reify`, `roll`, `unroll`, `foldImm` … | **missing, buildable** | an environment argument in `vN`/`vO`, the `μ`/`tvar` clauses, Core's `RelMu` laws at the index; `withload_sized` is `withloadS_compat` with a size measure. Very high; not checked |
| F10 | `cC` .arr (the `⊸` clause) | — | 10: `bind`, `lam`, `lamDead`, `app` … | **same** (#834) | `cN .arr` is Core's plain wand at the function's own world, read at every later index and every view consistent with the composite (§8.1). The Kripke reading along `ExtR` is gone: no configuration forced it |
| F9 | `cC_nu_iff`, `nuRel_coind`, `cB_step` | spec §7 | 4: `reify`, `nuIn`, `nuOut`, `unfoldN` | **same** (#837) | Core's greatest fixed point at the chain's signature (§12): `cN_nu_iff`, `cN_nu_coind`, `cN_nu_unfold`, `cBN_step`; `reify`'s candidate not derived (§12.5) |

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
| E9 | `ewp_frame_then`, `ewp_frame_then_or`, `cwp_then`, `cwp_then_div` … | — | 3: `effThen`, `effThenDiv`, `effHandleL` | **built** (#835 §10.3: `erwp_frame_then`, `then_cancelN`, `cfin_runN`, `cfin_cancelN`, `seq_raise_runN`) | `erwp_ubind` (`SI/UbindGN.lean`) and its cancel/raise/claim companions are stated without unrestricted operations in `Σ_M` and at a finaliser meeting `FinOK`; Core's `hP`/`hU`/`ThenLe` form and a finaliser row holding `Div` are missing, buildable (map E6, E7) |
| E10 | `ewp_handle_vals`, `ewp_handle_valsB`, `ewp_handle_tail`, `ewp_handle_last` … | — | 4: `effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL` | **not derived** for `effHandleV`/`VB` (#835 §10.1: the clauses at `vN`); the tail and last instances **built** (#835 §10.5: `erwp_handle_tail`, `erwp_handle_last`) | `erwp_handle` (`SI/HandleN.lean`; needs no `hdv`), `erwp_kappa_*`; the clauses' reading at `vN` and the split of `tabN (ofEff n E 0 fs ++ S)` (map E8), the tail and last instances (map E11): missing, buildable |
| E11 | `ewp_kappaC_resume`, `ewp_kappaC_cancel`, `ewp_kappaCell`, `ewp_kappa_resume` … | — | 3: `divFuel`, `reify`, `effHandleVB` | **same**; the fuel handler's instances built (#835: `erwp_kappaC_resume_in`, `erwp_hnd_tick`) | `erwp_kappa_resume`, `erwp_kappaC_resume`, `erwp_kappa_cancel`, `erwp_kappaC_cancel`, `erwp_kappaCell`, `erwp_ccatch` (`SI/HandleN.lean`) |
| E12 | `stop_sem` | spec §28 | 1: `effHandleVB` | **built** (#835: `stop_semN`, `erwp_handleS`) | the BOXED-κ stop lemma at `erwp` (map E10). Not derived; obstruction not verified |
| E13 | `cwp_bind`, `cwp_of_ewp`, `effWp_of_ewp`, `cwp_out` … | spec §14 | 21: `iterate`, `divFuel`, `reify`, `withbor1U` … | **departed, forced by `erwp`** | a `Div` row is a row of the table; `erwp` is step-indexed, so Core's coinductive `cwp` and its bookkeeping have no counterpart, and each `cwp` branch is the `ewp` branch's `erwp` lemma. Reason: `Depart831N.erwp_of_noFinal`; the split: `Depart831N.cN_effOf_divB` (§6.3) |
| E14 | `cwp_iterate` | spec §14 | 1: `iterate` | **built** (#835: `erwp_iterateC`; at an invariant read at the index, `erwp_iterateCI`) | `erwp_iterate` (`SI/LoopN.lean`) is stated where the tick always answers *next*; the version answering in `vN nextTy` (the close branch) is missing, buildable from its induction |

### 2.1 Counts

| Status | Entries |
|---|---|
| same | 41 (F5, F6 in #836; F9 in #837) |
| departed (built) | 12 (K1, K3, K4, V10, R1, R2, R3, R4, R5, R7, R8, R11) |
| departed, forced by `erwp`'s definition | 1 (E13) |
| departed, no configuration | 0 |
| departed, to build | 7 (E3, E5, E6, E9, E10, E14, F7) |
| missing, buildable | 21 |
| missing, unclear | 1 (E12 the BOXED-κ stop lemma) |
| **total** | **83** |

The chain-only entries V11, G11 and G12 are counted here. They have no Core lemma: the chain's
judgment carries a step index and a view (`SemJN`'s `n` and `c`), and Core's has neither.

### 2.2 Departed without a configuration

K4, V10's lifetime match, E13 and F10 were listed here. K4/V10 now have a configuration and E13
is forced by `erwp`'s definition (§6.3); F10 returned to Core's plain wand in #834 (§8.1). None
remain.

### 2.3 Missing, unclear

- **F9** is built in #837 (§12); of its rules, `reify` is not derived (§12.5).
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
| 55 | `iterate` | yes | portable | W1 K1 K5 G3 C3 E1 E2 E4 E8 E13 E14 | K5 E8 E14 | proved (`iterate_compatN`, §10.2) | `cwp_iterate` → E14 at an indexed invariant (`erwp_iterateCI`) |
| 56 | `divFuel` | yes | portable | W1 G3 C3 E1 E2 E4 E8 E11 E13 | E8 | proved (`divFuel_compatN`) | `fuel_total`, `divFuel_steps`, `fuelK_frame` |
| 57 | `reify` | yes (#837) | portable (#837) | W1 W9 K1 K5 V4 G3 C3 F9 E1 E2 E4 E8 E11 E13 | — | waits (unclear): §12.5 | `reify_compat` |
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
| 83 | `roll` | no | out | W3 F8 | F8 | mechanical once built |  |
| 84 | `unroll` | cut | out | W3 F8 | F8 | mechanical once built |  |
| 85 | `foldImm` | no | out | W1 W2 W3 W4 W6 K1 K2 V2 V3 V4 V5 V11 G3 F3 F8 R8 | W4 F8 | mechanical once built | `foldImmV`, `travK` |
| 86 | `foldOwn` | no | out | W1 W2 W3 W4 W6 H2 K1 K2 V11 G3 F8 | W4 F8 | mechanical once built | `foldOwnV` |
| 87 | `foldReuse` | no | out | W1 W2 W3 W4 W6 H3 H5 K1 K2 V11 G3 F8 | W4 F8 | mechanical once built | `foldReuseV` |
| 88 | `foldOwnG` | no | out | W1 W2 W3 W4 W6 K1 K2 V11 G3 F3 F6 F8 | W4 F6 F8 | mechanical once built | `FoldP` traversal |
| 89 | `nuIn` | yes (#837) | portable (#837) | F9 | — | proved (#837: `nuIn_compatN`) |  |
| 90 | `nuOut` | yes (#837) | portable (#837) | F9 | — | proved (#837: `nuOut_compatN`) |  |
| 91 | `unfoldN` | yes (#837) | portable (#837) | W1 W2 W3 W6 K1 V4 G3 C1 F9 R6 E1 E2 E4 E8 E13 | — | proved (#837: `unfoldN_compatN`) | `nuRel_coind` |
| 92 | `effSub` | yes | portable | C3 E3 E4 E13 | E3 | proved (`sub_compatN`) |  |
| 93 | `effPerform` | yes | portable | C3 E4 E5 E6 E13 | E5 E6 | proved (`perform_compatN`) |  |
| 94 | `effAwait` | yes | portable | W1 K2 V8 V11 G1 G2 G3 G4 G5 G6 G9 G11 G12 C1 C2 C3 F10 R6 E1 E2 E3 E4 E5 E6 E7 E8 E13 | V8 G1 G2 G4 G6 G9 G11 G12 C2 E3 E5 E6 E7 E8 | proved (`await_compatN`) | composes `perform`, `raise`, `sub`, `ret`, `var`, `sumE`, `let` |
| 95 | `effRaise` | yes | portable | C3 E4 E5 E7 E13 | E5 E7 | proved (`raise_compatN`) |  |
| 96 | `effLet` | cut | portable | K2 G1 G4 G5 G6 G9 G11 G12 C3 R6 E1 E2 E4 E8 E13 | G1 G4 G6 G9 G11 G12 E8 | proved (`let_compatN`, §10.2) |  |
| 97 | `effThen` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | proved (`then_compatN`, §10.3) |  |
| 98 | `effThenDiv` | cut | portable | K2 V9 G1 G4 G5 G6 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E13 | G1 G4 G6 G11 G12 E3 E8 E9 | proved (`thenDiv_compatN`, §10.3) |  |
| 99 | `effHandleV` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 F1 E1 E4 E10 E13 | W9 K5 G1 G11 G12 E10 | waits: E10 (§10.1) |  |
| 100 | `effHandleVB` | cut | pending | W9 K5 V5 V9 G1 G3 G7 G11 G12 C3 F1 R6 E1 E4 E10 E11 E12 E13 | W9 K5 G1 G7 G11 G12 E10 E12 | waits: E10 (§10.1); E12 built |  |
| 101 | `effHandleT` | cut | portable | W9 K5 V9 G1 G3 G11 G12 C3 E1 E2 E3 E4 E8 E10 E13 | W9 K5 G1 G11 G12 E3 E8 E10 | proved (`handleT_compatN`, §10.5) | `ewp_handle_tail`, `ansesTy_at`, `Row.tab_ofEff_self` |
| 102 | `effHandleL` | cut | portable | W9 K1 K2 K5 V8 V9 G1 G3 G11 G12 C3 R6 E1 E2 E3 E4 E8 E9 E10 E13 | W9 K5 V8 G1 G11 G12 E3 E8 E9 E10 | proved (`handleL_compatN`, §10.5) | `ewp_handle_last`, `last_cont`, `worksTy_at`, `exitsTy_at` |
| 103 | `letPoly` | cut | portable | G5 C1 | — | mechanical now |  |
| 104 | `alpha` | yes | portable | V1 | V1 | mechanical once built |  |

### 3.1 Counts

| Class | yes | cut | no | total |
|---|---|---|---|---|
| proved | 7 | | | 7 |
| mechanical now | 21 | 1 | | 22 |
| mechanical once built | 29 | 13 | 28 | 70 |
| waits (unclear) | | 2 (`nuOut`, `effHandleVB`) | 3 (`nuIn`, `unfoldN`, `reify`) | 5 |

The table is as #831 left it. In #837 `ν` entered the fragment: `nuIn`, `nuOut` and `unfoldN`
are proved, and `reify` waits on §12.5.

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
| G12 at a conclusion not `F`/`F_Σ` | `cN_of_valid`: a computation may assume its resource valid, at every type (at `ν` from #837, §12.3) |
| G2 | `gN_soloP` |
| G4 | `gN_persistent`, `gN_cons_persistent` |
| G6 | `gN_extR` |
| G7 | `gN_outlives` |
| G8 | `gN_congr` |
| G9 | `gN_noOwn` |
| G11 | `gN_le` |
| K5 | `LocTy.extR_empty` |
| W4 | `erwp_bind_frame` (the inner run at the empty table, any outer local table; the continuation at the index the run leaves, the returned resource consistent and valid) |
| C2 | `cN_bind`, by induction on `C` (at `ν` from #837: unfold, `cBN_bind`, roll) |
| W7 | `rwp_box`, `erwp_box` |
| V8 | `vN_noOwn_of_ownFree` |
| F2 | `bang_app` (at any later world) |
| F4 | `host_call_sound` at `vN`, through `vN_iff_vP` at the first-order types |
| V1 | `vN_tyEq`, `vO_tyEq`, `cN_tyEq`, `tabN_tyEq`, `finN_tyEq`, `retN_tyEq` |

The hardest case, G12 at a conclusion that is not `F`/`F_Σ`, is `cN_of_valid`: at `⊸` the resource
is a part of the composite the wand runs from. With `ν` read as empty it needed the conclusion
to have a reading at every spine position, and the compatibility lemmas whose proof reads it
(`app`, `bind`, `unitE`, `tensorE`, `sumE`, `zeroE`) carried `noNuSpine C`. Since #837 `ν` has
Core's clause and the premise is gone (§12.3).

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

Branches `rule-791-l4b`, `rule-791-view` and `rule-791-tail`. The paper mapping is
`scope-835-handlers.md`. Part 1 (`rule-791-l4`) built E3, E5–E8, W9, E12, E14 and ported `effSub`,
`effPerform`, `effRaise` (`scope-835-handlers.md` §4). Parts 2–4 are this section.

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
still quantifies `Θ′`, the view and the list. The step is refuted below (`not_kapRelKTyN`).

The answers' reading at the view (§10.2) settles one part of this step: at the stop's own world and
view, `⊸`'s clause hands `κ` an argument whose composite with `κ`'s share is consistent with the
view, so the answer meets the inner table's `ConsistentX` (with `ResU.Valid`, `consistentX_right`).

**Core's step does not hold at the chain** (`Core/Chain/Kappa835N.lean`). `KapRelKTyN` states it:
`KapRelN` at the stop's world `Θ`, view `c`, the outer row's table and answer at `Θ`/`c`, and the
operation's entry, at the index above, gives `vN (kTy Σ R q B F) δ Θ k κ ρ`. `not_kapRelKTyN`
refutes it. Two configurations, every hypothesis discharged, both at the stop's own list `[]`, both
at the stuck `κ = ()` and the answer type `Mut 'x 1`, at the empty row answering `1`:

- *The world* (`not_kTy_world`, `kapRelN_world`). At the empty world no `Mut` value exists, so the
  stop owes `κ` nothing and `KapRelN` holds. `U` reaches the world `∅ + (ℓ′, α) ↦ 𝒱⟦1⟧` (an
  `ExtA` extension), at the stop's own view and list, where the answer `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`
  exists and `() (inj₁ ()) ℓ′` is stuck from the typed world of the two cells (`world_two`).
- *The view* (`not_kTy_view`, `kapRelN_view`). At the world with the key `(ℓ′, α)` and a view with
  no lifetime at `ℓ′`, the only `Mut` answer is at `ℓ′`, not consistent with the run's view, which
  the row's table reads (§10.2); `KapRelN` holds again. `U` reads `κ` at the same world and list at
  a view consistent with its share that puts `ℓ′` at `α`, and the same run is stuck.

So each of `U`'s world and view quantifiers, alone, asks the handled continuation at answers its
stop does not owe it at. The configurations refute the step, a statement about `KapRelN`; they do
not refute the rule, and a proof of E10 by another route would read more of `κ` than `KapRelN`.

**The three routes.**

1. *Transport by a lemma about `erwp`.* `KapRelN` does not imply `U`'s clause (above). The run's
   world enters its answers contravariantly (`tabN`'s `vN B δ Θ`), and an answer at `Θ′` is not one
   at `Θ` (the world configuration); `erwp_extΦ` moves a run along `LocFam.Ext`, and `Θ.view c` is
   not below `Θ′.view c′` where `c′` differs from `c` off the share (the view configuration).
2. *A Kripke share.* The share would owe the continuation at every `ExtR`-later world and every
   consistent view. The share's continuation is `erwpC Φ Tb Q n`, at one `LocFam` and one table, so
   this is a change to `erwp` itself (its stops owing runs at other location typings and tables),
   not to `KapRelN` or `contShareN` alone. Every stop under a live `mut` lend crosses the Mut Frame's
   fold, and `not_extRFoldTransfer` shows `ExtR` at the lender's share does not give `ExtR` at the
   borrowed continuation's share from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`: a key added above `A` (D8 at the
   world). Not built; an inner world other than `Θ′ + (ℓ, A)` was not examined.
3. *The list quantifier.* `U`'s "every record list" is ours, not Core's: `vCE`'s `U` is Kripke along
   `Ext` from the value's own list, and `vN` reads no list (D2, `coreMutImm_not_extF`). Both
   configurations hold at the stop's own list, at which `extF` is reflexive, so no reading of the
   list quantifier closes the step.

`reify` (§12.5) reads the loop made at a tick through `U X` (`thunkRN`, `vN`'s `U` clause with the
candidate in place of `cN`), so its first disjunct asks the tick's continuation at the same worlds
and views; no separate configuration is built for it.

`effHandleT` and `effHandleL` give the clauses no `κ` and do not need this step; their tail and last
instances are built (§10.5).

### 10.2 Answer consistency: a row's table reads its answers at the view

`SemJN` reads a judgment at a view `c` consistent with its resource (D7). A rule that runs typed
code after a computation at a row (`effLet`'s `N`, `effThen`'s `N` and `D`, `iterate`'s step on the
next state, a handler's `h_ret`) reads that code at the run's view, from the resource the
computation returned. Across a stop that resource is the continuation's share beside the answer the
stop was resumed at.

**The reading.** `tabN`, `finN` and `cN`'s `F_Σ` clause read each answer as
`vN B δ Θ ∧ ConsistentX c` (`Core/Chain/Goal791N.lean`): an answer's resource enters the run, and is
read at the run's view as every resource entering a run is (`SemJN`'s start, `U`'s thunk, `⊸`'s
composite). The lenders' twins `tabR` (`Cancel791N.lean`) and `tabG` (`Reborrow791N.lean`) read
theirs alike. Then `tabN_ansC`: every answer of a row's table is consistent with its view, and
`let_compatN` is Core's `let_compatC` with no premise beyond Core's.

**Who hands the answers back, and why each meets the reading.**

- *A lending constant, relaying an answer from the lender's table into the callback's run at the
  moved view* (`setLife c ℓ α`). Route 1: `Row.Suspend`'s answer clause (`VOutlives ∅ bnd o.B` at a
  bound closed at the empty context, `Const791.OK`) puts the answer in `Res_⊤`, which holds no borrow
  cell, so it is consistent with every view (`consistentX_of_outlives`). `tabN_tabR_twin` and
  `tabN_tabG_twin` read it, at the added premise `hbnd : LifeCtx.empty.Defines bnd`; every caller has
  it (`Const791.OK`'s first conjunct). An unwinding row's answers are at `0` (`ansN_zero`); it is never
  resumed.
- *A handler inside the program* (route 2). The clause runs at the handled run's view and resumes `κ`
  from its own run's resource, consistent with that view (`rwp_consistentX`, `erwp_consistentAns`);
  where the clause is typed code, `⊸`'s clause reads the argument's composite at the view. The fuel
  handler answers `tick` at `∅` (`fuel_totalN`, `consistentX_empty`).
- *The scheduler at the top* (`Goal791SchedN`). `SchedOKN` at `rowTabN` now asks the scheduler's
  clauses to resume with answers consistent with the view. Goal791SchedN has no proved instance in the
  tree; its intended one, `HS` (`PoolSpawnN.lean`) at the hardest case's row, answers `park` at `∅`:
  `hardestRow_entry_PB` shows `rowTabN hardestRow`'s answer at `(nP, 0)` is `enParkN`'s exactly, so
  `hs_schedOKN` meets the reading unchanged. At any row whose answer types are persistent the reading
  is the old one (`ansN_persistent`). At a row with a non-persistent answer type the hypothesis asks
  more of the scheduler.

**Route 3 was not needed.** The answer question arises because a resumption brings a resource into a
run at a fixed view; the reading above is the one `SemJN` and `⊸` already make for the other ways a
resource enters a run.

### 10.3 Rules ported

| Rule | Lemma | File | Core |
|---|---|---|---|
| `divFuel` | `divFuel_compatN` (`fuel_totalN`, `fuel_tick_zeroN`, `fuel_tick_succN`, `erwp_hnd_tick`, `erwp_kappaC_resume_in`, `erwp_pureSteps`) | `Core/Chain/Fuel835N.lean` | `divFuel_compatX` (`fuel_total`, `fuel_tick_zero`, `fuel_tick_succ`, `hnd_tick`, `ewp_kappaC_resume_in`, `ewp_pureSteps`) |
| `effAwait` | `await_compatN` (`let_compatN_persist`, `erwp_idxLe`) | `Core/Chain/Let835N.lean` | `await_compatC` |
| `effLet` | `let_compatN` (`erwp_frame_plain`, `entN_plain`, `erwp_consistentAns`, `tabN_ansC`) | `Core/Chain/Let835N.lean` | `let_compatC` |
| `iterate` | `iterate_compatN` (`erwp_iterateCI`, `tickB_sig`) | `Core/Chain/Iter835N.lean` | `iterate_compatX` (`cwp_iterate`) |
| `effThen` | `then_compatN` (`erwp_frame_then`, `then_cancelN`, `cfin_runN`, `cfin_cancelN`, `seq_raise_runN`, `errOkN_of_sub`) | `Core/Chain/Then835N.lean` | `then_compatC` (`ewp_frame_then_or`, `then_cancel`, `cfin_run`, `cfin_cancel`, `seq_raise_run`, `errOk_of_sub`) |
| `effThenDiv` | `thenDiv_compatN` (`then_compatN`) | `Core/Chain/Then835N.lean` | `then_compatC_div` |

`fuel_totalN` inducts on the index alone (E13). `erwp_iterateCI` is E14 with the invariant read at
the index and owed up to the index the step is applied at (`⊸`'s clause); its *next*/*close* steps are
Core's `turnK_next`/`turnK_close`, which ask no closedness of the step or the state. E9's lemmas are
Core's, each by induction on the index (and, for the cancel runs, Core's recursion on the cancel row);
the finaliser and the continuation are owed up to the index the frame is read at. A `Div` row is a row
of the chain's table (E13), so Core's table beside (`Px`) and key erasure (`er`) have no counterpart;
`effThenDiv` is `then_compatN`, its `hcap` giving the cancel-row record vacuously. Unspent: `effThen`'s
`hSD : Row.divB SD = false` and `hUq : S.Uniq` (neither is read by Core's `then_compatC` at a row
without `Div` either; `hSD` selects Core's `ewp`/`cwp` branch, which E13 removes).

### 10.4 Not built

- E10's tail and last instances: built in part 4 (§10.5).
- `effHandleV`, `effHandleVB`: wait on E10 (§10.1), whose Core step is refuted (`not_kapRelKTyN`).
- `withloadU` (#834 §8.4) is unchanged.

### 10.5 Built in part 4: the tail and last handlers (`rule-791-tail`)

| Rule | Lemma | File | Core |
|---|---|---|---|
| `effHandleT` | `handleT_compatN` (`erwp_handle_tail`, `erwp_frame_plain_or`, `ansesTy_atN`, `tabN_ofEff_self`, `tabN_ofEff_ne`, `capTag_ofEffN`, `erwp_consistentPA`) | `Core/Chain/HandleT835N.lean` | `handleT_compatC` (`ewp_handle_tail`, `ewp_frame_plain_or`, `ansesTy_at`, `Row.tab_ofEff_self`, `Row.tab_ofEff_ne`, `capTag_ofEff`) |
| `effHandleL` | `handleL_compatN` (`erwp_handle_last`, `last_contN`, `worksTy_atN`, `exitsTy_atN`, `erwp_frame_then`, `erwp_frame_plain_or`) | `Core/Chain/HandleL835N.lean` | `handleL_compatC` (`ewp_handle_last`, `last_cont`, `worksTy_at`, `exitsTy_at`, `ewp_frame_then`) |

Each is Core's proof at `erwp`, through `erwp_handle_le` at the handled row's table. The handler's
values are read off its run at the run's start (`erwp_val_post`, W9), as Core reads them off `wpTS`.
The clauses are Core's syntax (`tailTuple`, `lastTuple`, `resK`, `lastN`, `lastD`, `exitK`), and so
are their steps, except that each clause's `β` step is split off and paid (`erwp_step`). The rest
is `tailClause_steps_body`, `lastClause_steps_body`. So the answering function's run, the work's
run, the finaliser and the frame's answer are all below the stop's index, where `KapRelN` owes `κ`
(`erwp_idxLe`, `erwp_consistentAns` at the index the step left). `κ`'s cancel branch at `[handle-last]`
is the table of the operation's own cancel row (Core's `lastTc`). There it is the entry's cancel
obligation itself (`OpTabN.Sub`, which `erwp_handle_le` asks), and `LastFinOK`'s first conjunct
makes it not `⊤`.

**Two readings at the view.** Typed code reads its argument at a view consistent with it (`⊸`).
- The answering functions, the works and `h_ret` get the handled run's payloads and value. The
  handled run starts from the part of the resource consistent with the view (`gN_splitC`). Its
  stops and its value are consistent too (`rwpG_consistentXV`, `consistentX_left`).
  `erwp_consistentPA` moves the run to `T.withPA c n`, the table whose entries of the handler's
  name read their payload at `c`; `erwp_handle_le` reads the clauses there.
- The answer `κ` is resumed at is the answering function's (or the work's) value. It is
  consistent with the view across that run's resumptions (`erwp_consistentAns`), which is §10.2's
  answer reading. The exit's argument is a part of the work's value.

**The frame at the record list.** Core's `ewp_frame_then` reads its frame at the record list
(`Fr : List SRec → WProp`); `[handle-last]`'s frame is `κ`'s relation at the stop's list. The
chain's `erwp_frame_then` and `then_cancelN` read it the same way now, carried along the
continuations' `extF` (`hFe`), as `erwp_frame_plain` does. `then_compatN` passes its list-free frame.

**Restated:**

| Declaration | Was | Is |
|---|---|---|
| `then_cancelN` | `Fr : WProp` | `Fr : List SRec → WProp` with `hFs` (same members) and `hFe` (along `extF`); `hD` and the unrestricted condition read `Fr ls` |
| `erwp_frame_then` | `Fr : WProp` | the same; `hU`, `hD`, `hkv` and the conclusion read `Fr ls` |

**Unspent:** the rules' `n ≠ 0` and `n ≠ Div` (`hn0`, `hnd`), in both rules. Core reads `hnd` only
at its `Row.divB` split and `hn0` only in its `ewp_handle`, and neither has a counterpart at the
chain (E13; `erwp_handle_le` takes no `n ≠ 0`). `handleT_compatN` and `handleL_compatN` do not take
them.

### 10.6 The scheduler's answers

The brief asked whether the requirement §10.2 added to `Goal791SchedN` can be derived from
`SchedOKN`'s other fields. The requirement is that `SchedOKN` at `rowTabN` has the scheduler resume
with answers consistent with the view. **Not derived; obstruction not verified.**

- **Where the requirement sits.** It is not a field. It is inside `SchedOKNLe.op`'s premise: the
  clause is asked to run for every `κ` with `KapRelN … en …`. `KapRelN` resumes `κ` only at the
  entry's answers `en.PB`, which at `rowTabN` are `vN B δ Θ ∧ ConsistentX c`. The premise is
  contravariant in `PB`. Reading the answers without `ConsistentX` makes `KapRelN` stronger, so
  `op` asks less. No other field (`down`, `names`, `tags`, `fin`, `wc`, `qdown`, `ret`) reads `PB`.
  Dropping the requirement therefore means taking `op` at the plain reading and obtaining it at
  the view's reading.
- **Why `erwp_consistentAns`'s argument does not reach it.**
  - *In a program's handlers* (`erwp_handle_tail`, `erwp_handle_last`, the fuel handler), the proof
    builds the clause's run, and the proof resumes `κ`, at the value of a run it holds as an
    `erwp`. That value is consistent with the view.
  - *At the scheduler*, the clause's run is the hypothesis `op` itself. `κ`'s resumption happens
    inside that hypothesis, which takes `κ`'s relation as an input. To use `op` at the plain
    reading, `erwp_schedHandle_le` → `erwp_handle_le` must hand it a `KapRelN` resumable at every
    answer in `vN B`. The `κ` it builds resumes the task's continuation. The task's run is at
    `rowTabN`, read off `FundamentalN`, so that continuation is owed only at answers consistent
    with the view.
  - The step needed is therefore an `erwp` at the scheduler's table from a resource inconsistent
    with the view. `erwp` does not read the view, and no lemma gives such a run.
- **What would make it follow.** One of:
  - a reading of `op` that asks the clause only at runs that keep the view, for example `KapRelN`
    whose resumption also assumes the composite consistent. That restates the requirement; it does
    not derive it;
  - a parametricity fact about the clause's run. `erwp` does not provide one.
- **The statement is unchanged.** `Goal791SchedN` and `hs_schedOKN` are as before. The hardest
  case's row answers `park` at `∅` (`hardestRow_entry_PB`), so its instance meets the requirement.

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
| `arrNew` | `arrNew_compatX`, `tabFill_wp`, `wpTS_tab`, `alloc_block` (`Core/ArrayWp.lean`) | `rwpG_tab`/`erwp_tab` (the `tab` step at the index: `alloc_blockN`, `n` of `TWNC.alloc`, a block from `finDom_block`), `tabFill_wpN` by Core's induction: `bang_app` (F2), `erwp_bind_frame` (W4), `rwp_store` |
| `arrFree` | `arrFree_compatX`, `dropFill_wp` | `erwp_det` at `Head.drop`, `erwp_free`, `bang_app`, `erwp_bind_frame` |
| `arrEmpty`, `sliceEmptyI`, `sliceEmptyM` | `famEmpty_compatX` (`Core/SliceOps.lean`) | `vN_fam_mk` at `0` |
| `sliceSplitI`, `sliceSplitM` | `famSplit_compatX` | `vN_fam_split`, `erwp_det` at `Head.split` |
| `sliceGetM` | `famGet_compatX` (`Core/Slices.lean`) | as `arrGet`, the leaf a `mut` one (`noOwn` of `mutL`) |
| `sliceLenM` | `famSize_compatX` | as `arrSize` |
| `sliceReplaceM` | `sliceReplaceM_compatX` | `erwp_M_antiFrame` at the view (R2, as `withswap_compatN`) at the leaf, `rwp_load`, `rwp_store`, `sepRange_pick` |
| `sliceSwapM` | `sliceSwapM_compatX` | the same at one leaf (`i = j`) or two nested (`sepRange_pick2NW`) |
| `sliceBorrowM` | `sliceBorrowM_compatX`, `wpTS_M_frameFam`/`wpTS_M_frameList` (`Core/SliceFrames.lean`) | `erwp_M_frameFamN`: the list induction over the one-cell frame at the empty table (`erwp_M_frameR`, as `withbor2_compatN`), each cell its own key `Θ + (ℓᵢ, αᵢ)`, `αᵢ₊₁` fresh for the world after `ℓᵢ`; the callback reads every leaf at the innermost lifetime through `Mut`'s slack `@aδ ⊑ b` |
| `sliceBorrowI` | `sliceBorrowI_compatX`, `wpTS_I_frameFam` | `erwp_I_frameListRN` at the pure row's table: the list induction over `erwp_I_frameRR` (R5 at an incoming claim), one `imm` record per cell (`LocTy.addImm`), the inner frames' run read at the lender's view by `erwp_tieEntryR` |
| `sliceBorrowMU` | `sliceBorrowMU_compatX` (`Core/EffBorrow.lean`), `wpG_M_frameFam` | the list induction over `erwp_M_frameR` at a `Row.Unwind` table (abortive entries), as `withbor2U_compatN` |
| `sliceBorrowIU` | `sliceBorrowIU_compatX`, `wpG_I_frameFam` | `erwp_I_frameListRN` at the row's table, as `withbor1U_compatN` |
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

### 11.2b Built in `Core/Chain/FamSwap836N.lean`, `FamNew836N.lean`, `FamImm836N.lean`

| Row | Chain lemma | Core proof |
|---|---|---|
| `sliceSwapM` | `sliceSwapM_compatN` (`sepRange_pickW`, `sepRange_pick2NW`) | `sliceSwapM_compatX` |
| `arrNew` | `arrNew_compatN` (`erwp_tab`, `tabFill_wpN`) | `arrNew_compatX`, `wpTS_tab`, `tabFill_wp` |
| `sliceBorrowI` | `sliceBorrowI_compatN` (`sliceBorrowI_sem`, `erwp_I_frameListRN`) | `sliceBorrowI_compatX`, `wpTS_I_frameFam` |
| `sliceBorrowIU` | `sliceBorrowIU_compatN` (`sliceBorrowIU_sem`, `erwp_I_frameListRN`, `fin_claimArrI`) | `sliceBorrowIU_compatX`, `wpG_I_frameFam` |

**`sliceSwapM`** is `sliceReplaceM_compatN`'s steps. At `i = j` one anti-frame opens the leaf's
cell, which is read twice and written twice. At distinct leaves each leaf is opened by its own
`erwp_M_antiFrame` at the view, the inner one at the outer one's table (`erwp_mono`: the empty
table stops nowhere); the contents are read and written crosswise, each moving to the other cell
with its witness, which lies in that cell's stratum (the leaf's uniformity clause). The family is
rebuilt at the end's index by `sepRange_pick2NW` (`sepRange_pick2N` with the rest read at a
weaker predicate).

**`arrNew`.** `alloc_worldN`/`alloc_blockN` are Core's `alloc_world`/`alloc_block` at `TWNC`.
`rwpG_tab` is `wpTS_tab` at the index: the `tab` step is the configuration's one head step
(`head_tab_inv`), to `tabFill`, a non-value; the run after it is the continuation's from the world
`alloc_blockN` builds, its update composed with the allocation's (`UpdVN.trans`), the index paying
for the step. `erwp_tab` is `rwpG_tab` at `erwp`. `tabFill_wpN` is Core's induction, the filled
cells read at the index left after each store; the placeholders are consistent with every view
(`consistentX_sepRange_own`).

**The `n`-cell Imm Frame.** `erwp_I_frameRR` is `erwp_I_frameR` with the callback's raises at
`opTableR Tb R` and the lender's at `opTableR Tb (claimI ℓ v ρ_P̂(v) ⋆ R)`, `R` in the lend's
stratum; only the `raise` case differs (the lend's claim joins `R`). `erwp_I_frameListRN` is the
list induction over it at an abortive table, each frame:

- lends its leaf `imm` at `αⱼ` below the frame's rest, the payloads' stratum, the result's and the
  bound, its record `(pⱼ, αⱼ)` in the inner frames' world `Θ.addImm (pⱼ, αⱼ)`, whose run is read at
  the lender's view (`erwp_tieEntryR`, `erwp_tieEntry` at `opTableR`);
- hands the inner frames the bound `@R ⊓ αⱼ ⊓ γ` as printed;
- moves what the inner frames returned to the world without its record
  (`LocTy.extR_of_addImm`), and its claim joins theirs, the cells owned again (`claimL` at the
  frames' index).

The callback runs at the world holding every record (`LocTy.addImms`), each lent below the bound
and on the callback's list, so its resource extends there (`LocTy.extR_addImms`). It receives
every leaf at the innermost lifetime (`immLeafN`, `vN_immLeaf`; `immCell` reads `α ⊑ ⊓s`). At an
unwinding row the row's table reads no record (`tabN_unwind_addImms`), and the finaliser consumes
the composite claim at a raise as in `sliceBorrowMU_sem`.

### 11.3 Not built

Every row of §11.1 is built at `SemJN`. Like the unit's other rows, the four `*_compatN` of
§11.2b are lemmas that no fundamental-property case reads yet.

## 12. Unit L7: `ν` at `erwp` (#837)

### 12.1 Core's clause and its laws

Core reads `νX. C` (`Core/Relation.lean`, `cC .nu`; `Core/NuRel.lean`) as the greatest fixed point
of one unfolding of the observation tree `C`, written in `Prop` as an existential over candidates
(`docs/scope-recursion.md` §3.1):

    cC (νX. C) ls δ e ρ  =  C.NuShape → ∃ R : CPred, R ⊆ cB (nuEnv C R) C δ ∧ R ls e ρ

`cB η C` is `cC`'s `F`, `&`, `F_Σ`, `⊸` and `∀` clauses with the answer of each leaf read under
the type-variable environment `η`; `nuEnv C R` reads the variable `U X` as `thunkR R` (Core's `U`
clause with the candidate in place of `𝒞⟦νX. C⟧`) and gives it the closed type `U(νX. C)`, which
the `Imm` clause's `CohE` reads (`tClose`). The leaves are positive (`NuLeaf`, `VTy.Poly`: `X`
only under `⊗`, `⊕`, `[@a]`), so `cB` is monotone in the candidate (`cB_mono`, `nuF_mono`). The
laws: `nuRel_coind` (coinduction), `nuRel_out`/`nuRel_roll`, `cC_nu_unfold`, and `cC_nu_iff`
(`𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at `NuOk`, through `cB_unroll` and `vCE_nuEnv`). Every
relation law reaches `ν` the same way: unfold, apply the law's `cB` version, roll (`cC_step` with
`cB_step`, `cC_bind` with `cB_bind`, `cC_tyEq_aux` with `cB_tyEq` at `nuEnvU`). Core cites spec §7
and no [TR] number: `ν` is not in the paper.

### 12.2 The reading at `erwp`

Core's answer, at the chain's signature. A candidate is `cN`'s signature at a fixed `δ`
(`CandN : LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop`, Core's `CPred` with
the world, the view and the index added), and

    cN (νX. C) δ Θ c n ls e ρ  =  C.NuShape → ∃ R : CandN, R ⊆ cBN U(νX. C) R C δ ∧ R Θ c n ls e ρ

`cBN S R` is `cN`'s `F`, `&`, `F_Σ`, `⊸`, `∀` clauses (Core's `cB`), the leaf answers read by
`vNX S (thunkRN R)`. A row's operation answers are read as in `cN`, at the view
(`vN B δ Θ ∧ ConsistentX c`, §10.2), through `tabN`/`finN`. `vNX S P`/`vOX S P` are `vN`/`vO` with one type variable: `X` reads `P`
(`True` in the observable view, Core's `nuP false`), every other variable is empty, and the `Imm`
clause's witness reads the closed type `A[S/X]` (Core's `tClose`). `thunkRN R` is `vN`'s `U`
clause with the candidate in place of `cN`: at every `ExtR` extension of the world at the thunk's
resource, every view consistent with it and every record list (Core's `thunkR`). No departure:
the step index passes through the candidate unchanged, as the world and the view do.

The chain has no type-variable environment (F8), so the one variable of a `ν` body is carried by
`vNX`, a copy of `vN` with Core's environment at one entry; `vNX S (vN S δ) A δ = vN A[S/X] δ`
(`vNX_inst`, Core's `vCE_subst` at `scons`) is what makes one unfolding at `𝒞⟦νX. C⟧` the
unrolling.

### 12.3 `cN_of_valid` at `ν`

`cN_of_valid` says a computation may assume its resource valid: `(Valid ρ → cN C … ρ) → cN C … ρ`.
With `ν` read as `False` it fails at `ν`: from `Valid ρ → False` nothing gives `False` (the
premise holds at every invalid `ρ`). That is why it carried `noNuSpine C`, and with it `app`,
`bind`, `unitE`, `tensorE`, `sumE` and `zeroE`. With the fixed point the law holds at `ν` by
coinduction: the candidate `R′ = {ρ | Valid ρ → 𝒞⟦νX. C⟧ ρ}` is a post-fixed point, since at a
valid `ρ` the unfolding of `𝒞⟦νX. C⟧` is one at `R′` (`cBN_mono`), and `cBN` may assume validity
(`cBN_of_valid`, the tree version, by `cN_of_valid`'s own induction).

### 12.4 Built (`Core/Chain/Goal791N.lean`, `Iface834N.lean`, `TyEq834N.lean`, `Nu837N.lean`)

| Core | Chain |
|---|---|
| `cC .nu`, `cB`, `vCE (nuEnv C R)`, `effRetE`, `thunkR`, `CPred` | `cN .nu`, `cBN`, `vNX`/`vOX`, `retNX`, `thunkRN`, `CandN` |
| `cB_mono`, `nuF_mono` | `cBN_mono` (`vNX_mono`, `retNX_mono`, `vNX_occ`), along `CandN.LeOK`: `U X` reads a candidate only at `OK` worlds |
| `nuRel_coind`, `nuRel_out`, `nuRel_roll`, `cC_nu_unfold` | `cN_nu_coind`, `cN_nu_out`, `cN_nu_roll`, `cN_nu_unfold` |
| `vCE_nuEnv`, `vC_inst_envS`, `cB_unroll`, `effTab_instT`, `cC_nu_iff` | `vNX_inst_occ`, `vNX_inst_poly`, `retNX_inst`, `tabN_instT`, `thunkRN_nuCand`, `cBN_unroll`, `cN_nu_iff` |
| `cC_step` at `ν` (`cB_step`) | `cN_head` at `ν` (`cBN_head`); `cBN_step`, `cBN_pureSteps` |
| `cC_congr` at `ν` (`cB_congr`) | `cN_congr` at `ν` (`cBN_congr`, `vNX_congr`, `vOX_congr`, `retNX_congr`) |
| `cC_tyEq_aux` at `ν` (`cB_tyEq`, `cB_poly_ty`, `nuEnvU`) | `cN_tyEq` at `ν` (`cBN_tyEq`, `cBN_poly_ty` at the closed type `1`) |
| `cC_bind` at `ν` (`cB_bind`) | `cN_bind` at `ν` (`cBN_bind`) |
| (chain only) the index | `cN_down` at `ν` (`cBN_le`, `vNX_down`): the candidate closed upward in the index at `Down` worlds |
| (chain only) the view | `cN_of_valid` at `ν` (`cBN_of_valid`), §12.3 |
| `nuIn_compatX`, `nuOut_compatX` | `nuIn_compatN`, `nuOut_compatN` |
| `unfold_compatX`: `candN`, `candN_post`, `map_ok`, `node_ok` | `unfoldN_compatN`: `candNN`, `candNN_post`, `map_okN`, `node_okN`, over Core's terms and reductions (`Core/Nu.lean`). The candidate holds at the indices up to the step's, at `OK` worlds and at views consistent with the resource, where `U X` reads it; the step is at every world (`LocTy.extR_empty` at `!`'s empty resource) |

`noNuSpine` is gone: `cN_of_valid`, `cN_bind`, `app_compatN`, `bind_compatN`, `unitE_compatN`,
`tensorE_compatN`, `sumE_compatN` and `zeroE_compatN` hold at every conclusion. `CTy.inFrag`
admits `ν` at a covered body (`CTy.inFragNu`, `VTy.inFragNu`: the body's variable `X`).

Restated:
- `noEffSpine` excludes `ν` (was `True` there): `cN_extA` at `ν` would need its trees' leaves
  stable along `ExtA`, and they hold effect rows and `⊸`. `cN_extA` has no caller.
- `ExtRLit791.tyC` is `Mut 'x 1 ⊸ F 1` (was `Mut 'x 1 ⊸ ν(F 1)`), `vUgen`'s codomain with it;
  `not_valid_at_lend` is stated at the thunk `()` and an index `n > 0` (was any `v`, any `n`),
  refuted from the typed world of the two cells (`world_two`). `extRL_breaks_extA` keeps its
  statement.
- `cN_of_valid`, `cN_bind` and the six rules lost the premise `noNuSpine C`; `noNuSpine`,
  `noNuSpine_of_inFrag` and `noNuSpine_effOf` are removed.

### 12.5 Not built

- **`reify`** (Core's `reify_compatX`, `candR`, `reify_next`, `reify_close`). Core's candidate
  holds a loop made at a tick, whose continuation is owed at every `Ext`-extension of the list the
  loop is observed at (`candR`'s first disjunct). On the chain the loop is read through `U X`
  (`thunkRN`, as `vN`'s `U` clause), at every record list, while the tick's stop owes its
  continuation only at `extF`-extensions of the stop's own list (`entN`'s `wc := extF`). The
  first disjunct of the chain's candidate therefore has no source at a list the stop's
  continuation is not owed at. Not derived. `thunkRN` is `vN`'s `U` clause, so the loop is also
  asked at the worlds and views at which E10's Core step is refuted (§10.1, `not_kapRelKTyN`); no
  configuration is built for `reify` itself.
