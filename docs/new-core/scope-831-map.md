# #831: the rule-by-rule map for `FundamentalN`

Branch `rule-791` (from a711a05c). `FundamentalN` (`Core/Chain/Goal791N.lean`) asks `SemJN` of
every `CDerives` derivation whose judgment is in the fragment (`JdgInFrag`). This document maps
each of `CDerives`'s 104 constructors (`Core/Fundamental.lean:200`) to Core's compatibility lemma
(the case of `fundamentalC`, `Core/Fundamental.lean:773`), its fragment status, and its chain
counterpart. The Lean configurations are `Core/Chain/Map831N.lean`.

Kernel target: `FundamentalN` over `erwp` at the per-lend world; the map is the plan for proving
it rule by rule, following each of Core's printed proofs.

## 1. Reading the table

**Frag.** Whether the constructor's conclusion can be in the fragment (`VTy.inFrag`,
`CTy.inFrag`; type variables, `μ`, families, opaque types and `ν` are outside):
- **yes**: the conclusion is in the fragment when its parameters are, and every premise's
  judgment is then in the fragment too;
- **cut**: the conclusion can be in the fragment while a premise's judgment is outside it (an
  intermediate type that does not appear in the conclusion: `bind`'s `A`, `app`'s `A`, a
  handled row's `E`, `unroll`'s `μ`, …). `FundamentalN`'s induction gets no hypothesis at such a
  premise until the excluded former has a clause (§4). The rule's own port is unaffected;
- **no**: every instance of the conclusion is outside the fragment, so `FundamentalN` does not
  quantify over it.

**Chain.**
- **proved**: a compatibility lemma at `SemJN` exists (named);
- **portable**: Core's proof is followed step by step; the chain lemma for each step is named,
  and a missing one is marked *buildable* (with the existing lemma it would be built from).
  *Buildable* is a reading of Core's proof against the chain's lemmas, not a build;
- **blocked**: backed by a configuration in Lean with every hypothesis discharged;
- **pending**: not derived; obstruction not verified. Treated as portable-pending.
- **out**: outside the fragment; §4 says what bringing it in would need.

Shared chain pieces the rows cite (missing unless a file is named; each is a lemma of Core's
run-up, at `gN`/`vN`/`erwp`):
- **G1** `gN` at the context premises: a split along `Ctx.SplitP` (Core's `gDenC_split`), a slot
  at `SoloP` (`gSepC_soloP`), a dead or banged context owning nothing (`gSepC_deadP`,
  `gSepC_persistent`). Buildable from `gN`'s definition.
- **G2** `gN` along `ExtR` at the context's resource (Core's `gDenC_local`): buildable, `vN_extR`
  slot by slot with `ExtR.left`/`.right`.
- **G3** a frame beside a run (Core's `wpTS_bind_frame`/`ewpTS_bind_frame`). At the empty table
  the parts exist: `rwp_of_erwp_empty` (`Lend791N.lean:201`), `rwp_frame` (`SI/WpN.lean:254`),
  `rwp_bind` (`SI/WpN.lean:223`), `erwp_of_rwp`/`erwp_bindR` (`SI/BindN.lean:87/93`); one lemma
  composing them is buildable. At a row's table see E5.
- **G4** a closed value of a dead context's judgment is one at every substitution (Core's
  `semV_dead_closed`): buildable.
- **G5** `SemJN` from `vN` of a value: `erwp_val` (`SI/ErwpN.lean:229`), exists.
- **G6** `gN` at a lower index (`gN_le`, from `vN_le`): buildable. The chain's `⊸` quantifies over
  `k ≤ n`, which Core's has no counterpart of.
- **G7** the view's consistency at a split part: `SemJN` gives `ConsistentX c ρ` of the whole;
  `consistentX_left`/`_right` (`SI/LocTy.lean:595/603`) ask `ResU.Valid ρ`, which
  `erwp_of_valid` (`Cancel791N.lean:180`) supplies at the run. Buildable at each run; not verified
  at a conclusion that is not an `F`/`F_Σ` (the clauses reach their run first).
- **G8** `vN_tyEq`/`cN_tyEq` (Core's `vC_tyEq`/`cC_tyEq`, `Core/Alpha.lean`): missing; `vN_congr`
  covers only `δ`-agreement. Buildable by Core's induction; the largest structural piece.

Effect pieces (`Core/EffFin.lean`, `Core/DivHandle*.lean`):
- **E1** `RowLe S S′ → OpTabN.Le (tabN …)`, for `erwp_tabLe` (`SI/TabLeN.lean:77`).
- **E2** a row's lookup into its table (`Row.tab_find`) and `cancelOKN` at the empty context
  (`ent_start`).
- **E3** `tabN`'s `CtxClosed` at a context with no handler or catcher (for `erwp_bind`); only
  `empty_ctxClosed`, `OpTabN.ctxClosed_of_fin` exist.
- **E4** a raise's introduction at `raiseStopN`.
- **E5** the frame at a row's table (`ewp_frame_plain`/`ent_plain`): owning across must-resume
  stops, owning nothing where the row cancels, empty at an unrestricted row, with the cancel
  obligations carried. `erwpG_frame` (`SI/AntiStopN.lean:440`) and `erwp_frameL`
  (`SI/FinPerformN.lean:33`) are its special cases.
- **E6** `erwp_ubind` with unrestricted operations in `Σ_M` (`hP`, `hU`) and `ThenLe` read as its
  side conditions. **E7** `erwp_ubind` with a finaliser whose row holds `Div`.
- **E8** the clauses' reading at `vN` for `erwp_handle`'s premise (`KapRelN`), and the split of
  `tabN (ofEff n E 0 fs ++ S)` into inner and outer tables. `handle_sem`, `clauses_sem`,
  `kap_sem` at `sV` (`SI/Sem.lean`) are the model.
- **E9** `vN` read off `cN (.ret A)` at a value (Core's `wpTS_val_post`).
- **E10** the BOXED-κ stop lemma at `erwp` (Core's `stop_sem`).
- **E11** the tail- and last-clause instances (`tailTuple`, `lastTuple`, `LastFinOK`).

All of E1–E9 and E11 are buildable by Core's proofs over the chain's existing `erwp` lemmas
(`erwp_handle` needs no `hdv`; a row holding `Div` is a row of the table, so Core's `cwp`
branches are the same lemmas). E10 is not derived.

## 2. The table

| # | Constructor | Core lemma | Frag | Chain | Counterpart |
|---|---|---|---|---|---|
| 1 | `var` | `var_compatC` (`Compat.lean:47`) | yes | **portable** | `gSepC_soloP`, `wpTS_val` → G1 (`gN` at `SoloP`), `erwp_val` |
| 2 | `unitI` | `unitI_compatC` (`Compat.lean:56`) | yes | **portable** | `gSepC_deadP`, `wpTS_val` → G1, `erwp_val` |
| 3 | `tensorI` | `tensorI_compatC` (`Compat.lean:63`) | yes | **portable** | `gDenC_split`, `wpTS_bind_frame` ×2, `wpTS_val` → G1, G3 at the empty table (`rwp_of_erwp_empty`, `rwp_frame`, `rwp_bind`, `erwp_of_rwp`), G6 (`vN_le`/`gN_le`), G7 |
| 4 | `sumI₁` | `sumI₁_compatC` (`Compat.lean:80`) | yes | **portable** | `wpTS_bind`, `wpTS_mono`, `wpTS_val` → `erwp_bind` (`empty_ctxClosed`) or `erwp_bindR`, `erwp_mono`, `erwp_val` |
| 5 | `sumI₂` | `sumI₂_compatC` (`Compat.lean:87`) | yes | **portable** | as `sumI₁` |
| 6 | `thunkF` | `thunkF_compatC` (`Compat.lean:105`) | yes | **portable** | `wpTS_val`, `cC_head`, `gDenC_dead_cons`, `gDenC_local` → `erwp_val`, `cN_head`, `gN`'s dead slot by definition, G2 |
| 7 | `thunkV` | `thunkV_compatC` (`Compat.lean:118`) | yes | **portable** | `wpTS_val`, `forceE_of_not_ret`, `gDenC_local` → `erwp_val`, G2 |
| 8 | `ret` | `ret_compatC` (`Compat.lean:130`) | yes | **portable** | the identity (`jdgC`) |
| 9 | `bind` | `bind_compatC` (`Compat.lean:179`) | cut | **portable** | `gDenC_split`, `cC_bind`, `cC_head`, `gDenC_mk` → G1, G7, `cN_head`; `cN_bind` (Core's `cC_bind`, by induction on `C`: `erwp_bindR` at `F`/`F_Σ`, the clauses' parts elsewhere, with G2/G6 to re-enter `M` at the clause's world and index): buildable |
| 10 | `force` | `force_compatC` (`Compat.lean:145`) | yes | **portable** | `gSepC_soloP`, the thunk at `Ext.refl` → G1, `LocTy.extR_refl` |
| 11 | `lam` | `lam_compatC` (`Compat.lean:154`) | yes | **portable** | `cC_head`, `gDenC_mk` → `cN_head`, G2 and G6 (the chain's `⊸` is Kripke along `ExtR` and the index) |
| 12 | `lamDead` | `lamDead_compatC` (`Fundamental.lean:79`) | yes | **portable** | `lam`'s, and a live `1` slot read as dead (`gSepC_cons_persistent`): buildable |
| 13 | `app` | `app_compatC` (`Compat.lean:164`) | cut | **portable** | `gDenC_split`, `gSepC_soloP`, the function at the argument → G1, G7, `cN`'s `⊸` at `extR_refl`, `k = n` |
| 14 | `withI` | `withI_compatC` (`Compat.lean:222`) | yes | **portable** | `cC_head` ×3, `gDenC_dead_cons` → `cN_head` |
| 15 | `proj₁` | `proj₁_compatC` (`Compat.lean:249`) | yes | **portable** | `cN`'s `&` clause, first part |
| 16 | `proj₂` | `proj₂_compatC` (`Compat.lean:256`) | yes | **portable** | `cN`'s `&` clause, second part |
| 17 | `topI` | `topI_compatC` (`Compat.lean:263`) | yes | **portable** | `cN .top` is `True` |
| 18 | `unitE` | `unitE_compatC` (`Compat.lean:269`) | yes | **portable** | `gDenC_split`, `cC_bind`, `cC_head` → G1, G7, `cN_bind`, `cN_head` |
| 19 | `tensorE` | `tensorE_compatC` (`Compat.lean:282`) | cut | **portable** | as `unitE`, and `vN`'s `⊗` clause |
| 20 | `sumE` | `sumE_compatC` (`Compat.lean:304`) | cut | **portable** | as `unitE`, and `vN`'s `+` clause |
| 21 | `zeroE` | `zeroE_compatC` (`Compat.lean:330`) | cut | **portable** | as `unitE`; `vN .zero` is `False` |
| 22 | `allI` | `allI_compatC` (`Compat.lean:345`) | yes | **proved** | `allI_compatN` (`Goal791N.lean:941`) |
| 23 | `allE` | `allE_compatC` (`Compat.lean:483`) | yes | **portable** | `cC_tyEq` at `instLife`, the `∀` clause → `cN_tyEq` (G8) |
| 24 | `bangThunkF` | `bangThunkF_compatC` (`Compat.lean:380`) | yes | **portable** | `gSepC_persistent` and `thunkF`'s steps → G1 (banged context owns nothing), G2 |
| 25 | `bangThunkV` | `bangThunkV_compatC` (`Compat.lean:394`) | yes | **portable** | as `bangThunkF` at `thunkV` |
| 26 | `bangE` | `bangE_compatC` (`Compat.lean:406`) | yes | **portable** | `wpTS_mono` → `erwp_mono` |
| 27 | `copyBang` | `copyBang_compatC` (`Compat.lean:412`) | yes | **portable** | `gSepC_deadP`, `wpTS_val`, `wpTS_lolli` → G1, `erwp_val`, `cN_head` |
| 28 | `releaseBang` | `releaseBang_compatC` (`Compat.lean:431`) | yes | **portable** | as `copyBang` |
| 29 | `boxI` | `boxI_compatC` (`Compat.lean:496`) | yes | **portable** | `atLife_eq`, `wpTS_box`, `gSepC_outlives` → `vN_outlives` over `gN` (buildable); a run at the empty table from `Res_α` ends in `Res_α` (Core's `wpTS_box`): buildable |
| 30 | `boxE` | `boxE_compatC` (`Compat.lean:450`) | yes | **portable** | `wpTS_mono` → `erwp_mono` |
| 31 | `immSub` | `immSub_compatC` (`Compat.lean:456`) | yes | **proved** | `immSub_compatN` (`Goal791N.lean:905`) |
| 32 | `mutSub` | `mutSub_compatC` (`Compat.lean:468`) | yes | **proved** | `mutSub_compatN` (`Goal791N.lean:892`) |
| 33 | `alloc` | `alloc_compatX` (`Compatibility.lean:579`) | yes | **portable** | `gSepC_deadP`, `wpTS_val`, `wpTS_alloc` → G1, `erwp_alloc` (`SI/HandleN.lean:110`), `cN_head`, `vN_le` |
| 34 | `free` | `free_compatX` (`Compatibility.lean:539`) | yes | **portable** | `wpTS_free` → `erwp_free` (`SI/HandleN.lean:125`); `dFree_sem` (`Inst791N.lean:72`) is the instance at `Γ = []`, `A = 1` |
| 35 | `tokMint` | `tokMint_compatX` (`Tok.lean:61`) | no | **out** | `Tok = .opq .tok`; §4 opaque |
| 36 | `tokBurn` | `tokBurn_compatX` (`Tok.lean:82`) | no | **out** | `Tok = .opq .tok`; §4 opaque |
| 37 | `swap` | `swap_compatX` (`Compatibility.lean:594`) | yes | **portable** | `wpTS_lolli` ×3, `vC_local`, `wpTS_load`/`wpTS_store` → `vN_extR`, `erwp_bindR` with `rwp_load`/`rwp_store` (`SI/HeapN.lean:171/241`), `erwp_det`, `erwp_val` |
| 38 | `copy` | `copy_compatX` (`Compatibility.lean:653`) | yes | **portable** | `ptoImmS_dup` → `compS_imm_dup` (`SI/IStopN.lean:98`); `ImmWitW` is a proposition and is kept |
| 39 | `releaseImm` | `forgetImm_compatX` (`Compatibility.lean:675`) | yes | **portable** | `wpTS_I_forget` → `erwp_garbage` (`SI/BindN.lean:79`), `noOwn_of_imm` (`SI/RebAcrossC.lean:42`) |
| 40 | `releaseMut` | `forgetMut_compatX` (`Compatibility.lean:694`) | yes | **portable** | `wpTS_M_forget` → `dRelease_sem` (`Inst791N.lean:53`, at `Γ = []`), G1 to generalise |
| 41 | `releaseUnk` | `forgetUnk_compatX` (`Compatibility.lean:713`) | yes | **portable** | `wpTS_val` → `erwp_val` |
| 42 | `lit` | `lit_compatX` (`Integers.lean:289`) | yes | **portable** | `gSepC_deadP`, `wpTS_val`, `vP_lit` → G1, `erwp_val`, `vN`'s `int` clause |
| 43 | `hostOp` | `hostOp_compatX` (`Integers.lean:298`) | yes | **portable** | `host_call_sound`, `wpTS_head` → `erwp_det` (`Head.host`); `host_call_sound` at `vN` (`hostSig` uses only `int`, `⊗`, `+`, `1`, `0`): buildable |
| 44 | `arrNew` | `arrNew_compatX` (`Arrays.lean:500`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 45 | `arrFree` | `arrFree_compatX` (`Arrays.lean:560`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 46 | `arrSize` | `arrSize_compatX` (`Arrays.lean:265`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 47 | `arrReplace` | `arrReplace_compatX` (`Arrays.lean:369`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 48 | `arrLen` | `arrLen_compatX` (`Arrays.lean:132`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 49 | `arrGet` | `arrGet_compatX` (`Arrays.lean:171`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 50 | `arrCopy` | `arrCopy_compatX` (`Arrays.lean:224`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 51 | `arrRelease` | `arrRelease_compatX` (`Arrays.lean:253`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 52 | `countFold` | `countFold_compatX` (`CountFold.lean:94`) | yes | **portable** | Core: `countLoop_wp` (induction on `len − i`: `wpTS_count`, `wpTS_bind_frame`, `bang_app`, `wpTS_val`). Chain: `erwp_det`, `erwp_bind` (`empty_ctxClosed`), `erwp_val`, G3; `bang_app` at `vN` (a `!(A ⊸ B)` applied at a later world): buildable |
| 53 | `countTry` | `countTry_compatX` (`CountFold.lean:182`) | yes | **portable** | `countFold`'s, with the `case` steps by `erwp_det` |
| 54 | `boundedFix` | `boundedFix_compatX` (`BoundedFix.lean:91`) | yes | **portable** | Core: `cC_boundedFix` (`cC_head`), `fixSelf_valid` by induction on the budget along `Ext`. Chain: `cN_head`; `fixSelf_valid` at `vN` along `ExtR`: buildable, local to the rule |
| 55 | `iterate` | `iterate_compatX` (`DivIterate.lean:281`) | yes | **portable** | Core: `cwp_iterate` with the close projection. Chain: `erwp_iterate` (`SI/LoopN.lean:97`), stated where the tick always answers *next*; the version whose tick answers in `vN nextTy` (the close branch to `F R`): buildable from its induction; `tabN`'s `CtxClosed` at `iterK` (E3): buildable |
| 56 | `divFuel` | `divFuel_compatX` (`DivFuel.lean:392`) | yes | **portable** | Core: `divFuel_steps`, `fuel_total` (induction on the budget). Chain: `erwp_det` for the steps; the fuel handler as an `erwp_handle` instance with its clauses through `erwp_kappa_resume`/`erwp_kappa_cancel`: buildable (E8) |
| 57 | `reify` | `reify_compatX` (`DivReify.lean:513`) | no | **out** | `reifyTy`'s answer `U(Loop_Σ B R)` is `ν` (`Types.lean:1256`); §4 ν |
| 58 | `sliceBorrowM` | `sliceBorrowM_compatX` (`Slices.lean:60`) | no | **out** | `Array`; §4 families |
| 59 | `sliceBorrowI` | `sliceBorrowI_compatX` (`Slices.lean:176`) | no | **out** | `Array`; §4 families |
| 60 | `sliceGetM` | `sliceGetM_compatX` (`Slices.lean:315`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 61 | `sliceLenM` | `sliceLenM_compatX` (`Slices.lean:319`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 62 | `sliceSplitI` | `sliceSplitI_compatX` (`SliceOps.lean:83`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 63 | `sliceSplitM` | `sliceSplitM_compatX` (`SliceOps.lean:87`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 64 | `sliceEmptyI` | `sliceEmptyI_compatX` (`SliceOps.lean:99`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 65 | `sliceEmptyM` | `sliceEmptyM_compatX` (`SliceOps.lean:103`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 66 | `arrEmpty` | `arrEmpty_compatX` (`SliceOps.lean:108`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 67 | `sliceReplaceM` | `sliceReplaceM_compatX` (`SliceOps.lean:136`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 68 | `sliceSwapM` | `sliceSwapM_compatX` (`SliceOps.lean:299`) | no | **out** | families (`Array`/`ArrayImm`/`[Mut]`); §4 |
| 69 | `withbor1` | `withbor1_compatX` (`Compatibility.lean:937`) | yes | **proved** | `withbor1_compatN` (`ImmLend833N.lean`): the lend's record in the callback's world (`LocTy.extR_addImm`, Core's `ext_add`), the result back by `LocTy.extR_of_addImm` (`ext_drop`), the Imm Frame `erwp_I_frameR`, the run read at the lender's view (`erwp_tieEntry`) |
| 70 | `withbor2` | `withbor2_compatX` (`Compatibility.lean:1028`) | yes | **proved** | `withbor2_compatN` (`ImmLend833N.lean`): the Mut Frame `erwp_M_frameR` at the pure row, the callback's application under the pair framed beside the borrow, `vN_local` for the result |
| 71 | `withbor3` | `withbor3_compatX` (`Compatibility.lean:1109`) | yes | **portable** | `w3`'s 13 steps (`chain-interpretation.md` §6.3) at the empty table: `withbor3S_compat` (`Reborrow791N.lean:808`) without its finaliser frame, `erwp_M_antiFrame` (`SI/AntiStopN.lean:257`) around `erwp_M_frame`; restatement at `Δ`: buildable |
| 72 | `withload` | `withload_compatX` (`Compatibility.lean:252`) | yes | **portable** | `wl`'s steps (`chain-interpretation.md` §6.3) at the empty table: `withloadS_compat` (`Withload791N.lean:549`), `erwp_reborrow` (`SI/RebAcrossC.lean:96`) for 6.150; restatement at `Δ`: buildable |
| 73 | `withswap` | `withswap_compatX` (`Compatibility.lean:1194`) | yes | **portable** | `wpTS_M_antiFrameX`, `wpTS_load`/`wpTS_store`, `wpTS_bind_frame` → `erwp_antiFrame_view` (`SI/LocTy.lean:485`, `consistentX_get`), `rwp_load`/`rwp_store`, G3; the reseal into the stored family at the anti-frame's return as in `withbor3S_compat`'s step 13: not checked in detail |
| 74 | `withbor1U` | `withbor1U_compatX` (`EffBorrow.lean:452`) | yes | **proved** | `withbor1U_compatN` (`ImmLend833N.lean`): as `withbor1`, the Imm Frame across the row's raises (`erwp_I_frameR`), the finaliser frame at a raise (`erwp_ubindRaise`, `fin_claimI`); `opTable_ext` is not needed (`entN` reads no list) |
| 75 | `withbor2U` | `withbor2U_compatX` (`EffBorrow.lean:281`) | yes | **proved** | `withbor2U_compatN` (`ImmLend833N.lean`), at any `Δ` and a `Row.Unwind` row (abortive unrestricted operations included): the Mut Frame across raises `erwp_M_frameR`, `erwp_claimX_abort`, `erwp_ubindRaise` |
| 76 | `withbor3U` | `withbor3U_compatX` (`EffBorrow.lean:362`) | yes | **portable** | `withbor3S_compat`, restated as `withbor2U`'s row |
| 77 | `withloadU` | `withloadU_compatX` (`EffBorrow.lean:554`) | yes | **portable** | `withloadS_compat`, restated as `withbor2U`'s row |
| 78 | `sliceBorrowMU` | `sliceBorrowMU_compatX` (`EffBorrow.lean:651`) | no | **out** | `Array`; §4 families (the `sm` constant) |
| 79 | `sliceBorrowIU` | `sliceBorrowIU_compatX` (`EffBorrow.lean:732`) | no | **out** | `Array`; §4 families |
| 80 | `lolliE` | `lolliE_compatX` (`Compatibility.lean:512`) | cut | **portable** | `gDenC_split`, `wpTS_bind_frame` ×2, the function at `Ext.refl` → G1, G3, G6, G7, `extR_refl`, `rwp_consistentXV` |
| 81 | `allEV` | `allE_compatX` (`Compatibility.lean:731`) | yes | **portable** | `wpTS_bind`, `vC_tyEq` at `instLife` → `erwp_bindR`, `erwp_mono`, `vN_tyEq` (G8) |
| 82 | `ofRet` | the identity (`ofRet _ ih => ih`) | yes | **portable** | the identity: `SemJN` at `.val A` is `cN (.ret A)` |
| 83 | `roll` | `roll_compatX` (`Fundamental.lean:55`) | no | **out** | `μ`; §4 |
| 84 | `unroll` | `unroll_compatX` (`Fundamental.lean:60`) | cut | **out** | the premise is at `μ`; the conclusion `A[μX.A/X]` is in the fragment only where `X` is not free. §4 μ |
| 85 | `foldImm` | `foldImm_compatX` (`FoldImm.lean:625`) | no | **out** | `μ`; §4 |
| 86 | `foldOwn` | `foldOwn_compatX` (`FoldOwn.lean:358`) | no | **out** | `μ`; §4 |
| 87 | `foldReuse` | `foldReuse_compatX` (`FoldReuse.lean:426`) | no | **out** | `μ`; §4 |
| 88 | `foldOwnG` | `FoldP.foldOwnG_compatX` (`FoldOwnG.lean:1023`) | no | **out** | `μ` and families; §4 |
| 89 | `nuIn` | `nuIn_compatX` (`Nu.lean:601`) | no | **out** | `ν`; §4 |
| 90 | `nuOut` | `nuOut_compatX` (`Nu.lean:606`) | cut | **out** | the premise is at `ν`; the unrolling is in the fragment only where `X` is not free. §4 ν |
| 91 | `unfoldN` | `unfold_compatX` (`Nu.lean:576`) | no | **out** | `ν`; §4 |
| 92 | `effSub` | `sub_compatC` (`EffFin.lean:1446`) | yes | **portable** | Core: `effWp_sub`. Chain: `cN_effOf`, `erwp_tabLe` (`SI/TabLeN.lean:77`); `RowLe S S′ → OpTabN.Le (tabN …S…) (tabN …S′…)` (E1): buildable |
| 93 | `effPerform` | `perform_compatC` (`EffFin.lean:1454`) | yes | **portable** | Core: `ewp_bind_pure_frame`, `ewp_perform_here` (`Row.tab_find`, `ent_start`). Chain: `erwp_bind` (`SI/BindN.lean:36`), `erwp_performG` (`SI/LendCancelProg.lean:35`); E2, E3: buildable |
| 94 | `effAwait` | `await_compatC` (`Fundamental.lean:159`) | yes | **portable** | Core composes `perform`, `raise`, `sub`, `ret`, `var`, `sumE`, `let`; the chain's port composes their chain rows |
| 95 | `effRaise` | `raise_compatC` (`EffFin.lean:1470`) | yes | **portable** | Core: `ewp_bind_pure_frame`, `ewp_raise_here`, `vC_noOwn_of_ownFree`. Chain: `erwp_bind`; a raise's introduction at `raiseStopN` (E4, built inline in `erwp_handle`'s proof, `SI/HandleN.lean:447`): buildable; E2, E3; `vN` of an `OwnFree` type owns nothing: buildable |
| 96 | `effLet` | `let_compatC` (`EffFin.lean:1488`) | cut | **portable** | Core: `gDenC_split`, `effWp_step`, then `ewp_frame_plain` (or `cwp_bind` at a `Div` row). Chain: G1, `erwp_det`, `erwp_bind`, E3; the row frame (G3 at a row, Core's `ewp_frame_plain`/`ent_plain`: an owning frame across must-resume stops, owning nothing where the row cancels (`hW`), empty at an unrestricted row (`hU`)): buildable from `erwpG_frame`'s stop case and `erwp_garbage`. A `Div` row is a row on the chain (no `cwp`) |
| 97 | `effThen` | `then_compatC` (`EffFin.lean:1539`) | cut | **portable** | Core: `gDenC_split`, `ewp_frame_then` (`hfin`/`ThenLe`, `hP`/`PendPers`). Chain: `erwp_ubind` (`SI/UbindGN.lean:107`), `erwp_ubindClaim`, `erwp_ubind_cancelRun`, `erwp_ubindRaise`, `erwp_ubindClaimF`, `erwp_cfin_run`; `erwp_ubind` is stated without unrestricted operations in `Σ_M` and at a finaliser meeting `FinOK`: the version with Core's `hP`/`hU` (E6) and `ThenLe` read as the frames' side conditions: buildable; E5 for `Γ₂` beside `D` |
| 98 | `effThenDiv` | `then_compatC` / `then_compatC_div` (`EffFin.lean:1539/1602`) | cut | **portable** | `effThen`'s, and at a finaliser row holding `Div` (`hcap`), `erwp_ubind` with a finaliser that may tick (E7): buildable |
| 99 | `effHandleV` | `handleV_compatC` (`EffFin.lean:1810`) | cut | **portable** | Core: `gSepC_deadP`, `wpTS_val_post`, `ewp_handle_vals` (reads `hdv`). Chain: `erwp_handle` (`SI/HandleN.lean:447`; needs no `hdv`), `erwp_kappa_*`, `erwp_fold_at`/`erwp_unfold_at`; the clauses' reading at `vN` (`clauses_sem`/`kap_sem`/`handle_sem` at `sV`, `SI/Sem.lean`, are the model) and the split of `tabN (ofEff n E 0 fs ++ S)` into the inner and outer tables (E8); `vN` read off a value's `cN (.ret A)` (E9): buildable |
| 100 | `effHandleVB` | `handleV_compatCB` (`EffBoxed.lean:438`) | cut | **pending** | Core reads the BOXED-κ stop lemma `stop_sem` (`Fundamental.lean`, `stop_lemma`) and `ewp_handle_valsB`. Chain: E8, E9, and `stop_sem` at `erwp` (E10). E10 is not derived; obstruction not verified |
| 101 | `effHandleT` | `handleT_compatC` (`DivHandle.lean:680`) | cut | **portable** | Core: `wpTS_val_post`, `ewp_handle_tail` (or `cwp_handle_tail` at a `Div` row). Chain: `erwp_handle`; E8, E9, the tail-clause instance (`tailTuple`, E11): buildable |
| 102 | `effHandleL` | `handleL_compatC` (`DivHandleLast.lean:899`) | cut | **portable** | Core: `ewp_handle_last`/`cwp_handle_last` (`hCancel`, `hSu`, `LastFinOK`). Chain: `erwp_handle`; E8, E9, the last-clause instance (`lastTuple`) and `LastFinOK` read as the cancel obligations `cancelOblN` (E11): buildable |
| 103 | `letPoly` | `letPoly_compatC` (`PolyLet.lean:69`) | cut | **portable** | `gDenC_dead_cons`, `psub_fill`, `cC_head` → `cN_head`; the substitution lemmas are syntactic; the premise `hV` at any `j` is a cut |
| 104 | `alpha` | `alpha_compatJ` (`Fundamental.lean:766`; `alpha_compatC`, `Alpha.lean:915`) | yes | **portable** | `cC_tyEq` ∘ `CTy.alphaB_sound` → `cN_tyEq` (G8) |

## 3. The two risks

### 3.1 Risk 1: `withbor1U` and `LocTy.above`

**Answer (#833): with Core's `ls₀` and `Keeps`, Core's step goes through, and both rules are
proved.** `LocTy.above a` keeps the keys and the `imm` records lent strictly above `a`;
`LocTy.ExtR`'s record conjunct is Core's `Keeps` (`LocTy.Keeps`: the records relevant to the
resource, relevance read off the lifetime a record was lent at); `ImmWitW` matches a record no
shorter-lived than the cell, which makes it relevant to its cell (`chain-interpretation.md` §2.2, §3.2).

Core's step (`Core/EffBorrow.lean:452`, the last block): the Imm Frame hands the callback a list
with the lend's record added at `α`, and the callback is run there by its own Kripke clause,
`hvf ls′ (ext_add hadd hout₂)`. On the chain the record goes into the callback's world
(`LocTy.addImm`), an `ExtR` extension at the callback's resource in `Res_α`
(`LocTy.extR_addImm`, Core's `ext_add`); the callback's result `['x] B`, in `Res_α`, returns to
the world without the record (`LocTy.extR_of_addImm`, Core's `ext_drop`). The callback's run is at
the world's view, which has one more `imm` record than the lender's; an unwinding row's table (and
the pure row's) never resumes, so the relation reads its tie only at the entry, whose list is the
frame's and holds the record (`erwp_tieEntry`). `withbor1_compatN`, `withbor1U_compatN`
(`Core/Chain/ImmLend833N.lean`).

The old configuration (`callback_any_inst`, removed in 6ede48eb: at the old `above`, `𝒱⟦U(Imm 'x 1 ⊸ F 1)⟧` admitted
every value at a callback holding a `mut` borrow) rested on no extension holding an `Imm` value;
at the same world and resource the world with one more record is an extension
(`Map831N.extR_addImm_inst`) holding one (`Map831N.imm_at_extension`).

**Headlines.** `constN_w2`/`w3`/`wF`/`wl` and their `_inst`, `goal791Sched_of`, the `*Prog`
results, `erwp_consistent` and the `vN`/`cN` laws keep their statements. `withload`'s image cells at
`Imm` positions get their lifetimes from the run's tags (`lifeBoundW_of_entry`, Core's
`lifeBound_of_tagged`), which needs the entry tie to match a record's lifetime (`ImmTieL`).

### 3.2 Risk 2: `cN_extA` at `F_Σ R`

**Verdict: needed by no rule.** Core has no computation-level transport along `Ext`:
`fundamentalC`'s proofs move values (`vC_local`) and contexts (`gDenC_local`) along `Ext`, and
the one table-level transport, `opTable_ext` (`Core/EffBorrow.lean:439`), is used only by
`withbor1U_compatX` (`:490`) and `sliceBorrowIU_compatX` (`:786`), to carry the callback's ends
(a value of `B`, or a stop of an abortive table) along `Ext` for the Imm Frame's premise `hQ`.
On the chain:
- a run's world is fixed (`cN … Θ` is `erwp (Θ.view c) …` at `Θ`'s tables), and `U`/`⊸` give
  the body at every `ExtR` extension directly, so `thunkF`, `thunkV`, `lam`, `withI`, `force`,
  `app` move only values and contexts (`vN_extR`, G2);
- the Imm Frame's `hQ` at `erwp` (`erwp_I_frame*`, `SI/IStopCancelN.lean`) asks the post to be
  stable along `Ext` of the *list*, and `opTableN`'s entries (`entN`) do not read the list, so
  `opTable_ext`'s counterpart is immediate; the callback's ends are values, carried by `vN_extR`.

**Provable?** Not derived; obstruction not verified. Where it would be needed is an `erwp` lemma
over tables whose payloads grow and whose answers agree (`chain-interpretation.md` §7): the
table's answers at `Θ′` are `vN B δ Θ′`, which `vN_extA` makes larger, while the continuation
was given only answers at `Θ`. Since no rule needs it, it is on no unit's path.

## 4. Out of the fragment: what bringing each former in would need

Core's clauses and laws are as surveyed in `Core/Relation.lean`, `Core/RelMu.lean`,
`Core/NuRel.lean`, `Core/SepRange.lean`, `Core/SliceFrames.lean`. No chain file has a family, `μ`
or `ν` clause (`sV`, `SI/Sem.lean`, reads them as `False` too).

**Families (arrays, `ArrayImm`, `[Mut]` slices; 21 rows, and the `sm` constant).** Core's clause
(`Relation.lean:151`): `v = arr(ℓ, c)`, `c < 2³¹`, `sepRange (λm. 𝒱⟦L⟧(loc m)) ℓ c`, one clause
for every leaf (`Ref`, `Imm`, `Mut`). Needs, on the chain:
1. a `fam` clause in `vN` and `vO`: an indexed `sepRange` of leaves at `Θ` and the index, with
   `vP_fam_iff`/`_mk`/`_idx`/`_split`/`_join`, `noOwn_fam`, `noOwn_arrayImm` (`Core/Arrays.lean`,
   `Core/SliceFrames.lean`), and the existing laws (`vN_down`, `vN_congr`, `vN_extR`,
   `vN_outlives`, `vN_outlivesLe`) re-proved over it;
2. `erwp` rules for the array primitives (`arrNew`'s `tab`, `arrFree`'s step, `idx`, `size`,
   `split`, `replace`, `swap`; Core's `ArrayWp.lean` lemmas and `tabFill_wp`, `Arrays.lean`);
3. the `n`-cell frames: Core's `wpG_M_frameFam`/`wpTS_M_frameFam` and `wpG_I_frameFam`/
   `wpTS_I_frameFam` are list inductions over one-cell frames (`wpG_M_frameList`, …). The chain
   has the one-cell frames across stops, raises and layered cancel runs (`erwp_M_frameCRG`,
   `erwp_M_antiFrameCR`, `erwp_I_frameC`, `tabG_can`); the family frame is their list induction,
   each Mut Frame at `Θ + (ℓᵢ, α)` (one key per cell); its table the guarded twin, with
   `tabG_can` per layer;
4. for `sliceBorrowI`/`IU`: risk 1's `aboveL` change first (an `imm` lend of `n` cells adds `n`
   records);
5. for the `sm` constant: items 1–3 at `Row.Suspend`, and `sliceBorrowMU_compatX`'s two side
   conditions (`VOutlivesLe` at `A` and `B`, which `Const791.OK` carries). `sm`'s type contains
   `.array`, so `Const791.InFrag` fails for it and `ConstsN` (hence `goal791Sched_of`) does not
   ask for it today.

**`μ` and type variables (`roll`, `unroll`, the four folds).** Core's `μ` clause is a least
fixed point, impredicative over candidates `P : Bool → List SRec → Val → WProp`, with a type
environment `η` that `tvar` reads (`tEnvP`), and side conditions `A.NoMut 0` and `Cl 0`. Needs:
1. an environment argument for `vN`/`vO` (candidates over `LocTy → Nat → Val → WRes`), the `μ`
   and `tvar` clauses, and the laws `vCE_some`, `vCE_rename`, `vCE_subst`, `vCE_mono_at` (the
   `NoMut` side condition is what keeps a stored family `famL` fixed under the unrolling),
   `vC_roll`, `vC_unfold`, `vC_mu_iff`, `vC_ind`/`vC_mu_ind` (`Core/RelMu.lean`) at the index;
2. `foldImm`: `withload_sized` at `erwp` (the chain's `withloadS_compat` with a size measure,
   `dsize`), and `vC_immReborrow_mu_iff`; it reads `Imm (μ…)`, so the `Imm` clause's `ImmWitW`
   at a `μ` type (`RefPos.mu`, already in Core's syntactic positions);
3. `foldOwnG`: the family clause too.

**`ν` (`nuIn`, `nuOut`, `unfoldN`, `reify`).** Core's clause (`cC .nu`) is a greatest fixed point
written as `∃ R, R ≤ cB(nuEnv C R) C ∧ R ls e ρ`, not indexed (`Core/Nu.lean`'s `unfold_compatX`
uses no approximation). Needs a reading at `erwp`: a candidate `R` downward closed in the index
with `cN`-level `cB`/`nuEnv`, and `cB_unroll`, `nuF_mono`, `nuRel_coind`, `cC_nu_iff` at the index.
`reify` needs it too: its answer is `U(Loop_Σ B R)`, and `Loop_Σ` is a `ν` type
(`Core/Types.lean:1256`). The choice of reading is a design decision; not checked here.

**Opaque types (`tokMint`, `tokBurn`).** `Tok` is `.opq .tok` (`Core/Tok.lean:32`). Core's clause
is `k.rel v`; for `Tok` a fresh unit cell. Needs an `opq` clause in `vN` reading `k.rel` at the
world (for `Tok`, a resource clause like `Ref 1`) and its laws: small.

## 5. Summary

**Counts (104 constructors).**

| Class | Rows |
|---|---|
| proved | 7 (`immSub`, `mutSub`, `allI`, `withbor1`, `withbor1U`, `withbor2`, `withbor2U`) |
| portable | 63 |
| blocked | 0 |
| pending | 1 (`effHandleVB`) |
| out of the fragment | 33 |

Fragment status: 57 **yes**, 16 **cut**, 31 **no**.

| Group | Rows | proved | portable | blocked | pending | out |
|---|---|---|---|---|---|---|
| structural | 44 | 1 | 43 | | | |
| borrows | 11 | 6 | 5 | | | |
| effects/handlers | 16 | | 15 | | 1 | |
| data (families, `μ`, opaque) | 29 | | | | | 29 |
| codata (`ν`) | 4 | | | | | 4 |

**Blocked rows.** None. `withbor1`/`withbor1U` were blocked at the old `above` (§3.1); with Core's `ls₀` and `Keeps` they are proved.

**Proposed units.** Each follows Core's printed proofs row by row; estimates are relative, from
the size of Core's proofs and the chain pieces each needs.

1. **Structural** (44 rows; G1–G8, `cN_bind`). Mostly mechanical over existing `erwp` lemmas;
   the pieces with weight are `cN_bind` (Core's `cC_bind` by induction on `C`), G7 at non-`F`
   conclusions, and G8 (`vN_tyEq`/`cN_tyEq`, Core's `Alpha.lean`). Effort: medium; G8 alone is a
   third of it. Unblocks every `cut` row's own port.
2. **Borrows** (11 rows). (a) `withbor2`/`withbor3`/`withload` at the pure row and the three
   `U` forms at `Δ` and at `Unwind` rows: restatements of the proved constants, small to medium.
   (b) `withswap`: the anti-frame and its reseal (`withbor3S_compat`'s step 13), medium.
   (c) `withbor1`/`withbor1U`: done (#833; §3.1).
3. **Effects/handlers** (16 rows; E1–E11). Medium for `sub`/`perform`/`raise`/`await`/`let`
   (E1–E5); high for `then` (E6, E7) and the handlers (E8, E9, E11), which are the bulk; `iterate`,
   `divFuel`, `boundedFix`, `countFold`/`countTry` medium. `effHandleVB` needs E10 (the BOXED-κ
   stop lemma at `erwp`): not derived, the unit's hardest case.
4. **Data** (29 rows, and the `sm` constant): families (21 rows: the `fam` clause, the array
   steps, the `n`-cell frames across stops), high; opaque types (2 rows), small; `μ` and type
   variables (6 rows: an environment in `vN`, the `μ` clause and Core's `RelMu` laws at the
   index), very high.
5. **Codata** (4 rows): a reading of `ν` at `erwp` (a design choice first), then Core's `NuRel`
   laws; high.

Order by uncertainty: 2(c) and 3's E10 first (each may change a definition), then 1, the rest of
2 and 3, then 4 and 5. `FundamentalN` on the fragment needs 1–3; the `cut` rows also need 4 and 5
wherever a derivation passes through an excluded former.

**Unspent hypotheses, unused results.** Map only: no rule was proved, so no printed premise was
spent beyond those in the configuration (`callback_any` reads no premise of `withbor1U`).
`Row.Suspend.of_unwind` and `suspend_of_unwind` are the bridge the `U` rows' restatement reads;
`erwp_I_frameC`, `erwp_frame_cancelRun`, `erwp_handleLe` and `handle_sem` are unused today and
named as the counterparts above. No uniqueness/functionality result was needed.

**Untranscribed in the run-up** (Core lemmas the portable rows read and the chain lacks): G1, G2,
G4, G6–G8, `cN_bind`; E1–E11; Core's `ls₀` for records (`aboveL`) and `Keeps`; `wpTS_box`,
`host_call_sound`, `bang_app`, `fixSelf_valid` at `vN`; for the excluded formers, §4.
