# The new Core: evidence from the #770 spikes

What each part of SPEC §62 rests on. The spikes live on local branches of `experiments/DtorUnwind`;
the branches are not pushed and not merged (they are evidence, not library code). Each was rebuilt
and its axioms checked (`[propext, Classical.choice, Quot.sound]` or fewer; no `sorry`, `axiom`,
`native_decide`).

In the middle column, a name marked *program* is a program file or namespace: the test programs
proved at that part's rules, not a result of its own. Every other name is a Lean result.

| Part | Result (Lean name) | Branch, commit |
|---|---|---|
| Step-indexed `ewp`; storing scheduler, unbounded loop, no fuel | `ewp_handle`, `adequacy`, `progStore_orDiverges`, `progConsume_orDiverges` | `dtor-unwind` 9f0571da |
| `[handle]` at Core's borrow-free types without `hdv` | `handle_sem`, `kap_sem` | `dtor-unwind` 6969c14f |
| Index-relative `mut` cells; 6.48, 6.59 at the index | `UpdMutN`, `not_mutMutMemberStep`, `updVN_frame`, `six59VN` | `dtor-unwind` 99fc8d04, 20641658 |
| Handlers over Core's worlds | `erwp_handle`, `erwp_ccatch`, `erwp_safe` (progress only) | `dtor-unwind` f0b46033 |
| `mut`/`imm` lends live across a stop | `erwp_M_frame`, `erwp_I_frame`; *programs* `LendProg`, `ILendProg` | `dtor-unwind` 9b3559c5, a2014997 |
| Raises and performing finalisers under a live lend | `erwp_M_frameR`, `erwp_frameL`; *program* `RaiseLendProg` | `dtor-unwind` a2014997 |
| A stop of an unrestricted operation owns nothing in κ's share | `unr_share_no_own` | `dtor-unwind` a215e597 |
| Stacks assumed nested last-in-first-out (refuted) | `resume_frame_short`, `resume_frame_not_stratumLe` | `dtor-unwind` f7cf6381 |
| Re-entry at the same image (refuted) | `not_rebReentryAgreeN` | `dtor-unwind` 35b418de |
| Re-choosing the image; worlds by invariants (refuted) | `not_rebRelabelAgreeN`, `not_immFrameWitSwapN`; `not_witSwapIWN` | `dtor-unwind` dc73543b; `reb-inv` beca0399 |
| Eliminating reborrows across stops (needed; copies only) | `not_plainImmArg_progMin`, `immReborrow_frz` | `reb-elim` 20d81c2e |
| Canonical images: reborrows across stops | `erwp_reborrow`, `erwp_reborrowDeep`; *programs* `RebProg`, `DeepRebProg` | `reb-canon` 9dd738be, e9bc9734 |
| Anti-Frame across stops | `erwp_M_antiFrame`, `erwp_withbor3`; *program* `AntiLendProg` | `reb-canon` e9bc9734 |
| Core's world-dependent results over canonical worlds (`Core.Stdio` not covered): the content is `Core.C.fundamentalC` at `TWNC`; `Core.C.adequacyC` re-derives the library's statement | `Core.C.fundamentalC`, `Core.C.adequacyC`, `Core.C.rebChooseTW_top`, `Core.C.rebChooseTW_deep` | `canon-core` 01d6e927 |
| The one-stack assumption is in the relation, not the world | `not_extFoldTransfer`, `extK_iff_ext_cell` | `forest` 2a264e68 |
| Resumption at any `Ext` world | `extF`, `TWN.linDisj`, `ext_extF`; *program* `HandlerLendProg` | `reb-canon` 75b298b8, 5cc03032 |
| Capture as its own operation; cross-task scopes (rules over any body; programs with one child and a fixed order of events) | `cerwp_scope`, `cerwp_scopeM`; *programs* `CrossProg`, `CrossProgM` | `reb-canon` 18b15971 |
| The cactus invariant: stated, not yet used | `CactusInv`, `cactus_step`, `cactus_move`, `joinReady_fd` | `reb-canon` 18b15971 |
| Lifetimes on continuation types alone, single chain (refuted) | `not_fdFromLifetimeTypes` | `single-rel` 4a8f94c4 |
| Tree-ordered lifetimes; a graft adds order facts | `fdFromLifetimeTypesT`, `not_fdFromThunkTypesT`, `graft_mono`; `Tree/Comparability.lean` over the scan of `Tree/ChainUses.lean` | `tree-life` e8f4ada6 |
| Tree-stratified carrier; graft without renaming | `compLawsRT`, `chainEquiv`, `ResUT.Valid.graft`, `graftCell_admitted` | `tree-life` 1f305c9f |
| `✓`, `#` and flattening along `chainEquiv` | `chain_valid_iff`, `chain_hash_iff`, `chain_flat_iff` | `tree-life` 4466412d |
| Semantic types re-read along the tree (`kmono_mut` holds for every `τ` and `kmono_thunk` for every computation predicate, by the definitions of `vMut` and `vThunk`) | `reread`, `kmono_unit`, `kmono_sum`, `kmono_imm`, `kmono_mut`, `kmono_ref`, `kmono_box`, `kmono_thunk`, `trU_not_kmono`; for example `round7_write` | library: `Support/Model/Tree/KSem.lean`, `KSemGraft.lean` (from `tree-life` ea57fa14) |
| BoLo 6.25–6.59 over the tree carrier | `ResUT.six52`, `ResUT.six59` and the `Tree/Port` files | `tree-life` 01ac9316–9fdb1c7b |
| The resume condition at every type, from the branch hypotheses (`hbr`, `hnα`) | `joinFd_of_branch`, `TWNC.noOwnUnder` | `tree-life` bfe33dab, c4addc10 |
| Re-reading: semantic types read at the tree, `mut` cells re-read as it grows | `RR`, `RR.func`, `RR.refl`, `RR.inStratum`, `RR.exists_of` | library: `Support/Model/Tree/Reread.lean` |
| Store types as codes; re-typing where no `mut` cell is held | `KTy`, `KTy.interp`, `interp_retype`, `RR.exists_retype`, `RR.trans_retype` | library: `Support/Model/Tree/World/Codes.lean` |
| The relation's types at the tree: value types downward closed and monotone, computation types downward closed and read at `cerwpT`, `F A` Kripke along `KeepRel` (a bare run is not); a re-read `mut` cell's invariant is its store type (by `RC`'s definition) | `STy`, `STy.reread`, `STy.mu_fold`, `STy.allBody_mono`, `STy.list_cons`, `RC.mut_extends`, `cerwpT_le`, `cerwpT_post_mono`, `SCmp.ret_kripke`, `SCmp.ret_le`, `SCmp.loopBody_mono`, `SCmp.loop_nonempty`, `STy.thunkRet_intro`, `Obs.cerwpT_not_keepKripke` | library: `Core/TreeSem.lean`, `Core/TreeSemC.lean`, `Core/TreeSemObs.lean` |
| The tree world; its extension carries a resource, `●` commutes with re-reading, the world is re-read | `TWd`, `TWd.Ext.trans`, `RR.split_retype`, `WInv.reread` | library: `Support/Model/Tree/World/World.lean` |
| Frame records and the typed tree world with canonical images; the template choice carried by re-reading and coherent; at the `Classical` choice the images are `canonT`/`canonDT` | `FrameRecT`, `TWNT`, `canonTc`, `canonDTc`, `TWNT.templ_reread`, `TWNT.tcCoherent`, `TWNT.tcCarried_exists`, `canonTc_tmplT`, `canonDTc_tmplT` | library: `Support/Model/Tree/World/Records.lean`, `Templ.lean`, `InvUses.lean` |
| Every typed tree world satisfies the invariant; one `mut` cell per location; no `own` cell of a lent location beneath a borrow | `twnt_invHolds`, `TWNT.mutOne`, `TWNT.noOwnUnder` | library: `Support/Model/Tree/World/TInvHolds.lean`, `Coherent.lean`, `InvUses.lean` |
| Row 5.27's `↭` across a re-reading, masked at a run's own records; 6.48 at that reading (pointwise, departure D5) | `UpdX`, `UpdX.of_rr`, `UpdX.trans`, `UpdX.frame`, `UpdX.of_updV`, `updX_refl_imm`, `UpdX.inv`, `updX_refl_mut`, `InvKept` | library: `Support/Model/Tree/World/UpdX.lean`, `UpdXInv.lean` |
| The mask is needed (a lend left open at a stop) | `lend_open_admitted`, `lend_open_needs_mask` | library: `Support/Model/Tree/World/UpdXMasks.lean` |
| Clause 3 of two covered `mut` cells is not covered, on the tree and on the printed chain | `clause3_not_cov`, `clause3_chain` | library: `Support/Model/Tree/World/Clause3.lean` |
| The end of an `imm` lend from the condition at the escrow's exclusive locations; the condition at `ℓ` alone is not enough | `FdEsc`, `immEnd_valid_of_fdEsc`; `twnt_config`, `immEnd_esc_config`, `immEnd_esc_chain`, `config_not_fdEsc` | library: `Support/Model/Tree/World/FdEsc.lean` |
| The condition from branch points; kept across a masked update | `escBeneathT`, `fdEscOfBranch`, `fdEsc_of_points`, `fdEsc_of_updX` | library: `Support/Model/Tree/World/EscBeneath.lean`, `StepKeep.lean` |
| Where κ resumes, over the tree carrier | `extFT`, `extFT.rr`, `extFT.trans`, `extFT_comp` | library: `Support/Model/Tree/World/ExtF.lean` |
| `extFT` refuses no resumption the tree world's extension allows (R4) | `ext_extFT`, `r4_extExtFT`; `ExtLT` admits and refuses: `extLT_admits_drop`, `not_extLT_drop_relevant`, `not_extLT_drop_longer` | library: `Support/Model/Tree/World/ExtExtF.lean`, `Core/TreeHeadlines.lean` |
| Runs of a counted length; final configurations; safe or divergent | `StepsN`, `stepsN_of_steps`, `stepsN_plug_split`, `Final`, `final_opPlug`, `OrDiverges` | library: `Core/StepsN.lean` |
| The step-indexed relation over the tree world, and its rules | `twp`, `EndT`, `twp_kripke`, `twp_bind`, `twp_frame`, `twp_frame_w`, `twp_extend`, `twp_update`, `endT_inv` | library: `Core/TreeWp.lean` |
| Operations over the tree world: the continuation's share keeps the entry's qualifier | `cerwpT`, `contShareT`, `opTableT`, `fdAt_iff`, `cerwpT_perform`, `contShareT_resume`, `contShareT_resume_rr` | library: `Core/TreeWpEff.lean` |
| The cactus invariant over the tree world: kept by step, growth, move, spawn and join; adequacy derived through `cactusT_step` at one branch (no programs yet) | `CactusInvT`, `cactusT_step`, `cactusT_extend`, `cactusT_move`, `cactusT_spawn`, `cactusT_join`, `cerwpT_adequacy` | library: `Core/TreeCactus.lean` |
| The resume condition at the escrow's exclusive locations, at a join, from the cactus invariant and the other branches' points; without points it fails | `fdEsc_at_join`; `cactusT_config`, `cactusT_not_fdEsc`, `config_not_joinPt` | library: `Core/TreeCactus.lean` |
| Other branches' steps keep that condition; without the printed `↭` at `twp`'s end they need not (refuted) | `stepKeepsFdEsc`; `not_stepKeepsFdEscNoUpd`, `copy_end_refused`, `copy_config` | library: `Core/TreeStepKeep.lean` |
| Headlines at one branch: adequacy; a step keeps others' open lends (R1); a lend is not ended while a stored branch holds part of it (R2); a join's valid end leaves the others nothing of the lend (R3) | `topAdequacyT`, `r1_stepKeepsFdEsc`, `r2_endBlockedByHolder`, `r3_joinEndNeedsFdEsc`, `fdEsc_of_end_valid`, `config_end_refused` | library: `Core/TreeHeadlines.lean` |
| A must-resume `κ` is linear and not consumable | `kTy_lin` | library: `Core/Classes.lean` |
| World operations over the tree world; store typing growth | `TWd.addTy_ext`, `Cov.mono`, `RR.mono`, `winv_swap` | `tree-wp` fc49ed48, 44667d04 |

The target programs are in `corpus/pending/` on the local branch `pending-770`, stacked on
`fs-769`; neither is pushed.
