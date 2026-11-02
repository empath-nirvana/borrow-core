# The new Core: evidence from the #770 spikes

What each part of SPEC §62 rests on. The spikes live on local branches of `experiments/DtorUnwind`;
the branches are not pushed and not merged (they are evidence, not library code). Each was rebuilt
and its axioms checked (`[propext, Classical.choice, Quot.sound]` or fewer; no `sorry`, `axiom`,
`native_decide`).

In the middle column, a name marked *program* is a program file or namespace: the test programs
proved at that part's rules, not a result of its own. Every other name is a Lean result.

| Part | Result (Lean name) | Branch, commit |
|---|---|---|
| Destructors on every exit | `CDerives.effLetD`, `resourceSafety` | `dtor-unwind` ea63f889 |
| Cancellation as a corollary; early loop close | `Cancel.lean` (file); `d_stepD`, `loopProg_safe` | `dtor-unwind` |
| A lend whose callback raises | `d_lendD`, `lendD` | `dtor-unwind` 471a5d2d |
| Owned resources across a suspension | `d_kDtor`, `dtors_kappa` | `dtor-unwind` 9b2a2eb5 |
| `hdv` is guardedness | `rtSafety`, `effLetDDiv` | `dtor-unwind` aabb1c68 |
| Step-indexed `ewp`; storing scheduler, unbounded loop, no fuel | `ewp_handle`, `adequacy`, `progStore_orDiverges`, `progDrop_orDiverges` | `dtor-unwind` 9f0571da |
| `[handle]` at Core's types without `hdv` | `handle_sem`, `kap_sem` | `dtor-unwind` 6969c14f |
| Index-relative `mut` cells; 6.48, 6.59 at the index | `UpdMutN`, `not_mutMutMemberStep`, `updVN_frame`, `six59VN` | `dtor-unwind` 99fc8d04, 20641658 |
| Handlers over Core's worlds | `erwp_handle`, `erwp_ccatch`, `erwp_safe` | `dtor-unwind` f0b46033 |
| `mut`/`imm` lends live across a stop | `erwp_M_frame`, `erwp_I_frame`; *programs* `LendProg`, `ILendProg` | `dtor-unwind` 9b3559c5, a2014997 |
| Raises and performing finalisers under a live lend | `erwp_M_frameR`, `erwp_frameL`; *program* `RaiseLendProg` | `dtor-unwind` a2014997 |
| A stop of an unrestricted operation owns nothing in κ's share | `unr_share_no_own` | `dtor-unwind` a215e597 |
| Stacks assumed nested last-in-first-out (refuted) | `resume_frame_short`, `resume_frame_not_stratumLe` | `dtor-unwind` f7cf6381 |
| Re-entry at the same image (refuted) | `not_rebReentryAgreeN` | `dtor-unwind` 35b418de |
| Re-choosing the image; worlds by invariants (refuted) | `not_rebRelabelAgreeN`, `not_immFrameWitSwapN`; `not_witSwapIWN` | `dtor-unwind` dc73543b; `reb-inv` beca0399 |
| Eliminating reborrows across stops (needed; copies only) | `not_plainImmArg_progMin`, `immReborrow_frz` | `reb-elim` 20d81c2e |
| Canonical images: reborrows across stops | `erwp_reborrow`, `erwp_reborrowDeep`; *programs* `RebProg`, `DeepRebProg` | `reb-canon` 9dd738be, e9bc9734 |
| Anti-Frame across stops | `erwp_M_antiFrame`, `erwp_withbor3`; *program* `AntiLendProg` | `reb-canon` e9bc9734 |
| Core's world-dependent results over canonical worlds (`Core.Stdio` not covered) | `Core.C.fundamentalC`, `Core.C.adequacyC`, `Core.C.rebChooseTW_top`, `Core.C.rebChooseTW_deep` | `canon-core` 01d6e927 |
| The one-stack assumption is in the relation, not the world | `not_extFoldTransfer`, `extK_iff_ext_cell` | `forest` 2a264e68 |
| Resumption at any `Ext` world | `extF`, `TWN.linDisj`, `ext_extF`; *program* `HandlerLendProg` | `reb-canon` 75b298b8, 5cc03032 |
| Capture as its own operation; cross-task scopes (one child, a fixed order of events) | `cerwp_scope`, `cerwp_scopeM`; *program* `CrossProg` | `reb-canon` 18b15971 |
| The cactus invariant: stated, not yet used | `CactusInv`, `cactus_step`, `cactus_move`, `joinReady_fd` | `reb-canon` 18b15971 |
| Lifetimes on continuation types alone, single chain (refuted) | `not_fdFromLifetimeTypes` | `single-rel` 4a8f94c4 |
| Tree-ordered lifetimes; a graft adds order facts | `fdFromLifetimeTypesT`, `not_fdFromThunkTypesT`, `graft_mono`; `Tree/Comparability.lean` over the scan of `Tree/ChainUses.lean` | `tree-life` e8f4ada6 |
| Tree-stratified carrier; graft without renaming | `compLawsRT`, `chainEquiv`, `ResUT.Valid.graft`, `graftCell_admitted` | `tree-life` 1f305c9f |
| `✓`, `#` and flattening along `chainEquiv` | `chain_valid_iff`, `chain_hash_iff`, `chain_flat_iff` | `tree-life` 4466412d |
| Semantic types re-read along the tree | `reread`, `kmono_unit`, `kmono_sum`, `kmono_imm`, `kmono_mut`, `kmono_ref`, `kmono_box`, `kmono_thunk`, `trU_not_kmono`; for example `round7_write` | `tree-life` ea57fa14 |
| BoLo 6.25–6.59 over the tree carrier | `ResUT.six52`, `ResUT.six59` and the `Tree/Port` files | `tree-life` 01ac9316–9fdb1c7b |
| The resume condition at every type | `joinFd_of_branch`, `TWNC.noOwnUnder` | `tree-life` bfe33dab, c4addc10 |
| The cactus invariant over the tree world; adequacy from it (no programs yet) | `CactusInvT`, `cactusT_step`, `cactusT_extend`, `cactusT_move`, `cerwpT_adequacy` | `tree-wp` 89c0f8a7 |
| World operations over the tree world; store typing growth | `TWd.addTy_ext`, `Cov.mono`, `RR.mono`, `winv_swap` | `tree-wp` fc49ed48, 44667d04 |

The target programs are in `corpus/pending/` on the local branch `pending-770`, stacked on
`fs-769`; neither is pushed.
