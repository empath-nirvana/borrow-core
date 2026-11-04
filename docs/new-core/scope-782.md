# Scope: semantic types read at the lifetime tree (#782)

Part of #771, row 5. SPEC §62 ("Semantic types read at the tree"); `structure.md` §4, §7.1.
Depends on row 4 (#781): the tree world `TWd`, re-reading `RR`, the codes `KTy`, and the
relation `twp`/`cerwpT` are in the library.

## 1. Plan

**Two layers.** A `mut` cell's invariant is index-free: the tree carrier's `MutT.P` is a predicate
on values and resources at the tree, and the world reads it at the code typing (`Cov`, `sem Θ`).
So the cell's store type is a code (`KTy`, condition 16's ruling), and the relation's types are a
second layer over it, step-indexed and read at the tree world:

- **Store types** (`KTy`, `World/Codes.lean`, unchanged): `1`, `+`, `Imm`, `Mut`, `[a]`, `ref`. A
  `mut` cell stores its code read at the current tree. `KTy` gains no former here, so no proof of
  #781 that cases on it changes.
- **The relation's value types** (`STy`, new): `P n w v ρ` at the step index `n` and the tree
  world `w`, with two laws as fields: downward closed in `n` (`Down`) and monotone along
  `w.Ext w′ ρ` with `ρ` re-read at `w′` (`Mono`). Every former is an `STy` constructor, each law
  proved from the components'.
- **The relation's computation types** (`SCmp`): predicates on terms at the index and the world,
  downward closed. `F A` is read at `cerwpT` (whose carrier is `twp`), so a computation type is
  "read at the relation". As in Core (`Core/Relation.lean`: "the Kripke quantifier over `Ext`
  sits at `U` only"), a computation type reaches a value only under `U`, whose quantifier over
  extensions makes the thunk monotone.

**The formers** (`structure.md` §7.1), where each lands:

| Former | Spike | Here |
|---|---|---|
| `1`, `+`, `0` | `vUnit`, `vSum` (`kmono_unit`, `kmono_sum`) | `STy.unit`, `STy.sum`, `STy.zero` |
| `⊗` | none | `STy.tensor` (re-reading splits along `●`: `RR.split_retype`) |
| `Imm @a A` | `vImm` (`kmono_imm`) | `STy.imm`, any `STy` payload |
| `Mut @a A` | `vMut` (`kmono_mut`, by definition) | `STy.mut` at a store code; what carries it: the re-read invariant is the code read at the new tree (`RC.mut_inv`, `RC.mut_extends`, §3) |
| `[a] A` (boxes) | `vBox` (`kmono_box`) | `STy.box` |
| `ref A` | `vRef` (`kmono_ref`) | `STy.ref` |
| `!A`, `Unk`, `I32`/`I64` | none | `STy.bang`, `STy.unk`, `STy.int` |
| lifetimes | the formers take a tree node `a`; no quantifier | `SCmp.all`: `∀α ⊏ c. C`, `α` below `c` in the current tree |
| thunks `U C` | `vThunk` (`kmono_thunk`, by definition) | `STy.thunk` (at every extension and list keeping the records it reads, `KeepRel`), `STy.thunkC`, `STy.thunkRet`; what carries it: `cerwpT_le` (new), `STy.thunkC_val`, a share's resume (`STy.kont_of_share`) |
| `F A`, `⊸`, `&`, `⊤` | none | `SCmp.ret` at `cerwpT`, `SCmp.arr`, `SCmp.amp`, `SCmp.top` |
| `μX. A` | none | `STy.mu`: least fixed point over `STy` candidates; fold/unfold at a monotone body |
| `νX. C` | none | `SCmp.nu`: greatest fixed point over `SCmp` candidates; fold/unfold at a monotone body |
| type variables | none | `STy.var` at an environment `Nat → STy` |
| families `[L]` | none | `STy.fam` (`sepRange` at the tree) |
| opaque types | none | `STy.opq` (`Opaque.rel` at the tree) |
| continuation and task types | none | no new former (`scope-789.md` §2.4): `STy.kont` = `U (B ⊸ C)`, `STy.kontBox` = `[@d] U (B ⊸ C)`, `STy.task` = `[@d] U C` (`Core/TreeSemK.lean`); a captured `κ` is a value of its type (`STy.kont_of_share`), carried and resumed (`STy.kontBox_resume_after`) |

**Layout.**

| File | Contents |
|---|---|
| `Support/Model/Tree/KSem.lean` | from `Tree/KSem.lean`: `KMono`, `MonoΘ`, existence of the re-reading at a semantic typing (`RC.exists_cell`, `RR.exists_stratum`, `RR.exists`, `reread`, `reread_extends`), `vMut`, `vThunk`, the `kmono_*` results |
| `Support/Model/Tree/KSemGraft.lean` | from `Tree/KSemGraft.lean`: round 7 (`round7_refused_before`, `round7_admitted_after`, `round7_write`) and `trU_not_kmono` |
| `Core/TreeSem.lean` | `STy`, every value former with `Down` and `Mono`; `μ`; type variables; the `mut` re-reading results |
| `Core/TreeSemC.lean` | `cerwpT_le`, `opTableT_down`; `cerwpT_nil_of_imm`; `SCmp`, the computation formers; thunks at `cerwpT`; `ν`; `∀` over lifetimes |
| `Core/TreeSemK.lean` | continuation and task types; `STy.kont_of_share`, `STy.kontBox_resume_after`, `STy.not_kontBox_of_view` |
| `Core/TreeSemKEx.lean` | the instances, at a proper extension (`dExt`, `dExt_proper`: a fresh child grafted into a chain): `κ = λy. K[y]` (`kontV_step`), a share holding a value built at any world (`share_val`, `share_viewR`), depth 1 and depth 3 (`kontBox_depth1`; `kontBox_depth3`, a view whose witness holds the two enclosing views), `STy.reread` on the nested view (`reread_v3`), round 7 at codes (`round7_codes`: `STy.mut_reread`, `RC.mut_extends`), the rules-out instances, `nilRun_stuck` |
| `Core/TreeSemObs.lean` | `Obs.cerwpT_not_keepKripkeNil` (a bare run owning no records is not Kripke along `KeepRel`); `Obs.d1_nonvacuous` (the depth-1 resume configuration has starts) |
| `Support/Model/Tree/World/ExtF.lean`, `Core/TreeWpEff.lean` | slice (d)'s (#807, D13 of `scope-781.md`), unchanged here: `KeepRel`, `contShareT` resumed at any list keeping the records the share reads |

`Core/` because the computation types read `cerwpT` and the opaque types read `Core.Opaque`.

## 2. Departures

| # | Departure | Why |
|---|---|---|
| E1 | `Mut`'s payload is a store code, not an `STy` | A cell's invariant is index-free (`MutT.P`); a step-indexed payload (a thunk in a cell) needs step-indexed cell invariants, which the carrier does not have. Every code is a `STy` (`STy.code`), and Core's `μ` already keeps `X` out of `Mut` payloads (`VTy.NoMut`). |
| E2 | One mode: no observable view (`vCE false`) | Core reads an `Imm` payload with `U` relaxed to `True`. Here an `Imm` payload is read in full; row 6 adds the view if `Imm`'s rules need it. |
| E3 | The value types read the record list. They own no records: `SCmp.ret` runs at its list owning none | See §5. A continuation owning the records of lends its own branch opened (row 6) is not a value of a type here. E3b, `F A` carrying `U`'s quantifier over later lists, is reverted to Core's answer: `SCmp.ret` is a bare run, and thunks are introduced as `thunkF_compatC` does (§5). |
| E4 | `SCmp.arr` quantifies the index below `n` | Downward closure of a function type at a step index needs it; Core's `cC` has no index. |

## 3. Rules out

- **A value type not monotone along extension.** Every `STy` carries `Mono`. (`trU_not_kmono`
  shows only that a cell carried by `trU` is not a value of this `Mut`, whose invariant is the
  store type read at the current tree; against a `Mut` keeping the predicate a cell was stored
  with, the evidence is `graft_carried_refuses` against `round7_write`, an expressiveness
  argument. `RC.mut_inv`, `RC.mut_readback` and `not_rc_of_inv_ne` hold by `RC`'s definition and
  rule out nothing beyond it.)
- **A bare run read as `F A`.** `Obs.cerwpT_not_keepKripkeNil`: a bare `cerwpT` run owning no
  records, the records `F A` runs at, is not Kripke along `KeepRel` (the stuck `() ()` over a view
  at `[]` would be a run at the lend's own list owning no records, and, framed beside the lend's
  record, `let a = alloc () in () ()` a run at the empty world, against adequacy). A thunk of
  `F A` is introduced from its computation at every later list (`STy.thunk_intro`), not from a run
  at the current one.
- **A continuation stored past its lend.** `STy.not_box_of_view`: a boxed value holding a view at
  `α` is not of `[@d] A` unless `d` is strictly below `α`; at the `κ` of the instances, boxed at
  its lend's own lifetime or at the root (`not_kontBox_at_lend`, `not_kontBox_at_root`).
- **A thunk type that holds of a stuck thunk holding a borrow.** Read at the list, a thunk is a run
  at the lists keeping its lend's record. Read at `[]`, it would hold of every thunk holding a view
  (`cerwpT_nil_of_imm`, `nilRun_stuck`).

## 4. Status and hypotheses

Built for every former but `Mut` at a payload that is not a store code (E1, #790) and effect rows
(`CTy.eff`, no `SCmp` former: `SCmp.ret` takes a table with its `Local`/`Down` proofs, and nothing
yet builds a row's table with its entries downward closed), continuation and task types included.
The value types are downward closed and monotone along extension and `KeepRel`; the computation
types are downward closed, `F A` a bare run (`SCmp.ret`), Kripke along the whole-list re-reading
(`SCmp.ret_reread`) and monotone in `A` (`SCmp.ret_le`), and reach values under `U`, whose
quantifier is the only one over later lists keeping what a thunk reads. A thunk is introduced from
its computation at every world and list over its environment's type (`STy.thunk_intro`,
`STy.thunkRet_intro`, `STy.thunkRet_lam`: Core's `thunkF_compatC`/`thunkV_compatC`). Each former `VTy.NoMut` lets `X` occur under is monotone in
it (`STy.sum_le` … `STy.fam_le`), and `μ` in its body (`STy.mu_le`), so `μ` folds and unfolds at
every body built from them, shown at `STy.allBody_mono` and `STy.list_cons`; a map from `NoMut`
bodies to monotone bodies is not built. `ν` folds at Core's shape `F(A ⊕ U X) & F B`
(`SCmp.loopBody_mono`, `SCmp.loop_nonempty`).

**The instances** (`Core/TreeSemKEx.lean`) are at a proper extension: before it, `0 ⊐ 1 ⊐ 2 ⊐ 3 ⊐
4` is a chain and `5` a bare child of the root; after it, `5` is a child of `3` (`dExt`,
`dExt_proper`). The resume list adds a record at `5`. `kontBox_depth1` and `kontBox_depth3` keep
both conjuncts of `STy.kontBox_resume_after`. At depth 3 the share's view holds the views of the
two enclosing lends in its witness, so the share reads all three records (`relFT_d3`), and
`KeepRel` re-reads the three, their escrows re-read at the new tree, while the fourth is dropped
(`not_relFT_d3`, `keep_d3`). `STy.reread` is met on the nested view (`reread_v3`); `STy.mut_reread`
and `RC.mut_extends` on round 7's `mut` cell at codes along `beforeP → graftP`, where the re-read
invariant admits the handler's borrow the old one refuses (`round7_codes`). The instances fix an
empty operation table (`tbE`: a stop of the resumed run is refused), a must-resume entry (`enU`,
`q = .lin`: its cancel branch is vacuous) answering `()` (answer type `1`), and the frame
conditions `True` and `fdNil enU () True`.

**Starts.** The depth-1 resume configuration (world `wD₁`, list `lsD1' ℓ₀ ℓ₂`, no records owned,
`ℓ₀`'s view) has starts: the run there of the stuck term does not hold at every index and pair of
locations, since otherwise `let a = alloc () in let b = alloc () in () ()`, opening the two lends
(`twp_lendOpen`) and framing off the second view and both records (`twp_frame`), would be a run at
the empty world, against adequacy (`Obs.d1_nonvacuous`). For the depth-3 configuration no start
is exhibited: its share is a view whose witness holds views, and no rule of the library builds
one (`twp_lendOpen` lends a unit cell and hands out a view with an empty witness; there is no
reborrow rule at the tree yet, row 6). That it has none is not shown either.

**What the rest of the relation provides** (`scope-781.md`, SPEC §62, decision 74). Adequacy over
several branches (`multiBranchAdequacyT`) goes through `cerwpT_adequacy` at one branch, with the
stored continuations in pool form (`KapSchedT`, `PoolT`): each share resumes at `KeepRel`, the
condition the value types here read, and every two are apart at each other's record masks. It
does not rest on `CactusInvT` over several branches. The results here are about one continuation
at `KeepRel`; the instances (`Core/TreeSemKEx.lean`) are configurations of that condition, not of
a pool. Borrows shared across tasks are excluded by the pool invariant itself (#795); the view
the instances' `κ` holds is of a lend whose record is in its own stop list. The tree has no `withborU` rule yet (row 6).
A run giving up a copy of an `imm` view held elsewhere (D4) is resolved by #806 (`EndT` reads
`UpdA`); nothing here depends on it.

Headline hypotheses, classified: (a) the situation the statement is about; (s) a side condition
the library discharges by a named result. None stands in for an unproved fact.

| Result | Hypothesis | Class |
|---|---|---|
| `STy.reread`, `STy.mut_reread` | `hE : w.Ext w′ ρ` | (a); met at a proper extension in `reread_v3`, `round7_codes` |
| | `hc : CovR (sem w.Θ) w.K ρ` | (s) a part of a world in `WInv` (`cov_of_comp`) |
| `cerwpT_le` | `Tb.Local`, `Tb.Down`, `Q.Down` | (s) `opTableT_local`, `opTableT_down`, `postOf_down` |
| `opTableT_down` | every entry `Down` | (a) |
| `STy.mu_fold`/`_unfold`, `SCmp.nu_fold`/`_unfold` | a monotone body | (a); met by `STy.list_body_mono`, `STy.allBody_mono`, `SCmp.loopBody_mono` |
| `RC.mut_inv`, `RC.mut_readback`, `not_rc_of_inv_ne` | the cell's code `Θ′ ℓ = A`; the re-reading | (a); by `RC`'s definition |
| `SCmp.ret_le`, `cerwpT_post_mono` | `Tb.Local`; the value types included | (s) `opTableT_local`; (a) |
| `SCmp.ret_reread` | `hE`, `hr`, `hl : SRecsRR` | (a) |
| `Obs.cerwpT_not_keepKripkeNil`, `Obs.cerwpT_not_keepKripke` | none: refute `Obs.KeepKripkeRunNil` (`O = O′ = []`) and `Obs.KeepKripkeRun` with every hypothesis of `cerwpT_adequacy` discharged | — |
| `Obs.d1_nonvacuous` | none: every hypothesis of `cerwpT_adequacy` discharged | — |
| `STy.mu_le` | the bodies ordered pointwise | (a) |
| `RC.mut_extends` | coverage, the code kept (`Θ′ ℓ = Θ ℓ`), the payload re-read and agreed on | (a); coverage and agreement (s) from `WInv` and `TWd.Ext`; met in `round7_codes` |
| `STy.thunk_intro_env`, `STy.thunkRet_intro_env`, `STy.thunkRet_lam_env` | `hG : G.Mono`, the environment monotone along the tree | (a) `thunkF_compatC`'s `gDenC_local`; met at every value type (`STy.env_mono`) |
| | `hM`: the computation at every world and list, over a covered resource meeting the environment | (a) the term's semantic computation, as `thunkF_compatC`'s `SemC` premise |
| | `hg`: the environment met here; coverage of the resource | (a) `thunkF_compatC`'s `gDenC`; coverage (s) `cov_of_comp` |
| `STy.thunk_intro`, `STy.thunkRet_intro`, `STy.thunkRet_lam` | the `_env` forms at `G := τΓ.env γ` | as above; `thunkRet_lam` met at `λ_. inj₁ ()` (`STy.thunkRet_constInl`), `thunk_intro` at a value (`STy.thunkC_val`) |
| `STy.thunk_force` | coverage of the resource and of the list's escrows | (s) `cov_of_comp`, `RecInv.cov_ls` |
| `cerwpT_nil_of_imm` | a top-level `imm` cell of the resource | (a) |
| `STy.kont_of_share`, `STy.kontBox_of_share` | `hκ`: `κ a` steps only to `K[a]` | (a) what `κ` is; met by `kontV_step` |
| | `hB`: the answer type is read by the entry's answer | (a) the operation's signature (`OpSig.entT`'s `PBv := 𝒱T⟦o.B⟧`, `scope-789.md` §2.1) |
| | `h`: the share, owning no records, owing `cerwpTC` at `postOf A` | (a) the stop (`cerwpT_perform`); met by `share_viewR` |
| | `hd`: the share in `Res_d` | (a) BOXED-κ's premise; met by `viewR_inStratum` |
| | `n < k` | (a) the index below the stop's |
| `STy.kontBox_resume_after` | the above; coverage of the share; `hE`, `hr`, `hk : KeepRel` | (a); coverage (s) as above; met in `kontBox_depth1`/`_depth3` at a proper extension and a `KeepRel` that is not `SRecsRR` (`not_rr_d1`, `not_rr_d3`) |
| | `hls`: the records of `ls′` covered | (s) `RecInv.cov_ls`: the resume is read off the carried value (`STy.kont_resume` at the reflexive extension), which needs it |
| | the composite `σ` covered (in the resume conjunct) | unspent: `F A` is the run itself (`STy.kont_resume` gives it) |
| `STy.not_box_of_view` | a view at `α` in the resource, `¬ d ⊏ α` | (a) |
| `SCmp.ret_val`, `STy.thunkC_val` | coverage | (s) as above |
| `reread` (`KSem`) | `MonoΘ Θ` | (a); met by `monoΘ₇` |

## 5. E3: the value types read the record list

**The question**: does a thunk type read at `cerwpT`, with boxes at a lifetime, give a stored
continuation holding borrows the meaning "resumable at any later world and record list that keeps
the records its share reads", without the value types reading the list?

**No.** A thunk's meaning is a run, and a run is at a list (`twp`'s `ls`, which the world's record
invariant reads: `RecInv`). A value type that does not read the list can run its thunk only at a
list fixed in advance, and the only list every world has is `[]`. At `[]`, a run over a resource holding a view holds of every term: no world whose list is empty
holds an `imm` cell, since the list's records are the world's lineage (`TIT`) and every `imm`
cell of the world's agreement is a record's cell or a chain position (`CoverageT`). This is
`cerwpT_nil_of_imm` (`Core/TreeSemC.lean`), and at the instances' view, a term that never steps is
such a run (`nilRun_stuck`). So the record a continuation's view needs, its lend's, is what such a
type cannot express: its thunk type holds of every thunk holding a borrow, resumable or not, and
"rules out a `κ` that cannot resume" is unprovable of it.

**The reading.** `STy`'s predicate reads the list (`P n w ls v ρ`), and its monotonicity is along
extension at every list keeping the re-readings of the records of `ls` the resource reads
(`KeepRel`, the per-branch condition of the continuation share, D13 of `scope-781.md`, slice (d)'s
(#807): `Support/Model/Tree/World/ExtF.lean`'s `KeepRel` block and `Core/TreeWpEff.lean`'s
`contShareT`). Every former's downward closure and monotonicity is
proved at it: the formers other than thunks pass the list to their components, at parts of the
resource (`KeepRel.of_compS_left`/`_right`, `KeepRel.of_imm_res`, `KeepRel.of_get_sub`); thunks
quantify over it (`KeepRel.trans`). The answer depends on `KeepRel`: a whole-list re-reading
(`SRecsRR`) refuses a resume after another branch ended a record of its own open at the stop,
which the hardest case needs (`not_rr_d1`, `not_rr_d3`).

**`F A` is a bare run; thunks as Core introduces them (E3b).** A bare `cerwpT` run is not Kripke
along `KeepRel`: `twp` quantifies over starts whose list re-reads its list whole, and at `[]` a
resource holding a view has none (`cerwpT_nil_of_imm`), so Kripke along `KeepRel` would make the
stuck `() ()`, over the view of a lend the program opens, a run at the lend's own list, and
`let a = alloc () in () ()` a run at the empty world, which adequacy refutes
(`Obs.KeepKripkeRunNil`, `Obs.cerwpT_not_keepKripkeNil`, `Core/TreeSemObs.lean`; the refutation
is at no records owned, the lend's record in the run's list, the stuck run framed beside it by
`twp_frame`). That matters only to a thunk built from a run at the current list. Core never builds
one so: `cC (.ret A)` is a bare `wpTS` run, and `thunkF_compatC` builds the thunk from `SemC` at
the later list with the context moved there (`gDenC_local`). So does the tree. `F A`
(`SCmp.ret`) is a bare run at its list, Kripke along the whole-list re-reading (`SCmp.ret_reread`);
the quantifier over later lists keeping what the thunk reads is `U`'s alone (`STy.thunk`); and a
thunk is introduced from its computation at every world and list over its environment's type,
the environment carried by that type's monotonicity, which every `STy` has (`STy.thunk_intro`,
`STy.thunkRet_intro`, `STy.thunkRet_lam`). A captured `κ` is a value of `U (B ⊸ F A)` because
the share resumes at every such list (`kont_run_of_share`, `STy.kont_of_share`). The alternative,
`twp`'s start condition weakened from `SRecsRR` to `KeepRel` (which would make `cerwpT` itself
Kripke along `KeepRel` and `cerwpT_nil_of_imm` false), is not Core's answer and is not done. A continuation owning the records
of lends its own branch opened is row 6's.

