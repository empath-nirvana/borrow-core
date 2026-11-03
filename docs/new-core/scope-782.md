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
| `Core/TreeSemKEx.lean` | the instances: `κ = λy. K[y]` (`kontV_step`), a share holding a view built (`share_viewR`), depth 1 and depth 3 (`kontBox_depth1`, `kontBox_depth3`), the rules-out instances, `nilRun_stuck` |
| `Support/Model/Tree/World/ExtF.lean`, `Core/TreeWpEff.lean` | ported from `si-781d` (commit `5b6b4a0c`, D13): `KeepRel`, `contShareT` resumed at any list keeping the records the share reads |

`Core/` because the computation types read `cerwpT` and the opaque types read `Core.Opaque`.

## 2. Departures

| # | Departure | Why |
|---|---|---|
| E1 | `Mut`'s payload is a store code, not an `STy` | A cell's invariant is index-free (`MutT.P`); a step-indexed payload (a thunk in a cell) needs step-indexed cell invariants, which the carrier does not have. Every code is a `STy` (`STy.code`), and Core's `μ` already keeps `X` out of `Mut` payloads (`VTy.NoMut`). |
| E2 | One mode: no observable view (`vCE false`) | Core reads an `Imm` payload with `U` relaxed to `True`. Here an `Imm` payload is read in full; row 6 adds the view if `Imm`'s rules need it. |
| E3 | **Resolved (#794): the value types read the record list.** They own no records: `SCmp.ret` runs at its list owning none | See §5. A continuation owning the records of lends its own branch opened (row 6) is not a value of a type here. |
| E4 | `SCmp.arr` quantifies the index below `n` | Downward closure of a function type at a step index needs it; Core's `cC` has no index. |

## 3. Rules out

- **A value type not monotone along extension.** Every `STy` carries `Mono`. (`trU_not_kmono`
  shows only that a cell carried by `trU` is not a value of this `Mut`, whose invariant is the
  store type read at the current tree; against a `Mut` keeping the predicate a cell was stored
  with, the evidence is `graft_carried_refuses` against `round7_write`, an expressiveness
  argument. `RC.mut_inv`, `RC.mut_readback` and `not_rc_of_inv_ne` hold by `RC`'s definition and
  rule out nothing beyond it.)
- **A bare run read as `F A`.** `Obs.cerwpT_not_keepKripke`: a bare `cerwpT` run is not Kripke
  along `KeepRel` (the stuck `() ()` over a view at `[]` would be a run at the lend's own list, and
  `let a = alloc () in () ()` a run at the empty world, against adequacy). `F A` asks the run at
  every later list (`SCmp.ret`).
- **A continuation stored past its lend.** `STy.not_box_of_view`: a boxed value holding a view at
  `α` is not of `[@d] A` unless `d` is strictly below `α`; at the `κ` of the instances, boxed at
  its lend's own lifetime or at the root (`not_kontBox_at_lend`, `not_kontBox_at_root`).
- **A thunk type that holds of a stuck thunk holding a borrow.** Read at the list, a thunk is a run
  at the lists keeping its lend's record. Read at `[]`, as before E3 was resolved, it holds of
  every thunk holding a view (`cerwpT_nil_of_imm`, `nilRun_stuck`).

## 4. Status and hypotheses

Built for every former but `Mut` at a payload that is not a store code (E1, #790) and effect rows
(`CTy.eff`, no `SCmp` former: `SCmp.ret` takes a table with its `Local`/`Down` proofs, and nothing
yet builds a row's table with its entries downward closed), continuation and task types included.
The value types are downward closed and monotone along extension and `KeepRel`; the computation
types are downward closed, `F A` Kripke along `KeepRel` (`SCmp.ret_kripke`) and monotone in `A`
(`SCmp.ret_le`), `&` Kripke when its components are (`SCmp.amp_kripke`), and reach values under
`U` (`STy.thunkRet_intro`). `⊸`, `∀α ⊏ c` and `ν` are not Kripke by themselves; a thunk of one is
proved at every extension directly. `μ` folds at every body `VTy.NoMut` admits
(`STy.allBody_mono`, `STy.list_cons`); `ν` at Core's shape `F(A ⊕ U X) & F B`
(`SCmp.loopBody_mono`, `SCmp.loop_nonempty`).

Headline hypotheses, classified: (a) the situation the statement is about; (s) a side condition
the library discharges by a named result. None stands in for an unproved fact.

| Result | Hypothesis | Class |
|---|---|---|
| `STy.reread`, `STy.mut_reread` | `hE : w.Ext w′ ρ` | (a) |
| | `hc : CovR (sem w.Θ) w.K ρ` | (s) a part of a world in `WInv` (`cov_of_comp`) |
| `cerwpT_le` | `Tb.Local`, `Tb.Down`, `Q.Down` | (s) `opTableT_local`, `opTableT_down`, `postOf_down` |
| `opTableT_down` | every entry `Down` | (a) |
| `STy.mu_fold`/`_unfold`, `SCmp.nu_fold`/`_unfold` | a monotone body | (a); met by `STy.list_body_mono`, `STy.allBody_mono`, `SCmp.loopBody_mono` |
| `RC.mut_inv`, `RC.mut_readback`, `not_rc_of_inv_ne` | the cell's code `Θ′ ℓ = A`; the re-reading | (a); by `RC`'s definition |
| `SCmp.ret_le`, `cerwpT_post_mono` | `Tb.Local`; the value types included | (s) `opTableT_local`; (a) |
| `SCmp.ret_run` | coverage of the resource and of the list's records | (s) `cov_of_comp`, `RecInv.cov_ls` |
| `SCmp.ret_kripke`, `STy.thunkRet_intro` | coverage of the resource | (s) `cov_of_comp` |
| `Obs.cerwpT_not_keepKripke` | none: refutes `Obs.KeepKripkeRun` with every hypothesis of `cerwpT_adequacy` discharged | — |
| `RC.mut_extends` | coverage, the code kept (`Θ′ ℓ = Θ ℓ`), the payload re-read and agreed on | (a); coverage and agreement (s) from `WInv` and `TWd.Ext` |
| `STy.thunk_intro` | `C` Kripke along `KeepRel`; coverage of the resource | (a), met at `F A` (`SCmp.ret_kripke`) and `&`-trees of them; coverage (s) `cov_of_comp` |
| `STy.thunk_force` | coverage of the resource and of the list's escrows | (s) `cov_of_comp`, `RecInv.cov_ls` |
| `cerwpT_nil_of_imm` | a top-level `imm` cell of the resource | (a) |
| `STy.kont_of_share`, `STy.kontBox_of_share` | `hκ`: `κ a` steps only to `K[a]` | (a) what `κ` is; met by `kontV_step` |
| | `hB`: the answer type is read by the entry's answer | (a) the operation's signature (`OpSig.entT`'s `PBv := 𝒱T⟦o.B⟧`, `scope-789.md` §2.1) |
| | `h`: the share, owning no records, owing `cerwpTC` at `postOf A` | (a) the stop (`cerwpT_perform`); met by `share_viewR` |
| | `hd`: the share in `Res_d` | (a) BOXED-κ's premise; met by `viewR_inStratum` |
| | `n < k` | (a) the index below the stop's |
| `STy.kontBox_resume_after` | the above; coverage; `hE`, `hr`, `hk : KeepRel` | (a); coverage (s) as above; met in `kontBox_depth1`/`_depth3` at a `KeepRel` that is not `SRecsRR` (`not_rr_d1`, `not_rr_d3`) |
| `STy.not_box_of_view` | a view at `α` in the resource, `¬ d ⊏ α` | (a) |
| `SCmp.ret_val`, `STy.thunkC_val` | coverage | (s) as above |
| `reread` (`KSem`) | `MonoΘ Θ` | (a); met by `monoΘ₇` |

## 5. E3 and #794: the value types read the record list

**The question** (#794): does #796's thunk type (`STy.thunk`/`SCmp`, read at `cerwpT`), with boxes
at a lifetime, already give a stored continuation holding borrows the meaning "resumable at any
later world and record list that keeps the records its share reads", without the value types
reading the list?

**No.** A thunk's meaning is a run, and a run is at a list (`twp`'s `ls`, which the world's record
invariant reads: `RecInv`). A value type that does not read the list can run its thunk only at a
list fixed in advance, and the only list every world has is `[]`: #796's `SCmp.ret` ran at `[]`.
At `[]`, a run over a resource holding a view holds of every term: no world whose list is empty
holds an `imm` cell, since the list's records are the world's lineage (`TIT`) and every `imm`
cell of the world's agreement is a record's cell or a chain position (`CoverageT`). This is
`cerwpT_nil_of_imm` (`Core/TreeSemC.lean`), and at the instances' view, a term that never steps is
such a run (`nilRun_stuck`). So the record a continuation's view needs, its lend's, is what such a
type cannot express: its thunk type holds of every thunk holding a borrow, resumable or not, and
"rules out a `κ` that cannot resume" is unprovable of it.

**The change.** `STy`'s predicate reads the list (`P n w ls v ρ`), and its monotonicity is along
extension at every list keeping the re-readings of the records of `ls` the resource reads
(`KeepRel`, the per-branch condition of the continuation share, D13 of `scope-781.md`, ported from
`si-781d` commit `5b6b4a0c`: `Support/Model/Tree/World/ExtF.lean`'s `KeepRel` block and
`Core/TreeWpEff.lean`'s `contShareT`). Every former's downward closure and monotonicity is
re-proved: the formers other than thunks pass the list to their components, at parts of the
resource (`KeepRel.of_compS_left`/`_right`, `KeepRel.of_imm_res`, `KeepRel.of_get_sub`); thunks
quantify over it (`KeepRel.trans`). The answer depends on `KeepRel`: a whole-list re-reading
(`SRecsRR`) refuses a resume after another branch ended a record of its own open at the stop,
which the hardest case needs (`not_rr_d1`, `not_rr_d3`).

**`F A` along `KeepRel`.** A thunk built from a run of `F A` at the current world needs `F A`
Kripke along `KeepRel`. A bare `cerwpT` run is not: `twp` quantifies over starts whose list
re-reads its list whole, and at `[]` a resource holding a view has none (`cerwpT_nil_of_imm`), so
Kripke along `KeepRel` would make the stuck `() ()`, over the view of a lend the program opens, a
run at the lend's own list, and `let a = alloc () in () ()` a run at the empty world, which
adequacy refutes (`Obs.KeepKripkeRun`, `Obs.cerwpT_not_keepKripke`, `Core/TreeSemObs.lean`; the
refutation is at the lend's record owned, `O = [lendRec ℓ]`, the program's own). So `F A`
(`SCmp.ret`) is, over a covered resource, a run at every extension and every list keeping the
records the resource reads: `U`'s quantifier at `F`. It is Kripke along `KeepRel` by
`KeepRel.trans` (`SCmp.ret_kripke`), uniformly; `STy.thunkRet_intro` is restored; a captured `κ`
is a value of `U (B ⊸ F A)` because the share resumes at every such list (`kont_run_of_share`,
`STy.kont_of_share`). The alternative, `twp`'s start condition weakened from `SRecsRR` to `KeepRel`
(which would make `cerwpT` itself Kripke along `KeepRel` and `cerwpT_nil_of_imm` false), changes
the relation under every rule of slice (d) and is not done here. A continuation owning the records
of lends its own branch opened is row 6's.

