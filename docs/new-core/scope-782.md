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
| thunks `U C` | `vThunk` (`kmono_thunk`, by definition) | `STy.thunk`, `STy.thunkC`, `STy.thunkRet`; what carries it: `cerwpT_kripke` (`STy.thunk_intro`) and `cerwpT_le` (new) |
| `F A`, `⊸`, `&`, `⊤` | none | `SCmp.ret` at `cerwpT`, `SCmp.arr`, `SCmp.amp`, `SCmp.top` |
| `μX. A` | none | `STy.mu`: least fixed point over `STy` candidates; fold/unfold at a monotone body |
| `νX. C` | none | `SCmp.nu`: greatest fixed point over `SCmp` candidates; fold/unfold at a monotone body |
| type variables | none | `STy.var` at an environment `Nat → STy` |
| families `[L]` | none | `STy.fam` (`sepRange` at the tree) |
| opaque types | none | `STy.opq` (`Opaque.rel` at the tree) |
| continuation and task types | none | **not here: #789 designs them** |

**Layout.**

| File | Contents |
|---|---|
| `Support/Model/Tree/KSem.lean` | from `Tree/KSem.lean`: `KMono`, `MonoΘ`, existence of the re-reading at a semantic typing (`RC.exists_cell`, `RR.exists_stratum`, `RR.exists`, `reread`, `reread_extends`), `vMut`, `vThunk`, the `kmono_*` results |
| `Support/Model/Tree/KSemGraft.lean` | from `Tree/KSemGraft.lean`: round 7 (`round7_refused_before`, `round7_admitted_after`, `round7_write`) and `trU_not_kmono` |
| `Core/TreeSem.lean` | `STy`, every value former with `Down` and `Mono`; `μ`; type variables; the `mut` re-reading results |
| `Core/TreeSemC.lean` | `cerwpT_le`, `opTableT_down`; `SCmp`, the computation formers; thunks at `cerwpT`; `ν`; `∀` over lifetimes |

`Core/` because the computation types read `cerwpT` and the opaque types read `Core.Opaque`.

## 2. Departures

| # | Departure | Why |
|---|---|---|
| E1 | `Mut`'s payload is a store code, not an `STy` | A cell's invariant is index-free (`MutT.P`); a step-indexed payload (a thunk in a cell) needs step-indexed cell invariants, which the carrier does not have. Every code is a `STy` (`STy.code`), and Core's `μ` already keeps `X` out of `Mut` payloads (`VTy.NoMut`). |
| E2 | One mode: no observable view (`vCE false`) | Core reads an `Imm` payload with `U` relaxed to `True`. Here an `Imm` payload is read in full; row 6 adds the view if `Imm`'s rules need it. |
| E3 | The value types do not read the records list | As `vImm`/`vMut` of `Reread.lean`. `SCmp.ret` runs at the empty list owning no records; the records a lend opens are row 6's. |
| E4 | `SCmp.arr` quantifies the index below `n` | Downward closure of a function type at a step index needs it; Core's `cC` has no index. |

## 3. Rules out

- **A type whose meaning is not monotone along extension.** `trU_not_kmono`: a `Mut` whose
  invariant is carried as the fixed predicate it was stored with (row 5.57's extension by
  falsity, `trU`) leaves `Mut`'s meaning at the grown tree. Every `STy` carries `Mono`, so such a
  type is not one.
- **A re-read `mut` cell whose invariant changes.** `RC.mut_inv`: the re-read cell's invariant is
  its location's code read at the new tree, so a lender reads back a value of the store type
  (`RC.mut_readback`). Any other invariant is not a re-reading (`not_rc_of_inv_ne`).

## 4. Status and hypotheses

Built as planned; every former but continuation and task types (#789). The value types are
downward closed and monotone; the computation types are downward closed, `F A` and `&` also
Kripke (`SCmp.ret_kripke`, `SCmp.amp_kripke`), and reach values under `U`. `∀α ⊏ c` is read at the
lifetimes below `c` in the current tree, so it is not Kripke by itself; its thunk is.

Headline hypotheses, classified: (a) the situation the statement is about; (s) a side condition
the library discharges by a named result. None stands in for an unproved fact.

| Result | Hypothesis | Class |
|---|---|---|
| `STy.reread`, `STy.mut_reread` | `hE : w.Ext w′ ρ` | (a) |
| | `hc : CovR (sem w.Θ) w.K ρ` | (s) a part of a world in `WInv` (`cov_of_comp`) |
| `cerwpT_le` | `Tb.Local`, `Tb.Down`, `Q.Down` | (s) `opTableT_local`, `opTableT_down`, `postOf_down` |
| `opTableT_down` | every entry `Down` | (a) |
| `STy.mu_fold`/`_unfold`, `SCmp.nu_fold`/`_unfold` | a monotone body | (a); met by `STy.list_body_mono`, `SCmp.stream_body_mono` |
| `RC.mut_inv`, `RC.mut_readback`, `not_rc_of_inv_ne` | the cell's code `Θ′ ℓ = A`; the re-reading | (a) |
| `RC.mut_extends` | coverage, the code kept (`Θ′ ℓ = Θ ℓ`), the payload re-read and agreed on | (a); coverage and agreement (s) from `WInv` and `TWd.Ext` |
| `STy.thunk_intro` | `C` Kripke | (s) `SCmp.ret_kripke` at `F A` |
| `SCmp.ret_val`, `STy.thunkC_val` | coverage | (s) as above |
| `reread` (`KSem`) | `MonoΘ Θ` | (a); met by `monoΘ₇` |
