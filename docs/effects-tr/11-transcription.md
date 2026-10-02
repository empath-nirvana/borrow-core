# §11 Transcription guide

[← §10 Findings](10-findings.md) · [index](README.md) · next: [§12 Sources and novelty](12-sources.md)

This is the mechanisation plan: the order in which the results depend on one another, and for
each, the lemmas of BoLo's [TR] (`3764117-supplement.pdf`), of phase B
(`experiments/EffModelRel`, branch `effmodel-rel`) and of borrow-core's `Core/` whose technique
it reuses. A mechanisation should follow the proofs as written, step by step, and build what each
step names; where a proof here is shorter than the one it cites, it says so.

Numbers: `D` definitions, `L` lemmas, `T` theorems, `C` corollaries, `O` open problems, each
`§.n`. [TR] numbers are [TR]'s own, Definitions and Lemmas in two sequences: "[TR] 6.65" is a
Lemma or Theorem, "[TR] Def 6.1" a Definition.

---

## 11.1 Layers, in order

| layer | contents | depends on | where it lives | status |
|---|---|---|---|---|
| 0 | the binary relation and its laws: D3.8–D3.15, D6.1–D6.5, L6.1–L6.5, T6.5, C6.6, T7.1, T7.2, T7.4–T7.10, T7.12–T7.14, T7.15.1, T7.16 (identity return clause) | — | phase B, `experiments/EffModelRel` | **mechanised** (phase B) |
| 1 | §1's changes to phase B's syntax: `lend` answering the capability, `Res` instances, `punch`/`tkt`, rows; L6.4 | 0 | phase B's files, extended | paper |
| 2 | the moded predicate: D1.1–D1.8, D2.1–D2.9, L2.1–L2.3 | 1 | a `Moded.lean` over phase B's intrinsic terms (phase B's `Syntax.lean` header plans it) | paper |
| 3 | the machine: D3.1–D3.7, L3.1 | 1 | new | paper |
| 4 | the resource world at the own fragment: D4.1–D4.6, L4.1, L4.2 | — | BoLo's carrier (`BoCa.Fig16.ResU`, or borrow-core's `WRes`) | paper |
| 5 | the unary relation: D5.1–D5.8, L5.1–L5.18, T5.1, T5.2, C5.3 | 2, 3, 4 | new; the shape of borrow-core's `Core/EffWp.lean`, `Core/EffRules.lean` | paper |
| 6 | agreement and operational soundness: D6.6, L6.7, T6.6, T6.7, C6.8 | 0, 3, 5 | new | paper (cases) |
| 7 | the laws proved here: T7.3, T7.11, T7.16 (any return clause) | 0 | phase B's `Laws.lean`, extended | paper |
| 8 | the kernel lift of T1: D9.1, L9.2, T9.2 | 5, borrow-core `Core/` | borrow-core `Core/EffWp.lean` | abortive half mechanised (borrow-core); in-place half paper, O2 |

Layers 0 and 7 are independent of 2–6: the laws hold for un-moded terms, and only their
operational reading (T6.7) needs the rest.

## 11.2 Dependencies, result by result

| result | uses |
|---|---|
| L2.1 | D2.1–D2.3 |
| L2.2 | D1.1, D1.4, D2.5, D2.8 |
| L2.3 | L2.2.3; PB `Cmp.ren`, `Cmp.den_ren` |
| L3.1 | D3.6 |
| L3.2 | D3.13; PB `Cmp.den`, `iter` |
| L4.1 | D4.1; [TR] 6.9, p. 5 (`●`, `▸◂`, `⦇·⦈`, `⟦·⟧`, `↭`) |
| L4.2 | D4.2; [TR] 6.2, 6.3, 6.43 |
| L5.1 | D3.6, D5.1 |
| L5.2 | D5.2, D5.3, L3.1; [TR] 6.135, 6.136, 6.141, 6.142, 6.143, 6.145, 6.48, 6.49 |
| L5.3 | L5.2.2, L4.2.2; [TR] 6.48, 6.148, 6.149 |
| L5.4 | D5.4–D5.6, L4.2 |
| L5.5 | D2.3, L2.1, L5.4.1, L4.2 |
| L5.6 | D4.5, D5.8, L5.1, L5.2, L4.2 |
| L5.7 | L5.2, L5.3, L5.5, L5.8; [TR] 6.152–6.162 (pattern) |
| L5.8 | L4.2.1, L5.2.4 |
| L5.9 | L5.4.2, L5.2.5 |
| L5.10 | L5.5.1, L5.6, L5.4.2, L5.4.3, L2.2.4, L4.2.3–4 |
| L5.11 | L5.4.1, L4.2.1 |
| L5.12 | L5.4.2, L5.4.3, L2.2.4, D1.5 (well-formed `Ψ`) |
| L5.13 | L5.4.3, L4.2.3 |
| L5.14 | L5.1, L5.2, L5.3, L5.5, L5.6, L5.4, D4.4, D4.5 |
| L5.15 | L5.2.6, L5.6, D4.3, D5.4 (`CoOK`) |
| L5.16 | L5.2.6, L5.6, D4.5 |
| L5.17 | L5.13, L5.4.2, L4.2.4, L5.2.6 |
| T5.1 | L2.1, L5.7–L5.17 |
| L5.18 | D3.6 |
| T5.2 | T5.1, L5.2.1, L4.1, L3.1, L5.18 |
| L6.7 | D6.6; PB `Tree.bindC`, `Tree.hnd`, `Tree.addFin`, `Tree.runL` |
| T6.6 | T5.2, L5.15, L6.7; PB `catchOp_self`, `catchAb_self`, `coStep_self` |
| T6.7 | T6.6, C6.6, L2.3; PB `close`, `Cmp.den_ren` |
| T7.3 | PB `TreeRel.abE`, `Tree.addFin`, `catchAb_ne`, `fresh_of_free`, `soundness` |
| T7.11 | PB `hnd_op_self`, `PureClause`, `CTy.opA`, `CtxEq.of_den` |
| T7.16 | PB `hnd_transparent`, `nuA_gL`, T6.5 |
| L9.2 | D2.7, D3.6, D9.1 |
| T9.2 | L9.2, D5.2; borrow-core `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU`; [TR] 6.64–6.66, 6.112, 6.104, 6.27, 6.28, 6.48 |

## 11.3 BoLo [TR] reused, by number

| [TR] | what | reused in |
|---|---|---|
| p. 5 (§5) | `Res`, `Cell`, `●`, `#`, `✓`, `⦇ρ⦈`, `⟦ρ⟧`, `↭`, `ρ|ι` | D4.1, L4.1 |
| p. 6 | `wp(e){Q̂}`, `⋆`, `─⋆`, `emp`, `!`, `[α]` | D5.2; T9.2 |
| 6.2, 6.3 | `●` commutative, associative | L4.2.2 |
| 6.9 | `▸◂` iff `●` defined | L4.1.1 |
| 6.27, 6.28 | a `mut` cell under `↭` | T9.2 |
| 6.43, 6.116 | `imm` idempotence, I-dup | D4.2 (`Pers`), L4.2 |
| 6.47, 6.48, 6.49 | `↭` reflexive, framed, transitive | L5.2.7, L5.3 |
| 6.64, 6.65, 6.66 | Imm Frame, Mut Frame, Anti Frame | T9.2 (the lifted statements) |
| 6.104, 6.112 | `[α]` over `⋆`; `Nf` | T9.2 |
| 6.135, 6.136 | `wp-bind`, `wp-val` | L5.2.7, L5.2.3 |
| 6.141, 6.142, 6.143, 6.145 | `wp-alloc`, `wp-free`, `wp-load`, `wp-store` | L5.2.6, L5.15, L5.16, L5.17 |
| 6.146 | `wp-ramify` | L5.2.4 |
| 6.148, 6.149 | `wp-M-forget`, `wp-I-forget` | L5.3, L4.2.3 |
| 6.151 | the Fundamental Property, by compatibility lemmas | T5.1 |
| 6.152–6.162 | `id`, `1I`, `1E`, `⊗I`, `⊗E`, `⊕I`, `⊕E`, `⊸I`, `⊸E`, `∀I`, `∀E` compatibility | L5.7, L5.10, L5.11 (pattern) |
| 6.165, 6.166 | `alloc`, `free` compatibility | L5.17 |
| 6.169 | `swap` compatibility (load and store of an owned cell) | L5.15 case 2 |
| 6.172–6.174 | `withbor` compatibility (ownership lent and returned) | L5.15 (shape); T9.2 (setting) |

**What [TR] has that this calculus does not use.** The `imm`/`mut` cells, lifetimes, `[α]`, `N`,
`↺`, and every lemma about them (6.16–6.63, 6.96–6.134, 6.144, 6.147, 6.150) are not used by
§§1–8: the calculus has no borrow types (L4.1). They enter at T9.2, the kernel lift.

**The technique [TR] builds that this document relies on.** [TR] proves its Fundamental Property
without step-indexing because its calculus terminates and its `wp` is total correctness, and it
stratifies a `mut` cell's predicate by lifetime (§5's `Mut_α`). §9.4 uses the first: `bfix` keeps
the calculus terminating. The second is not needed while capability states are ground (§9.4
item 3, O4).

## 11.4 Phase B, by name

| here | phase B (`EffModelRel/…`) |
|---|---|
| D1.1, D1.2, D1.3 | `Syntax.lean`: `Mode`, `G`, `G.den`, `Sig` |
| D1.8 | `ktyB`, `kty` |
| D1.9 | `Val`, `Cmp` (with §1's changes) |
| D3.8–D3.12 | `Tree.lean`: `Act`, `Dtor`, `Tree`, `Strm`, `CoSem`, `CTy.opA`…`CTy.dtorsA`, `Tree.bind`, `Tree.bindC`, `Tree.hnd`, `catchOp`, `catchAb`, `coK`, `coStep`, `Tree.runL`, `Tree.addFin` |
| D3.13 | `Denot.lean`: `Val.den`, `Cmp.den`, `mkK`, `iter` |
| D3.14, D3.15 | `Obs.lean`: `Ev`, `Outcome`, `Obs`, `Wd`, `Act.exec`, `Wd.unwind`, `Tree.obs`, `Context`, `holeTy`, `close`, `CtxEq` |
| D4.7, L4.3 | `World.lean`: `St`, `W`, `W.le`, `W.sub`, `W.gcP`, the updates and their lemmas |
| D6.1–D6.5 | `Rel.lean`: `AR`, `DtorR`, `DR`, `TreeRel`, `StrmRel`, `VR`, `CRU`, `IR`, `ER`, `LR` |
| L6.1 | `TreeRel.mono`, `StrmRel.mono`, `VR.mono`, `CRU.mono` |
| L6.2 | `Compat.lean`: `opA_rel`, `abA_rel`, `actA_rel`, `nuA_*`, `dtorsA_rel`, `abA_dtors_rel` |
| L6.3 | `bindC_rel`, `Tree.bind_rel`, `hnd_rel`, `addFin_rel`, `runL_rel` |
| T6.5 | `Fundamental.lean`: `Val.fp`, `Cmp.fp`, `fundamental` |
| L6.5, C6.6 | `Adequacy.lean`: `Inv`, `adequacy`, `soundness` |
| L2.3 (renaming) | `Rename.lean`: `Cmp.ren`, `Cmp.den_ren` |
| T7.1, T7.2, T7.4–T7.7, T7.12–T7.14, T7.16 | `Laws.lean`: `alg_*`, `alg_dtor`, `h_ret`, `h_op`, `h_fwd`, `h_fwd_ab`, `idem_nu`, `nu_nu`, `new_nu`, `no_accidental_handling` |
| T7.8, T7.9 | `Tensor.lean`: `tensor`, `absorb_pure` |
| T7.10, T7.15.1 | `Examples.lean`: `not_absorb_*`, `lent_state_survives`, `print_print_not_commute`, `nu_op_fails_multishot` |

## 11.5 borrow-core `Core/`, by name

The unary relation (§5) is SPEC §19's `ewpTS` at this calculus's machine. borrow-core's Lean is
for the kernel's machine and its `CDerives` judgement, so it is a model to follow, not a library
to import:

| here | borrow-core |
|---|---|
| D5.2 | `Core/EffDefs.lean` `wpG` (with the `TW`/`Tagged` conjuncts dropped: no lifetime records) |
| D5.3 | `ewpStep`, `ewpTS` |
| L5.2 | `Core/EffWp.lean` `ewp_fold`, `ewp_unfold`, `ewp_ind`, `ewp_val`, `ewp_mono`, `ewp_step`, `ewp_bot` |
| L5.10 | `Core/EffRules.lean` `let_compatC` |
| L5.12, L5.13 | `perform_compatC`, `raise_compatC`, `ewp_perform_here`, `ewp_raise_here` |
| L5.14 | `handle_compatC`, `ewp_handle`, `ewp_kappa_resume`, `ewp_kappa_cancel` |
| L5.17 ([bfix]) | `Core/BoundedFix.lean` `fixSelf_valid`, `boundedFix_compatX` |
| L4.2.4 | `Core/Persistent.lean` `vP_empty_of_persistent` |
| T9.2 (abortive half) | `Core/EffWp.lean` `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU` |

## 11.6 What has no Lean anywhere yet

- the moded predicate (§2) and the three rule changes of §10;
- the machine of §3.1 with the static continuation and the owning lend;
- the whole unary relation (§5) at this calculus;
- the decoding and agreement (D6.6, T6.6), and operational soundness (T6.7);
- T7.3 in general, T7.11, T7.16 at any return clause;
- L9.2 and the in-place half of T9.2.

## 11.7 Open problems

| | statement | where | what is missing |
|---|---|---|---|
| O1 | ν/op at a non-contractible qualifier | T7.15 | a binary relation in which continuation values own pending names |
| O2 | the in-place half of T9.2, written out | §9.3 | the line-by-line transcription of [TR] 6.65's `↭` steps across a framed in-place segment |
| O3 | [TR] 6.65 lifted at a suspending table for an owning lend of a borrowed source | §9.3 | not derived; no obstruction verified |
| O4 | capability states of higher type in the binary relation | §9.4, §9.5 | a binary analogue of BoLo's lifetime-stratified `mut` cells |
