# The chain interpretation

The semantic interpretation of types over Core's step-indexed chain relation, at the per-lend
world `LocTy` and the typed world `KW` (`scope-835-tables.md` §10). It is the rule-level track of
#791 (structure.md §3, §7): every #791 constant and every `CDerives` rule but three is proved
compatible at `SemJN`; the three (`effHandleV`, `effHandleVB`, `reify`) are the named assertion
`HandlerLawN`, and plain adequacy of every closed program, its handlers inside it, follows
(`Goal791N`, §6.4).

The configurations each design choice rests on are indexed in `configurations.md`. The plan for
`FundamentalN` is `scope-831-interface.md` (the lemma interface and units L1–L7), over the
rule-by-rule map `scope-831-map.md`. How the design got here is Appendix A.

## 1. Where it is

| File | What it holds |
|---|---|
| `Core/Chain/SI/LocTy.lean` | the world `LocTy`, its orders `ExtA`/`ExtR`, `Keeps`, `addImm`, the view, `ConsistentX`, `erwp_consistent`, the reseal at the lend's entry |
| `Core/Chain/SI/UpdN.lean` | `ImmTieL`, the relation's entry tie; `rwp`, `rwpG`, `rwpG0` read it (`SI/WpN.lean`, `SI/RwpG.lean`) |
| `Core/Chain/RelBase791N.lean` | the definitions the relation is built on: `TEntN`, `CandN`, `thunkRN`, `nuEnvN`, `EnvDownN`, `ImmWitW`, the fragment predicates (`VTy.inFrag`, `JdgInFrag`) |
| `Core/Chain/Goal791N.lean` | `vN`, `vO`, `cN`, `tabN`, `finN`, `retN`, `gN`, `SemJN`, `rowTabN` at `KW`; the laws |
| `Core/Chain/*KW835N.lean` | the compatibility lemmas at `cN`, every rule but `effHandleV`, `effHandleVB`, `reify`; the constants (`ConstKW835N`: `ConstN`, `ConstsN`, `FundamentalN`, `constN_*`, `constsN_of`) |
| `Core/Chain/FundamentalKW835N.lean` | `MissingN`, `fundamentalN_all`, `fundamentalN_of` |
| `Core/Chain/HandlerLawN.lean` | `HandlerLawN`, its non-vacuity at a clause that resumes `κ` (`handle_resume_inst`) |
| `Core/Chain/Adequacy791N.lean` | `Goal791N`, `goal791N`; the instance `prog791` |
| `Core/Chain/ConfigsKW835N.lean`, `StopKW835N.lean` | the configurations that read `vN`/`cN`; BOXED-κ's stop lemma at `SemJN` |
| `Core/Chain/Lend791N.lean`, `Cancel791N.lean` | the suspending `mut` lend: row lemmas, cancel runs at their rows' tables, the finaliser frame; `withbor2S_compat`, `constN_w2` |
| `Core/Chain/Reborrow791N.lean` | guarded tables, the Mut Frame with its fold, the anti-frame across stops; `withbor3S_compat`, `constN_w3` |
| `Core/Chain/Field791N.lean` | the frame at a field; `withborFS_compat`, `constN_wF` |
| `Core/Chain/ImmImage791N.lean`, `Withload791N.lean` | the observable view `vO`'s facts, the reborrow's image at `vN`; `withloadS_compat`, `constN_wl` |
| `Core/Chain/ImmLend833N.lean` | `withbor1`, `withbor1U`, `withbor2`, `withbor2U` at `SemJN` |
| `Core/Chain/Inst791N.lean` | the compat lemmas instantiated, every hypothesis discharged; `Const791.OK` inhabited |
| `Core/TreeGoal791.lean` | `Row.Suspend`, `CTy.SuspendC`, `Const791`, `Const791.OK` (shared with the tree track) |

The relation's `↭` (`UpdN`, `PredStep`, `MutStep`) and `EndOKG` are as the chain relation has
them; its `mut` frames (`erwp_M_frame*`, `erwp_M_antiFrame`, `erwp_withbor3`, `rwp_M_frame`) are
used at the view, not restated. `LocFam` gained the `imm` records and the relation's entry the
`imm` tie (§2.5).

## 2. The world

### 2.1 Keys and families

```
structure LocTy where
  fam : Loc → (b : Life) → Option (Nat → Val → SPropS Loc Val b)
  imm : List SRec := []
```

`Θ ℓ b` is the payload family of the `mut` cell lent at `ℓ` at the lifetime `b`. The key is the
lend, as Core's records are one per lend (`SRec = FrameRec × Life`, `Core/FrameRecords.lean`).

- A lend at `(ℓ, α)` is `Θ.add ℓ α F`; every other key is kept (`LocTy.add_keep`), the source's
  `(ℓ, β)` among them.
- A lend's lifetime is fresh: strictly shorter-lived than every key present (`LocTy.Fresh`). A
  bounded world has a fresh lifetime below any bound (`LocTy.exists_fresh`), and a lend keeps it
  bounded (`LocTy.fresh_add`). `LocTy.OK Θ := Θ.Down ∧ Θ.Bounded`.
- The family stored at `(ℓ, a)` reads the world only above `a`:
  `famL a P Θ = P (Θ.above a)`, Core's `ls₀` in `ptoMutS`. A fresh lend adds nothing above a key
  present (`LocTy.above_add`), so a stored family stays the payload read at the current world
  (`fam_add_self`). The lifetime stratification, not the step index, makes the stored family a
  fixed function; no recursive world is needed.
- `mutL a P Θ n v ρ`: `v = loc ℓ`, `ρ = ℓ ↦ mut(a, w, χ, famL a P Θ j)` with `n ≤ j`, and
  `Θ ℓ a = some (famL a P Θ)`. This is Core's `ptoMutS` over the world.

### 2.2 `above`, the two orders, `Keeps`

- `Θ.above a`: the keys strictly longer-lived than `a` and the `imm` records lent strictly above
  `a`. This is Core's `ls₀` (`x ∈ ls₀ ↔ x ∈ ls ∧ x.2 ⊐ b`).
- `LocTy.ExtA Θ Θ′`, the world-relative order: entries only added, nothing added above a key
  present, every `imm` record kept (`ImmLe`). A fresh lend is one step (`LocTy.extA_add`); it is
  transitive.
- `LocTy.Keeps Θ Θ′ ρ := ∀ x ∈ Θ.imm, CellIn ρ x.2 → x ∈ Θ′.imm`: the records relevant to `ρ` are
  kept, a record being relevant when `ρ` holds a borrow cell no longer-lived than the lifetime it
  was lent at.
- `LocTy.ExtR Θ Θ′ ρ`, the resource-relative order `U` and `⊸` are Kripke along: every key at a
  lifetime `a` with `CellIn ρ a` is kept and `above a` is unchanged, and `Keeps Θ Θ′ ρ`. `ExtA`
  is `ExtR` at every resource (`LocTy.ExtA.extR`). `ExtR` departs from Core's `Ext` twice (§5,
  D4 and D5).
- An `imm` lend's record is `LocTy.addImm (r, α)`. At a resource in `Res_α` the world with it is
  an `ExtR` extension (`LocTy.extR_addImm`, Core's `ext_add`, [TR] 6.64) and the world without it
  is one too (`LocTy.extR_of_addImm`, Core's converse step at the Imm Frame's exit).

### 2.3 The `imm` records

`Θ.imm` is Core's record list for `imm` lends, moved into the world: each record with the
lifetime it was lent at. A `mut` lend leaves it alone (`LocTy.add_imm`). `vN`'s `Imm` clause reads
its witness there (`ImmWitW`, §3.2). The relation reads the records against the run's list at its
entry (§2.5).

### 2.4 The view and consistency

The relation's location typing `LocFam` is per location (`{fam, imm}`, `fam` a partial map to
`Σ b, family`). A run reads the world at a view `c : Loc → Option Life`, the lifetime each
location's live `mut` cell is at:

```
Θ.view c ℓ := (Θ ℓ b).map ⟨b, ·⟩  where c ℓ = some b;   none where c ℓ = none
(Θ.view c).imm := Θ.imm
```

- `Φ.set` at a lend is the view of the per-lend lend:
  `(Θ.add ℓ α F).view (setLife c ℓ α) = (Θ.view c).set ℓ α F` (`LocTy.view_add`). The relation's
  lend frames, stated at `Φ.set`, are the per-lend lend seen from its run.
- `ConsistentX c ρ`: every `mut` cell of `ρ`'s exclusive walk is at `c ℓ`. A held `Mut` argument
  is a top-level cell, so it is at its view lifetime (`consistentX_get`). Composites and parts
  keep it (`consistentX_compS`, `consistentX_left`/`_right`, the parts needing `ResU.Valid`).
- A run keeps it: from a resource consistent with `c`, every value or stop the run reaches
  returns a resource consistent with `c` (`erwp_consistent`, at any `LocFam`).
- The anti-frame's reseal at the lend's own entry: a `Mut @β` value of the world's shape at a
  view with `c ℓ = β` gives the anti-frame its `Φ ℓ = (β, F)`, and the reseal into the lower
  member is a `MutStep` there (`reseal_at_entry`, `erwp_antiFrame_view`).

### 2.5 The relation's entry tie

```
ImmTieL I ls := ∀ x ∈ I, x ∈ ls          -- SI/UpdN.lean
```

`rwp`, `rwpG` and `rwpG0` are entered only where `ImmTieL Φ.imm ls` holds: every `imm` record of
the location typing is a record of the run's list, at its lifetime. In that list form it is kept
locally: `EndOKG` keeps a list's members (`ImmTieL.perm`), a lend's body extends the list
(`ImmTieL.of_sub`), and the reborrow lemmas run their callbacks at the same location typing and
list. At a run's first entry the tie and the typed world's invariant (`TI`) put a witness's
record on the list, which is Core's `CohE (rsOf ls)` (`desc_mem_of_tie`, `cohE_of_immWitW`).

Statements the tie changed: `rwp_compose`/`rwpG_compose` take it; `rwp_safe`, `rwpG_safe`,
`erwp_safe` and `erwp_adequacy` take `ImmTieL Φ.imm []` (`erwp_adequacy` discharges it by
default); `rwpG_extΦ`/`erwp_extΦ` take `Φ.ImmLe Φ′`; `PoolSchedAdequacyN` and `progOfN_orDiverges`
take `imm = []`; `goal791N` reads `erwp_adequacy` at the empty world. The capture bridges into `crwpG` (`crwpG_of_rwpG`,
`cerwp_of_erwp`, `cerwp_bindRwp`, `cerwp_alloc`, `cerwp_free`, `cerwp_scope`, …) take
`Φ.imm = []`: `crwpG`'s entry does not carry the tie (§7).

## 3. The interpretation

### 3.1 The pieces

| Piece | Definition (`Goal791N.lean`) | Core counterpart |
|---|---|---|
| `vN A δ Θ n v ρ` | `𝒱⟦A⟧δ` at the world and the index | `vCE`, clause by clause, `⋆` as `ResU.CompS` |
| `vO A δ Θ n v ρ` | the observable view an `imm` payload is held at: `vN`'s clauses with `U C` read as `True`, `!A` and `Mut`'s family at `vN` | `vCE false` |
| `1`, `⊗`, `0`, `+`, `Ref`, `[@a]`, `!`, `Unk`, `I32/I64` | `vCE`'s clauses | `vCE` |
| `Mut @a A` | §3.2 | `ptoMutS` |
| `Imm @a A` | §3.2 | `ptoImmS` at `vCE false`, with `CohE` |
| `U C` | `C` at every `Θ′` with `Θ.ExtR Θ′ ρ` and `Θ′.OK`, every view `c` with `ConsistentX c ρ`, every record list | `vCE`'s `U`, Kripke along `Ext` |
| `F A` | at every floor `lo`, `erwpK KW.PostK (·.Θ.view ·.c)` from `⟨Θ, c, lo⟩` at the empty table, post `𝒱⟦A⟧` at the world reached; it is `erwp (Θ.view c) (opTableN OpTabN.empty) 𝒱⟦A⟧` (`cN_ret_iff`) | `cC`'s `F` (`wpTS`) |
| `A ⊸ C` | at the function's own world `Θ`: every `k ≤ n`, every argument in `𝒱⟦A⟧` at `Θ` composed with the function's resource, every view consistent with the composite | `cC`'s `⊸`, a wand at the same world (#834) |
| `C & D`, `⊤` | componentwise; `True` | `cC` |
| `∀'x ⊏ @c. C` | every `α ⊏ @cδ` (`LtLife`), vacuous where `@cδ` is undefined | `cC`'s `∀` |
| `F_Σ R` | at every floor `lo`, `erwpK KW.PostK` from `⟨Θ, c, lo⟩` at the table of the row's layers (`tabN`, read at the world `KW`, each entry owing along `KW.Owed`), post `retN` | `cC`'s `eff` (`effTab`, `finObl`, `effRet`) |
| `entN q B PA PB fin` | qualifier; abortive iff `B` is empty and `q ≠ lin`; payload and answer at every list; the cancel obligation where `capB q B`; resumed under `extF` | `effTab`'s entry (D8) |
| a row's answers (`tabN`, `finN`, `F_Σ`) | `vN B δ Θ ∧ ConsistentX c`: read at the view, as every resource entering a run is (D7) | `vC true B` |
| `finN` | `none` at `⊤`; else `cancelOblN` at the cancel row's table, at the view | `finObl` |
| `gN δ Θ Γ γ n ρ` | the live slots' values over a split of `ρ` | `gSepC` |
| `SemJN Δ Γ e j` | every `δ ⊨ Δ`, `γ`, world `Θ` with `Θ.OK`, view `c` with `ConsistentX c ρ`, index `n`, list `ls`, resource in `𝒢⟦Γ⟧`, `Ctx.LiveWithin Γ γ` | `SemC` |
| `rowTabN S` | `tabN (F_S 1) ∅`: the table a task at the row `S` runs at, at each world | `rowTab S` |

### 3.2 `Mut` and `Imm`

```
Mut a A at δ, Θ, n:  ∃ α, a.interp δ = some α ∧ ∃ b, α ≤ b ∧
                     mutL b (vN A δ) Θ n v ρ ∧
                     ∀ Θ′ j u r, vN A δ Θ′ j u r → r ∈ Res_b

Imm a A at δ, Θ, n:  ∃ α, a.interp δ = some α ∧ immCell α (vO A δ Θ n) v ρ ∧
                     ∀ ℓ s u σ h, ρ = ℓ ↦ imm(s, u, σ) → ImmWitW Θ.imm ℓ s A δ
ImmWitW I ℓ s A δ := ∃ x ∈ I, ⊓s ≤ x.2 ∧ ∃ d, DescR x.1 d ∧ CohE [d] ℓ A δ
```

- `Mut` is Core's `ptoMutS` shape: the slack `@aδ ⊑ b` (which `mutSub` reads), the cell at `b`
  holding a member of the family the world stores at `(ℓ, b)`, and the uniform conjunct (every
  value of `A` in `Res_b`, Core's `hunif`). The lend sites build the borrow at `b = α`; the
  reborrows open the source at its own `b` (`consistentX_get` gives `c ℓ = b`).
- `Imm` is Core's `ptoImmS` shape: one `imm` cell `imm(s, u, σ)` with `@aδ ⊑ ⊓s`, the payload in
  `vO`. The witness is Core's `CohE` at a descendant `d` of a world record (the record's own cell,
  a chain position, or a sub-record's cell). The lifetime match `⊓s ≤ x.2` makes the witness
  relevant to its cell for `Keeps`, so `vN_extR` keeps it. An `imm` lend's cell `imm({α}, …)` is
  witnessed by the lend's record at `α`; `withload`'s new cells `imm({β}, …)` by the source's
  record.

### 3.3 The fragment

`cN` reads `ν` at a `NuShape` body (`scope-831-interface.md` §12); every value-type former has a
clause. `vN`/`vO` are `vNE`/`vOE`
at the empty environment: a type variable is its entry's candidate (`False` at the empty
environment) and `μX. A` is Core's least fixed point, the candidate joint over the mode, the world
and the index (`scope-831-interface.md` §13). `VTy.inFrag`/`CTy.inFrag` mark the formers read;
`JdgInFrag Γ j` a judgment whose context and type use only those; `Const791.InFrag` a constant
whose type does.

## 4. The row and the constants' premises

`Row.Suspend S 'x @bnd` (`Core/TreeGoal791.lean`): every operation not unrestricted, named
(`n ≠ 0`), its payload and answer types free of `'x` and outliving `@bnd` (`VOutlives ∅ bnd`),
and each capturable operation's cancel row meeting the same clauses (`CTy.SuspendC`). SPEC §62
("Typing: suspension") states it.

- The outliving clauses put payloads and answers in the stratum of every lend `α ⊏ @bnd`
  (`vN_inStratum_bnd`; `OpTabN.LendOKCR`'s `pa`/`pb`) and leave their reading unchanged by a
  fresh lend (`vN_add_eq_bnd`).
- A bound defined at the empty context is `⊤` (`interp_top_of_defines_empty`), so answers lie in
  `Res_⊤` and are consistent with every view (`consistentX_of_top`, `consistentX_of_outlives`);
  `erwp_claimX` reads that, and so do the twins of the callback's table and the lender's, which
  read their answers at different views (`tabN_tabR_twin`, `tabN_tabG_twin`).
- At such a bound the clause excludes, outside a box or `!`, `Imm @b A`, `Mut @b A`, `U C`, `Unk`,
  and a box at a lifetime with a variable. A box at a closed lifetime and `! A` pass.
- `answer_not_inStratum` (`Lend791N.lean`) is why the answer clause is there: `U(F 1)` has values
  outside every stratum.
- The cancel-row clause admits cleanup that performs (`suspend_closingOp`).

`Const791.OK` is the corresponding `CDerives` rule's premises at the empty context, `Row.Unwind`
read as `Row.Suspend`, plus `LifeCtx.empty.Defines bnd` (Core's rules fix the bound to
`Δ.meetOfDom`, which meets it: `defines_meetOfDom_empty`). The constants are `w2` (`withbor2U`),
`w3` (`withbor3U`), `wF` (the field reborrow, `withborFE`), `wl` (`withloadU`) and `sm`
(`sliceBorrowMU`).

## 5. Departures from Core

Each row is a place where the chain's reading differs from Core's. "Configuration" names the Lean
result that forces the difference (`configurations.md` has each); "no configuration yet" means
none is recorded and the departure is a choice still open. The IDs in brackets are
`scope-831-interface.md`'s entries.

| | Departure | Core | Configuration |
|---|---|---|---|
| D1 | `mut` lends are keys `(ℓ, b)` of the world, and `Mut` reads the key (`mutL`); a run is at the view [R1, R2, R4] | `ptoMutS ℓ α ls₀`: the cell stores `P ls₀` | `perLocShape_not_reborrow` (a per-location key is overwritten by a reborrow; the per-lend world keeps the value: `perLocShape_lend_reborrow`); `reseal_untyped` (the anti-frame's reseal needs the location typed) |
| D2 | values read no record list: `vN` has no `ls` argument [K1, R5] | `Imm` reads `CohE (rsOf ls)`, `Mut` stores its payload at `ls₀` | `coreMutImm_not_extF`: a list-reading payload is not stable along `extF`, at which the chain resumes |
| D3 | `imm` records live in the world; `Imm`'s witness is `ImmWitW` there; the relation's entry carries `ImmTieL` [K3, V10, R7, R8] | `CohE (rsOf ls)` read off the run's list | `not_wlImage_vN` (no `Imm` clause over `vN`'s arguments gives `withload`'s step 8); `immAgreeErwp_both`, `not_wlImageA_vN` (no agreement read off the unchanged `erwp` does); `not_effOf_guarded`, `immTie_guard_fails` (a guard on `cN`'s run clauses breaks `cN_effOf`); `immTieL_world_ref` (the entry tie excludes the second world) |
| D4 | `ExtR` asks "nothing added above" only at the lifetimes of keys present [K1] | `Ext` asks it above every `b` with `CellIn ρ b` | `extRL_breaks_extA`: read literally, `U` is not Kripke along `ExtA`, at a stuck application from a typed world of two `mut` cells |
| D5 | `Keeps` reads a record's relevance off its lifetime; `ImmWitW` carries the lifetime match `⊓s ≤ x.2`; `extR_of_addImm` has no relevance premise [K4, V10] | `Keeps` reads relevance off the location (`Rel`); the converse of `ext_add` ([TR] 6.64) takes a relevance premise, discharged at the Imm Frame's exit by `not_rel_lineage` | `not_unwindArgStepLoc` (`Depart831N`): Core's location reading fails at `tabN_unwind_eq`'s world-level step, a step of our unwinding-row proof that Core does not take; candidate for the post-merge refactor (`scope-831-interface.md` §6.3) |
| D6 | `⊸` is Kripke along `ExtR` and down the index [F10] | `cC .arr` is a wand at the same list | the index is the step-indexed `−∗` of `sC`, the chain's carrier; returned to Core's plain wand in #834 (`scope-831-interface.md` §8.1); no longer a departure |
| D7 | `U`, `⊸` and `SemJN` quantify views consistent with the resource (`ConsistentX`), on the exclusive walk; a row's table reads its answers at the view (`tabN`'s `ConsistentX c`) [R11] | Core has no view; the tree track uses `Covers`/`vThunk` | for the exclusive walk over the whole flattening: `flat_part_config`. For consistency in place of `Covers`: no configuration yet (the argument is prose, Appendix A.4). For the answers: every resource that enters a run is read at the run's view, the answer a resumption brings included; each producer meets it (`scope-831-interface.md` §10.2): a lending constant's relay by `Row.Suspend`'s answer clause (`consistentX_of_outlives`), a handler by its own run at the view (`erwp_consistentAns`), the scheduler `HS` at the hardest row by its `∅` answers (`hardestRow_entry_PB`) |
| D8 | an entry's continuation is resumed under `extF` (`entN`'s `wc`) | `Ext` | `not_extFoldTransfer`, `resume_not_ext`: `Ext` is not kept across a fold. `ext_extF`: no restriction relative to `Ext` |
| D9 | the interpretation carries a step index; rules owe `vN_le`, `gN_le` and consistency at a split [V11, G11, G12] | no index | none needed: the index is the relation's |
| D10 | a `Div` row is a row of the table; Core's coinductive `cwp` has no counterpart [E13] | `cwp` and its bookkeeping | no configuration: it is how `erwp` is defined |
| D11 | `withload`'s image is typed at the source's type, the record's positions read across `TyEq` (`immWitW_root`/`…Mut`/`child`/`childMut`, `RefPos.tyEq`, `MutPos.tyEq`); the first entry is unfolded and `erwp_rebGen` applied at the canonical image | `vC_tyEq` converts the source to the record's type; `RebChooseTW` picks the image inside `wpTS_reborrow` | no configuration yet; `vN_tyEq` is not built (L2) |
| D12 | the capture bridges into `crwpG` are read at `Φ.imm = []` | — | no configuration: `crwpG`'s entry does not carry the tie yet (#821). (`goal791N` starts at the empty world, whose `imm` is `[]`: a closed program starts at the empty list) |

What is Core's, not a departure: `Mut`'s slack and uniform conjunct; `Imm`'s payload at the
observable view; `∀` vacuous where the bound is undefined; `vN_extR` as `vC_local`;
`vN_outlives`/`vN_outlivesLe` as [TR] 6.60.

## 6. What is proved

The headlines are registered in `scripts/AxiomCheck.lean`, and `scripts/CheckAxioms.lean` checks
every declaration; axioms are within `propext`, `Classical.choice`, `Quot.sound`.

### 6.1 Laws (`Goal791N.lean`)

| Law | Scope |
|---|---|
| `vN_down`, `vO_down`, `cN_down`, `tabN_down`, `finN_down`, `retN_down`; `vN_le`, `cN_le` | every former; computations at `Θ.Down` |
| `vN_congr`, `vO_congr`, `cN_congr`, `tabN_congr`, `finN_congr`, `retN_congr` (with `immWitW_congr`) | `δ` read only at free variables |
| `vN_extend_of_not_free`, `gN_extend_of_not_free` | a variable not free |
| `vN_extR`, `vO_extR` | every former, along `ExtR` at the value's resource (Core's `vC_local`) |
| `vN_extA` | every former, from `vN_extR` and `ExtA.extR` |
| `cN_extA` | every former but an effect row (`noEffSpine`) |
| `vN_local` | every former: a value at the world with a lend, its resource in the lend's stratum, is one at the world without it |
| `vN_outlives`, `vN_outlivesLe` | Core's [TR] 6.60 |
| `vN_inStratum_bnd`, `vN_add_eq_bnd`, `vN_above`, `vN_fam_down` | §4; a stored family read at the world |
| `cN_effOf`, `retN_effOf` | `F_Σ R` is `erwp` at the row's table |
| `cN_head` | closed under a pure head step backwards (Core's `cC_head`) |
| `vN_mu_iff` (`vN_roll`, `vN_unfold`), `vN_ind`, `vBN_mu_ind`; `vBN_some`, `vBN_rename`, `vBN_subst`, `vBN_congr_occ`, `vBN_mono_at` | Core's `RelMu` at the chain: the unroll equation at the same index, the induction principle, the environment laws (`scope-831-interface.md` §13) |

### 6.2 Rules at `SemJN`

| Rule | Lemma | File | Premises beyond the rule's |
|---|---|---|---|
| `mutSub` | `mutSub_compatN` | `Goal791N` | none (Core's `ptoMutS_antitone`) |
| `immSub` | `immSub_compatN` | `Goal791N` | none (Core's `ptoImmS_antitone`) |
| `allI` | `allI_compatN` | `Goal791N` | none |
| `withbor1` | `withbor1_compatN` | `ImmLend833N` | none |
| `withbor1U` | `withbor1U_compatN` | `ImmLend833N` | `hd`: the finaliser's `SemJN` |
| `withbor2` | `withbor2_compatN` | `ImmLend833N` | none |
| `withbor2U` | `withbor2U_compatN` | `ImmLend833N` | `hd` |

The six borrow rows follow Core's proofs. The `imm` lend's callback runs at `Θ.addImm (r, α)`
(`LocTy.extR_addImm`); its run at that world's view is read as a run at the lender's
(`erwp_tieEntry`, at abortive tables only, which is every table these rules meet:
`scope-831-interface.md` §6.1); the result returns by `LocTy.extR_of_addImm`. `withbor2U` uses
the Mut Frame across the row's raises (`erwp_M_frameR`) and the claim's consistency
(`erwp_claimX_abort`).

### 6.3 The constants

Each `*S_compat` proves the constant a value of `!` its type at every `δ`, world and index, from
`Const791.OK`'s clauses and, where the constant has a finaliser, the finaliser's semantic judgment
`hd`. `constN_*` reads `hd` off `FundamentalN` at the finaliser's derivation; `constN_all` reads it
off `fundamentalN_all`, with no fragment premise.

| Constant | Compat lemma | `ConstN` | Instance, every hypothesis discharged |
|---|---|---|---|
| `w2` | `withbor2S_compat` | `constN_w2 : FundamentalN → InFrag → ConstN` | `withbor2S_inst`; `w2_ok`; `withbor2S_perform` (a callback that stops at a must-resume operation holding the borrow) |
| `w3` | `withbor3S_compat` | `constN_w3 : FundamentalN → InFrag → ConstN` | `withbor3S_inst`; `w3_ok` |
| `wF` | `withborFS_compat` | `constN_wF : FundamentalN → InFrag → ConstN` | `withborFS_inst`; `wF_ok` |
| `wl` | `withloadS_compat` | `constN_wl : ConstN` (no finaliser) | `withloadS_inst`, `constN_wl_inst`; `wl_ok` |

The instances are at the hardest case's row (`hardestRow`, `hardestRow_suspend`) and the bound
`LifeCtx.empty.meetOfDom`; finalisers `dFree` (`λr. free r`) and `dRelease` (`λr. ()`, Core's
`forget`, derived by `CDerives.releaseMut` in `w3_ok`/`wF_ok`).

**`w2`.** The lend at a fresh `α` below the bound, the content's stratum and the side condition
`⊢ A ⊒ @b` (`hO`, through `vN_outlivesLe`); the callback at `Θ.add ℓ α (famL α 𝒱⟦A⟧ Θ)` and
`setLife c ℓ α` (`view_add`), its argument `lend_mutL`; its stops fold the borrow
(`erwp_M_frameCR`); cancel runs at their cancel rows' own tables (`tabR`, `tabR_can`); the claim
consistent with `c` (`erwp_claimX`); the finaliser frame (`erwp_ubindClaimRT`, `fin_claim`); the
result back by `vN_local`.

**`w3`**, Core's `withbor3U_compatX` step by step:

| # | Chain |
|---|---|
| 1 | the constant at `PMap.empty` |
| 2 | `vN`'s `Mut` clause: `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `Θ (ℓ, β) = F_o` |
| 3–4 | the callback along `ExtR`; `vN_extR` carries both to the run's world |
| 5–6 | `mutL` unpacked; the uniform conjunct (Core's `hunif`) |
| 7 | `consistentX_get` gives `c ℓ = β`; `reseal_at_entry` the anti-frame's `hF` |
| 8 | `erwp_M_frameCRG` (the Mut Frame at a fresh `α ≤ β`, its fold at every stop), `erwp_M_antiFrameCR`/`erwp_M_antiFrame_cancelRunCR` (the anti-frame across stops, raises and layered cancel runs), `tabG_can`, `tabR_canA` |
| 9–10 | `LocTy.exists_fresh`; `lend_mutL`, the borrow's uniform conjunct from the source's |
| 11 | the callback at `Θ + (ℓ, α)`, view `setLife c ℓ α`, its table the guarded twin (`tabN_tabG_twin`) |
| 12 | `vN_local` at `['x] B` |
| 13 | `F_i k ⊆ F_o k` by the uniform conjunct and `vN_above`; the resealed cell a `Mut @a A` value beside the result and in every raise's claim (`fin_claimM`) |

**`wF`** is `w3`'s steps at the source `Mut @a (Ref A)`. Core prints no field-reborrow rule. The
load from the opened `ℓ ↦ own(loc ℓ₂)` is `rwp_load` under `erwp_bindR`; the Mut Frame is at
`ℓ₂` with the opened cell framed outside it (`erwp_frameGR`, `erwp_frame_cancelRunGR`,
`tabG_canF`); the view at `ℓ₂` is consistent through the source cell's walk (`exS_none_of_walk`,
`exS_mut_wit_get`, `consistentX_leftE`).

**`wl`**, Core's `withload_compatX` step by step:

| # | Chain |
|---|---|
| 1–4 | the constant at `∅`; the source `loc ℓ`; the callback; both at the run's world (`vN_extR`, `vN_le`) |
| 5 | `rwp_load_I` under `erwp_bindR`; the payload in `vO` |
| 6 | the record whose cell or chain view the source is: `cohE_of_immWitW` at the first entry, the cell by `TI.leInvW` or `TI.exIn` |
| 7 | the template: `six132_shape_fresh`, `tmpl_exists`, `tmplD_exists` |
| 8 | the image typed at `Imm̲ 'x A`: `relabel_vN` (Core's `relabel_obs`), `vO_transfer`; across raises and layered cancel runs: `erwp_rebGen`, `erwp_rebGen_cancelRun`, `tab_rebClosed` |
| 9 | the fresh `β := ↓(⊓s ⊓ g ⊓ @bnd δ)` |
| 10 | the pin: the image at the record's value |
| 11 | the callback at `δ['x ↦ β]`, `callback_at_image`; its table the constant's (`tabN_extend_suspendC`) |
| 12–13 | the result `['x] B` at `B`, `vN_extend_of_not_free` |

The image cells' lifetimes at `Imm` positions come from the run's tags (`lifeBoundW_of_entry`,
Core's `lifeBound_of_tagged`), which is why the entry tie matches a record's lifetime.

### 6.4 The statements

| Statement | Meaning |
|---|---|
| `ConstN c` | `c.OK → ∀ δ Θ n, Θ.OK → vN (! c.ty) δ Θ n c.val ∅` |
| `ConstsN` | `ConstN c` for every `c` with `c.InFrag` |
| `FundamentalN` | every `CDerives Δ Γ e j` with `JdgInFrag Γ j` gives `SemJN Δ Γ e j` |
| `MissingN` | `HandleVN ∧ HandleVBN ∧ ReifyN`: the three rules with no compatibility lemma, each as its `*_compatN` would be |
| `HandlerLawN` | a structure of the same three fields, a `Prop` hypothesis in `PinLaw`'s form |
| `Goal791N` | every closed program typed at `F 1` from constants meeting their premises, its handlers inside it, is `OrDiverges` |

```
fundamentalN_all : MissingN → CDerives Δ Γ e j → SemJN Δ Γ e j
fundamentalN_of  : MissingN → FundamentalN
constN_all       : MissingN → ∀ c, ConstN c
goal791N         : HandlerLawN → Goal791N
```

`fundamentalN_all` is `fundamentalC`'s induction, every case its rule's compatibility lemma at
`cN`. No lemma reads the fragment, so the induction holds at every derivation; `constN_all` reads
each finaliser's judgment off it, so `Goal791N` needs no fragment premise on the constants.
`goal791N`: `fundamentalN_all` at the program's derivation, at the empty world and view, the
constants' context met by their values (`gN_ctx791`); `F 1` at `KW` is `erwp` at the empty table
(`cN_ret_iff`), and `erwp_adequacy` gives `OrDiverges`.

| Conjunct | Rule | Core's lemma |
|---|---|---|
| `HandleVN` | `effHandleV` | `handleV_compatC` |
| `HandleVBN` | `effHandleVB` | `handleV_compatCB` |
| `ReifyN` | `reify` | `reify_compatX` |

**Non-vacuity.** `goal791N_premises_inst`: every premise of `Goal791N` at `prog791`, which
allocates a cell, lends it `mut` with the constant `withbor (2)` at the row `{wait}`
(`wait : 1 ↠^lin 1`), whose callback performs `wait` while it holds the borrow and then releases
it, frees the cell after the lend, and handles `wait` inside the program (`effHandleT`, its clause
resuming `κ`). `prog791_orDiverges : HandlerLawN → OrDiverges prog791`. `handle_resume_inst`: the
conclusion of `HandleVN`/`HandleVBN` at a handler whose clause resumes `κ`, at every handled
computation, every premise inhabited (`HandlerLawN.lean`).

### 6.5 Relation-level results the track rests on

`erwp_adequacy` (`goal791N`'s last step). `poolSchedAdequacyN` (`PoolN.lean`), `SchedOKN`,
`PoolSpawnN` (`HS`, `hs_schedOKN`); `hardestCase791` and `hardestCase791C` (`Hardest791N.lean`:
the hardest case, resumed and cancelled, as closed programs under the untyped scheduler `HS`,
through `progOfN_orDiverges`). They read no interpretation, and `Goal791N` reads none of them.

## 7. What is open

**`HandlerLawN`.** `effHandleV`, `effHandleVB` and `reify` have no compatibility lemma at `cN`.
The step that does not go through is `assert-boundary.md` §2.2: a clause that keeps `κ` hands it
to `vN`'s `U` clause, which reads `KW.OwedR`, where the stop owes it along `KW.Owed` at the floor
the stop chose. `assert-boundary.md` §3 ranks smaller assertions (a per-operation mark,
`StopReadNW`); each needs E10 at `OwedR` entries and the reading-parametrised fundamental lemma.

**Departures with no configuration yet** (D5, D6, D7's `Covers` half, D11, D12). Each is a
choice: a configuration that forces it, or a return to Core's reading. `scope-831-interface.md`
§5 lists what each return would touch.

**Other open items.**
- `Goal791Top` (`Core/TreeGoal791.lean`) is the tree track's form of `Goal791N`. No Lean lemma
  relates the two.
- `cN_extA` at `F_Σ R`: not derived, obstruction not verified. No rule needs it
  (`scope-831-map.md` §3.2): it would need an `erwp` lemma over tables whose payloads grow and
  whose answers agree.
- D4's configuration is built at `F 1` with the stuck application `() ℓ′`, refuted from the
  `TWNC` world of the two `mut` cells (`ExtRLit791.world_two`). No negative configuration for a
  wrong constant is built.
- The capture bridges at `Φ.imm = []` (D12): open until `crwpG`'s entry carries `ImmTieL`
  (#821).

## Appendix A. History

Each paragraph is one attempt, oldest first. The detailed scope documents of each step are in git
history: `docs/new-core/scope-791-rule.md` and `docs/new-core/scope-791-loctype.md` at 9ba78899.

**A.1 The first interpretation** (17d63b5f–b9e34d0e). `vN`/`cN` over `erwp` at the relation's
per-location `LocFam Φ`, `U` at every record list, `Imm` without records, no `Covers`.
`withbor2S_compat` (3dc8a14d) was proved with two row premises, `hSF` and `hSB`.

**A.2 The row clauses** (8e6412cf, 0f1bf3cf). `Row.Suspend` gained the answer clause and the
cancel-row clause (`CTy.SuspendC`); cancel runs at their cancel rows' own tables (`tabR`,
`erwp_M_frame_cancelRunCR`, `tabR_can`) took `hSF` out of `withbor2S_compat`.

**A.3 Core's `Mut` per location** (70cbb5be, ab7b6986). Reading Core's `ls₀` as the location
typing failed at a reborrow: `coreShape_not_reborrow`, now `perLocShape_not_reborrow`. Three
routes (records per lend; inclusion with pointwise content; a `Φ`-free content semantics) were
written down and none was built.

**A.4 The port of `withbor3_compatX`** (fb74df0b). The step map stopped at step 7: the
anti-frame reseals into a lower member, which `↭` admits only at a location the location typing
types (`reseal_untyped`). `vThunk`'s `Covers` (`SI/MutSemN.lean`) was checked as a way to type the
location and set aside: it covers the thunk's resource, not `⊸`'s argument, and names some family
rather than the payload's. `vThunk`/`Covers` are still defined and used nowhere.

**A.5 The per-lend world, first order** (7ac003bb, 46cd5573, 2b4a7523, 728b51d7). Keys
`(ℓ, lifetime)`, the view, consistency. A sketch (`LocTypeSketch`, removed) proved the reseal at
the lend's entry and that a fresh lend keeps `Mut` values typed. U1 put `LocTy`, `ExtA` and
`erwp_consistent` in the library, with consistency on the exclusive walk (`flat_part_config`
refutes the whole-flattening reading for a part). U2 made `U` Kripke along `ExtA`; `u_not_local`
(`LocalU791.lean`, removed in 55b83e3f, kept at 728b51d7) showed `U` is then not local along a
lend.

**A.6 The resource-relative order** (55b83e3f, 8555ac04, e17cbfa7). `U` and `⊸` along
`LocTy.ExtR`; `vN_extR`, `vN_local` at every former; `withbor2S_compat` rebuilt with the lend at
a fresh lifetime. Core's `Ext` read literally broke `vN_extA` at `U` (`extRL_breaks_extA`), so
`ExtR` asks agreement only above keys present.

**A.7 `w3` and `wF`** (c8d71ac9, 253c4809, e82f27dc, 6b282497). The uniform conjunct in `Mut`,
`withbor2S_compat` taking the lend below the side condition; the guarded tables, the Mut Frame
with its fold, the anti-frame across stops, raises and layered cancel runs; `withbor3S_compat`,
then `withborFS_compat` with the frame at the field.

**A.8 The review fixes** (eb98ef4c, e2a322f2, 19a70fda, 5664e968, 8c391c91). `Mut`'s slack;
`mutSub`, `immSub`, `allI` at `SemJN`; `∀` as Core's `cC`; `Row.Suspend` relative to `@bnd`;
`FundamentalN` on the fragment; the instances and `Const791.OK` inhabited.

**A.9 `withload`: three stops** (bf8a255c, c5dad9d6, e86b3611, d92de340). Core's list-reading
`Imm` is not stable along `extF` (`coreMutImm_not_extF`). No `Imm` clause over `vN`'s arguments
gives step 8 (`not_wlImage`). No agreement read off the unchanged `erwp` does
(`immAgreeErwp_both`, `not_wlImageA`). A tie between world records and the run's list was stated
(`ImmTie791N.lean`), with three placements, each meeting a proved statement; the guard on `cN`'s
run clauses was refuted (`not_effOf_guarded`).

**A.10 The tie in the relation** (2d177c41, 87188302, 05c8995f, d647cf83, a5900e71, a711a05c).
`LocFam`/`LocTy` carry `imm` records; `rwp`/`rwpG`/`rwpG0` take `ImmTieL` at their entry;
`Imm`'s witness `ImmWitW`; the observable view `vO`; 6.150 across raises and layered cancel runs;
`withloadS_compat` and `constN_wl`.

**A.11 The map and the `imm` lend** (411df822, 6ede48eb, e59ff710, 0270b87b, e2ca32a7,
63b3dd7e, 9ba78899). The rule-by-rule map; its configuration for the `imm` lend's step at the old
`above` (`callback_any_inst`) was answered by making `above` Core's `ls₀` with the records, `ExtR`
keep Core's `Keeps`, and `ImmWitW` carry the lifetime match. `withbor1U`, `withbor1`, `withbor2U`,
`withbor2` at `SemJN`. Then the lemma interface for `FundamentalN`.
