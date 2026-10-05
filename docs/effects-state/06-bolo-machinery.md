# 06 — The BoLo machinery we have, and how the effects work uses it

Inventory for #290. It records what is, at `main` = `8a1c326` (the `effects-state` worktree)
unless a branch or commit is named. It proposes nothing.

Conventions:

- `[TR]` is `~/repos/borrow_lang/3764117-supplement.pdf` and `[CONF]` is
  `~/repos/borrow_lang/3764117.pdf`. `[TR]` page numbers are the printed ones, which equal the
  PDF page. `[CONF]` pages are `415:N`.
- `[TR]` numbers Definitions and Lemmas in two sequences. `Paper/INDEX.md` lists every numbered
  result and definition row with its Lean declaration.
- Status words follow the brief: PROVED, REFUTED, PAPER-ONLY, ATTEMPTED-FAILED,
  REJECTED/ABANDONED, OPEN. Each result says which world it lives at.
  - "Core's relation" means `vC`/`cC`/`wpTS`/`ewpTS` (`Core/Relation.lean`, `Core/World.lean`,
    `Core/EffDefs.lean`). The GhostEnd documents call this the empty lend stack, σ = [].
  - "`vRL*`" means a GhostEnd relation family.
  - "EffModelRel" means that sibling calculus.
  - None of these is the planned Kripke world W.

---

## Part 1 — the machinery

### 1.0 Where it lives: three layers, two typed worlds

| layer | contents | role |
|---|---|---|
| `Paper/` | Literal transcriptions of `[TR]` §§1–6 and `[CONF]` §3: rows 1.x–5.x, Lemmas 6.1–6.176, Theorem 3.2 and Corollary 3.3. Each is tagged `[as printed]`, `[repair]`, `[variant]` or `[about ours]`. | The record of the paper. |
| `Support/TypedWorld/` | The *typed world* at BoLo's own types `Ty`: `TW`, `wpTS`, the frame rules, the invariant, the compatibility lemmas `*_compatX`. | `Paper/S6_8_FundamentalProperty/Lemmas.lean:164` (`fundamentalProperty`, 6.151) is proved from these. |
| `Core/` | The same typed world copied "with records typed at `VTy`", the CBPV types. Every Core file heading says so, e.g. `Core/FrameRules.lean:35`, `Core/Invariant.lean:38`, `Core/Wp.lean:34`. Core also holds the CBPV relation `vC`/`cC`, `CDerives`, `fundamentalC`, `adequacyC`, and the effect kernel. | The library. The effect kernel and every effects experiment import this layer, never `Support/TypedWorld`. |

`Support/TypedWorld` and `Core` are two parallel typed worlds. `Core/Embedding.lean` maps
`DerivesWf` into `CDerives` (`Core/README.md`, *Embedding*). No theorem identifies the two
worlds' relations; the README lists "no agreement with the old world" as open.

### 1.1 The resource algebra (`[TR]` §5, pp. 4–6; `[CONF]` Fig. 16–19)

All of it is in `Paper/S5_Model/Definitions.lean`.

| object | `[TR]` | Lean | shape and notes |
|---|---|---|---|
| `Life` | p. 4, row 5.9 | `:104` `abbrev Life := ℕᵒᵈ` | `⊤ = 0`, `⊔ = min`, `⊓ = max`, `⊏ = >`. In Lean, `⊏` is `<` on `ℕᵒᵈ` (`Sqsubset`, `:290`); `⊑` is its reflexive closure (`[repair]`, adjudications §12.3). `↓α ≜ α+1` is `down` (`:363`), and `Life.down_sqsubset : ↓a ⊏ a` is `Paper/S6_2_NonStandardLemmas/Lemmas.lean:602` (6.63). Memory `boca-life-is-nat-dual`: every raw `≤`/`<` at `Life` silently inverts, and `Cell`'s well-founded recursion runs along the paper's `⊏` (`:186–203`). |
| `Cell_α`, `Res_α`, `Imm_α`, `Mut_α` | p. 4, rows 5.1–5.6 | `CellF` `:172`, `Cell` `:186`, `Res` `:191` | Stratified by well-founded recursion on `Life`. |
| `CellU`, `ResU` | — | `CellU` `:239`, `ResU` `:268` | An unstratified presentation, `PMap Loc CellU`. It is proved equivalent to `Res_α` (`Res.stratumEquiv`, `:1054`; `Cell.stratumEquiv`, `:1023`). `Res_α` is `ResU.InStratum α` (`:619`). |
| `@ψ`, `@ρ`, `[α]P`, outlives | p. 5 rows 1–2; p. 6 row 4 | `Outlives := InStratum` `:666`; `box` `:669` | `[repair]` (§C.25). `@ρ ⊐ α` ranges over the borrow cells, so it holds vacuously where there are none, as Wagner confirmed (memory `wagner-confirms-outlives-semantics`). |
| `▸◂`, `▷◁`, `●`, `○` | p. 5 | `CellU.CompatS` `:1132`, `CompS` `:1141`, `CompR` `:1514`; `ResU.CompS` `:1186`, `CompR` `:1595` | `●` is strict composition (`imm ● imm` unions the lifetime sets). `○` is the relaxed composition used in `ag`. |
| `ex(ρ)`, `ag(ρ)`, `⦇ρ⦈`, `✓ρ` | p. 5 rows 10–14 | `ExW`/`ExS` `:939,1190`; `AgW` `:1644`; `ResU.Flat` `:1679`; `ResU.Valid` `:1685` | Flattening is a *relation* (walks), not a function. Memory `flattening-must-be-relational` records this as verified necessary on this carrier. |
| `⟦ρ⟧` (lowering to a heap) | p. 5 row 16 | `ResU.Lower` `:1694` | |
| `ρ₁ # ρ₂` | p. 5 row 17 | `ResU.Hash` `:1701` | |
| `ρ₁ ↭ ρ₂` | p. 5 row 18 | `UpdImm` `:1720`, `UpdMut` `:1726`, `Upd` `:1739`, `UpdV` `:1742` | `[repair]` (§12.39, D3). `imm ⇔ imm` fixes the lifetime set, value and witness. `mut ⇔ mut` fixes only the lifetime and predicate. That asymmetry is `[TR]` Definition 6.2 (`∼`, p. 11). |
| `reb_α(ρ)`, `↺_α P` | p. 5 row 19; p. 6 row 19 | `ResU.RebAt` `:1201`, `ResU.Reb` `:1251`, `reborrow` `:1268` | `[variant]`: the `imm` clause is read at a nonempty subset of the lifetime set (§12.67). |
| `ℓ ↦ v`, `ℓ ↦ Imm α P̂`, `ℓ ↦ Mut α P̂` | p. 6 rows 1–3 | `ptoOwn` `:752`, `ptoImm` `:1330`, `ptoMut` `:1340` | The typed-world forms carrying a record list are `ptoImmS`/`ptoMutS` (`Core/Relation.lean:51,43`). |
| `⋆`, `–⋆`, `!`, `∧`, `∀`, … | p. 6 | `sep` `:1226`, `wand` `:1233`, `bang` `:536`, … | |
| **И** (freshness) | p. 6 row 18 | `fresh` `:678` | `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)`, `[as printed]` (`[TR]`'s row includes `[α]`; `[CONF]` Fig. 19 omits it). |
| `wp(e){Q̂}` | p. 6 row 5 | `wp` `:1759` (guarded `↭`), `wpU` `:1774` (`[CONF]`'s unguarded `↭`) | `∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧, e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)`. The run ends at a **value**. |

The И lemmas are 6.108 `fresh_mono`, 6.109 `fresh_L`, 6.110 `fresh_R` and 6.111 `fresh_sep`
(`Paper/S6_5_NonStandardEntailments/Lemmas.lean:328,356,381,404`), and 6.112 `fresh_frame`
(`Paper/S6_3_FrameAndAntiFrame/Lemmas.lean:48`). 6.112 is the first step of 6.64, 6.65 and
6.150. In the typed world a fresh lifetime is also taken below every tag of the record list:
`exists_fresh` (`Core/Wp.lean:169`) and `strat_fresh` (`:164`).

### 1.2 Resources that arise: the typed world `TW` and its invariant

**Paper basis.** `[TR]` §6 quantifies over resources of the linear calculus, the resources
that arise. Memory `resources-are-of-the-calculus` marks this SETTLED. The prose
`docs/adjudications.md` §12.72 transcribes is:

> [CONF] 415:21: *"Conceptually, in a valid resource, every pair of aliases map to the same
> object and each has an immutable ancestor."* … [CONF] 415:19: *"At the moment the borrow is
> created, there is a particular witness — the value v and a resource ρ′ — for the payload
> predicate P̂(v)(ρ′) … ownership of this witness ρ′ is temporarily moved into the borrow."*

**`TW W ps rs`** (`Core/World.lean:110–165`; Support copy `Support/TypedWorld/`). This is an
inductive family of configurations. `W` is every frame together with the resource a `wp` runs
at, `ρ_f ● ρ`. It is reached from `∅` by the operations the printed proofs perform, one
constructor per operation:

- `alloc` (6.141), `free` (6.142), `store` (6.145);
- `immFrame` / `immEnd` (6.64's entry and exit);
- `mutFold` / `mutUnfold` (6.65 and 6.66);
- `reb` / `rebDeep` / `rebEnd` / `rebEndDeep` (6.150's entry and exit).

`ps` is the list of open 6.64 frames, as records `FrameRec = (le, v, R, T, δ)`
(`Core/FrameRecords.lean:34`). `rs` is the list of those frames' lineages. A 6.65/6.66 lend
leaves no entry in `ps`, because `mutFold`/`mutUnfold` keep `ps rs` unchanged
(`Core/World.lean:135–144`). The typing premises are at `vShape` (`:58`), the wp-free shape of
`𝒱⟦T⟧`. Tag: `[about ours: the configurations §6 quantifies over, as a family; §12.72]`.

**Tags.** `Tagged W ps ls` (`:171`) ties each member of the record list `ls : List SRec` (a
record with a lifetime tag) to an open frame whose lineage holds it.

**The invariant.** `TI W ps rs` (`Core/Invariant.lean:1836`) is the conjunction of:

- `ChainInv` (`Core/Images.lean:1484`);
- `LeInv`;
- uniqueness of the open frames at a location;
- no record's owned cell inside another record;
- `NestLife`;
- `NoMut`;
- `rs` = the lineages of `ps`;
- `Coverage`: every `imm` view in `ag(W)` is classified by a record (`:1832`).

`TW.inv : TW W ps rs → TI W ps rs` (`Core/Invariant.lean:2702`; Support copy
`Support/TypedWorld/Invariant.lean:2655`) is PROVED by induction on `TW`. This is the
"preservation of the invariant by every step" in the file heading (`Core/Invariant.lean:38`).
`TW.valid` (`:1802`): every `TW` world is `✓`.

§12.73 records why the invariant must be historical rather than pointwise. A configuration
(§12.68) is `✓`, and no pointwise condition excludes it. It is excluded only because no `TW`
world holds it (`Fig16.LogRel.ViewWitness.excluded`). This is the mechanised form of memory
`counterexamples-must-arise`: "the excluding property is HISTORICAL, not POINTWISE."

### 1.3 `wp` at the typed world: `wpTS`, `wpG`, `ewpTS`

| object | Lean | shape |
|---|---|---|
| `wpTS ls e Q` | `Core/World.lean:186` | `[TR]` p. 6's `wp` with `∀ρ_f # ρ` restricted to frames completing `ρ` to a tagged `TW fρ ps (rsOf ls)` world. The post-configuration is again `TW`/`Tagged`, with `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)`. The run is an allocator run under every allocator (SPEC §13). Every other conjunct is `Fig16.BoLo.wp`'s, verbatim. `[about ours; §12.72]`. |
| `wpTSAngelic`, `wpTSD` | `Core/World.lean:203`, `Core/Demonic.lean:223` | Some run / every run. |
| `wpG ls e Q` | `Core/EffDefs.lean:27–40` | `wpTS` with the run ending at an arbitrary term `t : Expr` (`:30,36`) and `Q` over terms. It keeps both final conjuncts: `TW fρ'p ps' (rsOf ls')` (`:39`) and `ps' ≡ ps ∧ ls' ≡ ls` (`:40`). `wpTS_iff_wpG` (`Core/EffWp.lean:43`): `wpTS = wpG ∘ valPost`. |
| `ewpTS ls e Π Q` | `Core/EffDefs.lean:68–75` | The least fixed point (written in `Prop`) of `ewpStep Π Q P = wpG (valPost Q ∨ Π · · P)`. `ewp_bot` (`Core/EffWp.lean:772`): at the empty table it is `wpTS`. |

The **lexical stop** the brief names is `Core/EffDefs.lean:39–40`. `wpG` requires every final
term to be a `TW` world with the *same* open 6.64 frames and the same record list as at entry.
A stop at `perform` or `raise` counts as a final term. So a 6.64 frame or 6.150 record opened
inside a run is closed by the time the run stops. A 6.65/6.66 lend has no `ps` entry. It is
closed at the stop by the frame lemma's exit (§1.4), and its box premise `[α]` must hold of
everything else the stop holds. The value-time `wp` carries the same pair of conjuncts at a
return (`Core/World.lean:198–199`). `docs/effects-tr/16-regress.md:26–29` and the audit
(`origin/effects-audit`, `docs/effects-audit.md` §3 item 4, §4.1 C1) both name this clause.

### 1.4 The frame rules: `[TR]` 6.64 Imm Frame, 6.65 Mut Frame, 6.66 Anti Frame (§6.3, pp. 22–27)

Printed statements:

- **6.64 (p. 22):** `ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Imm α P̂ –⋆ wp(e){[α](ℓ ↦ v –⋆ P̂(v) –⋆ Q̂)}) ⊨ wp(e){Q̂}`.
- **6.65 (p. 24):** if `P̂ ⊨ [β]P̂`, then `ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ –⋆ wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}) ⊨ wp(e){Q̂}`.
- **6.66 (p. 25):** `ℓ ↦ Mut α P̂ ⋆ (∀v. ℓ ↦ v –⋆ P̂(v) –⋆ wp(e){∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂)}) ⊨ wp(e){Q̂}`.

| rule | literal (`Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`) | Support typed world | Core typed world (`wpTS`) | Core at `wpG` (any final term) | over `ewpTS`, abortive table |
|---|---|---|---|---|---|
| 6.64 | `wp_I_frame` `:81` | `Support/TypedWorld/FrameRules.lean:58` | `wpTS_I_frameX` `Core/FrameRules.lean:58` | `wpG_I_frameX` `Core/EffWp.lean:75` | `ewpTS_I_frameU` `Core/EffWp.lean:828` |
| 6.65 | `wp_M_frame` `:256` | `:346` | `wpTS_M_frameX` `Core/FrameRules.lean:346` | `wpG_M_frameX` `Core/EffWp.lean:363` | `ewpTS_M_frameU` `:842` |
| 6.66 | `wp_M_antiFrame` `:469` | `:550` | `wpTS_M_antiFrameX` `Core/FrameRules.lean:550` | `wpG_M_antiFrameX` `Core/EffWp.lean:567` | `ewpTS_M_antiFrameU` `:854` |

All entries are PROVED. `Paper/INDEX.md` scores 6.64–6.66 `proved`.

**Typed-world statement shape** (`Core/FrameRules.lean:58`; 6.64 shown):

    ptoOwn l v ⋆ vC true T ls δ v ⋆
      fresh (fun α ρ => ∀ ls', AddAt ls ls' α → (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
        (ptoImmS l α ls' (fun ls₀ => vC true T ls₀ δ) ─⋆
          wpTS ls' e (fun ls'' v' => box α (ptoOwn l v ─⋆ (vC true T ls'' δ v ─⋆ Q ls'' v')))) ρ)
    ⊨ wpTS ls e Q

Its tag is `[variant: P̂ ≔ vC⟦T⟧δ, the record's type; hadm is TW.immFrame's premise; hQ (Q̂
stable along Ext …) is added; the callee is also handed the record its frame made]`. 6.65 adds
the hypothesis `hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β` (the printed `P̂ ⊨ [β]P̂`).

**The `wpG` versions are textual copies.** `diff` of `Core/FrameRules.lean:58–345` against
`Core/EffWp.lean:75–362`, with `wpTS`/`wpG` renamed to one name, shows only the type of `Q`
(`Val` vs `Expr`) and one docstring line differing. 6.65 differs in 8 lines, also renaming and
docstrings. The `EffWp` heading (`:12–15`) says 6.64–6.66 "hold at `wpG` by the proofs of
`Core/FrameRules.lean`, which never inspect the term the run ends at". The `wpTS` forms are not
derived from the `wpG` forms. 6.150 is set up the other way: `wpTS_reborrow` is derived from
`wpG_reborrow` (§1.5).

**What they are for.** These rules are how a borrow is opened and closed in a proof. The
borrow constants' compatibility lemmas use them:

- `withbor1_compatX` uses 6.64 (`Core/Compatibility.lean:973`);
- `withbor2_compatX` uses 6.65 at `↓β` (`:1066`);
- `withbor3_compatX` uses 6.66 then 6.65 (`:1151–1154`);
- `withswap_compatX` uses 6.66 (`:1235`);
- the slice borrows use them through `wpTS_M_frameList`/`wpTS_I_frameList`
  (`Core/SliceFrames.lean`), and the slice writes use 6.66 (`Core/SliceOps.lean:162,345,381,386`).

At the exit of 6.64 a record is ended by `TW.immEnd`; at the exit of 6.65 the cell is unfolded
by `TW.mutUnfold`.

### 1.5 The reborrow rule `[TR]` 6.150 (§6.7, p. 39) and `withload`

Printed: `ℓ ↦ Imm α (Иβ. ↺β P̂) ⋆ (Иβ. ∀v. P̂(v) –⋆ wp(e){[β]Q̂}) ⊨ wp(e){Q̂}`.

| form | Lean | status / tag |
|---|---|---|
| literal | `Fig16.BoLo.wp_reborrow`, `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean:1174` | PROVED*, `[restricted: to RebEscrow P̂ — the two inputs [TR] 6.55 adds]` (§12.61). |
| Core, any final term | `wpG_reborrow`, `Core/Reborrow.lean:232` | PROVED, `[variant: the chooser RebChooseTW in place of RebEscrow; β also below the world's stratum (H11); P̂₀ for the handed image, P̂ for the chosen one; R on the cell's payload]`. Its docstring: "The proof never inspects the term the inner run ends at, so a reborrow ends at a stopped operation as at a return." |
| Core, `wpTS` | `wpTS_reborrow`, `Core/Reborrow.lean:390` | PROVED, derived from `wpG_reborrow` via `wpTS_iff_wpG`. |
| chooser | `RebChooseTW`, `Core/Reborrow.lean:112` | `[about ours]`. A world-relative replacement for `RebEscrow`: given the handed reborrow it chooses `χ ∈ reb_β(ρ′)` with the 6.55 inputs, and types the entry and exit worlds (`TW.reb`/`rebEnd`). |

**Uses.** `withload_compatX` (6.175, `Core/Compatibility.lean:252,328`); `Core/Sized.lean:171`;
`withloadU_compatX` (`Core/EffBorrow.lean:548,600`). The paper's `withload ≜ λx.λf.(x, f (load
x))` is `[TR]` p. 4.

Related reborrow facts: 6.131 `reborrow_vShape` (`Core/ReborrowShapes.lean:47`), 6.132
`six132_shape` (Support), 6.120–6.134 (`Paper/S6_6_ReborrowingEntailments/Lemmas.lean`).

### 1.6 Outlives: 6.60 and SPEC §23

- **Printed (6.60, p. 21):** "If `Δ ⊢ T ⊐ @a`, `δ ∈ ⟦Δ⟧` and `ρ ∈ 𝒱⟦T⟧δ` then `@ρ ⊐ @aδ`", by
  induction on the outlives derivation. Literal: `vDen_outlives`
  (`Paper/S6_2_NonStandardLemmas/Lemmas.lean:3620`), `proved`.
- **Core:** `vC_outlives` (`Core/RelationFacts.lean:479`), both modes, for every list:
  `VOutlives Δ a T → vC b T ls δ v ρ → BoLo.Outlives ρ α`. `vC_outlivesLe` (`:575`) gives
  every stratum strictly below `@bδ` from the non-strict judgment.
- **The judgment:** `VOutlivesR Rb Rr` (`Core/Types.lean:1730`) with the instances
  `VOutlives` (`⊐`) and `VOutlivesLe` (`⊒`).
- **SPEC §23** (Entry 22, `SPEC.md:3463–3606`) relaxes two printed `⊏` premises to `⊑`: the box
  rule of `Δ ⊢ T ⊐ @a`, and `withbor`'s side condition. SPEC frames this as "an **extension** of
  the calculus, read against the model the paper defines … not a correction of the paper, and
  `Paper/` is unchanged."
  - The box modality itself stays strict (`[@x] T ⊐ 'x` holds; `Mut 'x T ⊐ 'x` is refused).
  - The side condition reaches each proof through 6.60 as `𝒱⟦A⟧δ ⊨ [@bδ]𝒱⟦A⟧δ` (6.173), and
    the frame is taken at `↓@bδ`.
  - SPEC §4 (Entry 3) relaxes `FrameLife.2` to non-strict and `TW.reb` to `StratumLe`
    (`Core/World.lean:92`). "No rule in Core uses the slack yet" (`Core/README.md`, Decisions
    taken 1).
- **What it is for.** It puts a payload or result in a stratum below which the frame's fresh
  lifetime is taken: 6.65's `P̂ ⊨ [β]P̂`, and 6.64's `[α]` exit box.

### 1.7 The relation, the Fundamental Property, adequacy, preservation, leak freedom

- **Relation.** `vCE`/`cC`/`cB` (`Core/Relation.lean:119,154,192`) form one `mutual` block.
  - `U` is Kripke over `Ext` (the record-list order, `Core/FrameRecords.lean:172`).
  - `F` is `wpTS`.
  - `Imm` uses `ptoImmS` with the coherence `CohE`, and `Mut` uses `ptoMutS`.
  - `F_Σ` (`.eff`) is `ewpTS … (opTable …) (effRet …)` (`:166–169`). So the effect kernel is
    inside Core's `cC`, not beside it.
  - `SemC` holds at every record list (`:228`).
  - The printed `𝒱⟦−⟧` is `[TR]` p. 4. Its repairs are §12.69–§12.72.
- **Fundamental Property.**
  - `[TR]` 6.151 (p. 40) / `[CONF]` Lemma 3.1 (415:17): "If `Δ; Γ ⊢ e : T` then `Δ; Γ ⊨ e : T`."
  - Paper/Support: `fundamentalProperty` (`Paper/S6_8_FundamentalProperty/Lemmas.lean:164`),
    `variant`: at `SemX`, with `Δ.Ok` and `Ctx.ScopedB` as hypotheses (§C.26), and no other.
  - Core: `fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j` (`Core/Fundamental.lean:434`), by
    induction over every constructor. The effect cases are `effSub`, `effPerform`, `effRaise`,
    `effLet`, `effThen`, `effHandle`, and the six `*U` borrow constants (`:509–524`).
    `fundamentalD` (`Core/Demonic.lean:284`) is the same at `wpTSD`.
- **Adequacy.**
  - `[CONF]` Theorem 3.2 / Corollary 3.3 (415:18): "If `⊨ e : 1` then `(∅, e) →* (∅, ())`."
  - Literal: `Paper/CONF/Results.lean:171,279`.
  - Core: `theorem32` (`Core/Fundamental.lean:558`, at `wpTS []`), `corollary33` (`:577`),
    `adequacyC` (`:590`). `adequacyD`/`adequacyD_safe`/`adequacyD_val`
    (`Core/Demonic.lean:312,325,334`) cover every run.
- **Leak freedom.** There is no separate theorem. It is adequacy's conclusion that the final
  memory is empty. The step is `reclaim` (`Core/Fundamental.lean:534`; `Paper/CONF/Results.lean:111`):
  `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅`.
- **Preservation.** There is no syntactic subject-reduction theorem. Preservation in this
  development means:
  - semantic preservation through `wp`: the post-configuration of every `wpTS`/`wpG` run is
    again a tagged `TW` world;
  - `TW.inv`, the invariant of every reachable world (§1.2).

  `docs/effects-calculus/99-open-questions.md` on `effects-calculus-spec` also records "No
  syntactic preservation theorem exists to carry typing along a run (07 §6, T-PRES)".

### 1.8 Methodological lessons that apply to effects work

From `~/repos/borrow_lang/CLAUDE.md` and the user's memory files. Each is quoted or closely
paraphrased, with the file named.

1. **Follow the printed proof; never take a shorter route** (CLAUDE.md §1;
   `shortcuts-cost-the-technique`). "A printed proof is not stand-alone. It is where a technique
   gets built, and later proofs reach for that technique." `[as printed]` scores the statement,
   not the proof. For effects this bears on every place where a frame or reborrow is re-proved
   at a new `wp` (`wpG_*X`, the `*U` compat lemmas, GhostEnd's `*R` rules): whether the printed
   route was followed.
2. **The paper is not wrong** (CLAUDE.md §2; `the-paper-is-not-wrong`). "Never report that a
   printed lemma is false, unsound, un-derivable, or a gap … The base rate is zero." "Say
   'cannot reconcile', name the exact printed step, and go looking for our mistake."
3. **Check the objects are transcribed before inventing a route** (CLAUDE.md §3;
   `do-not-reconstruct-a-printed-route`, `gaps-are-untranscribed-chunks`). Watch the two
   numbering sequences: Definition 6.2 (`∼`, p. 11) was missed for that reason. 6.40 is still
   `untranscribed` (`Paper/INDEX.md`).
4. **Add hypotheses; never edit printed statements or definitions** (CLAUDE.md §4). The memory
   `the-frame-narrowing-was-the-misstatement` records what editing `wp`'s frame quantifier cost:
   "That is an edit to a printed definition — the thing this project forbids", and it was
   unsound at an arising resource. The lexical stop (§1.3) is a conjunct of *our* `wpTS`/`wpG`,
   tagged `[about ours]`. It is not a printed row.
5. **A blocker is a claim** (CLAUDE.md §5; `blockers-must-be-machine-checked`). Report an
   obstruction only as an elaborating `def … : Prop` or a fully discharged Lean configuration.
   "Every report lists: unspent printed hypotheses; unused uniqueness/functionality results; and
   which printed lemmas in the run-up are untranscribed."
6. **Do not split cases the paper does not split** (CLAUDE.md §6). "If the printed step is one
   sentence and the mechanisation is a case tree, the case tree is probably ours."
7. **Resources are of the calculus; counterexamples must arise** (`resources-are-of-the-calculus`,
   `counterexamples-must-arise`, `stop-manufacturing-refutations`). "When a printed lemma seems
   to admit a bad resource, the first question is whether that resource arises — not which
   hypothesis to strengthen." The excluding property is "HISTORICAL, not POINTWISE … EVERY
   pointwise predicate fails `⋆`-closure."
8. **Arising tests are directional** (`arising-tests-are-directional`). "An over-approximate
   arising test is **sound for proving** a lemma … and **unsound for refuting** one." `TW` is the
   arising test of the typed world. GhostEnd's `TabAtS` guard (Part 2) is a second one, and no
   lemma relates the two.
9. **Attack the global invariant** (`attack-the-global-invariant`). "When a pointwise obligation
   will not close, … build the **global invariant** … it may already exist under a name that
   hides it."
10. **State goals through proved equivalences** (`state-goals-through-proved-equivalences`). "A
    target that keeps shifting under attack is evidence the target is wrong."
11. **Novelty is not evidence** (`novelty-is-not-evidence`). "Everything is new the first time
    you see it."
12. **CoherentX is dead** (`coherentx-is-the-faithful-invariant`, retracted by the owner
    2026-09-16: "we're not going back to CoherentX, that was a patch to work around dropping
    linearity"). This applies to any new pointwise "arising" predicate an effects relation
    introduces.
13. **Current state is not design** (`current-state-is-not-design`, user 2026-09-30: "just
    because we have done something a certain way, that does not mean it was the result of a
    careful design decision, or that it is locked in"). The lexical stop and `Row.Unwind` are
    current state.

---

## Part 2 — how the effects work uses the machinery

There are three verbs:

- **uses as printed:** invokes the existing Core/Support/Paper declaration;
- **re-derives:** builds a parallel relation, world, or twin rule beside the existing one;
- **bypasses:** reaches the same end by a mechanism other than the printed rule.

Where something does not reconcile, the entry names what our side lacks.

### 2.1 The effect kernel (`Core/EffDefs.lean`, `EffWp.lean`, `EffRules.lean`, `EffBorrow.lean`, `EffCancel.lean`, `EffPrograms.lean`, `EffExamples.lean`; SPEC §19)

**Uses as printed.**

- **The typed world.**
  - `wpG` is `wpTS` with the final term generalised. It quantifies over the same tagged `TW`
    frames and requires a tagged `TW` post-world (`Core/EffDefs.lean:27–40`).
  - `ewpTS` unfolds only through `wpG` (`:68–75`).
  - No effect file adds a `TW` constructor or a world component.
- **Inside the relation.** `cC`'s `F_Σ` clause is `ewpTS` (`Core/Relation.lean:166–169`). Two
  things are Kripke over `Ext`, as `vC`'s `U` clause is (§12.72):
  - the continuation's share, `contShare` (`Core/EffDefs.lean:144–149`);
  - `κ`'s relation, `KapRel` (`Core/EffRules.lean:569`).
- **6.64–6.66.** Through the `wpG` copies (§1.4): `wpG_I_frameX`, `wpG_M_frameX`,
  `wpG_M_antiFrameX`. These are lifted to an abortive table as `ewpTS_I_frameU`,
  `ewpTS_M_frameU`, `ewpTS_M_antiFrameU` (`Core/EffWp.lean:828,842,854`), each by
  `ewp_abortive` (`:811`: at an abortive table `ewpTS` is `wpG` once).
  - `withbor1U_compatX` uses 6.64 (`Core/EffBorrow.lean:446`).
  - `withbor2U_compatX` uses 6.65 (`:275`).
  - `withbor3U_compatX` uses 6.66 then `wpG_M_frameX` (`:356,397`).
  - The slice borrows use `wpG_M_frameX`/`wpG_I_frameX` per leaf (`Core/SliceFrames.lean:188,351`).
- **6.150.** `withloadU_compatX` (`Core/EffBorrow.lean:548`) calls `wpG_reborrow`
  (`Core/Reborrow.lean:232`) at `:600`.
- **6.60.** `vC_outlives`/`vC_outlivesLe` place a callback's answer and the operation arguments
  in the frame's stratum. `Row.Unwind` (`Core/EffBorrow.lean:133`) asks every operation
  argument type to be "free of `'x` and outliving every lifetime" (`VOutlives Δ a o.A` for every
  `Δ a`). `ewp_box_end` (`:118`) turns that into `[α]` at every end of the callback.
- **6.112.** `fresh_frame`, inside the `wpG` frame copies.
- **The Fundamental Property and adequacy.** `fundamentalC` has one case per effect rule and
  per `*U` constant (`Core/Fundamental.lean:509–524`). `adequacyD` runs the effect programs
  (`Core/EffPrograms.lean`, 14 call sites; `Core/EffExamples.lean`, 3).

**Re-derives.**

- **Frame-rule copies at `wpG`.** `Core/EffWp.lean:75–725` copies `Core/FrameRules.lean`
  line for line (§1.4). The printed route is followed. Nothing is re-proved differently, but
  there are two copies of each proof.
- **`*U` twin constants.** There are 7 pure borrow constants (`withbor1`–`3`, `withload`,
  `withswap`, `sliceBorrowM`, `sliceBorrowI`). Six have an unwinding twin: `withbor1U`,
  `withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU`
  (`Core/EffBorrow.lean:177–200,525,625–630`; `CDerives` cases at `Core/Fundamental.lean:509–520`).
  - Each twin's compat lemma re-runs the pure constant's printed proof (6.172–6.175) at
    `ewpTS`. Each docstring says so, e.g. "`[TR]` 6.173's proof (`withbor2_compatX`), with the
    frame over `ewpTS`" (`:269–274`).
  - None is derived from its pure twin.
  - `withswap` has no twin: "its callback takes the payload by value, and an unwind would
    abandon it" (SPEC §19, `SPEC.md:2628–2629`).
  - The twin's term is `withborUE d = λr. λf. (f [] r) then b. (r, b) unwind d r`. The
    finaliser `d` is a premise (`SPEC.md:2618–2623`).
- **`wpG_garbage`** (`Core/EffWp.lean:730`) is ours: a `NoOwn` part of the final resource may
  join `ρ⁺`. "This is what an unwind does to the continuation it abandons." No printed row
  corresponds to it. It uses only `wp`'s own `ρ⁺∣own = ∅` conjunct.

**Bypasses.**

- **No printed rule is bypassed.** An unwind ends a lend "exactly as at a return: 6.64's
  `immEnd`, and 6.65/6.66's unfold of the `mut` cell" (`SPEC.md:2754–2756`). That is the same
  `wpG_*X` exit.
- **What the kernel does not have is a lend open at a stop.**
  - The lexical stop (`Core/EffDefs.lean:39–40`, §1.3) closes every 6.64 frame and 6.150 record
    by the stop.
  - A 6.65 frame's `[α]` exit box excludes a continuation share that still holds the lend.
  - The typing side matches this. A borrow callback's row must be `Row.Unwind`: abortive, named,
    and with closed-data arguments. SPEC §19: "Non-abortive control operations stay inside a
    borrow's scope: every borrow callback's row is unwind-only" (`SPEC.md:2615–2616`).
  - "A non-abortive control operation crossing a borrow's scope (T1, #172)" is listed as Open
    (`SPEC.md:2966`).
- **Handlers open no lifetime.** `handle_compatC` (`Core/EffRules.lean:1092`) and `ewp_handle`
  (`:615`) take no `∀'h`. GhostEnd's README (`:112–116`) says the extent "the kernel does not
  establish … today, because handlers open no lifetime."

**What does not reconcile, and what our side lacks.**

- `TW`'s `ps` is already a stack of open 6.64 frames. `wpG` requires it unchanged at a stop, and
  a 6.65 lend has no entry in it (`Core/World.lean:135–144`). Our side lacks any world component
  that records a lend open at a stop. This is the audit's C1 (`origin/effects-audit`,
  `docs/effects-audit.md` §4.1) and OQ-44 on `effects-calculus-spec`.
- `Core/Handlers.lean:5–35` still describes "a handler is defined by its elaboration into core
  terms (SPEC §18, decision 48)". Decision 48 is superseded by memory `effects-are-core`
  (2026-09-30), and the audit (§3 item 3) calls the file "the withdrawn decision-52 sum
  encoding".

### 2.2 GhostEnd (`experiments/GhostEnd`, main; branches `gfp` @ `daf56c0`, `gfp-arising` @ `d31cbb3`, `borrow-callbacks` @ `5cfe062`)

These three are the only branches that touch GhostEnd. `effect-callbacks`, `loophandle` and
`lift-stage1` do not (checked with `git log main..HEAD` in each worktree). GhostEnd imports
`Core.*` and Restrat, never `Paper/` or `Support/TypedWorld/`. There is no `sorry` or `axiom`
on main or `5cfe062`.

**Uses as printed.**

- **6.64–6.66 in their `wpG` forms only.** The `wpTS_*X` forms have zero call sites.
  - 6.65 `wpG_M_frameX`: `Relend.lean:128`, `Nested.lean:187,376`.
  - 6.64 `wpG_I_frameX`: `ImmLend.lean:188`, `StackStep.lean:969`.
  - 6.66 `wpG_M_antiFrameX`: `Frames.lean:97`, `Nested.lean:182`, `StackStep.lean:611`.
- **`fundamentalC`.**
  - `Segment.lean:36`, `Program.lean:204`, `Closures.lean:121–154`, `Callee.lean:164,165,232`.
  - `Stacked.lean:613` (`gfpAt_nil : GFPAt [] := … fundamentalC h`).
  - `Arising.lean:374` @`d31cbb3`.
  - `adequacyC` is not used.
- **Core's relation and handler rule.** `withbor_spans_yields_cC` (`Program.lean:188`)
  concludes in Core's `cC (CTy.effOf S (Ref T ⊗ B))`. `handle_spans_yields` (`Handle.lean:72`)
  hands the body to `handle_compatC`.
- **6.60.** `vC_outlives` (`Values.lean:154`, `TypedD.lean:89`, `Typed.lean:336`,
  `ClosureBody.lean:170`), `vC_outlivesLe` (`Payload.lean:55`, `Handle.lean:66`,
  `Drop.lean:273`), and `gSepC_outlives` (`Chain.lean:107`).
- **6.50.** `updV_outlives` inside `wpG_tabAt` (`Table.lean:87`).
- **6.150 is not used.** `wpG_reborrow` appears only in comments (`Frames.lean:9`). README:
  "6.150 (↺): its added step (`ptoImm_dup`) is proved; the lift is not written" (`:810`).
- **`TW` and `Core/Invariant.lean`** are never used as a constraint. `TW` appears only in:
  - `tw_heap_any` and `record_shape_thunk` (`Bridge.lean:101,105`), which show that `TW` heap
    cells are untyped and records are `True` at `U`;
  - `tw_innerView` (`Below.lean:120` @`daf56c0`), which builds the refutation's world.

**Re-derives.**

- **Twin frame rules at resuming tables.** Each is proved by induction on its own least fixed
  point, with the printed `wpG_*X` at every unfolding:
  - 6.65: `ewpTS_M_frameR` (`Relend.lean:117`, over `Relend` `:57`);
  - 6.64: `ewpTS_I_frameR` (`ImmLend.lean:175`);
  - 6.66: `ewpTS_M_antiFrameR` (`Frames.lean:89`);
  - unwinding 6.65 with affine resumption: `withborR_compat` (`Drop.lean:108`, over
    `opTableO` `:49`), which reuses Core's `withborUE`.

  README: "This is 6.65's proof as printed, applied once per resumption" (`:126–127`).
  - `O151AsStated` (`Open.lean:76`), 6.65 directly over `ewpTS` at a resuming table, is OPEN.
- **Borrower-piece fixed points.** `Relend`, `Open`/`bodyAt`, `OpenD`/`bodyAtD`/`stopAtD`,
  `NestRelend(₂)`, `CloL`, `KapRelR`, `RBody*`, `TV`/`TVG`. All are stated over Core's `wpG`,
  `ewpTS`, `vC` and `Ext`. None defines a world.
- **Five parallel relation families beside `vC`/`cC`:**

| family | where | index | bridge to `vC`/`cC` |
|---|---|---|---|
| `vRL`/`cRL` | `Bridge.lean:215–241` | one lend `(S, x, T, δ, ℓ)` at one `α` | none. README: "a thunk that stops at `S` is in `vRL (U (F 1))` and not in `vC (U (F 1))`". It fails under an inner borrow (`thunkF_RL_fails_below`, `RLCompat.lean:435`). Verdict: "no-go for `vRL`/`cRL` as merged" (`README.md:507`). |
| `vRLg`/`cRLg` | `RLCompat.lean:505–529` | as `vRL`, `U` re-lend guarded by `TabAt` | none |
| `vRLs`/`cRLs`/`effRetS` (D16.1) | `Stacked.lean:237`ff | lend stack `σ : LStack` (`:107`) as a fixed parameter, lifetime vector `αs` | at σ = [] only: `vRLs_nil` (`:501`), `cRLs_nil`, `gfpAt_nil_iff`, `gfpAt_nil` (`:613`) |
| `vRLa`/`cRLa`/`effRetA` | `Arising.lean:171–212` @`d31cbb3` | D16.1 with `guardS σ αs P := TabAtS σ αs → P` at `U`, `⊸` and `∀` | at σ = [] only (`vRLa_nil` `:260` … `gfpAtA_nil` `:374`) |
| `vRLk`/`cRLk`/`effRetK` | `Extend.lean:59–107` @`5cfe062` | `∀` clause quantifies over stack extensions `τ ++ σ` | none, and no `_nil` lemma |

- **Its own invariant, the table.** `TabAt l α ρ` (`Table.lean:39`): every borrow cell is
  `⊒ α`, and every cell off `ℓ` is strictly above `α`. It is preserved by every run:
  `wpG_tabAt` (`:87`) and `wpTS_tabAt` (`:97`), from 6.50. The stack form is `TabAtS`
  (`Stacked.lean:290`).

**Bypasses, and how the ghost end relates to the printed rules.**

- **The ghost end is 6.65's exit run at a stop, then 6.65's entry at the resume.** It is not a
  third rule.
  - `freeze_at` (`Freeze.lean:50–55`): `ptoMutS l α ls P ⋆ Φ ls t ⊨ wpG ls t Φ`. It drops the
    borrower's view, a `NoOwn` single `mut` cell (`noOwn_ptoMutS`, `:42`), into `ρ⁺` through
    `wpG_garbage`.
  - README (`:86–93`): `wpG_M_frameX`'s exit "moves the cell `ℓ ↦ mut(α, v″, χ, P̂)` out of `ρ⁺`
    into `ℓ ↦ own(v″) ● χ` (6.27); it keeps `↭` from the start (6.28); it keeps the memories
    (6.25 under 6.8)."
  - The admissibility condition: "at the stop, the borrower's share less its view lies in `[α]`.
    A return meets it by typing (`[@x] B`). A stop has to meet it by the outlives premise"
    (`:103–105`).
  - `Imm`: the ghost end is set subtraction and resume is union (`imm_ghostEnd_split`,
    `imm_relend_union`, `ImmLend.lean:50,70`).
- **What is bypassed is the printed shape "one lend for the whole run of `e`".** Each stop ends
  every internal lend, and each resume opens a fresh one at a new `α′`. "Nothing of the earlier
  lend survives the stop" (`:127–128`). It is chosen instead of:
  - naturality (Restrat, `mut_not_natural`/`not_vDenNatural`);
  - refolding at the old lifetime (LoopBorrow's `refoldKripke_false`, cited at
    `README.md:184–187`, `Nested.lean:29`).
- **The relation families exist to re-read, at the fresh lifetime, everything that holds the
  lend across the stop.** GhostEnd works inside the lexical stop and does not change
  `wpG`/`ewpTS`.
- **Arising: GhostEnd's guard, not `TW`'s.**
  - `TW` does not exclude the GFP counterexample. `tw_innerView` builds the inner view
    `k ↦ M_3` as a `TW … [] []` world from `TW.alloc` then `TW.mutFold` (`Below.lean:120`
    @`daf56c0`), and the refutation runs from it.
  - The arising guard of PR #285 (open, created 2026-10-03, branch `gfp-arising`) is
    `guardS`/`TabAtS`, justified by:
    - `wpG_tabAtS_one` (`Arising.lean:112`), from 6.50;
    - `tabAtS_start_one` (`:120`);
    - `tabAtS_comp` (`:83`);
    - `not_tabAtS_innerView` (`:130`);
    - `wpG_below_not_arises` (`:139`).
  - `Core/Invariant.lean`'s `TI` is structural over `TW`'s constructors. `TabAtS` is a
    lifetime-stratum condition relative to the lend stack. No lemma relates the two.
  - `TabAtS` is proved preserved only at a one-entry stack (`wpG_tabAtS_one`).
  - By the directional rule of §1.8 item 8, `TabAtS` is a second arising test whose agreement
    with `TW` is not established.

**Status and worlds.**

- **PROVED at Core's relation (σ = []):**
  - `withbor_spans_yields_cC`, `handle_spans_yields`, `spans_two_yields`, `loop_spans_yields`;
  - `withborR_spans_yields_cC` (`Drop.lean:195`), `handleR_spans_yields`, `callee_spans_yields`;
  - `imm_spans_yield`, `nested_spans_yield`, `nested₂_spans_yield`;
  - `withbor_reborrow_spans_yield` (`Stacked.lean:1093`);
  - the stacked lemmas `stack_step_other`/`_reborrow`/`_imm` (`StackStep.lean:392,563,1003`).
    These are stated over `OpenS`/`bodyS` and fold to `ewpTS` at [] (`openS_nil_ewp`, `:1112`).
- **PROVED at a `vRL*` relation:** `gfpAt_nil` (σ = [] only); `lam_RLa`, `allI_RLa`,
  `arr_elimA`, `all_elimA` @`d31cbb3`; `callback_ext`, `callback_ext_one`, `all_elimK`
  @`5cfe062`.
- **OPEN (named `Prop`s, not derived):** `GFP`/`GFPAt` (`Stacked.lean:305,312`), `GFPA`/`GFPAtA`
  at σ ≠ [], `RelendOfTyped` (`Open.lean:45`), `O151AsStated` (`:76`), `RBodyOfTyped`,
  `RBodyTOfTyped`, `KernelInvariant` (`Kernel.lean:47`), `URelend` (`Bridge.lean:133`).
- **REFUTED @`daf56c0`:** `not_gfpAt_below : ¬ GFPAt [e₀]` and `not_gfp : ¬ GFP`
  (`Below.lean:196,282`). The term is a closed `CDerives` derivation (`allBelow_derives`, `:162`).
  - The witness argument is a `TW` world (`tw_innerView`), so it arises in `TW`'s sense.
  - PR #285 (open) argues it does not arise at `[x]` under `TabAtS` (`wpG_below_not_arises`).
  - The file itself says what it measures: "D16.1 reads that value at `σ`, with `'y` a plain
    variable, and never at `σ·y`: no clause of D16.1 extends the stack" (`Below.lean:32–36`).
- **The README's verdict at 3j:** "Repairing GFP needs a construct the list does not contain: a
  reading of values at an extended stack in D16.1's `U`, `∀` or `⊸` clause, or borrow rules whose
  callback is a premise (a `CDerives` change)". #279 is under the user's tier-2 hard stop
  (2026-10-02): "If its run reports a new unknown … **tier 2 halts** and the language ships at
  tier 1 (T1 kept)."

**What our side lacks.**

- A future-world quantifier over the stack component at `U` and `⊸`. Only `∀` is extended
  (`Extend.lean`); `docs/effects-tr/17-borrow-callbacks.md:28–31` @`5cfe062`.
- Kripke monotonicity for `gRL*`.
- A lemma relating `TabAtS` to `TW`/`TI`.
- A handler extent `'h` in `[handle]`.
- 6.150 lifted to a resuming table.

### 2.3 Restrat (`experiments/Restrat`)

- **Uses as printed.** `restrat_segment` takes `Core.SemC` and yields `Core.cC` at the shifted
  `δ` (`Restrat/Segment.lean:73–82`). It also uses `vDen_all_iff` (`:36`).
- **Re-derives.**
  - A re-stratification action `Emb` (`Injection.lean:31`) and `relU`/`relRU`
    (`Carrier.lean:132,138`).
  - Naturality `Agree` for every connective, including `ptoMut` (`Propositions.lean:234`),
    `reb` (`Reborrow.lean:174`) and И (`fresh_bwd`/`fresh_fwd`, `Propositions.lean:260,268`).
  - A `run_meta` audit (`Audit.lean:121`) checking that no definition of the relation, model,
    typed world or Core computes a lifetime.
- **Bypasses.** Nothing printed. It asks whether a whole computation can be moved to another
  stratum, as an alternative to ending lends.
- **Status.**
  - `not_vDenNatural` (`Open.lean:30`) is REFUTED at `Mut 'a (Imm 'b 1)`. README: "Whether `ρ₀`
    arises at a run is not checked. The refutation is of naturality stated over all resources"
    (`README.md:96–97`).
  - `WpNatural` (`Open.lean:37`) is OPEN: "I have not derived `WpNatural`, and I have not
    verified that any obstruction to it is real."
- GhostEnd imports `Restrat.MutCounterexample`/`Restrat.Reborrow` (`GhostEnd/Witness.lean:1–2`).

### 2.4 EffModel and EffModelRel (sibling calculi)

- **EffModel** (phase A of #235) is a standalone executable model: no Mathlib and no Core
  import.
  - Its `lend c x M` (`EffModel/Syntax.lean:184–185`) runs `M` against a comodel. There is no
    lifetime, resource or frame rule.
  - T1 is a syntactic `susp` bound check (`EffModel/Typing.lean:485–496`).
  - Laws are `#guard`s.
  - **It bypasses every BoLo notion.**
- **EffModelRel** (phase B). README: "Standalone: no Mathlib, imported by nothing" (`:7`).
  - **Uses as printed:** nothing.
  - **Re-derives:**
    - its own world `EffRel.W`, a partial bijection of names with states (`World.lean`);
    - a binary relation with `fundamental` (`Fundamental.lean:278`) and `soundness`
      (`Adequacy.lean:258`);
    - a unary token algebra `Own := Kind → Nat → Nat` (`Own.lean:37`);
    - a cell model `EffCell` whose places are stratified by a `Nat` level standing in for
      `Mut_α`, with an invariant `VSt` (`Cell.lean:293`);
    - lends as reservation tokens (`Inv.lend`/`Inv.reclaim`, `Cell.lean:667,678`).
  - **Bypasses:** lends end by token bookkeeping, not by 6.64–6.66 or 6.150. Freshness is name
    allocation, not И. Arising is its own `Inv`, not `TW`.
  - **Bridge to Core: none.** `docs/effect-model.md` §8.7 (`:735–785`) proposes T16, "Port
    §8.2's worlds onto Core's typed worlds", which is not built. §9.4 (`:960–975`) says
    `relabel_reb`, `relabel_obs` and `ResU.Reb` were "Read and not reused … All three live on
    BoLo's carrier (`ResU`), which none of the models here use".
  - **World.** Results here are at EffModelRel's own world, not at Core's relation and not at W.
  - **Lacks:** any map from `EffCell` tokens/levels into `ResU`/`Res_α`, and a binary relation
    on Core.

### 2.5 The handler spikes and the coeffect experiments

| experiment | uses as printed | re-derives | bypasses | world |
|---|---|---|---|---|
| HandlersAsBorrows (#184) | Paper layer: `effect_safety = Fig16.LogRel.Typed.adequacy _ (d_prog h)` (`Safety.lean:55–57`); `effect_safety_open` from `fundamentalProperty` at `SemX` (`:71–74`); `withbor2Ax` | a source fragment and its translation `translate_typed` (`Translate.lean:190`); no relation, world or frame rule | none. README §7: "No printed definition or statement was edited. `DerivesWf`, the FP and adequacy are used exactly as the library states them" | `Support/TypedWorld` (`SemX`), angelic adequacy only |
| HandlersControl (#185) | Paper adequacy for every program (`Behind.lean:199`, `Reentry.lean:271`, `Outlives.lean:138`, `Capture.lean:229,277,334`); 6.64, 6.60 and 6.62 cited in prose only | inversion lemmas over `DerivesWf` (`no_uniform_comp`, `not_borrowSpansForward`, `lam_bang_persistent`) | state behind control by explicit requests at bounded depth | `Support/TypedWorld` |
| SecondClass | `fundamentalC` (`RecLog.lean:147–149`, `AbortClause.lean:101–111`); `handle_compatC` (`Prompts.lean:75–82`); `boundedFix_compatX` | nothing | prompt freshness is static (`n ∉ Σ`), the kernel's own `hnS`, not И | Core |
| Coeffects | `fundamentalC` (`Judgment.lean:72–75`); `io_every_run`; `withbor` 2 and 3; reborrow as contraction | an elaboration layer `KDem` into `CDerives` | none: "There is no new rule, no new index on CDerives, and no new semantic case" | Core |
| CoeffectsStrict | `CDerives` rules and `vCE` clauses (`Context.lean:70–126`) | run-level laws (`fold_unique`, `handle_unique`, …) as `PureSteps`/`Evals` | the handler as `foldOwn` of a free model, predating `ewpTS` | runs, not the relation |

SPEC §19's Motivation names #184 and #185 as the spikes behind the kernel (`SPEC.md:2274–2285`).
`Core/Handlers.lean` (`:11`) mirrors `experiments/CoeffectsStrict`'s `Handler.lean`.

### 2.6 Borrow-only experiments the effects work leans on

| experiment | uses as printed | re-derives / bypasses | status |
|---|---|---|---|
| LoopBorrow (T1, #172) | `fundamentalC` + `theorem32D` (`Instances.lean`); `TW.immFrame`, `TW.mutFold`/`mutUnfold` | `wpTS_M_refold` (`Refold.lean:100`): 6.65's fold–run–unfold re-proved inline at Core's `TW` with the rest in `Res_{↓α}`, not via `wpTS_M_frameX`; `six27_down` (`:37`) | PROVED obstructions: `not_upd_of_new_mut`/`_ended_mut`/`_new_imm` (`Obstruction.lean:49,60,71`); `refoldKripke_false` (`:245`), at a consumer frame that arises (`refold_fails_at_consumer_frame`, `Dormant.lean:261`); `not_markerInstallable` (`:182`). README: "A lend that spans observations does not close in this model … needs a model change: a borrow that `↭` lets outlive the run that opens it. That change is not verified sound, and nothing here shows the spanning lend unsound." |
| FrameEnd | `Paper/` and `Support/Model/*` only | a full fork of the typed world: own `TW` (`World.lean:74`) with a changed `immEnd` (`:115`), own `wpTS`, twin 6.64–6.66 (`FrameRules.lean:109,399,603`), twin `TW.inv`, own `fundamentalProperty`/`adequacy`; no bridge | `frame_image_empty` (`:68`): "The subtraction removes nothing at 6.64's end". Not landed. |
| FrameTheorems / TwoRun | Core `wpTS`/`TW`/`Tagged`; `fundamentalC`; `TW.mutFold` (`Callback.lean:290`) | heap-level `Footprint` read off `wpTS` | `wpTS_footprint` PROVED; `EveryRunFootprint` refuted in TwoRun (`not_everyRunFootprint`, `Refute.lean:133`); `ReadFootprintTyped` OPEN |
| Outlives (landed as SPEC §23, built at `b1cde24`) | `fundamentalC`, `wpTS_M_frameX` at `↓β` (`Compat.lean:111`) | sibling judgment `LDerives` with `fundamentalL`/`adequacyL`; twin 6.60 lemmas | `not_vC_outlives_le` (`Obstructions.lean:88`): 6.60 fails with the `Mut` rule at `⊑` |
| Shifts | paper `Ty`, axiom types by `rfl` | — | `withborMI` OPEN: "`wpTS_I_frameX` takes `hQ` … The postcondition the anti-frame supplies contains `ptoMutS` … not stable along arbitrary `Ext`. I have not derived `withborMI_compat`." |
| BorrowedClosures | 6.123, 6.61 (`Reborrow.lean:43,99`); now `Support/Model/Unr.lean` | — | PROVED |

---

## Part 3 — summary table

The "experiments" column names GhostEnd (GE), Restrat (RS), EffModelRel (EMR), LoopBorrow (LB),
FrameEnd (FE) and the handler spikes (HAB/HC). U = uses as printed, R = re-derives,
B = bypasses, — = not involved.

| machinery item | paper ref | Lean (Core unless noted) | effect kernel | experiments |
|---|---|---|---|---|
| `Life = ℕᵒᵈ`, `↓α` | `[TR]` p. 4 row 5.9; 6.63 p. 22 | `Paper/S5_Model/Definitions.lean:104,363`; `Paper/S6_2…:602` | U (via `wpG` frames, `exists_fresh`) | GE U; RS R (`Emb` moves strata); EMR B (`Nat` levels) |
| resource algebra, `●`/`○`, `⦇ρ⦈`, `✓`, `#` | p. 5 | `Paper/S5_Model/Definitions.lean:1132–1701` | U (inside `wpG`) | GE U; RS U (naturality per connective); EMR B (`Own`, `EffCell` tokens) |
| `↭` (`UpdV`) | p. 5 row 18; Def. 6.2 p. 11 | `:1720–1742` | U (`wpG`'s conjunct) | GE U (6.50 in `wpG_tabAt`); LB U (obstructions read `↭`); FE R |
| `[α]`, outlives `@ρ ⊐ α` | p. 6 row 4; p. 5 | `Outlives` `:666`, `box` `:669` | U (`ewp_box_end`) | GE U (admissibility of the freeze) |
| И freshness | p. 6 row 18; 6.108–6.112 pp. 29–31, 22 | `fresh` `:678`; `fresh_frame` `Paper/S6_3…:48`; `exists_fresh` `Core/Wp.lean:169` | U (in the frame copies) | GE U (each re-lend chooses a fresh `α` by 6.65's H4); RS R (`fresh_bwd`/`fwd`); EMR B; SecondClass B (static name freshness) |
| `TW` (resources that arise) | §6 ambient; `[CONF]` 415:19, 415:21; adjudications §12.72 | `Core/World.lean:110` | U (`wpG` quantifies over it; no new constructor) | GE U only inside `wpG`, never as a constraint; refutation's world built in it (`tw_innerView`); FE R (fork); EMR B |
| `TI`, `TW.inv` | §12.73 | `Core/Invariant.lean:1836,2702` | U (through `wpG` lemmas) | GE — (own `TabAt`/`TabAtS` instead, no relating lemma); FE R |
| `wpTS` | p. 6 row 5 (`[about ours]` relativisation) | `Core/World.lean:186` | U (`wpTS_iff_wpG`, `ewp_bot`) | GE U; LB U; FrameTheorems U |
| `wpG` and its lexical stop | not printed (`[TR]` `wp` ends at a value) | `Core/EffDefs.lean:27–40` | U (defines it) | GE U (works inside it: freeze at each stop); EMR B |
| 6.64 Imm Frame | `[TR]` p. 22 | `Core/FrameRules.lean:58`; `wpG_I_frameX` `Core/EffWp.lean:75` (copy) | U via copy; `ewpTS_I_frameU`; `withbor1U` | GE U (`wpG` form) + R (`ewpTS_I_frameR`); HC prose only |
| 6.65 Mut Frame | `[TR]` p. 24 | `:346`; `wpG_M_frameX` `:363` (copy) | U via copy; `ewpTS_M_frameU`; `withbor2U`/`3U` | GE U + R (`ewpTS_M_frameR`, `withborR_compat`); ghost end = 6.65 exit at a stop + entry at resume; LB R (`wpTS_M_refold`); FE R; Outlives U |
| 6.66 Anti Frame | `[TR]` p. 25 | `:550`; `wpG_M_antiFrameX` `:567` (copy) | U via copy; `ewpTS_M_antiFrameU`; `withbor3U` | GE U + R (`ewpTS_M_antiFrameR`); FE R |
| 6.150 ↺ rule | `[TR]` p. 39 | `wpG_reborrow` `Core/Reborrow.lean:232`; `wpTS_reborrow` `:390`; literal `Paper/S6_7…:1174` (proved*) | U (`withloadU_compatX`) | GE — (not lifted to resuming tables; README `:810`); RS R (`reb_iff`) |
| `withbor1`–`3`, `withload`, `withswap`, slices | 6.172–6.176 pp. 45–48 | `Core/Compatibility.lean:252,937,1028,1109,1194` | R: six `*U` twins re-run 6.172–6.175 at `ewpTS`; no `withswapU` | GE U (`withborUE` reused in `withborR_compat`); HAB U (`withbor2Ax`); Coeffects U |
| 6.60 outlives; SPEC §23 | `[TR]` p. 21 | `vC_outlives` `Core/RelationFacts.lean:479`, `vC_outlivesLe` `:575`; `VOutlivesR` `Core/Types.lean:1730` | U (`Row.Unwind`, `ewp_box_end`) | GE U; Outlives R (twin lemmas, `LDerives`) |
| Relation `vC`/`cC`, Kripke `Ext` | p. 4; §12.69–§12.72 | `Core/Relation.lean:119,154` | U (`F_Σ` clause in `cC`; `contShare`, `KapRel` Kripke over `Ext`) | GE R (five `vRL*` families; bridge only at σ = []); EMR R (own binary relation, no bridge) |
| Fundamental Property | 6.151 p. 40; `[CONF]` 3.1 415:17 | `fundamentalC` `Core/Fundamental.lean:434`; `fundamentalProperty` `Paper/S6_8…:164` (variant) | U (effect cases in `fundamentalC`) | GE U (`gfpAt_nil`); GFP at σ ≠ [] OPEN/REFUTED as stated; HAB/HC U (paper layer); SecondClass, Coeffects U; FE R; EMR R (own `fundamental`) |
| Adequacy | `[CONF]` 3.2, 3.3 415:18 | `adequacyC` `:590`; `adequacyD` `Core/Demonic.lean:312` | U (`adequacyD` for effect programs) | GE — (not used); HAB/HC U (paper, angelic); LB U (`theorem32D`); EMR R (`soundness`, `adequacyU`) |
| Preservation | no syntactic theorem; `TW.inv` + post-world `TW` | `Core/Invariant.lean:2702` | U (post-world `TW` at every stop) | GE R (`TabAtS` preserved at one entry only) |
| Leak freedom | `[CONF]` 3.3's empty memory | `reclaim` `Core/Fundamental.lean:534` | U (via `adequacyD`) | HAB U (`effect_safety`: "every handler's state is freed"); EMR R (`no_place_store`) |

---

## Sources read

- `~/repos/borrow_lang/3764117-supplement.pdf` ([TR]), via `pdftotext`: pp. 1–6 (§§1–5), p. 21
  (6.60), pp. 22, 24, 25 (6.64–6.66), p. 39 (6.150), p. 40 (6.151–6.154).
- `~/repos/borrow_lang/3764117.pdf` ([CONF]): 415:17–18 (Lemma 3.1, Theorem 3.2,
  Corollary 3.3); the prose at 415:19 and 415:21 as quoted in `docs/adjudications.md` §12.72.
- `~/repos/borrow_lang/CLAUDE.md`.
- Memory: `MEMORY.md`, `resources-are-of-the-calculus`, `counterexamples-must-arise`,
  `attack-the-global-invariant`, `the-paper-is-not-wrong`, `shortcuts-cost-the-technique`,
  `blockers-must-be-machine-checked`, `state-goals-through-proved-equivalences`,
  `arising-tests-are-directional`, `stop-manufacturing-refutations`, `novelty-is-not-evidence`,
  `do-not-reconstruct-a-printed-route`, `gaps-are-untranscribed-chunks`,
  `boca-life-is-nat-dual`, `flattening-must-be-relational`,
  `the-frame-narrowing-was-the-misstatement`, `formalize-the-paper-not-an-approximation`,
  `coherentx-is-the-faithful-invariant`, `wagner-confirms-outlives-semantics`, `effects-are-core`,
  `current-state-is-not-design`.
- borrow-core @ `8a1c326`:
  - `Paper/INDEX.md`; `Paper/S5_Model/Definitions.lean`; `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`
    (heads); `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean:1160–1185`;
    `Paper/S6_8_FundamentalProperty/Lemmas.lean:120–166`;
  - `Core/README.md`, `Core/World.lean`, `Core/Relation.lean`, `Core/FrameRules.lean` (heads and
    diff), `Core/Reborrow.lean:105–406`, `Core/Invariant.lean` (heads, `TI`, `TW.inv`),
    `Core/Wp.lean` (declarations), `Core/Fundamental.lean`, `Core/Demonic.lean:280–340`,
    `Core/RelationFacts.lean:470–490`;
  - `Core/EffDefs.lean`, `Core/EffWp.lean`, `Core/EffBorrow.lean:40–600`,
    `Core/EffRules.lean` (declarations, `KapRel`, `ewp_handle`, `handle_compatC` head),
    `Core/Handlers.lean:1–50`;
  - `SPEC.md` §19 (`:2270–2984`), §23 (`:3463–3530`); `docs/adjudications.md` §12.72–§12.73;
    `docs/decisions.md` 19–20.
- `experiments/GhostEnd` (README, `Freeze.lean`, `Stacked.lean`, `Bridge.lean`, `RLCompat.lean`,
  `Relend.lean`, `ImmLend.lean`, `Frames.lean`, `Table.lean`, `Program.lean`, `Open.lean`,
  `Kernel.lean`, `Drop.lean`, `Handle.lean`) on main, and `Below.lean` @`daf56c0`. `Arising.lean`
  @`d31cbb3` and `Extend.lean` @`5cfe062` were read through a delegated survey; their cited
  lines were not all re-opened.
- Through the same delegated survey, with spot checks of `Restrat/Open.lean:30,37`,
  `Restrat/README.md:75–100`, `LoopBorrow/Refold.lean:100`, `LoopBorrow/Obstruction.lean:245`,
  `EffModelRel/README.md:7`, `HandlersAsBorrows/Safety.lean:50–58` and
  `FrameEnd/FrameRules.lean:68`: the READMEs and Lean of Restrat, EffModel, EffModelRel,
  HandlersAsBorrows, HandlersControl, SecondClass, Coeffects, CoeffectsStrict, FrameEnd,
  FrameTheorems, TwoRun, LoopBorrow, Outlives, Shifts and BorrowedClosures.
- `origin/effects-audit`: `docs/effects-audit.md` §3–§5 (read in `~/repos/borrow-core-effects-spec`).
  `effects-calculus-spec`: `docs/effects-calculus/01-scope.md:350–395`, and
  `99-open-questions.md` (OQ-44 and the T-PRES note), as grep hits.
- GitHub (read only): issues #172, #279, #290; PR #285 (open, 2026-10-03).
