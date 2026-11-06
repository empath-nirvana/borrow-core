# #791 at the rule level, over the chain relation `erwp`

Branch `rule-791`, from `tree-core` (7cf4769c). The Lean is `Core/Chain/Goal791N.lean` (the
interpretation, its laws, the restated statements) and `Core/Chain/Lend791N.lean` (the frames
the suspending `mut` lend needs, and its compatibility).

Kernel target: the semantic interpretation of types over `erwp` (`Core/Chain/SI/*`), the
semantic judgment over it, and compatibility of the `mut` lend whose callback row may suspend
inside the borrow (`Const791.w2`). structure.md §7 step 1 for the chain, and the first #791
constant.

## 1. The interpretation

Every piece names the Core technique it follows.

| Piece | Definition | Follows |
|---|---|---|
| value types `vN A δ Θ` | `P k v ρ` at the per-lend world `Θ` (`SI/LocTy.lean`), downward closed in `k` | Core's `vCE` clause by clause; the world is `scope-791-loctype.md` §2 |
| `1`, `⊗`, `0`, `+`, `Ref`, `!`, `I32/I64` | `vCE`'s clauses, `⋆` written as `ResU.CompS` | `vCE`; `sV` (`SI/Sem.lean`) |
| `Mut @a A` | `mutL α (vN A δ) Θ`: a location whose `mut` cell at `α = @aδ` holds the member `j ≥ k` of `A`'s family read at `Θ` above `α`, the family `Θ` stores at `(ℓ, α)` | `ptoMutS` (`Core/Relation.lean`), with `Θ.above α` for `ls₀` |
| `Imm @a A` | one `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄`, `u, σ` in `𝒱⟦A⟧` | `ptoImmS` (`Core/Relation.lean`), without the record list (§3) |
| `[@a] A` | `𝒱⟦A⟧ ∧ ρ ∈ Res_α` | `box` (`vCE`'s `box` clause) |
| `U C` | `C` at every `Θ′` with `Θ.ExtA Θ′` and `Θ′.OK`, every view `c` with `ConsistentX c ρ`, every record list | `vCE`'s `U` (Kripke), along `ExtA` (`scope-791-loctype.md` §8 Q1) |
| `F A` | `erwp (Θ.view c) (opTableN ∅) 𝒱⟦A⟧` | `sC`'s `F` (`SI/Sem.lean`); `cC`'s `wpTS` |
| `A ⊸ C` | at every `Θ′` along `ExtA` (`OK`), every `k′ ≤ k`, every argument in `𝒱⟦A⟧` at `Θ′` composed with the function's resource, every view consistent with the composite | `sC`'s `⊸` (the step-indexed `−∗`); `cC`'s wand |
| `C & D`, `⊤` | componentwise; trivial | `cC` |
| `∀'x ⊏ @c. C` | `@cδ` defined, and every `α ⊏ @cδ`: `C` at `δ[x ↦ α]`, the term applied to `()` | `cC`'s `∀` clause (`LtLife`); empty where `@cδ` is undefined, as `TreeGoal791`'s `SCmp.none` (§3) |
| `F_Σ R` | `erwp (Θ.view c) (opTableN (tabN (F_Σ R) δ Θ c)) 𝒱⟦R⟧` | `cC`'s `eff` clause (`effTab`, `finObl`, `effRet`); `sProt`/`sFin` |
| `tabN` | one entry per layer, first match winning: qualifier, `abort = B.isZero && q != lin`, `PA = 𝒱⟦A⟧`, `PB = 𝒱⟦B⟧`, cancel obligation `finN fin` where `capB q B`, resumed under `extF` | `effTab`; `OpEntN` (`SI/ErwpN.lean`); `extF` from `SI/ExtF.lean` (§2 of structure.md) |
| `finN` | `none` at `⊤`; else the cancel run at the cancel row's table, `cancelOblN Φ (tabN F δ Φ)` | `finObl`; `sFin` |
| `retN` | `𝒱⟦R⟧` of the row's answer | `effRet`; `sRet` |
| `gN δ Γ γ` | the live slots' values over a split of the resource | `gSepC`; `gT` (`Core/TreeGoal791.lean`) |
| `SemJN Δ Γ e j` | every `δ ⊨ Δ`, every world `Θ` with `Θ.OK` (`Down ∧ Bounded`), every view `c` consistent with the resource, index, list; from `𝒢⟦Γ⟧` | `SemC`; `SemJT` |

`rowTabN S Θ c` is `tabN (F_S 1) ∅ Θ c`: the table a task at the row `S` is run at, as `rowTab S` on
the tree.

Formers outside the fragment, read as empty (and why): type variables and `μ` (I11, no `μ` in the
#791 constants), `ν` (I10), families (`[L]`, used only by `sliceBorrowMU`, whose unit is the slice
lends), opaque host types (no constant mentions them). `Unk` owns nothing, as `vCE`'s `emp`.

**Laws proved** (`Core/Chain/Goal791N.lean`): downward closure of `vN`, `cN`, every `tabN`
(`OpTabN.Down`) and `finN`; `vN_extA` (values stable along `ExtA`, every former); `cN_extA`
(computations stable along `ExtA`, every former but `F_Σ R`); `vN_local` (a value in a lend's
stratum does not read the lend, every former but `U`); `vN` and `cN` read `δ` only at the free
lifetime variables (`vN_congr`); `𝒱⟦A⟧` of an outliving `A` lies in the stratum (`vN_outlives`,
Core's `vC_outlives`). `scope-791-loctype.md` §9 lists the formers left out and why.

## 2. The restated statements

`ConstN c` (each `Const791` a value of `!` its type), `FundamentalN`, `ConstsN`, `BridgeN`,
`Goal791SchedN` (the `poolSchedAdequacyN` form at `rowTabN S Φ`), and `Withbor2SN` … the per-constant
statements, as `TreeGoal791`'s with `vN`/`cN`/`erwp` for `vT`/`cT`/`cerwpT`. Proved:
`goal791Sched_of`: `FundamentalN → ConstsN → Goal791SchedN`.

## 3. Departures from Core, each recorded

Departures 1–3 below describe the interpretation before the per-lend world; #825 replaced them
(`scope-791-loctype.md` §9): `Mut` reads the world, `U` is Kripke along `ExtA`, and the view's
consistency replaces `Covers`. Departure 1's `Imm` half stands. Decision 1 (2026-11-05) asked for
1–3 to be undone. `coreShape_not_reborrow`
(§5, "Decision 1") refutes reading Core's `ls₀` as the location typing, not Core's records-based
`Mut` (§7.3). What stops the port of Core's `withbor3_compatX` is the anti-frame's reseal at a
location the location typing does not type (`reseal_untyped`, §7.2); departure 1's record half
has no configuration.

1. **No record list in values; `Imm` without `CohE`.** `𝒱` reads neither `Φ` nor the record list
   (the chain's own answer, `SI/MutSemN.lean`: no recursive world). Core's `Imm` clause reads
   coherence with the records (`CohE`) and stores the members longer-lived than the cell
   (`ls₀`); these are what the reborrow constants (`withload`, the `imm` half) read. They are not
   in this interpretation; the `imm` half restores them.
2. **`U C` at every record list**, not Kripke along `Ext`: stronger, and what the frames
   (stated at every list) produce.
3. **No `Covers` (location typing of the resource) in `U`, `⊸` or `SemJN`.** `vThunk` asks
   `Covers Φ′ ρ`. With `Covers` in `U` the argument of `⊸` and the context of `SemJN` must carry
   it too, or a thunk cannot be forced on its arguments; and then the suspending lend's finaliser
   needs `Covers Φ` of the lend's claim, whose content is whatever value of `A` the callback left
   in the cell, of which nothing says `Φ` types it. Without `Covers`, a computation that opens a
   `mut` cell it was given (`rwp_M_antiFrame_sem`'s `Φ ℓ = (α, τ.fam α)`) cannot be proved at the
   interpretation. So the anti-frame constants (`w3`, `wF`, `withswap`) are not reachable from
   this interpretation as it stands. **Decision for the user** (§5).
4. **`∀'x ⊏ @c` is empty where `@cδ` has no interpretation** (Core's `cC` reads it as trivial
   there). The two agree at every `δ ⊨ Δ` for a bound `Δ` defines (`Δ.meetOfDom`). Without it,
   `ConstN` of a constant whose bound is undefined at some `δ` would ask the constant to run an
   arbitrary term as its callback.
5. **Entries resumed under `extF`**, not Core's `Ext`: `OpEntN.wc`. structure.md §2: no restriction
   relative to `Ext` (`ext_extF`).

## 4. NOT doing (stop and report)

- No change to `erwp`, `rwpG`, `EndOKG`, `UpdVN` or any relation definition.
- No field or condition added to an operation table (`OpEntN`) to make something pass.
- No second relation: no `erwpX`, `cerwp`, `twp`, `cerwpT`.
- No closed program presented as a rule-level result.
- No premise on a compatibility lemma that its typing rule does not supply; a premise the rule
  does not supply is named, said so, and listed in §5.
- No restriction of programs without saying so: every extra condition on `Row.Suspend` is listed
  in §5 with what it gives up.
- Tempting shortcuts that mean STOP: fixing `α` in the interpretation; reading `F_Σ` at a table
  other than the row's; proving the lend at a fixed callback.

## 5. State and open items

### Proved (all axioms within `propext`, `Classical.choice`, `Quot.sound`; in `scripts/AxiomCheck.lean`)

| Result | File | Hypotheses |
|---|---|---|
| `vN_down`, `cN_down`, `tabN_down`, `finN_down`, `retN_down`, `vN_le`, `cN_le` | `Goal791N` | `Φ.Down` for computations |
| `vN_congr`, `cN_congr`, `tabN_congr`, `finN_congr`, `retN_congr`, `vN_extend_of_not_free` | `Goal791N` | agreement of `δ`, `δ′` at the free variables |
| `cN_extΦ` (with `tabN_extΦ`, `finN_extΦ`, `cancelTabN_le`) | `Goal791N` | `Φ.Ext Φ′` |
| `vN_outlives` | `Goal791N` | `Δ.Models δ`, `@aδ = α`, `VOutlives Δ a A` |
| `cN_effOf`, `retN_effOf` | `Goal791N` | none |
| `bridgeN : BridgeN` | `Goal791N` | none |
| `goal791Sched_of : FundamentalN → ConstsN → Goal791SchedN` | `Goal791N` | the two named |
| `erwp_M_frameCR` | `Lend791N` | the frame's own (as `erwp_M_frameT`/`erwp_M_frameR`) |
| `erwp_M_frame_cancelRunCR` | `Cancel791N` | `DownFam`, `T.LendOKCR α`, `T.Twin T′`, the nested transfer `hcan` |
| `tabR_can` | `Cancel791N` | `DownFam`, `F.SuspendC x` |
| `erwp_ubind_cancelRunCR`, `erwp_ubindClaimRT` | `Cancel791N` | `Φ.Down`, `D` consuming the claim; for the latter the raises named (`m ≠ 0`) |
| **`withbor2S_compat`** | `Cancel791N` | `withbor2U`'s premises with `Row.Suspend` (`hA`, `hB`, `hS`, `hdc`), `d`'s semantic judgment (`hd`, the fundamental property at the premise). No row clause beyond `Row.Suspend`. |
| `constN_w2` | `Cancel791N` | `FundamentalN` |
| `suspend_closingOp` (the cancel-row clause admits a cancel row with a layer) | `Cancel791N` | the names nonzero |
| `cbRelease_sem` (the callback type is inhabited) | `Lend791N` | the bound defined |
| `answer_not_inStratum` (why the answer clause is in `Row.Suspend`) | `Lend791N` | none |
| `coreShape_not_reborrow` (the configuration for decision 1) | `Shape791N` | the locations distinct, `α < b < β` |
| `reseal_untyped` (with `stuckV_one`, `stuckV_not_two`, `unitV_all`): the anti-frame's reseal at a location `Φ` does not type (§7.2) | `Shape791N` | `@aδ = β`; `Φ ℓ = none` |

`ConstN`, `ConstsN`, `FundamentalN`, `BridgeN`, `Goal791SchedN`, `Withbor2SN`, `Withbor3SN`,
`WithborFSN`, `WithloadSN`, `SliceBorrowMSN` are stated (`Goal791N` §3). `Goal791Top` reads no
relation and is `TreeGoal791`'s as it stands.

### `Row.Suspend` (`Core/TreeGoal791.lean`)

The row predicate `Const791.OK` checks for every constant. Its clauses: every operation named,
not unrestricted, payload and answer free of `'x` and outliving every lifetime, and each
capturable operation's cancel row meeting the same clauses (`CTy.SuspendC`). The answer clause is
what the Mut Frame's re-lend at a resume reads (`OpTabN.LendOKCR.pb`; `answer_not_inStratum` is a
`U(F 1)` answer outside every stratum). The cancel-row clause is what a cancel run stopping
under the live lend reads; it admits cleanup that performs (`suspend_closingOp`). SPEC §62
("Typing: suspension") states both.

### Decision 1: Core's shape, and where it fails on the chain

`coreShape_not_reborrow` (`Core/Chain/Shape791N.lean`): with `Mut` in Core's shape on the chain
(`Φ ℓ = (α, 𝒱⟦A⟧ read at Φ above α)`, `mutC`), a value at `ℓ_b ≠ ℓ` whose cell is at `b`, holding
a `Mut @β 1` at `ℓ₂ ≠ ℓ`, is a value at `Φ` (`Φ ℓ = (β, 𝒱⟦1⟧)`) and is not one at `Φ.set ℓ α F`
for any `α < b < β` and any `F`. `Φ.set ℓ α Fi` is where a reborrow runs its callback
(`erwp_withbor3`: `Φ ℓ = (β, Fo)`, the callback at `Φ.set ℓ α Fi`); a callback holding a borrow
shorter than the source and longer than the reborrow is valid at `Φ`, and no Kripke order along
which Core's `Mut` values are stable reaches the reborrow's location typing. Cause: Core's records
are one per lend (a reborrow adds one and keeps the source's); the chain's location typing is one
family per location (a reborrow overwrites the source's). So the interpretation is not rebuilt in
Core's shape at `Mut`, and `w3`/`wF` are not built: every route found needs a design decision.

Routes, none built, none verified:

- **A. Location typing per lend** (Core's records): `Φ` an extension-only record of families, a
  reborrow adding an entry. A change to `LocFam`/`UpdN`, so a relation change: the user's.
- **B. Core's shape with inclusion and pointwise content**: the `Mut` clause asks the family to
  contain `𝒱⟦A⟧` read above `α` (writes), and the actual content to be a value (opening), and `U`
  is Kripke along "entries above every held borrow not added or changed, removal allowed, and the
  resource's own cells, deeply, unchanged". The reborrow's removal of `ℓ` then keeps the inclusion;
  what is left is a callback whose *actual* nested content holds a cell at `ℓ`, which a valid
  resource cannot (`ResU.Lower`, the flattening). Needs: uniqueness of locations in the
  flattening, read inside the frame's run. I have not derived it and have not verified that it
  holds of `ResU.Flat`.
- **C. Top-level typing over a `Φ`-free content semantics**: `Mut` reads `Φ ℓ = (α, 𝒱⟦A⟧)` with the
  family `Φ`-free (as now), cell contents and `Ref` contents read without `Φ`, `U` Kripke along
  agreement at the resource's top-level `mut` cells, Core's `𝒱⟦A⟧ ⊆ Res_α` in the `Mut` clause.
  `w2`, `w3`, `wF` look provable (the re-lend leaves the callback's top-level cells alone; payload
  and answer types, outliving every lifetime, hold no `Mut`). The cost: a `Mut` read out of a cell
  or a `Ref` is not typed by `Φ`, so it cannot be opened again; this is a restriction the
  fundamental property would meet at nested `Mut`s (load of a `Ref (Mut …)`, swap). Not shown that
  nothing needed is lost; so not built.

The record half of decision 1 (`Imm` with `CohE`/`ls₀`, `U` Kripke along Core's `Ext`) was not
attempted; I have no configuration for it. It meets the same question as the location typing:
whether a chain run keeps the records above a live borrow fixed (Core's `Ext`), which the frames'
families, fixed at the lend, would read.

### What the next unit needs

- §7 (unit 3): the port of `withbor3_compatX` stops at its anti-frame step (§7.2). A decision
  on how an opened `Mut` argument's location comes to be typed by `Φ` at the step index; then
  `w3` and `wF`. Routes A–C below were framed against `coreShape_not_reborrow`; §7.3 places that
  configuration, and §7.2 is the question they have to answer.
  `w3`/`wF` across `Row.Suspend` also need the anti-frame across raises and across cancel runs
  that stop at their rows' tables: `erwp_M_antiFrameC`'s cancel runs perform nothing
  (`cancelTabR OpTabN.empty`), the analogue of `erwp_M_frame_cancelRunCR` for the anti-frame.
- `wl` needs `Imm`'s records and `CohE` (the record half of decision 1); `sm` needs families
  (`[L]`), read as empty here.
- `FundamentalN`: every `CDerives` rule at `SemJN` (#789's ports), and `[handle]` at `cN`
  (`erwp_handle_le`) for `Goal791Top`.

### Unspent premises, unused results

- `Const791.OK`'s `∃ b, Defines b ∧ VOutlivesLe b A` for `w2` is unspent: the lend's lifetime is
  chosen below the content's stratum (`ResU.exists_stratum`), not from the type. Route C would
  spend it (`𝒱⟦A⟧ ⊆ Res_α`).
- `Row.Suspend`'s `o.n ≠ 0` is spent at the raises (`erwp_ubindClaimRT`'s `hTr`); in the
  cancel-row clause it is not read.
- Not used: `erwp_M_frameTF`/`erwpG_frameT`, `erwp_withbor3`, `erwp_reborrow`,
  `erwp_M_antiFrameC` (the anti-frame constants, not built).

## 6. Unit 2: the plan for the decisions of 2026-11-05

Kernel target: the interpretation in Core's shape; `withbor2S_compat` with only premises the
typing rule supplies; `w3` and `wF` across stops.

### Decision 2: the answer clause in `Row.Suspend`

`Row.Suspend` (`Core/TreeGoal791.lean`, the row predicate `Const791.OK` checks for every
constant) gains `∀ Δ a, VOutlives Δ a o.B`, the payload clause applied to the answer.
`Row.Suspend.of_unwind` still holds (an unwinding operation's answer is `0`). `hSB` leaves
`withbor2S_compat` and `constN_w2`; `tabN_lendOKCR` reads the clause from `hS`. SPEC §62
("Typing: suspension") states the clause.

### Decision 3: lifting `hSF`

`Row.Suspend` constrains the cancel row of every capturable operation by the same clauses,
recursively (`CTy.SuspendC`: every layer not unrestricted, named, free of `'x`, payload and
answer outliving every lifetime, and its own capturable layers' cancel rows likewise). Then:

1. `tabR F δ Φ R` / `finR F δ Φ R`: the table of a row's layers with every capturable entry's
   cancel obligation the cancel run ending at the claim `R` (`cancelOblRN`), recursively. It is
   the lender's twin of the callback's `tabN` (replacing `claimT`'s single table `T₁`).
2. `erwp_M_frame_cancelRunCR`: the Mut Frame over a cancel run whose table has abortive,
   must-resume and cancellable entries (`LendOKCR α`), from `cancelTabN T₁` at `Φ[ℓ ↦ (α, F)]`
   to `cancelTabR T₁′ (claimR …)` at `Φ`, its nested cancel obligations transferred by a premise
   (as `erwp_M_frameCR`'s `hcan`).
3. `tabR_can`: that premise, by induction on the cancel row, each level `erwp_M_frame_cancelRunCR`
   at the row's own table, `LendOKCR α` at it from `CTy.SuspendC`.
4. `erwp_ubind_cancelRunCR`: the finaliser frame over a cancel run at `cancelTabR (tabR …) R`,
   ending at `cancelTabN (tabN …)`: at the cancel's `raise` `D` consumes the claim (with or
   without an error payload); a nested cancellable stop's cancel run passes the frame by the
   same lemma one level down.
5. `withbor2S_compat` re-proved through them; no `hSF`.

### Decision 1: Core's shape

Core's `Mut` stores `𝒱⟦A⟧` at the records strictly longer-lived than the cell (`ptoMutS`'s
`ofS Q = P ls₀`), and its Kripke order `Ext` keeps exactly the records above every borrow of the
resource. On the chain the location typing `Φ` carries the families (`UpdN` changes a cell's
predicate only along `Φ ℓ`), so the transport is: a `Mut` value at `ℓ` with `Φ ℓ = (α, F)`,
`F = 𝒱⟦A⟧` read at `Φ` above `α`, and `U` Kripke along the `Φ` that keep the entries above every
borrow of the thunk's resource. Before rebuilding the interpretation the plan checks this shape
against the frames the constants run: `withbor3U` and `withborFE` re-lend a location at a shorter
lifetime (`erwp_withbor3`: the callback runs at `Φ.set ℓ α Fi`, `Φ ℓ = (β, Fo)`). The check is a
Lean configuration (`Core/Chain/Shape791N.lean`); if Core's shape fails there, the configuration
is the departure's justification and the interpretation keeps the chain's answer at `Mut`.

### Outcome

Decisions 2 and 3 are built (§5: `Row.Suspend`'s clauses, `withbor2S_compat` with no row clause
beyond them). Decision 1 stops at the configuration `coreShape_not_reborrow`: the routes left are
design decisions (§5, routes A–C).

## 7. Port of Core's withbor3_compatX

Kernel target: Core's proofs of `withbor3_compatX` (`Core/Compatibility.lean:1109`),
`withbor2_compatX` (`:1028`) and `withload_compatX` (`:252`), step by step on `erwp`.

### 7.1 `withbor3_compatX`, step by step

| # | Core step (`Core/Compatibility.lean`) | What it reads | Chain counterpart |
|---|---|---|---|
| 1 | `gSepC_deadP` (1114): the context owns nothing | `Ctx.DeadP Γ` | `ConstN`'s form: the constant at `PMap.empty` (`withbor2S_compat`'s first line). Exists. |
| 2 | `wpTS_val`, `wpTS_lolli`, `hβ₁` (1117–1128): the `Mut` argument is `loc ℓ`, β | `vCE`'s `Mut` clause up to the location | `cN`'s `⊸` clause and `erwp_det` at `Head.beta` (as in `withbor2S_compat`). Exists. |
| 3 | `wpTS_val`, `wpTS_lolli`, `hβ₂` (1130–1137): the callback `vf` at `ls₂`, `Ext ls₁ ls₂ ρ₂` | `vCE`'s `U` clause: Kripke along `Ext` | `cN`'s `⊸` at `k′ ≤ k`, the same list; `erwp_det`. Exists. The chain's `⊸` does not move the list. |
| 4 | `vC_local` (1140): the `Mut` value carried to `ls₂` | `Ext` keeps the members above every borrow of `ρ₁` | Not needed while `⊸` keeps the list. With `vN` reading the list (Core's `ls₀`), `vN_local` along `Ext`: **missing**, buildable as Core's `vC_local`. |
| 5 | unpack `ptoMutS ℓ α₀ ls₂ P ρ₁` (1141–1145) | the cell `mut(b, u, σ, Q)`, `α₀ ⊑ b`, `ofS Q = P ls₀` | `mutCell`: the cell at `α` holding the member `j ≥ n` of `𝒱⟦T₁⟧`. Exists, without `ls₀`. |
| 6 | `hunif` (1147–1149): `MutFrame`'s stratum premise, `∀ ls′ w σ, 𝒱⟦T₁⟧ w σ → σ ∈ Res_b` | `ptoMutS`'s last conjunct | `erwp_withbor3`'s `hoi` (`F_i k ⊆ F_o k`, the stratum `α` to `β`). `mutCell` lacks the uniform conjunct: **missing piece of Core's `ptoMutS`**, buildable (add the conjunct to `mutCell`). |
| 7 | `wpTS_M_antiFrameX` (1151) at `ℓ ↦ M α₀ 𝒱⟦T₁⟧`; inside it (`Core/FrameRules.lean:550`): the content read at the current list (`hofS`, `ext_stored_current`, 582), and at the end the content handed back written into the **unchanged** stored predicate `Qs` (`ptoMutX_write (Q := Qs)`, 620), with `hunif` and `lifeBound_of_tagged` | `ptoMutS` only; Core's `↭` fixes a `mut` cell's predicate, and `Qs` has no index | `erwp_M_antiFrame` (`SI/AntiStopN.lean:257`) inside `erwp_withbor3` (`:515`). It reads **`hF : Φ ℓ = some ⟨β, F_o⟩`** with the cell at the member `F_o j`, and reseals at `F_o k`, the member of the index left: a predicate change `↭` admits only at a location `Φ` types (`PredStep`). **No counterpart** at the interpretation: `vN`'s `Mut` does not give `Φ ℓ`, and neither does Core's (it has no location typing). §7.2. |
| 8 | `wpTS_M_frameX` at `β` (1154): the opened cell re-lent at the fresh `α` | `hunif`'s `β`; the content at `ls₂` | `erwp_M_frameF` inside `erwp_withbor3`; across `Row.Suspend`, `erwp_M_frameCR`/`erwp_M_frame_cancelRunCR` (`Lend791N`, `Cancel791N`). Exists for the frame. The anti-frame across raises and layered cancel runs: `erwp_M_antiFrameC` (`SI/AntiCancelN.lean:130`) covers cancel runs that perform nothing; the `tabR`-style extension is **missing**, buildable as unit 2's. |
| 9 | the fresh lifetime `a₂ ⊓ m` (1156–1159) | `ρ₂.exists_atLife`, `⊓Δδ` defined | `ResU.exists_stratum`, `Life.down` (`withbor2S_compat`). Exists. |
| 10 | the borrow at `δ[x ↦ α]` (1161–1166) | `vC_extend_of_not_free` | `vN_extend_of_not_free`. Exists. |
| 11 | `wpTS_bind`, `wpTS_bind_frame`, `hvf … α` (1167–1176): the callback at the borrow | `U`'s clause at `Ext.refl`, `∀`'s clause at `α ⊏ ⊓Δδ` | the thunk at `Φ.set ℓ α F_i` (`vN`'s `U` at every `Φ`); `erwp_ubindClaimRT` across `Row.Suspend`. Exists (`withbor2S_compat`'s pattern). |
| 12 | `wpTS_mono`, unpack `['x] T₂` (1177–1183) | `box`'s clause | `vN`'s `box` clause, `vN_extend_of_not_free`. Exists. |
| 13 | `wpTS_val` and the two wands (1184–1190): `MutFrame`'s `∀v′`, then `AntiFrame`'s `∃w … (ptoMutS ─⋆ Q)` | the resealed cell is a `Mut` value again | `MFPost l α F_i (AFPost l β F_o Q)`, `erwp_withbor3`'s `hA`. Exists in shape; reads step 7's reseal. |

The interpretation pieces the brief lists, against this proof: `withbor3_compatX` reads `ptoMutS`
(steps 5–7, 13) and `Ext` (steps 3, 4, 11). It does not read `ptoImmS`, `CohE` or `Covers`
(Core has no `Covers`; `Covers` is the chain's `vThunk`, `SI/MutSemN.lean`). `Φ.set` has no
Core analogue: Core's lend re-types nothing; it writes a new cell holding its predicate.

### 7.2 Step 7 has no chain counterpart: `reseal_untyped`

`Core/Chain/Shape791N.lean`, `reseal_untyped`: a `Mut @a (U(F 1))` value at the index `2` (the
cell `ℓ ↦ mut(β, λ_. (), ∅, 𝒱₂⟦U(F 1)⟧)`); the content `λ_. () ()`, in `𝒱⟦U(F 1)⟧` at the index
`1` (`stuckV_one`) and not at `2` (`stuckV_not_two`); at every `Φ` with `Φ ℓ = none` and every
index, no `↭` step (`MutStep`, `UpdMutN`'s clause) takes the cell to one whose predicate admits
that content. Every hypothesis is discharged. So the chain's reseal at the index left needs the
location typing to type the opened cell, and the interpretation (Core's or the current `vN`)
does not supply it: `ConstN` quantifies over every downward-closed `Φ`, and `⊸`'s argument comes
with no relation to `Φ`.

Not verified: that `ConstN (.w3 …)` itself fails at the current interpretation. The configuration
is the step, not the constant; I have not built the run (a callback writing `λ_. () ()` one step
before the index runs out) and have not verified that the constant is false.

What the chain has that reaches `Φ ℓ`: `vThunk`'s `Covers` (`SI/MutSemN.lean`, structure.md §7),
defined and used nowhere. As defined it would not close step 7: it covers the thunk's resource,
not `⊸`'s argument; and it gives `Φ ℓ = (β, F)` with the cell at *some* member of *some* `F`,
where `erwp_withbor3`'s `hoi` needs `F` to be `𝒱⟦T₁⟧`'s family (as `rwp_M_antiFrame_sem`'s
`Φ ℓ = (A, τ.fam A)`). Putting `Φ ℓ = (α, 𝒱⟦A⟧'s family)` into the `Mut` clause makes `vN` read
`Φ`, and then a nested `Mut`'s family reads `Φ`: that is `coreShape_not_reborrow`'s situation
(below). The STOP condition holds: a definition beyond Core's interpretation pieces would be
needed, and choosing it is a design decision.

### 7.3 `coreShape_not_reborrow` against Core's records-based `Mut`

It does not arise. Core's `ptoMutS` stores `P ls₀` with `ls₀` the members of the **record list**
above the cell; the record list is the same `List SRec` on the chain, and a `mut` reborrow leaves
it alone on both sides (Core's `withbor3_compatX` runs the callback at `ls₂`, step 11;
`erwp_withbor3` runs it at the `ls` it was given). The configuration's `famC` reads `Φ` above the
cell as if it were `ls₀`; `Φ.set ℓ α F` removes `ℓ` from `Φ` above `b` and so changes the family.
A `Mut` read Core's way, at the records, is unchanged by `Φ.set`. The configuration stays as a
documented non-route: it refutes reading `ls₀` as the location typing, not Core's technique. The
obstruction Core's technique meets on the chain is §7.2's, and it is the step index's, not the
records'.

### 7.4 `withbor2_compatX` and `withload_compatX`

- `withbor2_compatX`: steps 1–3 and 8–13 above, with the source an owned cell (`Ref`), so no
  step 7; `MutFrame` at `↓β` from the side condition `Δ ⊢ T₁ ⊒ @b` through `vC_outlivesLe`
  (1053–1057). Chain: `withbor2S_compat` (`Cancel791N`), proved, no `hSF`, no `hSB`. Since #827 it
  takes this step as Core does: the lend's lifetime is below the side condition's `@bδ`, and every
  value of `A` is in its stratum by `vN_outlivesLe` (Core's `vC_outlivesLe`), which supplies the
  borrow's uniform conjunct (step 6) and the content's stratum. `Const791.OK`'s
  `∃ b, Defines b ∧ VOutlivesLe b A` is now spent (`hO`).
- `withload_compatX`: reads `ptoImmS` with `CohE` at the loaded cell (the chooser of
  `wpTS_reborrow`), `wpTS_load_I`, `vC_local`, `vC_tyEq`. Chain: `erwp_reborrow`
  (`SI/RebAcrossC.lean:96`) exists; `vN`'s `Imm` has no `CohE` and no record list (departure 1),
  so the chooser is not read off the value. Not attempted: §7.2 stops the unit first.

### 7.5 State before #827

Interpretation unchanged (`Goal791N.lean`): step 2 of the brief changes only what the port reads,
and the port stops at step 7 before the pieces it would read (`hunif`, the record list) matter.
`w3` and `wF` (`withborFE` opens the source the same way) are not built. `withbor2S_compat` and
`constN_w2` are unchanged, with no `hSF` and no `hSB`.

Unspent printed premises at the stop: `Const791.OK`'s `VOutlivesLe` for `w2`; for `w3`, none read
yet past step 6. Unused: `rwp_M_antiFrame_sem`, `erwp_withbor3`, `erwp_M_antiFrameC`,
`erwp_reborrow`, `Covers`. Untranscribed in the run-up of `withbor3_compatX`: the chain
counterparts of steps 4 (`vN_local`, only if `vN` reads the list), 6 (`ptoMutS`'s uniform
conjunct), 7 (the reseal at a location `Φ` does not type) and 8's anti-frame across layered cancel
runs.

### 7.6 State after #827 (U4): every step built

`withbor3S_compat`/`constN_w3` (`Core/Chain/Reborrow791N.lean`) follow Core's `withbor3U_compatX`
(`Core/EffBorrow.lean`), whose proof is `withbor3_compatX`'s: the finaliser frame outermost, the
anti-frame at the source with the borrow handed back at every end, the Mut Frame inside it. Over
the per-lend interpretation (`scope-791-loctype.md` §11) the 13 steps are:

| # | Chain counterpart, built | State |
|---|---|---|
| 1 | the constant at `PMap.empty` | as `withbor2S_compat` |
| 2 | `vN`'s `Mut` clause: `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `Θ (ℓ, β) = F_o`, `F_o = famL β 𝒱⟦A⟧ Θ` | done |
| 3 | the callback along `ExtR` | as `withbor2S_compat` |
| 4 | `vN_extR` (Core's `vC_local`) carries both to the run's world; `vN_local` returns the result | done (#826) |
| 5 | `mutL` unpacked | done |
| 6 | `hunif`, `ptoMutS`'s last conjunct, now the `Mut` clause's: every value of `A` in `Res_β` | done; `w2` supplies it from `⊢ A ⊒ @b` (`vN_outlivesLe`, Core's 6.60) |
| 7 | `consistentX_get` gives `c ℓ = β`; `reseal_at_entry` gives the view's `hF`; the anti-frame reseals into `F_o k` | done (L1) |
| 8 | `erwp_M_frameCRG` (the Mut Frame at a fresh `α ≤ β`, its fold recorded at every stop), `erwp_M_antiFrameCR`/`erwp_M_antiFrame_cancelRunCR` (the anti-frame across stops, raises and layered cancel runs), `tabG_can`, `tabR_canA` | done, built in this unit |
| 9 | `LocTy.exists_fresh` below `β ⊓ βf ⊓ γ` | done |
| 10 | `lend_mutL`, `vN_extend_of_not_free`; the borrow's `hunif` at `α` from the source's by `α ≤ β` | done |
| 11 | the callback at `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ`, view `setLife c ℓ α` (`view_add`); its table the guarded twin (`tabN_tabG_twin`) | done |
| 12 | `vN_local` at `['x] B` | done |
| 13 | `F_i k ⊆ F_o k` by `hunif` and `vN_above` (the guard `hG`, the claim `hRin`); the resealed cell is a `Mut @a A` value (`hRout`) beside the result and in every raise's claim; `erwp_claimX`, `erwp_ubindClaimRT`, `fin_claimM` | done |

§7.2's obstruction (`reseal_untyped`) is answered by L1: the view types the cell at its own entry.
`erwp_withbor3` (`SI/AntiStopN.lean`) is not used: it is the composition at tables with no raises
and no cancellable stops; `erwp_M_antiFrameCR ∘ erwp_M_frameCRG` is its extension.
