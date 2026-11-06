# #791 at the rule level, over the chain relation `erwp`

Branch `rule-791`, from `tree-core` (7cf4769c). The Lean is `Core/Chain/Goal791N.lean` (the
interpretation, its laws, the rule checks `mutSub`/`immSub`/`allI`, the restated statements),
`Core/Chain/SI/LocTy.lean` (the per-lend world), `Core/Chain/Lend791N.lean` (the frames the
suspending `mut` lend needs), `Core/Chain/Cancel791N.lean` (`w2`), `Core/Chain/Reborrow791N.lean`
(`w3`), `Core/Chain/Field791N.lean` (`wF`) and `Core/Chain/Inst791N.lean` (their hypotheses
discharged). §8 is the current state.

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
| `Mut @a A` | `∃ b, @aδ ⊑ b ∧ mutL b (vN A δ) Θ ∧` every value of `A` in `Res_b`: a location whose `mut` cell at `b` holds the member `j ≥ k` of `A`'s family read at `Θ` above `b`, the family `Θ` stores at `(ℓ, b)` | `ptoMutS` (`Core/Relation.lean`), with `Θ.above b` for `ls₀`; the slack `@aδ ⊑ b` is what `mutSub` reads (`mutSub_compatN`) |
| `Imm @a A` | one `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄`, `u, σ` in `𝒱⟦A⟧` | `ptoImmS` (`Core/Relation.lean`), without the record list (§3) |
| `[@a] A` | `𝒱⟦A⟧ ∧ ρ ∈ Res_α` | `box` (`vCE`'s `box` clause) |
| `U C` | `C` at every `Θ′` with `Θ.ExtR Θ′ ρ` and `Θ′.OK`, every view `c` with `ConsistentX c ρ`, every record list | `vCE`'s `U` (Kripke), along the resource-relative `ExtR` (`scope-791-loctype.md` §10) |
| `F A` | `erwp (Θ.view c) (opTableN ∅) 𝒱⟦A⟧` | `sC`'s `F` (`SI/Sem.lean`); `cC`'s `wpTS` |
| `A ⊸ C` | at every `Θ′` along `ExtR` at the function's resource (`OK`), every `k′ ≤ k`, every argument in `𝒱⟦A⟧` at `Θ′` composed with the function's resource, every view consistent with the composite | `sC`'s `⊸` (the step-indexed `−∗`); `cC`'s wand |
| `C & D`, `⊤` | componentwise; trivial | `cC` |
| `∀'x ⊏ @c. C` | every `α ⊏ @cδ`: `C` at `δ[x ↦ α]`, the term applied to `()` | `cC`'s `∀` clause (`LtLife`), vacuous where `@cδ` is undefined; `allI_compatN` |
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
(computations stable along `ExtA`, every former but `F_Σ R`); `vN_extR` (values stable along
`ExtR` at their resource, every former); `vN_local` (a value in a lend's stratum does not read the
lend, every former); `vN` and `cN` read `δ` only at the free
lifetime variables (`vN_congr`); `𝒱⟦A⟧` of an outliving `A` lies in the stratum (`vN_outlives`,
Core's `vC_outlives`). `scope-791-loctype.md` §9 lists the formers left out and why.

## 2. The restated statements

`ConstN c` (each `Const791` a value of `!` its type), `FundamentalN`, `ConstsN`, `BridgeN`,
`Goal791SchedN` (the `poolSchedAdequacyN` form at `rowTabN S Φ`), and `Withbor2SN` … the per-constant
statements, as `TreeGoal791`'s with `vN`/`cN`/`erwp` for `vT`/`cT`/`cerwpT`. Proved:
`goal791Sched_of`: `FundamentalN → ConstsN → Goal791SchedN`.

## 3. Departures from Core, each recorded

Departures 1–3 below describe the interpretation before the per-lend world; #825 replaced them
(`scope-791-loctype.md` §9): `Mut` reads the world, `U` is Kripke along the resource-relative
order `LocTy.ExtR` (departing from Core's `Ext` as in `scope-791-loctype.md` §10,
`Core/Chain/ExtRLit791.lean`), and the view's consistency replaces `Covers`. Departure 1's `Imm` half stands. Decision 1 (2026-11-05) asked for
1–3 to be undone. `perLocShape_not_reborrow`
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
4. **Withdrawn.** `∀'x ⊏ @c` is Core's `cC` reading (vacuous where `@cδ` is undefined), and
   `allI_compatN` holds at it. The bound's definedness, which the constants read, is
   `Const791.OK`'s first conjunct: Core's rules fix the bound to `Δ.meetOfDom`, which every
   `δ ⊨ Δ` defines (`defines_meetOfDom_empty`).
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
| `perLocShape_not_reborrow` (the configuration for decision 1) | `Shape791N` | the locations distinct, `α < b < β` |
| `reseal_untyped` (with `stuckV_one`, `stuckV_not_two`, `unitV_all`): the anti-frame's reseal at a location `Φ` does not type (§7.2) | `Shape791N` | `@aδ = β`; `Φ ℓ = none` |
| `coreMutImm_not_extF` (with `coreMutImm_not_extF_inst`): Core's `Mut 'x (Imm 'y 1)` value is not stable along `extF` (§9.3) | `ImmShape791N` | `δ('x) ⊏ δ('y)`, the record lifetime `⊐ δ('x)`, the locations distinct; none in the instance |

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

`perLocShape_not_reborrow` (`Core/Chain/Shape791N.lean`): with `Mut` in Core's shape on the chain
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
  `w3` and `wF`. Routes A–C below were framed against `perLocShape_not_reborrow`; §7.3 places that
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
beyond them). Decision 1 stops at the configuration `perLocShape_not_reborrow`: the routes left are
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
`Φ`, and then a nested `Mut`'s family reads `Φ`: that is `perLocShape_not_reborrow`'s situation
(below). The STOP condition holds: a definition beyond Core's interpretation pieces would be
needed, and choosing it is a design decision.

### 7.3 `perLocShape_not_reborrow` against Core's records-based `Mut`

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

### 7.7 State after #828 (U5): the field reborrow

Core prints no field-reborrow rule, so there is no printed proof to follow: `withborFE` has no
`CDerives` constructor and no Core compatibility lemma. `withborFS_compat`
(`Core/Chain/Field791N.lean`) is §7.6's 13 steps at the source `Mut @a (Ref A)`, from the chain's
existing frames, with no new relation definition:

| # | Chain counterpart | Change from `w3` |
|---|---|---|
| 1 | the constant at `PMap.empty` | none |
| 2 | `vN`'s `Mut` clause: `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)` | `F_o = famL β 𝒱⟦Ref A⟧ Θ`; `Ref`'s clause gives `w₀ = loc ℓ₂`, `σ₀ = ℓ₂ ↦ own(u₀) ● σ_u`, `u₀ ∈ 𝒱⟦A⟧` |
| 3–5 | as `w3` | none |
| 6 | `hunif` | at `Ref A` (source); at `A` (`hunifA`) by a fresh `own` cell beside the value |
| 7 | `consistentX_get`, `reseal_at_entry`, `erwp_M_antiFrameCR` | then the `load` from the opened `ℓ ↦ own(loc ℓ₂)`: `rwp_load` under `erwp_bindR` |
| 8 | `erwp_M_frameCRG` | at `ℓ₂`, with `ℓ ↦ own(loc ℓ₂)` framed outside it: `erwp_frameGR`, `erwp_frame_cancelRunGR`, `tabG_canF` |
| 9–10 | `exists_fresh`, `lend_mutL` | at `ℓ₂`, below `β ⊓ βf ⊓ γ` |
| 11 | the callback at `Θ + (ℓ₂, α)`, view `setLife c ℓ₂ α` | consistency from the source cell's walk (`exS_none_of_walk`, `exS_mut_wit_get`) |
| 12 | `vN_local` | none |
| 13 | `F_i k ⊆ F_o k` | `ℓ₂ ↦ own(w) ● χ` is a `Ref A` value (`hoi`); the guard and claim at `ℓ₂` beside the framed cell are the guard and claim at `ℓ` |

What remains for `Goal791SchedN`/`Goal791Top` is listed in `scope-791-loctype.md` §12; §8 below
scopes the claims.

## 8. State after the review fixes (2026-11-05)

The review is `~/repos/scratch-archive/rule791/review.md`.

**What is proved, and its scope.** #791's `mut` half at the rule level: `withbor2S_compat`
(`w2`), `withbor3S_compat` (`w3`) and `withborFS_compat` (`wF`), each from `Const791.OK`'s
clauses and the finaliser's semantic judgment `hd`, every hypothesis discharged at the hardest
case's row in `Core/Chain/Inst791N.lean`. `Const791.OK` is inhabited for each, its finaliser's
`CDerives` judgment included (`w2_ok`, `w3_ok`, `wF_ok`), and `withbor2S_perform` applies `w2` to
a callback that performs while holding the borrow (at `A = B = 1`). The corollaries `constN_w2`/`constN_w3`/`constN_wF`
are conditional on `FundamentalN`, stated on the fragment and not proved. The `imm` half (`wl`)
waits on `Imm`'s record list and `CohE` (departure 1), which stops at §9.3 (`coreMutImm_not_extF`) and §10.4 (`not_wlImage`); `cN_extA` at `F_Σ R` is open; `sm` needs
the `fam` clause.

**`Mut`** is Core's `ptoMutS` shape: `∃ b, @aδ ⊑ b ∧ mutL b … ∧` the uniform conjunct at `b`.
`mutSub_compatN` is Core's `ptoMutS_antitone`. The lend sites build the borrow at `b = α`; the
reborrow and the field reborrow open the source at its own `b` (`consistentX_get` gives `c ℓ = b`).

**`Row.Suspend S 'x @bnd`** (`Core/TreeGoal791.lean`): payload and answer types outlive `@bnd`
(`VOutlives ∅ bnd`), which puts their values in the stratum of every lend `α ⊏ @bnd`
(`vN_inStratum_bnd`, `LendOKCR`'s `pa`/`pb`) and leaves their reading unchanged by a fresh lend
(`vN_add_eq_bnd`). `erwp_claimX` reads an answer's consistency with the view, since an answer
arrives from outside the run: the bound is defined at the empty context, so it is `⊤`
(`interp_top_of_defines_empty`), and the answer, outliving it, lies in `Res_⊤` (`vN_outlives`),
consistent with every view (`consistentX_of_top`). No clause beyond the outliving one is needed.
`CTy.SuspendC` likewise, without `n ≠ 0`, which no proof reads; `Row.Suspend`'s `n ≠ 0` is read by
`erwp_ubindClaimRT`'s `hTr`. Excluded,
exactly: a payload or answer type with, outside a box or `!`, an `Imm @b A` or `Mut @b A` (they
need `∅ ⊨ @bnd ⊏ @b`, and at the empty context `@bnd` is `⊤`, which no `@b` is strictly longer
than), a thunk `U C` or `Unk` (no `VOutlives` rule), or a box `[@b] A` at a `@b` with a variable;
and the same in cancel rows. A box at a closed lifetime, whatever it holds (`[@⊤] U C`
included), and `! A` pass. The narrowing to `VOutlives ∅ bnd` admits more
than the old "every lifetime" clause only at a bound below `⊤`, which the empty context does not
have. The hardest case's
callback row (`hardestRow`, `park` as `TJN` types it) meets it (`hardestRow_suspend`,
`hardestRow_entry`).

**`FundamentalN`** quantifies over derivations of judgments in the fragment (`JdgInFrag`:
context and type free of type variables, μ, families, opaque types and ν; decidable). A
predicate by recursion on a `CDerives` derivation cannot be written (it is a `Prop`; no large
elimination), so the scope is on the judgment. A derivation of a judgment in the fragment may
still cut through an excluded type inside; at such a cut the interpretation gives no reading, so
`FundamentalN` is not shown attainable by induction until those formers have clauses. `ConstsN`
and `Goal791SchedN` are scoped likewise (`Const791.InFrag`, the row's types).

The excluded cuts are not the whole remaining gap. Two more may change `vN`, and with it its laws
and the `*_compat` proofs:
- **In-fragment rules whose Core proofs read `ptoImmS`'s record list or `CohE`.** At least
  `withloadU`: its type (`withloadUTy`) uses `Imm`, `Mut`, `U`, `⊸`, `∀` and `F_Σ`, all in the
  fragment, and `withloadU_compatX` reads the source through `ptoImmS` with `CohE` and the
  record list, which `vN`'s `imm` clause does not carry (`scope-791-loctype.md` §12,
  departure 1). It is not expected to go through at the current `Imm` clause.
- **`cN_extA` at `F_Σ R`**, open (`scope-791-loctype.md` §10). Core's `withbor1U_compatX` and
  `sliceBorrowIU_compatX` carry the callback's table along `Ext` (`opTable_ext`, at an abortive
  table); their chain analogues are the candidates for needing `cN_extA`'s effect-row case or a
  table lemma like it. Whether they reduce to `opTableN_local` at an abortive row, and whether
  any other rule needs it, is not checked.

**Not done.** `extRL_breaks_extA` still rests on `ν` read as empty (M3): rebuilding it at
`F 0` needs a refutation of `erwp` from a resource holding a `mut` cell (a `TWNC` world with that
cell, its lowering and the run to the stuck term), which is not built. No negative configuration
for a wrong constant (M6) is built, for the same reason: refuting a run at the source's `own`
cell needs that world.

## 9. Port of Core's withload_compatX (#829)

Kernel target: `vN`'s `Imm` clause in Core's `ptoImmS` shape (the record list, `ls₀`, `CohE`), its
laws re-proved, and `ConstN (.wl …)` by Core's `withload_compatX` (`Core/Compatibility.lean:252`)
at a `Row.Suspend` callback row.

### 9.1 `withload_compatX`, step by step

| # | Core step (`Core/Compatibility.lean`) | What it reads | Chain counterpart |
|---|---|---|---|
| 1 | `gSepC_deadP` (257): the context owns nothing | `Ctx.DeadP Γ` | the constant at `PMap.empty`, as `withbor2S_compat`. Exists. |
| 2 | `wpTS_val`, `wpTS_lolli`, `hβ₁` (259–272): the `Imm` argument is `loc ℓ` | `vCE`'s `imm` clause up to the location | `cN`'s `⊸` clause, `erwp_det` at `Head.beta`. Exists. |
| 3 | `wpTS_val`, `wpTS_lolli`, `hβ₂` (274–281): the callback `v_f` at `ls₂`, `Ext ls₁ ls₂ ρ₂` | `vCE`'s `U`: Kripke along `Ext` | `cN`'s `⊸` along `ExtR` at the same list; `U` at every list (departure 2). Exists. |
| 4 | `vC_local true _ hext₂ hv₁` (283): the `Imm` value carried to `ls₂`; its `CohE (rsOf ls₂)` unpacked (284–288) | `Ext` keeps the records relevant to `ρ₁` (`Keeps`) and those above its cells | `vN_extR` along the world. With `vN` reading the list, `vN` stable along the list order: **missing**; Core's is `vC_local` along `Ext`. |
| 5 | `wpTS_bind`, `wpTS_load_I`, `ptoImmO_toImm` (290–295): the load, its payload observable at `ls₂` | `ptoImmS` (`ls₀` to `ls₂`: `ptoImmO_read`) | `rwp_load` under `erwp_bindR` (as `withborFS_compat`'s load). Exists for the load; the observable payload at the current list needs `vN`'s observable mode and `ptoImmO_read` at `vN`: **missing** (`vN`'s `Imm` payload is read at the full relation, not Core's `vCE false`). |
| 6 | the chooser `hesc` (297–318): `CohE` up to `TyEq`, `vC_tyEq`, `vShape_tyEq`, then `rebChooseTW_top` (a record's cell) or `rebChooseTW_deep` (a chain view) | `CohE`; inside the run, the world: `leInvW`/`exIn` (the cell is the record's), `witLB_of`, `tags_above`, `coh_mut` | `erwp_reborrowT` (`SI/RebCancelC.lean`) / `erwp_reborrow` (`SI/RebAcrossC.lean`) at the record's cell, image `canon r β`; `erwp_reborrowDeep` (`SI/RebStopD.lean`) at a chain view. They take the cell as the record's (`single r.le (immOf s r.v r.R hs)`); `vN`'s value gives `single ℓ (immOf s u σ h)` with `CohE`. Identifying `u = r.v`, `σ = r.R` reads the world (`TWNC.inv`'s `leInvW`), available at the first entry of `erwp`: buildable (unfold `erwp_eq` at the first world, then apply the lemma there). `TyEq` transport at `vN` (`vN_tyEq`): **missing**, buildable as `vC_tyEq`. |
| 7 | "Apply `↺V₂`" and 6.134 (319–326): `six132_shape_fresh`, `vC_vShape` | the observable payload's shape | `TmplSpec r (tmpl r)` (`tmpl_exists`, at the first world), `hshape` for `canon r β`. Exists at Core's `vC`; at `vN`: the shape of a `vN` value (`vN_vShape`): **missing**. |
| 8 | "Apply theorem 6.150" (327–329): `wpTS_reborrow` with the chooser | `RebChooseTW`, at the program's relation: the chosen image typed at `vC true⟦Imm̲ 'x T₁⟧` (`image_vC_of_shape`/`relabel_obs`, `Core/RelationFacts.lean:1626`) | `erwp_reborrow*` take the image's typing as the callback's premise (`∀ Bχ, ρ_b ● canon r β = Bχ → erwp …`), supplied before the run. `canon r β` typed at `vN⟦Imm̲ 'x T₁⟧`: `relabel_obs` at `vN`, **missing**, buildable only once `vN` has Core's `Imm` (its `Imm` positions read `CohE`, `coh_root`/`coh_mutI`). Across `Row.Suspend`: `erwp_reborrow` is at `RebOK` tables (non-abortive, `lin`), `erwp_reborrowT` at `RebOKC` with cancel runs that perform nothing (`T₁.RebOK`); raises and layered cancel runs (`tabR`-style, as `erwp_M_frame_cancelRunCR`/`erwp_M_antiFrameCR`): **missing**, buildable on the pattern of `erwp_reborrowT` + `tabR_canA`. |
| 9 | `ИR`, the fresh `β` (330–333): `m ⊓ g₂` below `⊓Δδ` and `ρ₂`'s stratum | `interp_defined_of_wf`, `exists_stratum` | `ResU.exists_stratum`, `defines_meetOfDom_empty`; additionally `β ⊑ ⊓s` (`hβs`) and `r.R ∈ Res_β` (`hRβ`), from the cell. Exists. |
| 10 | `─⋆R`, the pin (335–338) | `rebChooseTW_pin` | `vℓ = r.v` from step 6's identification. Exists. |
| 11 | the callback at `δ['x↦β]` (339–341): `hvf ls₂ (Ext.refl) β` | `U` at `Ext.refl`, `∀` at `β ⊏ ⊓Δδ` | the thunk at the run's world and view; its table the callback row's (`tabN`), which must be `RebOK*` at `β`: `Row.Suspend`'s payload/answer clause gives `PA`/`PB ∈ Res_β` (`vN_inStratum_bnd`). Exists in shape (`withbor2S_compat`'s pattern). |
| 12 | `wpTS_bind_frame` (342–347): the reborrow framed through the thunk, `vP_same` | values stable at same-member lists | `erwp_bindR`/frame; `vN` at same-member lists (`vC_local ∘ ext_of_same`): **missing** with `vN` reading the list, buildable. |
| 13 | `⊸E`, `wpTS_mono`, unpack `['x] T₂`, `vC_extend_of_not_free` (348–357) | the result at the run's last list `ls''` | `vN_extend_of_not_free`, `vN`'s `box` clause. Exists. |

Steps 1–3, 9–11 and 13 exist. Steps 4, 5, 7, 8 and 12 read `Imm` in Core's shape, which `vN` does
not have; step 8's extension across raises and layered cancel runs is the brief's step 3.

### 9.2 What Core's `Imm` brings into `vN`

Core's `imm` clause is `⌜v = ℓ ∧ CohE (rsOf ls) ℓ A δ⌝ ⋆ ptoImmS ℓ α ls (vCE false A · δ)`. Putting it
into `vN`:
- `vN` takes the record list (`vN A δ Θ ls k v ρ`), since `CohE` reads it and the payload is read
  at `ls₀`; the payload is read at Core's observable view (`vCE false`, `U` read as `True`), a
  second mode of `vN`.
- Every former that recurses passes the list, and `Mut` stores its payload at a list: Core's
  `ptoMutS` stores `P ls₀`, the members of `ls` strictly longer-lived than the cell. On the chain
  the stored family is `Θ (ℓ, b) = famL b (vN A · ls₀) Θ`, compared for equality at every re-read
  (`mutL`).
- `F A`'s post reads the run's last list (Core's `wpTS ls e (fun ls'' => vCE … ls'' δ)`).

### 9.3 The stop: Core's list-reading payloads are not stable along `extF`

Core keeps a list-reading payload fixed along `Ext`, whose second clause keeps exactly the records
longer-lived than every borrow cell of the resource (`vC_local`). The chain resumes a continuation
stopped under a live lend at every list `extF` admits (`entN`'s `wc := extF`, every frame's fold
keeps `extF`; `SI/ExtF.lean`), which keeps the records the share's views name and has no lifetime
clause.

`coreMutImm_not_extF` (`Core/Chain/ImmShape791N.lean`), every hypothesis discharged in
`coreMutImm_not_extF_inst`: with `δ('x) = b ⊏ δ('y) = c`, records `recU m`, `recU m'` at `t ⊐ b`,
`ls = [(recU m, t)]`, `ls' = ls ++ [(recU m', t)]`, the cell `ℓ ↦ mut(b, m, m ↦ imm({c}, (), ∅))`
is a value of Core's `Mut 'x (Imm 'y 1)` (`vCE`, Core's own definition) at `ls`; `extF ls ls'`
holds at it; `Ext ls ls'` does not; and it is not a value at `ls'`. The cell's stored predicate is
`𝒱⟦Imm 'y 1⟧` at `ls`, which differs from the one at `ls'` at the `imm` cell at `m'` (`CohE` finds
`recU m'` only in `ls'`).

Where it lands in the `mut` constants, with `Imm` in Core's shape:
- `withbor3S_compat`, step 13: the resealed cell is a `Mut @a A` value beside the result
  (`hRout`, `Core/Chain/Reborrow791N.lean:314`) at the run's last list. After a stop resumed at an
  `extF`-extension adding a record above the cell, `Θ (ℓ, b)`'s family (fixed at the source's list)
  is not `famL b (vN A · ls₀')`, at `A = Imm 'y 1`. The same at `withborFS_compat`'s reseal, and at
  `withbor2S_compat`'s returned `Ref A` (the cell's content, a member of the family fixed at the
  lend, re-read as `𝒱⟦A⟧` at the last list).
- Core's technique (`vC_local` along `Ext`) does not apply: the resumed list is related to the
  stopped one by `extF` only.

What each way out needs, none taken (each is a design decision):
- resuming under `Ext` at a lend's table: a change to `entN`'s `wc` and to every frame's fold
  (each proves `extF` for the lender's continuation); `SI/ExtF.lean`'s header says a fold does not
  keep `Ext` and names `not_ext_fold`, which is not in the tree, so that claim is not checked;
- a world invariant giving `Ext`'s lifetime clause from `extF` at typed worlds (a converse of
  `ext_extF`): not derived, and I have not verified that any obstruction to it is real;
- reading `F A`'s post at the run's first list instead of its last: not Core's shape; and
  `FundamentalN`'s bind across a stop then meets the same configuration for the context's values.

Not verified: that `ConstN (.w3 …)` fails with `Imm` in Core's shape. The configuration is the
step (a value re-read at an `extF`-related list), not a run of the constant ending at `ls'`; no
`TWNC` world typing `ls'` is built.

### 9.4 State

- `vN`'s `Imm` clause is unchanged (`Core/Chain/Goal791N.lean:98`); `w2`/`w3`/`wF`, their
  instances and the laws are untouched and still proved.
- `constN_wl` is not built: step 2 of #829 stops at §9.3 before the steps of §9.1 that read Core's
  `Imm` (4, 5, 7, 8, 12) can be built.
- Unspent: `Row.Suspend`'s payload/answer clause (would supply `RebOK*`'s `pa`/`pb` at `β`, step 11).
  Unused: `erwp_reborrowT`, `erwp_reborrowDeep`, `rebChooseC_tw`, `canon_obs`, `relabel_obs`.
  Untranscribed in `withload_compatX`'s run-up, at `vN`: `vC_local` (list order), `ptoImmO_read`,
  `vC_tyEq`, `vC_vShape`, `relabel_obs`/`image_vC_of_shape`; `erwp_reborrow` across raises and
  layered cancel runs.

## 10. Imm in the per-lend world (#829)

Kernel target: `vN`'s `Imm` clause read in the per-lend world, stable along `extF`, and
`ConstN (.wl …)` by Core's `withload_compatX` at a `Row.Suspend` callback row.

### 10.1 How an `imm` lend's payload is read across `extF`

`vN` takes no record list (`vN A δ Θ n v ρ`, `Core/Chain/Goal791N.lean`). Its `Imm` clause
(`immCell`) reads one `imm` cell `imm(s, u, σ)` with `@aδ ⊑ ⊓s` and the payload `(u, σ)` in
`𝒱⟦A⟧` at the world `Θ`. Nothing in it reads `ls`, so it is unchanged along `extF`, and along
`ExtR`/`ExtA` by `vN_extR`/`vN_extA` as they stand. §9.3's obstruction is to Core's list-reading
payload (`ls₀` inside a `Mut`'s stored family). The current clause does not have it.

### 10.2 What replaces `CohE`: nothing that reads only `vN`'s arguments

Core's `CohE (rsOf ls) ℓ A δ` does two things in `withload_compatX`:
- it names the record whose cell the source is (step 6, the chooser);
- it makes the source's type the record's type, up to `TyEq` (steps 6–8: `vC_tyEq`,
  `vShape_tyEq`, then `image_vC_of_shape` at the record's type).

On the chain, the first can be read off the run's first world. `rwpG` quantifies over
`TWNC fρ ps (rsOf ls)`, every `imm` cell of a typed world is a record's cell or an image's, and
`TWNC.reb` holds the record's `(le, v, R)`. The second cannot. The reborrow lemmas
(`erwp_reborrow`, `erwp_reborrowT`, `erwp_reborrowDeep`) hand the borrowed computation the
record's canonical image `canon r β`. That image is fixed by the record's template, chosen at
the record's type `r.T` (`TmplSpec`, `SI/TWNC.lean`). The callback's argument type is
`Imm̲ 'x A`, at the source's type.

`Core/Chain/ImmRec791N.lean`, every hypothesis discharged:
- `WlImage P` is step 8 at an `Imm` clause `P` read at `vN`'s arguments
  `(A, δ, Θ, n, v, ρ)`. At a run's first entry (`TWNC` at the list's records, `Tagged`), at a
  record of the list whose cell is the source, and with every premise `erwp_reborrow` reads
  (`¬ VFree x r.T`, `TmplSpec r (tmpl r)`, `r.R ∈ Res_β`, the image's shape, `β ⊑ ⊓s`),
  `canon r β` is a value of `Imm̲ 'x A` at `δ['x ↦ β]`.
- The cell is `ℓ ↦ imm({α}, loc ℓ′, ℓ′ ↦ own(()))`. It is the world of an `imm` lend of
  `ℓ ↦ own(loc ℓ′)` recorded at `Ref 1` (`world_ref`). It is also the world of one recorded at
  `U (F 1)` (`world_thunk`), since `vShape (U C)` is `True`. Both worlds are built from `∅` by
  `TWNC.alloc` twice and `TWNC.immFrame`, and both are tagged, `#`-valid with `∅` and lowered.
- At `U (F 1)` the template is `∅`: `Imm̲ (U C) = Unk`, whose shape is `emp`
  (`tmpl_thunk`, `tmplSpec_thunk`). So `canon r β = ∅` at every `β` (`canon_thunk`).
- `not_wlImage`: if `P` admits the cell at `Imm @a (Ref 1)` and has no value of `Imm 'x 1` at
  `∅`, then `¬ WlImage P`. `not_wlImage_vN` is the current clause at `ℓ = 0`, `ℓ′ = 1`, `α = 1`.

`P` is any clause over `vN`'s arguments. It admits the cell at some `Θ`, because the lend
recorded at `Ref 1` hands it at `Imm @α (Ref 1)` and the callback runs at some world. The
refutation uses that same `Θ`. `SemJN` and `rwpG` quantify over the world `Θ` and the typed
world `TWNC` independently, so the same `(Θ, cell)` occurs at the world recorded at `U (F 1)`.
A clause that reads `Θ` is covered. So is one that asks for coherence with *some* list
(`∃ ls, CohE (rsOf ls) …`): either way the clause holds at the lend's `Θ` and cannot see which
record the run's world holds.

So the information `CohE` carries (the source's type is its record's) is not available to an
`Imm` clause in the per-lend world. That is the difference from `Mut`. The relation reads the
per-lend world for `mut` cells, through the view `Θ.view c` (`PredStep`, `reseal_at_entry`). For
`imm` records it reads only the records on `ls`/`TWNC`, which carry `r.T` and never read `Φ`.

### 10.3 `withload_compatX`'s 13 steps under the per-lend reading

| # | Step (§9.1) | State |
|---|---|---|
| 1 | the constant at `PMap.empty` | exists |
| 2 | the `Imm` argument is `loc ℓ` (`cN`'s `⊸`, `erwp_det`) | exists |
| 3 | the callback along `ExtR` | exists |
| 4 | the `Imm` value carried to the run's world | exists (`vN_extR`; no list to carry) |
| 5 | the load, its payload | exists (`rwp_load` under `erwp_bindR`; the payload at `𝒱⟦A⟧`) |
| 6 | the chooser: the record whose cell the source is | the record's `(le, v, R)`: buildable from the first world (`TWNC`). Its type: **blocked** (`not_wlImage`) |
| 7 | the image's shape (`TmplSpec`, `hshape`) | exists, at the record's type |
| 8 | the image typed at `Imm̲ 'x A`; across raises and layered cancel runs | **blocked** at its first part (`not_wlImage`). The extension across raises and layered cancel runs (on `erwp_reborrowT` + `tabR_canA`) is buildable and not attempted |
| 9 | the fresh `β` | exists |
| 10 | the pin `vℓ = r.v` | buildable with step 6's identification |
| 11 | the callback at `δ['x ↦ β]`, its table `RebOK*` from `Row.Suspend`'s clause | exists in shape |
| 12 | values at same-member lists | exists (`vN` reads no list) |
| 13 | the result at `['x] B`, `vN_extend_of_not_free` | exists |

### 10.4 STOP

Step 8 needs the source's type to be its record's, and `not_wlImage` shows that no `Imm` clause
over `vN`'s arguments gives it. Getting it would mean one of:
- `vN` reading the run's record list (Core's `CohE (rsOf ls)`). This changes `vN`'s signature,
  hence the statements of every law and of `withbor2S_compat`/`withbor3S_compat`/
  `withborFS_compat`. With the payload read at the list, §9.3's `coreMutImm_not_extF` applies to
  `Mut` payloads too;
- the relation reading an `imm` entry of the per-lend world (a change to `rwpG`/`TWNC`'s
  records or `LocFam`), or `LocTy` carrying `imm` entries.

Each of these is on the brief's stop list. Nothing is changed: `vN`, its laws, `w2`/`w3`/`wF`
and their instances, `LocTy`, `Row.Suspend`, `CTy.SuspendC` and `Const791.OK` are as they were.

Not verified:
- that `ConstN (.wl …)` is false. The configuration is the step: the image the chain's reborrow
  lemmas hand the callback. No run of the constant is refuted, and no other way of giving the
  callback a resource at `ℓ′` is excluded in Lean: I have not proved that, in the world recorded
  at `U (F 1)`, no typed-world step other than an image of `r` (which is `∅`) adds a cell at `ℓ′`;
- whether, at a record whose type does match the source's, the image is a value of `Imm̲ 'x A`
  at `vN`'s full-relation payload reading. Core reads the payload at `vCE false` (`U` read as
  `True`), and `reb_witness_choice` shows the witness under a `Ref (U C)` is a choice. I have not
  derived this either way and have not verified that any obstruction is real.

Unspent premises: `Row.Suspend`'s payload/answer clause (step 11), `Const791.OK`'s `wl` clause
(`¬ VFree x A`, `¬ VFree x B`, the bound's definedness; only `¬ VFree x A` is read, by
`WlImage`). Unused: `erwp_reborrow`, `erwp_reborrowT`, `erwp_reborrowDeep`, `rebChooseC_tw`,
`canon_escrowAgree`, `relabel_obs`. Unused uniqueness results: `ResU.CompS.functional`,
`AgW.functional`, `CellU.immOf_inj` (the configuration needs none). Untranscribed in `withload_compatX`'s
run-up, at `vN`: `CohE` and its `TyEq` transport (`vC_tyEq`, `vShape_tyEq`), `ptoImmO_read` (the
observable payload), `vC_vShape`, `image_vC_of_shape`/`relabel_obs`; `erwp_reborrow` across
raises and layered cancel runs.
