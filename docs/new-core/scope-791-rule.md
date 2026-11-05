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
| value types `vN A δ : SemT` | `P k v ρ`, downward closed in `k` | `SemT` (`SI/MutSemN.lean`), Core's `vCE` clause by clause |
| `1`, `⊗`, `0`, `+`, `Ref`, `!`, `I32/I64` | `vCE`'s clauses, `⋆` written as `ResU.CompS` | `vCE`; `sV` (`SI/Sem.lean`) |
| `Mut @a A` | `vMut α (vN A δ)`: a location whose `mut` cell at `α = @aδ` holds the member `j ≥ k` of `A`'s family | `vMut` (`SI/MutSemN.lean`) |
| `Imm @a A` | one `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄`, `u, σ` in `𝒱⟦A⟧` | `ptoImmS` (`Core/Relation.lean`), without the record list (§3) |
| `[@a] A` | `𝒱⟦A⟧ ∧ ρ ∈ Res_α` | `box` (`vCE`'s `box` clause) |
| `U C` | `C` at every `Φ′` (downward closed) and every record list | `vThunk` (`SI/MutSemN.lean`), without `Covers` (§3) |
| `F A` | `erwp Φ (opTableN ∅) 𝒱⟦A⟧` | `sC`'s `F` (`SI/Sem.lean`); `cC`'s `wpTS` |
| `A ⊸ C` | at every `k′ ≤ k`, every argument in `𝒱⟦A⟧` composed with the function's resource | `sC`'s `⊸` (the step-indexed `−∗`); `cC`'s wand |
| `C & D`, `⊤` | componentwise; trivial | `cC` |
| `∀'x ⊏ @c. C` | `@cδ` defined, and every `α ⊏ @cδ`: `C` at `δ[x ↦ α]`, the term applied to `()` | `cC`'s `∀` clause (`LtLife`); empty where `@cδ` is undefined, as `TreeGoal791`'s `SCmp.none` (§3) |
| `F_Σ R` | `erwp Φ (opTableN (tabN (F_Σ R) δ Φ)) 𝒱⟦R⟧` | `cC`'s `eff` clause (`effTab`, `finObl`, `effRet`); `sProt`/`sFin` |
| `tabN` | one entry per layer, first match winning: qualifier, `abort = B.isZero && q != lin`, `PA = 𝒱⟦A⟧`, `PB = 𝒱⟦B⟧`, cancel obligation `finN fin` where `capB q B`, resumed under `extF` | `effTab`; `OpEntN` (`SI/ErwpN.lean`); `extF` from `SI/ExtF.lean` (§2 of structure.md) |
| `finN` | `none` at `⊤`; else the cancel run at the cancel row's table, `cancelOblN Φ (tabN F δ Φ)` | `finObl`; `sFin` |
| `retN` | `𝒱⟦R⟧` of the row's answer | `effRet`; `sRet` |
| `gN δ Γ γ` | the live slots' values over a split of the resource | `gSepC`; `gT` (`Core/TreeGoal791.lean`) |
| `SemJN Δ Γ e j` | every `δ ⊨ Δ`, every downward-closed `Φ`, index, list; from `𝒢⟦Γ⟧` | `SemC`; `SemJT` |

`rowTabN S Φ` is `tabN (F_S 1) ∅ Φ`: the table a task at the row `S` is run at, as `rowTab S` on
the tree.

Formers outside the fragment, read as empty (and why): type variables and `μ` (I11, no `μ` in the
#791 constants), `ν` (I10), families (`[L]`, used only by `sliceBorrowMU`, whose unit is the slice
lends), opaque host types (no constant mentions them). `Unk` owns nothing, as `vCE`'s `emp`.

**Laws proved:** downward closure of `vN`, `cN`, every `tabN` (`OpTabN.Down`) and `finN`;
monotonicity of values along `Φ` and the record list (they read neither); monotonicity of
computations along `LocFam.Ext` (`erwp_extΦ` with the table widened along `OpTabN.Le`); `vN` and
`cN` read `δ` only at the free lifetime variables (`vN_congr`); `𝒱⟦A⟧` of an outliving `A` lies in
the stratum (`vN_outlives`, Core's `vC_outlives`).

## 2. The restated statements

`ConstN c` (each `Const791` a value of `!` its type), `FundamentalN`, `ConstsN`, `BridgeN`,
`Goal791SchedN` (the `poolSchedAdequacyN` form at `rowTabN S Φ`), and `Withbor2SN` … the per-constant
statements, as `TreeGoal791`'s with `vN`/`cN`/`erwp` for `vT`/`cT`/`cerwpT`. Proved:
`goal791Sched_of`: `FundamentalN → ConstsN → Goal791SchedN`.

## 3. Departures from Core, each recorded

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
| `erwp_M_frameCR`, `claimT_canX`, `erwp_ubindClaimR` | `Lend791N` | the frames' own (as `erwp_M_frameT`/`erwp_M_frameR`, `erwp_ubindClaim`/`erwp_ubindRaise`) |
| **`withbor2S_compat`** | `Lend791N` | `withbor2U`'s premises with `Row.Suspend` (`hA`, `hB`, `hS`, `hdc`), `d`'s semantic judgment (`hd`, the fundamental property at the premise), and **`hSB`, `hSF`** below |
| `constN_w2` | `Lend791N` | `FundamentalN`, `hSB`, `hSF` |
| `cbRelease_sem` (the callback type is inhabited) | `Lend791N` | the bound defined |
| `answer_not_inStratum` (the configuration for `hSB`) | `Lend791N` | none |

`ConstN`, `ConstsN`, `FundamentalN`, `BridgeN`, `Goal791SchedN`, `Withbor2SN`, `Withbor3SN`,
`WithborFSN`, `WithloadSN`, `SliceBorrowMSN` are stated (`Goal791N` §3). `Goal791Top` reads no
relation and is `TreeGoal791`'s as it stands.

### Two row clauses `Row.Suspend` does not supply (decisions for the user)

`withbor2S_compat` takes two clauses on the callback's row that `Row.Suspend`
(`Core/TreeGoal791.lean`) does not state:

- **`hSB`: every answer type outlives every lifetime** (`∀ o ∈ S, ∀ Δ a, VOutlives Δ a o.B`),
  `Row.Suspend`'s payload clause applied to the answer. The Mut Frame re-lends at the resume and
  asks the answer's resource in `Res_{↓α}` (`OpTabN.LendOKCR.pb`, as `LendOK.pb`/`LendOKC.pb`).
  `¬ VFree x o.B` does not give it: `answer_not_inStratum` is a value of `U(F 1)` outside
  `Res_{↓α}` at every `α`. Not derived from `Row.Suspend`; obstruction at `OpTabN.LendOKCR.pb`,
  configuration `answer_not_inStratum`. This is the frame's premise; I have not verified that
  the constant itself fails at such a row. What the clause gives up: answers holding borrows or
  thunks (an answer `U C`); `1`, data, `!` types and boxes outliving everything are kept.
- **`hSF`: every capturable operation's cancel row has no layers** (`CTy.NoLayers`: not `⊤`, no
  operations). The lender's cancel run is the callback's with the borrow folded
  (`erwp_M_frame_cancelRun`), which asks the cancel row's table `LendOK α` and one table `T₁` for
  every operation (`claimT`). A cancel row with operations would need its operations' types
  constrained as `Row.Suspend` constrains the row's, and `claimT` per entry. Not derived;
  obstruction at `claimT`'s single `T₁` and `erwp_M_frame_cancelRun`'s `T₁.LendOK A`; no
  configuration built. What it gives up: cancel rows that perform (the default `finsNil` is kept).

### The decision on `Covers` (§3, departure 3)

With no `Covers`, the constants that open a `mut` argument are not reachable at this
interpretation: `w3` (`withbor3U` at `Row.Suspend`, the Anti-Frame on the source) and `wF` (the
field reborrow `withborFE`, which reads the field out of the borrowed record), as `withswap`.
Opening a cell at the index re-seals it at a lower member of its family, which `UpdN` allows only
along `Φ ℓ`'s family (`rwp_M_antiFrame_sem`'s `Φ ℓ = (α, τ.fam α)`), and nothing in the
interpretation says `Φ` types an argument's cell. I have not derived `w3`/`wF` and have not
verified that any obstruction is real. The candidate: `Covers` in `U`, `⊸` and `SemJN` (as
`vThunk`), with the lend's family carrying the lender's coverage
(`F j w r = 𝒱⟦A⟧ j w r ∧ Covers Φ r`, so the claim's content is covered when the finaliser takes
it) and `Mut`'s clause reading its family through `Φ ℓ`. That is an interpretation change, so it
is the user's: it re-opens `withbor2S_compat` at the finaliser's argument.

### What the next unit needs

- The `Covers` decision above, then `w3` and `wF` (`erwp_withbor3` and `erwp_M_antiFrameC`, the
  inner frame at a cell of the content), `wl` (the `imm` half: the record list and `CohE` back
  in `Imm`), `sm` (families).
- `FundamentalN`: every `CDerives` rule at `SemJN` (#789's ports), and `[handle]` at `cN`
  (`erwp_handle_le`) for `Goal791Top`.
- `BridgeN` is proved; `Goal791SchedN` follows from `FundamentalN` and `ConstsN`
  (`goal791Sched_of`).

### Unspent premises, unused results

- `Const791.OK`'s `∃ b, Defines b ∧ VOutlivesLe b A` for `w2` is unspent: the lend's lifetime is
  chosen below the content's stratum (`ResU.exists_stratum`), not from the type.
- `Row.Suspend`'s `o.n ≠ 0` is spent at the raises (`erwp_ubindClaimR`'s `hTr`).
- Not used: `erwp_M_frameTF`/`erwpG_frameT` (the fold-guarded tables, for the anti-frame
  constants), `erwp_withbor3`, `erwp_reborrow`.

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
