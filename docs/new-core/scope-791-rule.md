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
| `Imm @a A` | one `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄`, `u, σ` in `𝒱⟦A⟧` | `ptoImmS` (`Core/Relation.lean`), records dropped (§3) |
| `[@a] A` | `𝒱⟦A⟧ ∧ ρ ∈ Res_α` | `box` (`vCE`'s `box` clause) |
| `U C` | `C` at every `Φ′` (downward closed) and every record list | `vThunk` (`SI/MutSemN.lean`), `Covers` dropped (§3) |
| `F A` | `erwp Φ (opTableN ∅) 𝒱⟦A⟧` | `sC`'s `F` (`SI/Sem.lean`); `cC`'s `wpTS` |
| `A ⊸ C` | at every `k′ ≤ k`, every argument in `𝒱⟦A⟧` composed with the function's resource | `sC`'s `⊸` (the step-indexed `−∗`); `cC`'s wand |
| `C & D`, `⊤` | componentwise; trivial | `cC` |
| `∀'x ⊏ @c. C` | every `α ⊏ @cδ`, `C` at `δ[x ↦ α]`, the term applied to `()` | `cC`'s `∀` clause (`LtLife`) |
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
4. **Entries resumed under `extF`**, not Core's `Ext`: `OpEntN.wc`. structure.md §2: no restriction
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

(Filled in as the unit lands; see the end of this file.)
