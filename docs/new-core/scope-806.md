# Scope: a run may give up an `imm` view copy held outside it (#806)

Part of #771. This is departure D4's design (b) from #793. It is needed before #789's compatibility step. Branch `updx-806`, which builds on `spike-793` (6e6ac79e) and sits on top of `si-782`. Nothing is built until this doc is reviewed.

All of the Lean quoted below is in `docs/new-core/scope-806/Clause.lean`. Check it with `lake env lean docs/new-core/scope-806/Clause.lean` after `lake build Core.TreeConsume`. It elaborates. Every theorem in it has `#print axioms` ⊆ [propext, Classical.choice, Quot.sound].

**Kernel target.** `twp`'s post-configuration `EndT` reads a relaxed `↭`, `UpdXW`, in place of `UpdX`. The consequences:
- a run gives up a copy of a view, at any configuration, whenever its frame condition guarantees an absorbing copy;
- every existing tree result is re-proved;
- `twp_lendEnd` is unchanged.

## 1. The new clause

`UpdX` itself stays. Every `UpdX` built at the start of a segment (`twp_update`, `twp_lendOpen`, `twp_lendEnd`, the heap rules) is still a plain `UpdX`, and `UpdX.toW` lifts it.

`EndT`'s `↭` becomes `UpdXW`. It differs from `UpdX` in two ways:
- **Start side:** the end world's flattening `⦇fρ′⦈` may absorb an `imm` cell of the start.
- **End side:** a start cell may absorb an `imm` cell of the end.

```lean
/-- `χ` (at the end) absorbs the `imm` cell `ψ` (at the start), across the re-reading: same
value, witness re-read, lifetime set at least `ψ`'s. -/
def CellAbs (Θ : LocTy) (ψ : TCell K) (χ : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ RR Θ ψ.wit χ.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ χ.lsOf = some t ∧ s.set ⊆ t.set

/-- `ψ'` (at the end) is absorbed by `ψ` (at the start): lifetime set at most `ψ`'s. -/
def CellSub (Θ : LocTy) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ ψ'.kind = Kind.imm ∧ ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ ψ'.lsOf = some t ∧ t.set ⊆ s.set

def XOptW (Θ : LocTy) (E E' : Prop) (o : Option (TCell K)) (o' ow : Option (TCell K')) : Prop :=
  (∀ ψ, o = some ψ → ψ.kind ≠ Kind.own → ¬ E → ¬ E' ∧
    ((∃ ψ', o' = some ψ' ∧ XCell Θ ψ ψ') ∨ ∃ χ, ow = some χ ∧ CellAbs Θ ψ χ)) ∧
  (∀ ψ', o' = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' → ¬ E ∧
    ∃ ψ, o = some ψ ∧ (XCell Θ ψ ψ' ∨ CellSub Θ ψ ψ'))

def UpdXW (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' fρ' : TRes K') : Prop :=
  ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
    ∀ l, XOptW Θ (E l) (E' l) (σ.get l) (σ'.get l) (τw.get l)

#check @UpdXW   -- elaborates
theorem UpdX.toW … (h : UpdX Θ E E' ρ ρ') (hv : ResUT.Valid fρ') : UpdXW Θ E E' ρ ρ' fρ'   -- proved
```

In `EndT`, the clause `UpdX (sem w′.Θ) (recMask O₀) (recMask O′) ρ₀ ρ′` becomes `UpdXW (sem w′.Θ) (recMask O₀) (recMask O′) ρ₀ ρ′ fρ′`. Nothing else in `EndT` changes. The masks, `MaskDiff` and `InvKept` stay as they are.

**Why the end world, not the frame.** `twp_frame` runs the inner run in the same world as the outer one: the inner frame is `ρf ● ρ₂`, and the inner world is `fρ`. So an absorption the inner run proves at `⦇fρ′⦈` is already the outer's.

An absorber that is "the frame `ρf′`" does not carry through. Take an inner start cell `ψ₁` and a framed cell `ψ₂` at the same `ℓ` with different lifetime sets. The outer start cell is `ψ₁ ○ ψ₂`, with set `s₁ ∪ s₂`. After the inner run consumes `ψ₁`, the outer end cell is `ψ₂′`, with set `s₂`. No exact match exists on either side; only absorption by the world does. This is also why the end side needs `CellSub`.

This failure is an argument, not a configuration. I have not built a configuration for it and have not verified that the obstruction is real. It decides the design only as a precaution.

**Why `imm` only.** `CellAbs` forces `imm` on both sides, so every `mut` cell still falls under `XCell`, exactly as before. Consequences:
- `InvKept.trans` and `UpdX.inv` (both read the start side at `mut` cells) keep their proofs.
- `mut` is untouched: a `mut` cell has one holder (`not_compS_single_self`).

## 2. Results to re-prove, file by file

The statements stay the same unless a row says otherwise. "Mechanical" means the change is a new lemma name at the same site.

| File | Result | Statement changes? | Work |
|---|---|---|---|
| `Support/Model/Tree/World/UpdX.lean` | new: `XOptW.trans`, `UpdXW.trans`, `UpdX.transW` (a plain `UpdX` followed by a `UpdXW`), `UpdXW.widen`, `UpdXW.congr`, `UpdXW.frame`, `UpdX.toW` | new | **the main proofs** (§4 R1, R2) |
| same | `UpdX`, `XOpt`, `UpdX.trans`/`frame`/`widen`/`congr`/`of_rr`, `updX_refl_imm`, `UpdX.of_updV` | no; kept for segment starts | none |
| `…/World/UpdXInv.lean` | new: `UpdXW.inv`, `InvKept.transW` | new; same shape as `UpdX.inv`/`InvKept.trans` with `UpdXW` | the `mut` cells take the `XCell` disjunct |
| `…/World/UpdXMasks.lean` | `lend_open_admitted`, `lend_open_needs_mask` | no (about `UpdX`, not `EndT`) | none; add `UpdXW` versions only if review asks |
| `…/World/StepKeep.lean` | `fdEsc_of_updX` → `fdEsc_of_updXW` | **yes**: hypothesis `hu : UpdXW … ρ ρ′ fρ′` | it reads only the end side's "a start cell exists", which `XOptW` keeps |
| `Core/TreeWp.lean` | `EndT` | **yes** (§1) | — |
| same | `twp_here` | no | `UpdX.toW` |
| same | `twp_bind` | no | `UpdXW.trans`, `InvKept.transW` |
| same | `twp_frame`, `twp_frame_w` | no | `UpdXW.frame` |
| same | `twp_extend`, `twp_update` | no | `UpdX.transW` |
| same | `endT_inv` | **yes**: the conclusion's `XOpt … (σ.get l) (σ′.get l)` becomes `XOptW … (τw.get l)` with `∃ τw, Flat fρ′ τw`. It exposes the clause | `UpdXW.inv` |
| `Core/TreeHeap.lean` | `twp_alloc*`, `twp_free`, store/load (`UpdX.trans g₀.1 hu g₉` at :287, :337, :536; `g₉` passed at :463) | no | `UpdX.transW` |
| `Core/TreeStepKeep.lean` | `StepKeepsFdEsc`, `StepKeepsFdEscNoUpd` (defs), `stepKeepsFdEsc` | **yes**: the defs quote `EndT`'s clauses, so `UpdX … ρ ρ′` becomes `UpdXW … ρ ρ′ fρ′`. `not_stepKeepsFdEscNoUpd` is unchanged | `fdEsc_of_updXW` |
| `Core/TreePool.lean` | pool frame (:168 `UpdX.frame`, :211 `fdEsc_of_updX`) | no | `UpdXW.frame`, `fdEsc_of_updXW` |
| `Core/TreeHandle.lean` | bind through the handler (:123) | no | `UpdXW.trans`, `InvKept.transW` |
| `Core/TreeResume.lean`, `TreeSched*`, `TreePool*`, `TreeRelay*`, `TreeCactus`, `TreeHeadlines` | — | no | they read `EndT` only through the rules above. Rebuild and check |
| `Core/TreeLend.lean` | `twp_lendOpen`, `twp_lendEnd` | **no** (`twp_update`'s premise stays plain `UpdX`) | none |
| `Core/TreeConsume.lean` | `updX_consume_view_false`, `twp_refuses_consume_view(_at)`, `twp_frame_callee_refused`, `twp_child_refused` | **retired**: they refute what (b) admits. `updX_consume_view_false` stays true of `UpdX`. The others are replaced by §3's admitted results | — |
| same | `twp_consume_view_held`, `twp_bind_callee_consume`, `twp_lendEnd_after_consume`, `twp_admits_keep_view`, carrier lemmas | no | rebuild |

**Size estimate**
- 350–500 lines in `UpdX.lean`, `UpdXInv.lean` and `StepKeep.lean`; the bulk is `UpdXW.frame` and `XOptW.trans`.
- 60–120 lines at the Core sites.
- 250–400 lines for §3 in `Core/TreeConsume.lean`.
- About 700–1000 lines in all.

## 3. Theorem statements

`HoldsView`/`StmtConsumeFramed` elaborate as given in `Clause.lean`. The `def … : Prop` forms below are the targets, proved for every configuration, not only fixed ones.

```lean
def HoldsView (Θ : LocTy) (β : Life) (l : BoCa.Loc) {K : WCactus} (ρf : TRes K) : Prop :=
  ∃ τ χ, ResUT.Flat ρf τ ∧ τ.get l = some χ ∧ CellAbs Θ (viewCell (K := K) β) χ
```

**(T1) The admitted consume.** A run gives up a copy when every frame meeting `F` holds an absorbing copy.

```lean
theorem twp_consume_view_framed :  -- = StmtConsumeFramed
  ∀ F Q n w ls O e (Z ρ : TRes w.K) β l,
    ResUT.CompS Z (viewRes β l) ρ → (∀ w' ρf, F w' ρf → HoldsView (sem w'.Θ) β l ρf) →
    twp F Q n w ls O e Z → twp F Q n w ls O e ρ
```

**(T2) The admitted callee consume.** For the callee proved on its own copy (`twp_frame`'s inner run), `F₁` is any frame condition implying `HoldsView`. Callers discharge it with `twp_frame`'s `hF` obligation: the framed `ρ₂` holds the caller's copy, so `ρf ● ρ₂₀` holds it. The theorem is T1 at `F₁`, plus a corollary `twp_frame_callee_consume` that states it through `twp_frame` with `R` holding the caller's copy.

**(T3) The admitted child consume.** A spawned task gives up a copy at any frame condition implying `HoldsView`. The theorem is T1 at the child's frame condition.

The spikes' frame conditions cannot be kept as stated (§7, `twp_refuses_last_copy`). Those were `fun _ _ => True` for the callee and `fdMask (fun _ => False)` (`enSpawn`'s `Fe`) for the child. Both admit the empty frame, and at the empty frame the consume is refused under any reading of `↭`.

The issue's done-when "at the frame conditions those spikes used" is therefore read as "at those frame conditions strengthened by `HoldsView`" (design choice D-1 below). For the scheduler, this asks `enSpawn`'s `Fe` to carry the parent's copy, which is #795's resource hand-off. T3 is stated at the `twp` of the child, not through `HS`.

**(T4) The hardest case: a lend ends after one copy was given up while another task still holds a live copy.** Three parts.

- **(T4a) The given-up copy leaves nothing behind.** T1's conclusion runs from `Z`, which holds nothing more at `ℓ` than before. The world is unchanged (`consume_view_world`, proved).
- **(T4b) The end is refused while a live copy is outside the lender.** At every `F` admitting a frame that holds a copy, the lender, holding the lend cell and owning `lendRec 1`, cannot end holding `ℓ ↦ own(())`. **Proved already at today's `twp`, without reading `UpdX`:** `twp_refuses_lendEnd_live_copy` (`Clause.lean`). It is re-checked after the change and moved to `Core/TreeConsume.lean`. The reason: the end world would compose the frame's re-read copy with `own` at `ℓ`, and `▶◀` refuses that.
- **(T4c) Once the holder has returned its copy, the end is admitted by `twp_lendEnd`, unchanged.** The combined statement:

```lean
theorem twp_lendEnd_after_framed_consume
    (hρ₁ : ResUT.CompS Z (viewRes α l) ρ₁)               -- the lender's lend cell
    (hρ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf ())) ρ)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf)          -- the live holder has returned its copy
    (hO : lendRec l ∉ O) (hls : ∀ x ∈ ls, x.1 ≠ lendRec l)
    (hcallee : twp F₁ P n w ls' O₁ e₁ (viewRes α l))     -- a callee that gave up its copy (T2)
    (hrest : ∀ …, P … → twp F Q … (K.plug t) ρ)          -- after the end
    : twp F Q n w ((lendRec l, α) :: ls) (lendRec l :: O) (K.plug e₁) ρ₂   -- ρ₂ = ρ₁ ● v
```

The binders of `hcallee`/`hrest` (the `twp_frame` instance that frames the lender's copy around the callee, then `twp_bind`) are fixed in the build. T4b sits beside this as the refusal while `hF` cannot hold. `twp_lendEnd`'s statement and proof are not touched.

## 4. Risks, ranked

| # | Risk | Lean check |
|---|---|---|
| R1 | **`UpdXW.frame`.** The inner and outer worlds are the same `fρ′`, so start-side absorption carries over verbatim. The end side needs `CellSub` from `ψ₂′ ⊆ ψ₁ ○ ψ₂` (`lsc` union, erase and witness agreement across `○`, `xcell_compR`'s shape). Also needed: the `own`-left cases of `xopt_comp` redone with three options. | not checked |
| R2 | **`XOptW.trans` / `UpdXW.trans`.** The middle world `fρ₁ = ρf₁ ● ρ₁` absorbs `ψ`. By `ρ₁ → ρ₂`'s clause and the frame's re-reading, the end world absorbs every cell of `⦇ρf₁⦈(l) ○ ⦇ρ₁⦈(l)`, so it absorbs `ψ`. This needs "the world's flattening at an unmasked `imm` location only grows" as a lemma. Masks: an unmasked start stays unmasked (the clause's `¬E′`), as `XOpt.trans` already uses. | not checked |
| R3 | **`endT_inv` / `UpdXW.inv`.** `mut` cells take the `XCell` disjunct (`CellAbs` forces `imm`). The statement changes (§2). | not checked. The `mut`-only reading of `UpdX.inv`'s proof (`UpdXInv.lean:313`) was read, not built |
| R4 | **`RecInv` preservation** is not read off `↭`. A run must establish `RecInv` at its own end. A consume of the last copy fails there whatever `↭` says. | **checked**: `twp_refuses_last_copy` (`Clause.lean`) refutes the last-copy consume without reading `EndT`'s `UpdX` clause |
| R5 | **Who reads the old start-side clause.** Consumers of `EndT`'s `UpdX`: `UpdX.trans`/`frame` (rebuilt), `InvKept.trans` (`mut` only), `UpdX.inv` (`mut` only), `fdEsc_of_updX` (end side only). | **checked by grep**: no `UpdX` in `TreeCactus.lean`, `Recs.lean` (an import only), `TreeHeadlines`, `TreePoolSched`, `TreeResume`. `CactusInvT` and the record invariants (`TWNT`, `RecInv`, `TaggedT`) do not mention `UpdX` or `XOpt`. Not checked by build |
| R6 | **T1's proof.** It runs `Z` at the same world (`consume_view_world` needs the frame's absorbing cell to compose with `v` to itself: `CellAbs` with an empty witness gives that, `RR.of_empty`). It needs a flattening lemma for `Z ● v` when `Z` already holds a cell at `ℓ`. `flat_compS_view` asks `σ.get ℓ = none`, so it needs the `○` version. | not checked |
| R7 | **`StepKeepsFdEsc` statement change.** It is consumed by the scheduler invariant (`PoolT`, `cerwpT_schedHandle`); every use must pass `fρ′`. | not checked |

## 5. What #789's compatibility lemmas get

**What they get:** a rule whose semantic proof consumes an `imm` value can be proved at its own resource, through T1, whenever its frame condition implies `HoldsView` at the value's location. For example, `release_imm` on an `STy.imm` value with `STy.unit`'s `ρ = ∅` as the answer.

**The escape is not moot. It flips.** Under (b), a frame condition that *guarantees* a copy is what admits the consume, and one that admits a copy-free frame refuses it (`twp_refuses_last_copy`).

So #789 has to supply `HoldsView` at every consume. This is the typing fact that "someone else holds this borrow": the lender, or the caller's copy. It is not a hypothesis standing in for an unproved fact. Without it, the consume is refuted (R4).

Whether #789's frame conditions can carry `HoldsView` across stops and resumes (`fdAt`'s `fd`, `KapSchedT`) is not derived.

## 6. Not doing

- **Restoring ρ⁺** (design (a)). Garbage in another branch fails `twp_lendEnd`'s `hF` (`not_noneAt_view`).
- **`mut`.** One holder (`not_compS_single_self`); no `mut` lend at `twp` (D14). `CellAbs` forces `imm`.
- **Changing D15**, `OpEntT.Down` or `twp_kappa_cancel`.
- **Weakening `twp_lendEnd`.** Its statement and proof stay byte-for-byte. T4b must still hold.
- **Proving T1–T4 only at fixed configurations.** The configurations in `Clause.lean` and `TreeConsume.lean` are refutations and non-vacuity witnesses only.
- **Changing `UpdX`, `twp_update`'s premise, or `UpdXMasks`** to make proofs shorter.
- **A new judgment**, or a `HoldsView`-shaped premise on `twp` itself. It goes on the frame condition `F` only.
- **Hypotheses standing in for unproved lemmas** (R1, R2, R6 are proved, not assumed).

## 7. Kill criterion, and the fallback form

**(b) is dead if any of these happens:**
- A configuration, with every hypothesis discharged, satisfies all of `EndT`'s clauses except `UpdXW`, while `UpdXW.frame` or `UpdXW.trans` fails for it. That is, the composite of two admitted ends is not an admitted end.
- T4b fails under `UpdXW`. That would be an unsound end: a lend ending while a live copy is outside the lender.

Any of these is shown as a Lean configuration (a `def … : Prop` that elaborates, plus its instance). An informal "it does not go through" is not a kill.

**The fallback form, if (b) covers only part of the space.** The user allows "resource safety, except under these well-defined conditions". If some case cannot be admitted (expected candidate: R1's mixed lifetime sets at one location across `twp_frame`'s parts):
- T1–T3 stay admitted results.
- The excluded configurations become explicit hypotheses **on the frame condition or the resource**, never a list of programs. For example:

```lean
/-- At `ℓ`, every cell of the frame's flattening has the consumed view's lifetime set. -/
def UniformAt (β : Life) (l : BoCa.Loc) {K : WCactus} (ρf : TRes K) : Prop :=
  ∀ τ χ, ResUT.Flat ρf τ → τ.get l = some χ → χ.lsOf = some (TSet.single β)
```

- **The exclusion is a premise.** It is added beside `HoldsView` on `F`, or as a premise on the run's resource (`UniformAt β l Z`) of T1 and of `UpdXW.frame`.
- **It must not be vacuous.** Each exclusion is shown satisfiable at the #793 configuration (`fdMask`/`True` strengthened, the frame `viewRes (lfE 1) 1`).
- **The excluded cases are stated as excluded.** Their refutations are configurations.
- **It is a real exclusion, not a stand-in.** It must be refuted outside its scope, by a configuration. If the needed fact is merely unproved, the step stays open.

## Design choices for the user

- **D-1 (needed for T2/T3).** The spikes' frame conditions (`True`; `fdMask` at the empty mask) admit the empty frame, where any consume is refuted (`twp_refuses_last_copy`). The proposal: the admitted results are stated at those conditions **strengthened by `HoldsView`**. The alternative, keeping them literally, cannot be met by any `↭`.
- **D-2.** The absorber is the end **world** `fρ′` (proposed), not the frame `ρf′`. The frame alone does not carry through `twp_frame` with mixed lifetime sets (an argument, not checked).
- **D-3.** Absorption by lifetime-set inclusion (`CellAbs`/`CellSub`, proposed) versus an exact copy (`XCell` only). Exact copy is smaller and covers every view `twp` builds today (`viewCell α`). It fails R1's mixed-set case, which `STy.imm`'s general `TImm` reaches.
