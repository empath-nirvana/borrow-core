# FIX-RUN-END: the run-end relation `↭` as a field of `SemWorld`

**What this is.** The design that answers verifier finding 1 (the blocker in `AGREE.md`), and the
record of its implementation in the library (§8). Scope: finding 1 only. Findings 2–7 are noted
where this design touches them (§5.6) and are not changed. The review of this design ended with
two unresolved major findings (§Unresolved).

**What is checked.** Every result this file marks **(checked)** is proved in the library at
`SemWorld`: in `Targets/Restricted/RunEnd.lean`, `Targets/Restricted/CoreLaws.lean`
(`wpGW_of_wpG_nil`, the `_of_core` laws and their instances at `coreW`) and
`Targets/Restricted/Corollaries.lean` (`endState_prog`). `lake build Targets` builds them with no
`sorry` and no warning, and `Targets/AxiomCheck.lean` prints `#print axioms` of each, within
`[propext, Classical.choice, Quot.sound]`. The design was first checked at a local copy of
`SemWorld` that carried the field (`SemWorldU`, with `wpGWU`, `ewpWU` and the laws at it, in
`Checks/RunEndDesign.lean`); the library replaces that check. Its names carry over with
`SemWorldU`, `SliceShapeU`, `wpGWU`, `RunFrameU` and `coreWU` read as `SemWorld`, `SliceShape`,
`wpGW`, `RunFrame` and `coreW`, and `*_coreWU` as `*_core`; §8 lists the rest.

**Worlds** are tagged as in DESIGN §0: [Core σ=[]] is `coreW`; [W] is the end state's `M`;
[generic] is every `M`; a witness world is named (`leakW`, `carryW`). Witness worlds exist only to
check the laws of §2 and the exclusion of §3. They are not candidates for W.

---

## 0. The finding, as checked in Lean

At a558a94, `wpGW` (`Targets/Defs/World.lean:100-108`) ended every run under Core's `↭`,
`ResU.UpdV ρ π`, as a fixed conjunct, so no field of `SemWorld` reached it. The verifier's check
is `Targets/Checks/RunEnd.lean`, stated against that `wpGW`. It elaborated there with no warnings,
and its axioms are within `[propext, Classical.choice, Quot.sound]`. Against the field its
`wpGW_iff_runFrame` does not elaborate; each of its results is restated in
`Restricted/RunEnd.lean` (§8). It proves:

- **`wpGW_iff_runFrame`**, at every `M`. `wpGW` is `RunFrame ∧ ResU.UpdV ρ π ∧ Q`, and no field
  enters `UpdV`.
- **`at02_runEnd`, `wpGW_at02`**, at every `M`. Take a `wpGW` run of AT02's handled body from
  the empty configuration whose postcondition admits only values and operation-table stops. It
  ends at `Foo`'s stop, and `⦇π⦈` has no `mut` cell at the lent cell `c`. The proof uses
  determinism (`arun_rest_irr`) and LoopBorrow's `not_upd_of_new_mut`.
- **`at02_held_end`**, at every `M` meeting `SliceShape`, and **`at02_held_end_core`**. Consider
  the end at `Foo` holding the lend as `c ↦ mut(α, inj₁ (), ∅, ⊤)`. That is the shape [TR] 6.65
  gives a lend, and it arises (`held_arises`: `TW.alloc`, then `TW.mutFold`). At the nil index
  this end meets every other conjunct, `M.Fam` and R-T1 included, and fails `↭` alone.
- **`at02_unfolded_end`**, at every `M` meeting `SliceShape`. The same end with `c` unfolded
  (`c ↦ own(inj₁ ())`) meets every conjunct, `↭` included.

**What this establishes.** While `↭` is fixed, no world can end a run at a resuming operation
while holding, *as a borrow cell*, a `Mut` lend that the run opened. That is OQ-9 (a) for a `Mut`
lend, in the shape [TR] 6.65 gives a lend, and in the shape "the share carries the open lend".

There is another way to carry the lend. The cell is unfolded at the stop, and the lend is kept
only in the index. `↭` admits that end. Whether a world built that way can meet `MutFrameW` is not
checked. Meeting it means re-folding at the same lifetime, and LoopBorrow's `refoldKripke_false`
refutes that step only at Core's `Ext`.

**A 6.64 lend at the same stop** (**checked**, `at02_imm_end`, at every `M` meeting
`SliceShape`). End AT02's run at `Foo` in the configuration a 6.64 lend gives:
`c ↦ imm({α}, inj₁ (), ∅)`, with 6.64's record `immRec c` open in the visible frames `ps′` and in
the index `([(immRec c, α)], M.nil)`.

- It arises: `TW.alloc` of the cell, then `TW.immFrame` (`imm_arises`), with the record tagged at
  `α` (`imm_tagged`, by `frameLife_frame`).
- At the nil index it meets every other conjunct of `RunFrame`: the frame, the compositions, both
  lowerings (the end's by 6.26), the run, `NoOwn` and `M.Fam`.
- It fails R-T1, since the frame is open at the end and not at the start. It also fails `↭`
  (`not_updV_empty_immRes`, by LoopBorrow's `not_upd_of_new_imm`). So relaxing `Stop` alone does
  not admit this end.
- `StopVisible` (I2) excludes the same visible frame at every index, nil or not
  (`not_stop_imm_of_stopVisible`).

Scope. The unwinding constant's term is the same for 6.64 and 6.65: `withborUE d` is typed at
`withbor1UTy` (an `Imm` lend) and at `withbor2UTy` (a `Mut` lend). So this is AT02's machine run,
ended in the configuration a 6.64 lend gives. AT02's callback reads through `withswap`, which a
6.64 lend does not type, and no 6.64-typed program is built.

**Side result.** At Core's world, the end that holds the `Mut` lend passes R-T1. A 6.65 lend adds
no 6.64 frame and no record: `TW.mutFold` keeps `ps` and `rs`. So in Core it is `↭` alone that
keeps a `Mut` lend from spanning a stop. At the 6.64 end above, R-T1 and `↭` both fail at the nil
index. DESIGN §1.3's field table puts OQ-9 in `held`, `Fam` and `Stop`. The frame and record lists
those fields read do not see a `Mut` lend, and `Fam` admits the configuration that holds one.

---

## 1. What `↭` does in BoLo, and what reads it

**The definition** is [TR] p. 5, row 18, transcribed as `ResU.UpdV`
(`Paper/S5_Model/Definitions.lean:1742`). `⦇ρ₁⦈` and `⦇ρ₂⦈` must have the same borrows: equal
`imm` cells, and `mut` cells with the same lifetime and predicate. [TR] p. 6's `wp` row ends
every run with `ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)`.

[CONF] 415:23 says what `↭` is for:

> "Since the update relation constrains the reachable borrows to be exactly the same before and
> after running an expression, this definition embodies lexical borrowing. … the discarded
> fragment ρ⁺ must not contain any owned cells. This is essential for the memory reclamation
> component of adequacy (Theorem 3.2)".

Effects relax lexical borrowing. The brief expects "the wp and its stop condition" to change.
`↭` is part of that `wp`.

**Who reads it** (paper lemmas read against `[TR]` pp. 10–17):

| printed | Lean | read by, in Core | what it carries |
|---|---|---|---|
| 6.47, `ρ ↭ ρ` | `ResU.updV_self_iff` | `wpG_here` (`Core/EffWp.lean:962-969`); the value and load rules `wpTS_val`, `wpTS_load`, `wpTS_load_I` (`Core/Wp.lean:539, 661, 689`); `alloc_block` (`Core/ArrayWp.lean:73`) | a run that changes no cell |
| "`↭` ignores own cells", the step 6.141, 6.142 and 6.145 each take in one line | `updV_compS_own` (`Support/Model/Entailments.lean:311`) | `wpTS_alloc`, `wpTS_free`, `wpTS_store` (`Core/Wp.lean:606, 634, 729-731`); `alloc_world` (`Core/ArrayWp.lean:45`); `wpAt_alloc` (`Core/Blocks.lean:222`) | a run that adds or removes an own cell |
| 6.48, framing | `updV_frame` | `wpG_bind` (`EffWp.lean:878`, last step `:910-911`), `wpG_ramify` (`:978`, `:1001`), the `wpTS` forms in `Core/Wp.lean` | a resource framed through a run |
| 6.49, transitivity | `ResU.UpdV.trans` | `wpG_bind` (`:910`), `wpTS_store` (`Wp.lean:729`), `wpAt_alloc` (`Blocks.lean:222`) | two runs in sequence |
| 6.50 | `updV_outlives` | `wpTS_box` (6.147, `Core/Wp.lean:799-805`) | outlives survives a run |
| 6.27, 6.28, 6.29, 6.38, 6.39 | `ResU.six27`, `six28`, `six29`, `six38`, `six39` | the frame rules 6.64/6.65 and the anti-frame 6.66 (`Core/FrameRules.lean:157-223, 424, 508, 696`; at `wpG`, `EffWp.lean:174-240` in `wpG_I_frameX`, `:441, 525` in `wpG_M_frameX`, `:713` in `wpG_M_antiFrameX`) | at the end of the callback's run the lend is back in `π = ρ′ ● ρ⁺`, at the top, and `↭` survives folding and unfolding it |
| adequacy's reclaim | `reclaim` (`Core/Fundamental.lean:534`) | `theorem32` (`:558`), `theorem32D` (`Core/Demonic.lean:292`) | `∅ ↭ ρ⁺` and `ρ⁺∣own = ∅` force `ρ⁺ = ∅`, so nothing leaks |

**Safety does not read `↭`.** No stuck run means no use after free, and `wpTS_demonic` and
`wpTSD_safe` (`Core/Demonic.lean:240-262`) get it from two facts only: a run exists under the
allocator that replays the given run, and the machine is deterministic. Across a stop, the
continuation's run starts from the configuration the stop ended in, which is in `M.Fam`.

So the run-end relation is consumed by the steps that change no cell or only an own cell (6.47,
the own-cell step), by framing and sequencing (6.48, 6.49), by the box rule (6.50), by the frame
rules (6.27–6.29, 6.38, 6.39: the lend comes back), and by reclaim (nothing leaks).

---

## 2. The change

### 2.1 The field, and `wpGW`

```lean
structure SemWorld where
  Stk   : Type
  nil   : Stk
  /-- What the suspended computations at an index hold: their open 6.64 frames and their tagged
  records.  Where they are kept is OQ-9's question; under its option (b) nothing is held.  A
  6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not see it; a world that carries
  one open across a stop accounts for it through `Upd` and the index, either as a borrow cell in
  the run's resource or unfolded with the lend recorded in the index (OQ-9 (a), OQ-44). -/
  held  : Idx Stk → List FrameRec × List SRec
  Fam   : WRes → List FrameRec → Idx Stk → Prop
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  /-- The run-end relation: a run from the resource `ρ` at the index `i` may end at the index `i′`
  with `π = ρ′ ● ρ⁺`, its postcondition holding `ρ′`.  Core's is `↭` ([TR] p. 5 row 18,
  `ResU.UpdV ρ π`), which reads neither index nor `ρ′`.  On the nil slice it is Core's
  (`SliceShape`).  Whether, and how, a run may end holding a lend it opened is OQ-9's
  question. -/
  Upd   : Idx Stk → Idx Stk → WRes → WRes → WRes → Prop
  Ext   : Idx Stk → Idx Stk → WRes → Prop
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont →
            (Idx Stk → Expr → WProp) → WProp
  payStk : Life → Stk → Stk
  val   : Bool → VTy → Idx Stk → LSub → Val → WProp
  comp  : CTy → Idx Stk → LSub → Expr → WProp

/-- W's one-run wp: `wpG` over `M.Fam`, ending under `M.Stop` and `M.Upd`. -/
def wpGW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Q : Idx M.Stk → Expr → WProp) : WProp :=
  fun ρ => ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    M.Fam fρ ps i → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (i' : Idx M.Stk),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ (∃ k', ARun A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ M.Upd i i' ρ ρ' π ∧ NoOwn ρp ∧
      M.Fam fρ'p ps' i' ∧ M.Stop (ps, i) (ps', i') t ∧ Q i' t ρ'
```

`coreW` gains `Upd _ _ ρ _ π := ResU.UpdV ρ π`. The run-end conjunct stays where `UpdV` was, so
`wpGW` still has thirteen conjuncts in the same order. At `coreW` (reducible) the conjunct unfolds
to `ResU.UpdV ρ π`, and `wpGW_core` stays an unfolding: at the check's copy, `wpGWU coreWU` is
`wpGW coreW` by `Iff.rfl` (`wpGWU_core`, **checked**).

**Why the field reads the two indices.** The pin (§2.2) holds the relation to Core's on the nil
slice and leaves it open everywhere else.

**Why it reads the post's resource `ρ′`: a choice.** `theorem32D` uses `↭` once, at the end of
the top-level run (`Core/Demonic.lean:300-306`). The post is `⌜P v⌝`, so `ρ′ = ∅` (`subst hρ'e`),
`π = ρ⁺`, and `reclaim` is applied to `∅ ↭ ρ⁺`. At W, the law that carries this step
(`UpdReclaim`, §2.3 (b)) has to tell an end whose post holds nothing from an end whose post holds
a lend. Two ends of AT02 have the same `(i, i′, ρ, π)`:

| end | post `ρ′` | garbage `ρ⁺` | `π` |
|---|---|---|---|
| the lend held, at `Foo`'s stop | `c ↦ mut(α, …)` (the share's) | `∅` | `c ↦ mut(α, …)` |
| the cell leaked, at a value | `∅` | `c ↦ mut(α, …)` | `c ↦ mut(α, …)` |

This design reads `ρ′` so that `UpdReclaim` separates the post from the garbage with no law about
which index a value end reaches. `ρ′` is not forced. The alternative is a four-argument relation
`Upd i i′ ρ π` with the distinction moved to the index: reclaim stated only at ends on the nil
stack, and a law that a data-valued end of the top-level run is on the nil stack, so that the pin
gives Core's `reclaim` there. Since `Stop` sees the final term, that law can be a stop condition.
It has to be stated so as not to exclude an end that carries a lend at a value. Under the reading
of σ the pin uses (§2.2), a run that returns a thunk holding a suspended lend (§4.2's example)
ends at a value off the nil stack, so a law that every value end keeps its start's stack would
exclude it. Across platform answers the top-level run is a chain, and its last run need not start
on the nil stack. This design does not take that route, and does not claim it fails.

`upd2Reclaim_excludes_held` (**checked**) shows only that a four-argument reclaim law excludes the
held end at every end index it is stated at. It says nothing about the alternative.

**What the field does not read.** It does not see the term or the visible frames; `Stop` sees
those. Nothing derived below needs them in the run-end relation. A world that wants lends carried
only across stops can tie the two together through the index, which both fields see.

### 2.2 The pin, in done (`SliceShape`)

```lean
def SliceShape (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧
  (∀ b, M.payStk b M.nil = M.nil)
```

**The `←` half: the embedding.**

- DESIGN §4.2 reads "vC/cC are the σ = [] instance" as a structural nil slice plus an embedding of
  Core into W. The run-level content of that reading is `wpGW_of_wpG_nil` ([generic],
  **checked**): at every world meeting `SliceShape`, a `wpG` run is a `wpGW` run at
  `(ls, M.nil)`, ending at `(ls′, M.nil)`.
- It reads the `Fam` pin in both directions (the start's configuration is Core's, the end's is
  W's), and the `←` halves of the `Stop` and `Upd` pins.
- Without the `←` half of the `Upd` pin, a world whose relation at σ = [] is stricter than `↭`
  would meet `SliceShape`, and `SliceShape` would no longer give the embedding.
- `ConservativeWB` and `Conservative` at W go through it (§5.6, finding 3).

**The `→` half: kept for uniformity, and the one upper bound it gives.**

- No derived result in this design reads it. These checks do: `at02_runEnd_nil`, and
  `at02_held_end` and `at02_imm_end` as restated for the field (§5.2; each end fails `M.Upd` at
  its nil index), and `not_sliceShape_of_updTop` (**checked**).
- It is kept so that σ = [] means one thing across the pinned fields: at σ = [] the
  configurations, the stop and the run end are Core's.
- That uniformity is weaker than it looks. For `Fam` and `Stop`, conjuncts of done already bound
  the field from above at every index (`Arises`, `StopVisible`), and the `→` halves of their pins
  are nil-slice versions of those bounds. For `Upd` no conjunct of done does. Apart from
  `Adequate`'s leak bound (§3), the `→` half is the only upper bound on `M.Upd` that done is shown
  to place.
- It is the source of the constraint on OQ-44 below. AGREE asks the user to confirm it
  (decision 10).
- Pinning `←` alone would drop that constraint and those checks; no derived result of this design
  would change. Layer 3 (§3), the exclusion of a reachable leak, does not read the pin.

**What the pin bounds.** The `→` half bounds run ends from the nil slice to the nil slice. It does
not bound W's runs. In `wpGW` the end index `i′` is chosen with the end, and a run from σ = [] may
end off the nil slice, where neither `Stop` nor `Upd` is pinned. In `leakW` (§3, Layer 3) a
leaking run does. What bounds those runs from above is `Adequate` (§3, Layer 3) and, on the
generic route to adequacy, `UpdReclaim`, which quantifies over every end index (§2.3 (b)).

`coreW` is unaffected. Every index of `coreW` is nil, so `Upd` is `UpdV` at every index
(`sliceShape_coreWU`, `coreWU_upd`, by `Iff.rfl`, **checked**).

**The reading of σ = [] that the `→` half fixes: a constraint on OQ-44.**

- With the `Fam` pin, the `→` half reads σ = [] as "no lend is carried open anywhere in the
  configuration": not by the running computation, not in the frame, and not inside a suspension
  stored in a cell or held as a value (I1 and AT17 move suspensions as values). Under that reading
  a run that starts and ends at σ = [] carries no lend at either end, and Core's lexical `↭` is the
  right relation there whichever OQ-9 option is taken.
- Under a per-computation reading, σ counts only the lends the running computation carries. Then
  a run at σ = [] can resume a stored `κ` and close the `Mut` lend `κ` carries. The `Fam` pin
  admits the configuration, since `TW.mutFold` records nothing. If that run ends at σ = [], the
  `→` half makes its run end Core's `↭`, which it fails: `↭` forbids a run to end a borrow cell it
  started with (LoopBorrow's `not_upd_lend_ended`). So under a per-computation reading such a run
  must end off the nil slice, although it carries nothing at its end.
- `carryW` (§4) fits only the configuration-wide reading. The configuration holding the lend is
  also reached at the empty stack (`fam_nil_held_carryW`, **checked**). From there, no run whose
  resource holds the lend and that closes it has an end index (`not_close_from_nil_carryW`,
  **checked**).
- This is a constraint the end state places on OQ-44. It is no stricter than the old fixed `↭`,
  which applied at every index. It is AGREE decision 10.

**What the pin leaves open.** It says nothing about a run that starts or ends off the nil slice.
It covers every index whose stack is nil, whatever its records. So a run from the nil slice that
ends holding a new borrow cell has to end at a stack that is not nil.

### 2.3 What else constrains the field

**(a) The conjuncts of done that read it.** None of these statements changes. `M.Upd` is a
conjunct of the end a `wpGW` run provides, so it occurs positively in `wpGW` and in `ewpW`. Where a
conjunct has `wpGW` or `ewpW` decides what it does to `M.Upd`.

- **`Adequate` bounds it from above.** `M.comp` is in `Adequate`'s hypothesis, and through
  `EffInterp`, `M.comp` at an unr-free `F_S A` is W's runs. A weaker `Upd` admits more runs, so
  more programs at `([], M.nil)` from `∅`, and `Adequate` asks each of them to run safely to the
  empty memory. With `DataVals` (a data post holds nothing) it excludes a reachable leak. §3,
  Layer 3 checks this at a world that meets the pin, `EffInterp` and `DataVals`. It bounds leaks:
  it sees only what reaches the machine.
- **`ConservativeWB` and the pin's embedding bound it from below.** `ConservativeWB` asks W's
  relation to contain Core's values at row-abortive types. Through `RelElim` and `EffInterp` that
  asks `ewpW` to contain Core's runs at those types, which a weaker `Upd` makes easier.
  `wpGW_of_wpG_nil` (§2.2) is the same direction on the nil slice. `ShareCancel` asks for a
  cancel run in `ewpW`, which is the same direction.
- **The rule-shaped conjuncts are not monotone.** `FramesW` (`MutFrameUW`, `ImmFrameUW`,
  `MutFrameW`, `ImmFrameW`) and `SpanBorrows` in `I2`, `I5` (`I5beta`, `AntiFrameW`, `FrameW`),
  `I1`, `P11` (`HandleCompat`, `RedLaws`) and `FL` have `wpGW` or `ewpW` on both sides. It is in
  the callback's run under `─⋆` to the left of `Entails`, in a premise's run, in a share, or in a
  context's relation, and also in the conclusion. A weaker `Upd` weakens what they assume of the
  inner run and what they ask of the outer one, so neither "a weaker `Upd` makes them easier" nor
  "harder" holds in general. This design records no bound from them in either direction.

  They are not neutral either. A sketch, not built: at a world whose `Upd` lets a run end without a
  `mut` cell it started with (`leakW` is one, at a run from the nil slice that ends off it),
  `MutFrameUW`'s premise holds of a callback that frees the lent cell and returns, for a `Q` that
  asks for the cell, while its conclusion asks the lender's run to end holding a cell the memory
  no longer has. So the frames can exclude a world whose `Upd` drops a lend. The dropped lend is
  not a leak (the cell is freed), and `Adequate` does not see it. Which worlds the frames exclude
  is not established.

The rule-shaped conjuncts are where Core's proofs consume `↭`'s borrow content. The frame rules
read 6.27–6.29, 6.38 and 6.39 at the end of the callback's run: the lend is back at the top of
`π` (`Core/EffWp.lean:174-240, 441, 525`). The anti-frame reads 6.28 (`:713`). Framing and `bind`
read 6.48 and 6.49, `box` reads 6.50, the alloc, free, store, array and block rules read the
own-cell step, and the value and load rules read 6.47.

A W's proof of FL and of the frames by the printed route reads `M.Upd` through the W-level forms
of those lemmas, (d) below. Stated at every pair of indices, two of them exclude the two runs
that OQ-9 (a) with the cell kept makes of AT02. `UpdOutlives` fails at every world that admits
the held end, and `UpdMutBack` at every world that admits the run closing it ((d):
`not_updOutlives_of_opened`, `not_updMutBack_of_closed`). So a W that admits those runs cannot
take the printed route with those forms. It needs other forms off the nil slice, and what they
are is OQ-9 (a)'s and OQ-44's open question. That is a requirement on how W's proofs go. It is not
a bound done places on `M.Upd`.

**What done constrains of `Upd`'s borrow content.** Off the nil slice, no conjunct of done is
shown to constrain it. `Adequate` bounds leaks only. The rule-shaped conjuncts read
`M.Upd` on both sides, with no bound established in either direction. The conjuncts that carry
the borrow guarantees at W (`Arises`, `Exclusive`, `LifetimeSound`) do not read it (§3,
Layer 1b). The lend-back laws of (d) are where that content lives, and their form off the nil
slice is the open part of the field's specification.

`Arises`, `StopVisible`, `ShareResume`, `Exclusive` and `LifetimeSound` do not read `wpGW`.
`AdequateEvery` has `M.comp` in its hypothesis, but its conclusion is that a run continues to a
value or a stop of the row, which the replay gives of every program in `ewpW` whatever `Upd` is
(`wpTS_demonic`'s replay reads no run-end conjunct); it is not counted as a bound. The
program-level conjuncts do not read `M` (§3, Layer 1).

**(b) The generic route to adequacy.** These are hypotheses of `AdequateOfLaws`. They are **not**
conjuncts of done.

```lean
/-- **6.48 then 6.49 at W**, as `wpG_bind` composes two runs (`Core/EffWp.lean:910-911`): a run
from `ρ` at `i` ending at `i₁` with `π₁ = ρ′₁ ● ρ⁺₁`, then a run from `ρ′₁` at `i₁` ending at `i₂`
with `π₂`, together end at `i₂` with `ρ⁺₁ ● π₂`. -/
def UpdSeq (M : SemWorld) : Prop :=
  ∀ (i i₁ i₂ : Idx M.Stk) (ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π : WRes),
    M.Upd i i₁ ρ ρ'₁ π₁ → ResU.CompS ρ'₁ ρp₁ π₁ → M.Upd i₁ i₂ ρ'₁ ρ'₂ π₂ →
    ResU.Hash ρp₁ π₂ → ResU.CompS ρp₁ π₂ π → M.Upd i i₂ ρ ρ'₂ π

/-- **Reclaim at W** (`reclaim`, at `theorem32D`'s end): a run from the empty resource at σ = []
whose postcondition holds nothing leaves nothing borrowed, whatever index it ends at. -/
def UpdReclaim (M : SemWorld) : Prop :=
  ∀ (i' : Idx M.Stk) (π : WRes),
    M.Upd ([], M.nil) i' PMap.empty PMap.empty π → NoOwn π → π = PMap.empty

def AdequateOfLaws : Prop :=
  ∀ M : SemWorld, WLaws M → ShareResume M → UpdSeq M → UpdReclaim M → Adequate M
```

**Why they are hypotheses.** `AdequateOfLaws`'s proof is the replay and reclaim of
`wpTS_demonic` and `theorem32D` over `wpGW`. Two of its steps read the run end. Chained runs are
composed as `wpG_bind`'s last step composes them (`UpdV.trans` after `updV_frame`,
`Core/EffWp.lean:910-911`), and the garbage is emptied by `theorem32D`'s `reclaim`
(`Core/Demonic.lean:300-306`). While `↭` was fixed, both steps were Core's lemmas about the fixed
conjunct. With `↭` a field, the proof needs them as properties of `M.Upd`, so they are named
hypotheses, as `ShareResume` already is. The conclusion is unchanged. Both hold wherever `Upd` is
Core's at every index (`updSeq_of_core`, `updReclaim_of_core`, **checked**), so at `coreW`
nothing is lost.

I have not derived that `AdequateOfLaws` with the pin alone (without `UpdSeq` and `UpdReclaim`)
fails, and have not verified that any obstruction is real.

How each one is used:

- **A single run** (`Platform.none`, `theorem32D`). The run goes from `∅` at `([], M.nil)` to a
  value at some `i′`. `DataVals` at `i′` gives `ρ′ = ∅`, so `π = ρ⁺`. `UpdReclaim` gives
  `ρ⁺ = ∅`, and `Lower ∅ μ′` then gives the empty memory.
- **A chain across platform answers** (`AdequateRetAt` at a platform with operations). Run *k*
  ends at a stop at index `iₖ` with `π_k = ρ′_k ● ρ⁺_k`. The argument is data, so the post's `PA`
  part is `∅` and the share is all of `ρ′_k`. `ShareResume` at `iₖ` (reflexivity of `ExtPre`)
  gives the next run, from `ρ′_k`, with the garbage so far in its frame. `UpdSeq` composes the
  two, exactly as `wpG_bind` does. The composite ends at a value with post `∅`, and `UpdReclaim`
  empties the accumulated garbage.
- **A drive** (`AdequateDriveAt`, through `SafeDrive` and `FinalDrive` with the memory empty).
  `main` runs to a loop value, and each observation `nextE l` is a run from the loop's resource.
  `UpdSeq` composes each observation's run with the runs before it, as across platform answers.
  A finished drive answers `inj₁ a` with `a` data, so its post is `∅` (`RelShape`'s sum clause,
  then `DataVals`), and `UpdReclaim` empties the accumulated garbage.

**Decision: none of the laws of (b) and (d) is a conjunct of done.**

- Done already holds `Adequate M`, the guarantee `UpdSeq` and `UpdReclaim` serve, and `FL M J`,
  the target the laws of (d) serve.
- Moving them into `WLaws` would add device laws to done, which is finding 6's concern.
- It would also oblige every world under option (a) to compose its own accounting of carried
  lends, even a world that proves `Adequate` directly.
- Stated at every pair of indices, `UpdOutlives` and `UpdLendBack` exclude every world that admits
  the runs OQ-9 (a) with the cell kept makes of AT02, whatever predicate the world gives the lend
  ((d)). In done, they would make done exclude every such world, which is a choice against that
  shape of OQ-9 (a).

The decision can be reversed for `UpdReclaim`. Putting it in `WLaws` would bound `M.Upd` from
above in done itself, for leaks from an empty start at every end index. `AGREE.md` asks the user
to confirm (decision 9, §5.4).

**(c) No use after free.** No condition on `Upd` is needed (§1).

**(d) The W-level forms of Core's `↭` lemmas.** FL at W, `FramesW` at W and `AdequateOfLaws`'s
proof read `M.Upd` through these. Each is defined beside done and not in it, stated at every pair
of indices, in the shape Core's proof reads the printed lemma. The anti-frame (6.66) reads 6.28 in
the other direction (`Core/EffWp.lean:713`). That form is not stated here.

| family | Core | read by, in Core | at W | where `Upd` is Core's at every index | at `carryW` (§4) |
|---|---|---|---|---|---|
| 6.47 | `ResU.updV_self_iff` | `wpG_here`, `wpTS_val`, `wpTS_load`, `wpTS_load_I`, `alloc_block` | `UpdRefl` | `updRefl_of_core` (**checked**) | `updRefl_carryW` (**checked**) |
| the own-cell step | `updV_compS_own` | `wpTS_alloc`, `wpTS_free`, `wpTS_store`, `alloc_world`, `wpAt_alloc` | `UpdOwn` | `updOwn_of_core` (**checked**) | `updOwn_carryW` (**checked**) |
| 6.48 then 6.49 | `updV_frame`, `ResU.UpdV.trans` | `wpG_bind`, `wpTS_bind`; with no garbage, the transitivity `wpTS_store` and `wpAt_alloc` use | `UpdSeq`, (b) | `updSeq_of_core` (**checked**) | `updSeq_carryW` (**checked**) |
| reclaim | `reclaim` | `theorem32`, `theorem32D` | `UpdReclaim`, (b) | `updReclaim_of_core` (**checked**) | `updReclaim_carryW` (**checked**); at `leakW` it **fails** (`not_updReclaim_leakW`, **checked**) |
| 6.48, into the post | `updV_frame` | `wpG_ramify`, `ewp_frame_plain` (`FrameW`) | `UpdFrame` | `updFrame_of_core` (**checked**) | not checked |
| 6.50 | `updV_outlives` | `wpTS_box` (6.147) | `UpdOutlives` | `updOutlives_of_core` (**checked**) | **fails** (`not_updOutlives_carryW`, **checked**) |
| 6.27, 6.28 | `ResU.six27`, `six28` | `wpG_M_frameX` (6.65) | `UpdMutBack` | `updMutBack_of_core` (**checked**) | **fails** (`not_updLendBack_carryW`, **checked**) |
| 6.29, 6.38, 6.39 | `ResU.six29`, `six38`, `six39` | `wpG_I_frameX` (6.64) | `UpdImmBack` | `updImmBack_of_core` (**checked**) | not checked (`carryW` carries `mut` cells only) |

`UpdLendBack` is `UpdMutBack ∧ UpdImmBack` (`updLendBack_of_core`, **checked**). At `coreWU` all
seven hold (`updRefl_coreWU`, `updOwn_coreWU`, `updSeq_coreWU`, `updReclaim_coreWU`,
`updFrame_coreWU`, `updOutlives_coreWU`, `updLendBack_coreWU`, **checked**).

```lean
/-- **6.47 at W** (what `wpGW_here` and the value and load rules read, as `wpG_here` reads
`ResU.updV_self_iff`, `Core/EffWp.lean:969`): from a configuration W reaches, a run that changes no
cell ends at its own index with its resource as the post and no garbage. -/
def UpdRefl (M : SemWorld) : Prop :=
  ∀ (i : Idx M.Stk) (ρf ρ fρ : WRes) (ps : List FrameRec),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i → M.Upd i i ρ ρ ρ

/-- **The own-cell step at W** (`updV_compS_own`, as the alloc and free rules read it,
`Core/Wp.lean:606, 634`): from a configuration W reaches, a run that adds an own cell the frame
does not hold, or removes one, ends at its own index with the result as the post. -/
def UpdOwn (M : SemWorld) : Prop :=
  (∀ (i : Idx M.Stk) (ρf ρ fρ ρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → M.Fam fρ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → ResU.Hash ρf ρ₁ → M.Upd i i ρ ρ₁ ρ₁) ∧
  (∀ (i : Idx M.Stk) (ρf ρ ρ₁ fρ₁ : WRes) (ps : List FrameRec) (l : Loc) (v : Val),
    ResU.Hash ρf ρ₁ → ResU.CompS ρf ρ₁ fρ₁ → M.Fam fρ₁ ps i →
    ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁ → M.Upd i i ρ₁ ρ ρ)

/-- **6.48 into the post at W** (`updV_frame`, as `wpG_ramify` reads it,
`Core/EffWp.lean:1001`): a resource `ρ₂` framed through a run from `ρ₁` that ends at
`π₁ = ρ′₁ ● ρ⁺` is in the post, at the same two indices. -/
def UpdFrame (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ₁ ρ₂ ρ ρ'₁ π₁ ρ' π : WRes),
    M.Upd i i' ρ₁ ρ'₁ π₁ → ResU.CompS ρ₂ ρ₁ ρ → ResU.Hash ρ₂ ρ₁ →
    ResU.CompS ρ₂ π₁ π → ResU.Hash ρ₂ π₁ → ResU.CompS ρ'₁ ρ₂ ρ' → M.Upd i i' ρ ρ' π

/-- **6.50 at W** (`updV_outlives`, as `wpTS_box` reads it, `Core/Wp.lean:805`). -/
def UpdOutlives (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (ρ ρ' π : WRes) (α : Life),
    BoLo.Outlives ρ α → M.Upd i i' ρ ρ' π → BoLo.Outlives π α

/-- **6.27 then 6.28 at W**, as `wpG_M_frameX` reads them (`Core/EffWp.lean:441, 525`): the lend
is back at the top of `π`, and the run with it unfolded at both ends, its post the callback's with
the cell unfolded into it, ends at the same indices. -/
def UpdMutBack (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (l : Loc) (α : Life) (v : Val) (ρv ρb BM ρ' π : WRes)
    (h : ρv.InStratum α) (P : Val → SPropS Loc Val α) (hw : P v ⟨ρv, h⟩),
    BoLo.Outlives ρb α → ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρv h P hw)) BM →
    M.Upd i i' BM ρ' π →
    ∃ (v' : Val) (χ : WRes) (h' : χ.InStratum α) (hw' : P v' ⟨χ, h'⟩),
      ResU.CompS (π.del l) (ResU.single l (CellU.mutOf α v' χ h' P hw')) π ∧
      ∀ (W W' O O' ρ'' : WRes), ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W →
        ResU.CompS χ (ResU.single l (CellU.ownOf v')) W' → ResU.CompS ρb W O →
        ResU.CompS (π.del l) W' O' → ResU.CompS ρ' W' ρ'' → ResU.Valid O → ResU.Valid O' →
        M.Upd i i' O ρ'' O'

/-- **6.29, 6.38 and 6.39 at W**, as `wpG_I_frameX` reads them (`Core/EffWp.lean:174-240`). -/
def UpdImmBack (M : SemWorld) : Prop :=
  ∀ (i i' : Idx M.Stk) (l : Loc) (α : Life) (v : Val) (ρv ρb W BI ρ' ρp π : WRes)
    (h : ρv.InStratum (LSet.singleton α).join),
    ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W → ResU.Hash ρb W →
    BoLo.Outlives ρb α → BoLo.Outlives ρ' α → ResU.Hash ρ' ρp → NoOwn ρp →
    ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton α) v ρv h)) BI →
    ResU.CompS ρ' ρp π → M.Upd i i' BI ρ' π →
    ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton α) v ρv h)) π ∧
    ResU.Hash (π.del l) W ∧
    ∀ (O O' ρ'' : WRes), ResU.CompS ρb W O → ResU.CompS (π.del l) W O' →
      ResU.CompS ρ' W ρ'' → M.Upd i i' O ρ'' O'

def UpdLendBack (M : SemWorld) : Prop := UpdMutBack M ∧ UpdImmBack M
```

`UpdRefl` and `UpdOwn` read the configuration the run starts in (`M.Fam`), as `wpG_here` and
`wpTS_alloc` have it: at a world that carries lends, whether a cell of `ρ` is a carried one
depends on the stack, and the stack's cells sit in the full configuration (§4).

**Where the printed forms exclude a carried lend** (**checked**, at every `M`).

- `not_updOutlives_of_opened`: a world whose `Upd` lets a run from `∅` end with a `mut` cell at
  `α` at the top of its end (`π(c) = mut(α, v, χ, P̂)`, any `v`, `χ`, `P̂`, anything else in `π`)
  fails `UpdOutlives`. The run's resource outlives every lifetime, and its end holds a borrow at
  `α`.
- `not_updMutBack_of_closed`: a world whose `Upd` lets a run that starts with `c ↦ mut(α, …)` at
  the top, beside a resource that outlives `α`, end with no cell at `c` fails `UpdMutBack`, so
  `UpdLendBack`. 6.27 asks the lend to be back at the top of that end.
- These are the two runs OQ-9 (a) with the cell kept makes of AT02: the held end
  (`at02_held_end_carry`, §4) and the run that closes the lend later (`upd_close_carryW`).
  `carryW` admits both, so it fails both forms (`not_updOutlives_carryW` by `heldRes_get`,
  `not_updLendBack_carryW`).
- Both refuting instances start and end in configurations `carryW` reaches: `∅` at `([], ∅)`, and
  the lend at `([], heldRes c α)` (the two `carryW.Fam` conjuncts of `at02_held_end_carry`). The
  four forms read no configuration, as the printed lemmas do not.
- The frame rules apply 6.27 to a lend they have just made, which no index carries at the
  callback's start. A form restricted that way needs a notion of what an index carries, which
  `SemWorld` does not have (OQ-44). It is not stated here.

**(e) The freeze binder** (beside done). It acts on every field, so it gains one clause in each
half:

```lean
-- FreezeBinderLoc, beside the Stop clause:
(∀ π i i' (ρ₁ ρ₂ ρ₃ : WRes), M.Upd i i' ρ₁ ρ₂ ρ₃ ↔
   M.Upd (idxLocAct a π i) (idxLocAct a π i') (ρ₁.mapLoc π) (ρ₂.mapLoc π) (ρ₃.mapLoc π))
-- FreezeBinderLife, forward:
(∀ c (θ : Restrat.Emb c) i i' (ρ₁ ρ₂ ρ₃ : WRes), M.Upd i i' ρ₁ ρ₂ ρ₃ →
   M.Upd (idxLifeAct a θ i) (idxLifeAct a θ i') (θ.relRU ρ₁) (θ.relRU ρ₂) (θ.relRU ρ₃))
```

---

## 3. A degenerate world does not satisfy done

The task asks for this to be checked explicitly. The answer comes in five layers. Layers 1 and 1b
are what make it hold; Layer 3 is the device-level check.

**Layer 1: the program-level guarantees do not mention M.**

- Done's [prog] conjuncts are statements about `J` and programs. They do not mention `M`.
- **`endState_prog`** ([generic], **checked** at the library's `EndStateAt`) projects them out.
  Its conclusion is `RowAlgSafe RF ∧ RowLink RF ∧ AdmExtends Adm ∧ Tier2Pinned J Adm ∧
  AcceptsTier2 J ∧ I4a J Adm .any ∧ ExtendsNU J ∧ OutExtends J.out ∧ Soundness J ∧
  SoundnessContracts J ∧ ReleasedOnceAll J ∧ EffSafe J ∧ NoInterception J ∧ FinaliserOrder J`,
  and it holds for every `M`. (`ReleasedOnceAll J` is a tautology about runs, not a guarantee:
  RESTRUCTURE §2.4, finding #2. The restructured library's `combined_prog` projects B4 (`Sound J`)
  and B5 at closed programs (`ReleasedOnceReuse₀ J`) in its place, with A's properties at every
  admissible effect context.)
- With `i2Prog_of_endState` (already proved), done gives that AT02, AT04 and AT12 are typed,
  never stuck under any platform that respects its protocol, and end with the memory empty.
  These are the programs whose lends span stops.
- So no world, and no run-end relation, can make these guarantees true: done asserts them of
  `J`.
- On the device side, `SoundnessOfFL` (`FL M J → Adequate M → Soundness J`, proved, [generic])
  reads no `Upd`, so it is unaffected.

**Layer 1b: the borrow guarantees stated only at W do not read `Upd`.** Two borrow guarantees in
done have no program-level form: P10 `Exclusive M` and P9 `LifetimeSound M J.out`
(`Statements/Lifetimes.lean`: P9 "has no program-level form here").

- `Exclusive` (`Statements/Exclusivity.lean:25`) reads only `M.Fam` and `M.held`. Every
  configuration in `M.Fam` satisfies the aliasing invariant, counting the loans `held` names.
- `M.Fam` is a conjunct of every run end `wpGW` provides, separate from `M.Upd`. So a run end
  that a weaker `Upd` admits still lands in `M.Fam`, where `Exclusive` and `Arises` hold.
- `LifetimeSound` (`Statements/Lifetimes.lean:29`) reads only `M.val`.
- So the truth of neither depends on `M.Upd`. Two worlds that differ only in `Upd` meet both or
  neither, and a weaker `Upd` weakens neither.

**Layer 2: a sanity check on the pin.**

```lean
theorem not_sliceShape_of_updTop {M : SemWorld} (h : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π) :
    ¬ SliceShape M
```

- **Checked** at `SemWorldU`. The proof instantiates the pin at `([], M.nil)`, `([], M.nil)`,
  `∅`, `∅` and `mutCell c α v`. That would give `ResU.UpdV ∅ (mutCell c α v)`, and
  `not_updV_empty_of_held` refutes it.
- It reads only the `→` half. It excludes only a relation that relates everything on the nil
  slice too, which the pin rules out by definition. A relation that relates everything off the
  nil slice meets the pin (§2.2). Non-degeneracy off the nil slice rests on Layers 1, 1b and 3.

**Layer 3: a world whose `Upd` admits a reachable leak fails `Adequate`.**

```lean
/-- From every configuration `M.Fam` reaches at σ = [], a fresh cell left behind as a `mut` cell
ends a run at a value, at some end index. -/
def LeakAt (M : SemWorld) (α : Life) : Prop :=
  ∀ (ρf fρ'p : WRes) (ps : List FrameRec) (c : Loc) (v : Val),
    M.Fam ρf ps ([], M.nil) → ResU.CompS ρf (mutCell c α v) fρ'p → ResU.Valid fρ'p →
    ∃ i', M.Upd ([], M.nil) i' PMap.empty PMap.empty (mutCell c α v) ∧ M.Fam fρ'p ps i' ∧
      M.Stop (ps, ([], M.nil)) (ps, i') (.val .unit)

/-- Allocate a cell and return `()` with the cell still allocated. -/
def leakProg : Expr := bindE (.app alloc' (.inj₁ unit')) unit'

theorem not_adequate_of_leak {M : SemWorld} {α : Life} (hE : EffInterp M) (hD : DataVals M)
    (hL : LeakAt M α) : ¬ Adequate M
theorem not_endState_of_leak {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm}
    {α : Life} (hL : LeakAt M α) : ¬ EndStateAt J M Adm RF
```

How `not_adequate_of_leak` goes (**checked**, at `AdequateRetAt M Platform.none`, which
`Adequate M` gives through `platformNone_respects`):

1. Take any start configuration at `([], M.nil)` (frame `ρf`, run resource `∅`), any allocator
   `A` and any count `k`. The run of `leakProg` is an allocation followed by a β step
   (`leakProg_run`). It ends at `val ()`.
2. The end has `ρ′ = ∅`, `ρ⁺ = mutCell c α (inj₁ ())`, `NoOwn ρ⁺`, and the lowering
   `μ.upd c (inj₁ ())`. Each obligation comes from the start's `ResU.Hash ρf ∅`, the premise
   `wpGW` hands every run, and not from a pin:
   - a lowering `μ` of `ρf` from `lower_of_hash`, and `c = A.pick k μ 1` fresh by `Alloc.fresh`;
   - `ρf # c ↦ own(inj₁ ())` and its lowering from `hash_compS_own`;
   - `ρf # mutCell c α (inj₁ ())` by 6.24 (`ResU.six24`), so the end configuration
     `ρf ● mutCell c α (inj₁ ())` is defined and valid;
   - its lowering to `μ.upd c (inj₁ ())` by 6.25 under a frame (`ResU.lower_swap_mut_own`).
3. `LeakAt` supplies `Upd`, `Fam` and `Stop` at that end. `DataVals` supplies the post at `i′`.
4. So `wpGW`, then `ewpW` (one unfolding, at a value end), then `M.comp (F 1)` through `EffInterp`
   at the row `[]`, hold of `leakProg` at `([], M.nil)` from `∅`.
5. `AdequateRetAt M Platform.none` then requires `SafeRuns`. Under `Platform.none` the run reaches
   `val ()` with `c` allocated. That configuration is not `Final`, and it takes no step
   (`no_pstep_val`). So `¬ AdequateRetAt M Platform.none`, and `¬ Adequate M`.

`not_endState_of_leak` follows: `EndStateAt` holds `WLaws` (so `EffInterp` and `DataVals`) and
`Adequate`. It is new (§5.2): it is stated at the library's `EndStateAt`, which the check cannot
reach with the field.

**The witness `leakW`**: a world that meets the pin, `EffInterp` and `DataVals`, whose `Upd` and
`Stop` are true unless both ends are on the nil slice, and whose `Fam` is true off it.

```lean
/-- `leakW` without its relation at computation types; `ewpW` does not read `comp`. -/
def leakW₀ : SemWorld where
  Stk := Bool
  nil := false
  held _ := ([], [])
  Fam fρ ps i := i.2 = false → TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1
  Stop a b _ := a.2.2 = false → b.2.2 = false →
    (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Upd i i' ρ _ π := i.2 = false → i'.2 = false → ResU.UpdV ρ π
  Ext i i' ρ := Ext i.1 i'.1 ρ
  share _ _ _ _ _ _ := fun _ => False
  payStk _ _ := false
  val b A i δ v := vCE none b A i.1 δ v
  comp _ _ _ _ := fun _ => False

/-- `leakW`: at `F_S R` the relation is its own runs. -/
def leakW : SemWorld :=
  { leakW₀ with
    comp := fun C i δ e ρ => ∀ (S : Row) (R : VTy), C = CTy.effOf S R →
      ewpW leakW₀ i e (opTabW leakW₀ (rowTabW leakW₀ S δ)) (fun j v => leakW₀.val true R j δ v) ρ }
```

Lemmas, each **checked**: `sliceShape_leakW`; `effInterp_leakW` (by `effOf_inj`, the injectivity
of `CTy.effOf`); `dataVals_leakW` (`vC_data`); `leakAt_leakW` (the end index `([], true)`);
`not_adequate_leakW`, from `not_adequate_of_leak`; `not_updReclaim_leakW`.

**What excludes the leak.** `Adequate`, at a world that meets `EffInterp` and `DataVals`: the leak
reaches `M.comp` only through `EffInterp`, and the leaking end's post is `∅` only through
`DataVals`. `leakW`'s `comp` is its own `ewpW` at `F_S R` so that `EffInterp` holds by
construction. A `leakW` whose `comp` were Core's `cC` would fail `EffInterp`, since its `wpGW`
admits off-nil ends that `cC`'s `wpG` rejects, and then `EffInterp`, not `Adequate`, would be what
excludes it. On the generic route, `UpdReclaim` excludes `leakW` too. `leakW` is not shown to meet
the rest of `WLaws`: its `Fam` is `True` off the nil slice, so `RelElim` and `AdequateEvery` are
not expected to hold there. Nothing here needs them; `leakW` shows which conjunct does the
excluding.

**Layer 4: what bounds `Upd`, and what does not.**

- **The program level.** Done's program-level conjuncts state the guarantees over `J` and do not
  mention `M` (Layer 1). No choice of `Upd` makes them easier, and `SoundnessOfFL`, the route from
  the device to them, reads no `Upd`.
- **The borrow guarantees at W.** `Arises`, `Exclusive` and `LifetimeSound` do not read `Upd`
  (Layer 1b).
- **The device, from above.** `Adequate` bounds `M.Upd` from above: through `EffInterp`, a weaker
  `Upd` puts more programs in `M.comp` at `([], M.nil)` from `∅`, and `Adequate` asks each of them
  to run safely to the empty memory (Layer 3). On the nil slice the pin's `→` half bounds it
  (§2.2).
- **The device, no recorded bound.** `FramesW`, `SpanBorrows`, `I5`, `I1`, `P11` and `FL` read
  `M.Upd` on both sides (§2.3 (a)). They are not monotone in `Upd`, and this design records no
  bound from them. Their printed proofs consume `↭`'s borrow content (6.27–6.29, 6.38, 6.39,
  6.47–6.50, the own-cell step). At W that content is the laws of §2.3 (d). Stated at every pair
  of indices, two of them exclude every world that admits the runs OQ-9 (a) with the cell kept
  makes of AT02, so they are not candidates for done (§2.3 (d)).
- **Not a leak.** A run end that drops a lend, or changes a borrow's lifetime or predicate, without
  leaking an owned cell is not a leak, and `Adequate` does not see it. Its consequences for
  programs are excluded at the program level: a use after free is a stuck run (`Soundness J`), and
  a cell never freed is a non-empty final memory (B4, `Soundness J`'s `Final`; a release through a
  reused location is B5's, `ReleasedOnceReuse`). The frames
  can exclude a world whose `Upd` drops a lend (the sketch in §2.3 (a), not built); which such
  worlds a device conjunct excludes is not established.

So weakening `Upd` cannot make done true: done asserts the program-level guarantees of `J`
directly, and the borrow guarantees stated only at W do not read `Upd`.

DESIGN §1.0 and §4.2 say the laws "bound the relation from above at every index". Off the nil
slice that holds relative to `M.Upd`: the laws bound the relation by W's runs, and W's runs end
under `M.Upd`. §5.4 lists the lines to change.

**Not established.**

- No world has been built that meets every law of `WLaws` (and `ShareResume`) and admits a
  reachable leak. §2.3 (b) gives the reason for `UpdSeq` and `UpdReclaim` as hypotheses; it does
  not rest on such a world.
- There is no general Lean statement of the form "`Adequate M` excludes every reachable weak
  end". `not_adequate_of_leak` is the one-cell instance.
- No lemma shows that a weak `Upd` fails, or meets, any rule-shaped conjunct. The `MutFrameUW`
  sketch of §2.3 (a) is not built.

---

## 4. No OQ-9 option is chosen

There are three shapes for a `Mut` lend. Before this fix only the first two were expressible.

**(b) The ghost end.** `Upd` takes Core's value at every index:
`fun _ _ ρ _ π => ResU.UpdV ρ π`.

- `held := ([], [])`.
- The stack can record which lends to re-lend (GhostEnd's D16.1), or be `Unit`. `Upd` ignores
  it.
- At `Foo`'s stop the lend is ended. The cell is unfolded in the share, and the end meets every
  conjunct (`at02_unfolded_end`, restated through the pin).
- At resume, 6.65 is applied again at a fresh lifetime (`ewpTS_M_frameR`).
- `withbor_spans_yields_cC` puts AT02's shape in Core's `cC` at σ = []. It uses the pure
  `withbor`.
- `updRefl_of_core`, `updOwn_of_core`, `updSeq_of_core` and `updReclaim_of_core` give this shape
  the run-end laws, and `updFrame_of_core`, `updOutlives_of_core` and `updLendBack_of_core` the
  printed forms of §2.3 (d) (**checked**).

**(a), cell unfolded at the stop.**

- `Upd` is again Core's at every index, so every law of §2.3 (d) holds, as at (b).
- The stack records the open lend (location, lifetime, predicate) while the cell sits unfolded
  in the share. At resume it is folded again at the same lifetime.
- At the run end this shape is the same as (b). It differs in what the index records and in the
  lifetime of the re-fold.
- Whether it can meet `MutFrameW` is not checked (LoopBorrow `refoldKripke_false`, at Core's
  `Ext` only).

**(a), cell kept.** Off the nil slice, `Upd` differs from Core's. The witness is `carryW`. Its
stack is the `mut` cells carried open. Its relation takes the carried cells out at both ends,
`σ ∩ dom ρ` at the start and `σ′ ∩ dom π` at the end, by `ResU.delDom` (`ρ/dom(σ)`, the
restriction [TR] 6.56 uses). So a run whose own resource leaves a carried cell out, because the
cell sits in the frame or in a stored `κ` the frame holds, has its ends.

```lean
/-- The cells a world carries open across stops are `mut` cells. -/
def MutOnly (σ : WRes) : Prop := ∀ l ψ, σ.get l = some ψ → ψ.kind = Kind.mut

/-- At a location of `σ`, `ρ` holds `σ`'s cell or none. -/
def CarriedIn (σ ρ : WRes) : Prop :=
  ∀ l ψ, (σ.get l).isSome → ρ.get l = some ψ → σ.get l = some ψ

/-- (a) with the lend's cell kept, as a witness for the run-end laws. -/
def carryW : SemWorld where
  Stk := WRes
  nil := PMap.empty
  held _ := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1 ∧ MutOnly i.2 ∧ ∃ x, ResU.CompS i.2 x fρ
  Stop a b _ := (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Upd i i' ρ ρ' π := MutOnly i.2 ∧ MutOnly i'.2 ∧ CarriedIn i.2 ρ ∧ CarriedIn i'.2 π ∧
    (∃ x, ResU.CompS (π.restrictDom i'.2) x ρ') ∧
    (∀ l ψ, i'.2.get l = some ψ → (i.2.get l = none ∨ (ρ.get l).isSome) → π.get l = some ψ) ∧
    (∀ l ψ, i.2.get l = some ψ → ρ.get l = none → π.get l = none ∧ i'.2.get l = some ψ) ∧
    ResU.UpdV (ρ.delDom i.2) (π.delDom i'.2)
  Ext i i' ρ := Ext i.1 i'.1 ρ ∧ i'.2 = i.2
  share _ _ _ _ _ _ := fun _ => False
  payStk _ _ := PMap.empty
  val b A i δ v := vCE none b A i.1 δ v
  comp C i δ e := cC C i.1 δ e
```

In words, a run from `ρ` at stack `σ` to stack `σ′`:

- is Core's `↭` once the carried cells are taken out at both ends (`ρ/dom(σ) ↭ π/dom(σ′)`);
- holds in its post every carried cell its end holds (`π∣dom(σ′)` is part of `ρ′`);
- has, in its end, the end stack's cell for every lend it opened and every carried cell it held;
- does not hold at its end a carried cell it did not hold at its start, and that cell stays
  carried unchanged.

Lemmas, each **checked**:

- **`sliceShape_carryW`.** At σ = σ′ = `∅` the extra conjuncts are trivial and `ρ/dom(∅) = ρ`.
- **`updRefl_carryW`.** At a configuration `carryW` reaches, the run's resource holds a carried
  cell as the stack's (`carriedIn_of_fam`), so a run of no steps has its end. This holds at every
  carried index, so a value from a configuration whose carried cells sit in the frame (a handler
  clause that runs between AT02's stop and the resume without holding `κ`) ends.
- **`updOwn_carryW`.** An own cell added or removed is never at a carried location
  (`own_not_carried` for an added one, `CarriedIn` for a removed one), and `/dom(σ)` passes it
  through (`compS_delDom`), so `updV_compS_own` applies.
- **`updSeq_carryW`.** Run 1's garbage `ρ⁺₁` holds no cell at a location of `σ₁` or `σ₂`, and at
  `σ₂`'s locations the composite end is run 2's. Then, as `wpG_bind`'s last step does, 6.48 frames
  run 2 by `ρ⁺₁` and 6.49 composes, after `/dom(σ₁)` and `/dom(σ₂)`.
- **`updReclaim_carryW`.** A post of `∅` forces the end stack to be `∅`, and Core's `reclaim`
  applies.
- **`at02_held_end_carry`.** AT02's run from the empty configuration, which `carryW` reaches at
  the nil index, ended at `Foo` holding the lend as `c ↦ mut(α, inj₁ (), ∅, ⊤)`. At the index
  `([], heldRes c α)` it meets every conjunct of the run's end but the postcondition: the
  compositions, both lowerings, the run, `NoOwn`, `carryW.Fam` (`TW` by `held_arises`, `MutOnly`
  by `mutOnly_heldRes`, the stack a part of the configuration), `carryW.Stop`, and `carryW.Upd`
  (`upd_held_carryW`). The post holds the cell, and the garbage is `∅`.
- **`upd_close_carryW`.** The `Upd` conjunct of the continuation's run that closes the lend and
  frees the cell, from `([], heldRes c α)` with the cell as its resource to `([], ∅)` with
  nothing. The machine run is not built.

So the run-end laws of this design (the pin, `UpdRefl`, `UpdOwn`, `UpdSeq`, `UpdReclaim`) admit an
end that holds a `Mut` lend as a cell, as they admit (b)'s ends, and the end state chooses
neither. That is a statement about the run-end laws.

The printed route's other forms, stated at every pair of indices, do not admit it (§2.3 (d)).
`UpdOutlives` fails at the held end's `Upd` instance, and `UpdLendBack` fails at the closing
run's (`not_updOutlives_carryW`, `not_updLendBack_carryW`). They hold wherever `Upd` is Core's at
every index, which covers (b) and (a) with the cell unfolded. Neither is in done or in
`AdequateOfLaws`, so the end state still chooses no option. What they show is that a world under
(a) with the cell kept needs its own forms of 6.27–6.29, 6.38, 6.39 and 6.50 off the nil slice.

`carryW` is not shown to meet `EffInterp` or any other conjunct of done. Whether a world that
carries a lend open as a cell meets FL or done is OQ-9 (a)'s open question.

**Not established.**

- `carryW` is a witness for the five run-end laws only. Its relation is Core's at the record list,
  chosen only to fill the fields. `UpdFrame` is not checked at it. `UpdImmBack` is not checked at
  it, since it carries `mut` cells only.
- `carryW`'s stack holds the carried cells themselves. A write through a carried lend changes the
  cell, and the end stack records the new cell. Whether a world should carry lends that way, or by
  location, lifetime and predicate alone, is part of OQ-44.
- **An `Imm` lend carried open is not built.**
  - At AT02's stop, the 6.64 end with the frame open fails R-T1 and `↭` at the nil index
    (`at02_imm_end`), and `StopVisible` excludes its visible frame at every index
    (`not_stop_imm_of_stopVisible`). §0 gives the scope of that configuration.
  - An (a) world that keeps the `imm` cell at the stop needs `Upd` to admit it off the nil slice
    (`at02_imm_end`), and the 6.64 frame and record out of the visible frames
    (`not_stop_imm_of_stopVisible`); `held` is where `Arises` counts suspended frames. Where it
    keeps them is OQ-9's question.
  - `imm` composition does not cancel (6.43:
    `ℓ ↦ imm(α ∪ β, v, ρ′) = ℓ ↦ imm(α, v, ρ′) ● ℓ ↦ imm(β, v, ρ′)`). `updSeq_carryW` uses that a
    `mut` cell composes with nothing, so `carryW`'s accounting does not extend as it stands.
  - I have not derived an `imm` analogue of `carryW` and have not verified that any obstruction
    there is real.

---

## 5. Every change

This section is the plan as designed. It is implemented; §8 records where each change is, what was
re-proved, and where the library departs from the plan.

### 5.1 Lean definitions and statements

| file | change |
|---|---|
| `Defs/World.lean` | module docstring: "R-T1 by `M.Stop`, `↭` by `M.Upd`"; the fields list adds the run-end relation. `SemWorld`: field `Upd` after `Stop`, docstring §2.1. `held`'s docstring adds the sentence of §2.1: a 6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not see it; a world that carries one open across a stop accounts for it through `Upd` and the index, either as a borrow cell in the run's resource or unfolded with the lend recorded in the index (OQ-9 (a), OQ-44). `wpGW`: `ResU.UpdV ρ π` → `M.Upd i i' ρ ρ' π`, docstring. `coreW`: `Upd _ _ ρ _ π := ResU.UpdV ρ π` |
| `Statements/Device.lean` | docstring: the nil slice's run-end relation is Core's; the pin's `←` half is the embedding, and its `→` half bounds ends from the nil slice to the nil slice and not W's runs. `SliceShape`: the `Upd` conjunct after `Stop` (§2.2). New, beside `WLaws` and not in it: `UpdSeq`, `UpdReclaim` (§2.3 (b)); `UpdRefl`, `UpdOwn`, `UpdFrame`, `UpdOutlives`, `UpdMutBack`, `UpdImmBack`, `UpdLendBack` (§2.3 (d)) |
| `Statements/Composition.lean` | `AdequateOfLaws` gains `UpdSeq M → UpdReclaim M →`; docstring: the replay composes runs, platform answers and drive observations by `UpdSeq` and reclaims by `UpdReclaim` |
| `Statements/Binder.lean` | `FreezeBinderLoc`, `FreezeBinderLife`: the `Upd` clauses (§2.3 (e)) |
| `Statements/EndState.lean`, `Statements/Interface.lean`, others | no statement changes |

### 5.2 New Lean

Every name below is proved today in `Checks/RunEnd.lean` or `Checks/RunEndDesign.lean`, and is
moved and restated at the library's `SemWorld` (the check's `SemWorldU` read as `SemWorld`,
`RunFrameU` as `RunFrame`), except `at02_runEnd_nil` and `not_endState_of_leak`, which are new.

| file | names | proof route |
|---|---|---|
| `Restricted/CoreLaws.lean` (it imports `Statements.Interface`, hence `SliceShape`) | `wpGW_of_wpG_nil` ([generic]); `updRefl_of_core`, `updOwn_of_core`, `updSeq_of_core`, `updReclaim_of_core`, `updFrame_of_core`, `updOutlives_of_core`, `updMutBack_of_core`, `updImmBack_of_core`, `updLendBack_of_core` ([generic], `Upd` Core's at every index); their instances at `coreW` (the check's `updRefl_coreWU` … `updLendBack_coreWU`) | the pins of `Fam`, `Stop`, `Upd`; `updV_self_iff`; `updV_compS_own`; `wpG_bind`'s last step; `reclaim`; `updV_frame`; `updV_outlives`; `six27`, `six28`; `six38_steps_one_two`, `six38`, `six39` |
| `Restricted/Corollaries.lean` | `endState_prog` | projection |
| `Restricted/RunEnd.lean`, from the verifier's `Checks/RunEnd.lean` | `wpGW_iff_runFrame` (with `M.Upd i i' ρ ρ' π`); `at02_held_end` (fails `M.Upd` at the nil index, by the pin); `at02_unfolded_end` (meets it, by the pin); `at02_held_end_core` | §0; it imports `LoopBorrow.Obstruction` |
| `Restricted/RunEnd.lean`, new | `at02_runEnd_nil`: an end of AT02's run on the nil slice, under `SliceShape`, holds no `mut` cell at `c`. It replaces `at02_runEnd`, whose every-world form does not survive | `at02_runEnd`'s proof, with the `→` half of the `Upd` pin for its `↭` step |
| `Restricted/RunEnd.lean`, new | `not_endState_of_leak` | `not_adequate_of_leak` and `platformNone_respects`; `EndStateAt` holds `WLaws` and `Adequate`. It is stated at the library's `EndStateAt`, so it waits for the field |
| `Restricted/RunEnd.lean`, from `Checks/RunEndDesign.lean` | `not_sliceShape_of_updTop`; `upd2Reclaim_excludes_held`; `LeakAt`, `leakProg`, `leakProg_run`, `no_pstep_val`, `not_adequate_of_leak`; `leakW₀`, `leakW`, `effOf_inj`, `sliceShape_leakW`, `effInterp_leakW`, `dataVals_leakW`, `leakAt_leakW`, `not_adequate_leakW`, `not_updReclaim_leakW`; `MutOnly`, `CarriedIn`, `carryW`, `compS_delDom`, `delDom_of_disjoint`, `carriedIn_of_fam`, `own_not_carried`, `mutOnly_heldRes`, `heldRes_get`, `sliceShape_carryW`, `updRefl_carryW`, `updOwn_carryW`, `updSeq_carryW`, `updReclaim_carryW`, `upd_held_carryW`, `upd_close_carryW`, `at02_held_end_carry`, `fam_nil_held_carryW`, `not_close_from_nil_carryW`; `not_updOutlives_of_opened`, `not_updMutBack_of_closed`, `not_updOutlives_carryW`, `not_updLendBack_carryW` | §2.1, §2.2, §2.3 (d), §3 Layers 2 and 3, §4 |
| `Restricted/RunEnd.lean`, from `Checks/RunEndDesign.lean`'s last section | `immRec`, `immRes`, `immRec_noDesc`, `admWf_flag`, `vShape_flag`, `immRes_hash`, `immRes_valid`, `own_arises`, `imm_arises`, `imm_tagged`, `immAt_immRes`, `not_updV_empty_immRes`, `at02_imm_end`, `not_stop_imm_of_stopVisible` | §0; already at the library's `SemWorld`. In the library `at02_imm_end` also fails `M.Upd` at the nil index, by the pin |

The verifier's file already has `heldRes` (a definition) and `held_arises` (proved).

### 5.3 Proved results: what must be re-proved

| result | expected change |
|---|---|
| `sliceShape_core` | one more component, `fun _ _ _ _ _ => Iff.rfl` (`sliceShape_coreWU`, **checked**) |
| `wpGW_core` (and `wpGW_core_eq`, `ewpW_core`) | none expected: the conjunct is definitionally `ResU.UpdV ρ π` at the reducible `coreW` (`wpGWU_core`, by `Iff.rfl`, **checked**). If elaboration needs it, add a `show` |
| `wpGW_iff_runFrame`, `at02_runEnd`, `wpGW_at02`, `at02_held_end`, `at02_unfolded_end`, `at02_held_end_core` | restated (§5.2). `at02_runEnd`'s every-world form does not survive. `at02_held_end_carry` shows that the field's signature and the run-end laws admit the held end; it does not show that (a) is representable at a world that meets done |
| `wpGW_mono`, `wpGW_step`, `ewpW_fold`, `ewpW_unfold`, `ewpW_step`, `i5beta`, `wpGW_strip`, `redLaws_of_mono` | none expected: they carry the conjunct by position, and its position is unchanged |
| the generic composition results `soundnessOfFL`, `soundnessContractsOfFL`, `soundnessContractsOfFLWB`, `effSafeOfFL` (`Restricted/Composition.lean`) | none expected: none reads `wpGW`'s run-end conjunct. `soundnessContractsOfFL(WB)` read `ExtPre` and `Conservative(WB)`, and `effSafeOfFL` destructures `WLaws` into its nine conjuncts, whose number and order do not change (the new conjunct is inside `SliceShape`). Rebuilt in step 1 of §7 |
| every `*_core` result (`wlaws_core`, `i1_core`, `i2_core_abortive`, `i3_core`, `i5_core`, `framesW_core_abortive`, `antiFrameW_core`, `frameW_core`, `adequateEvery_core`, `adequateRetAt_core_none`, `conservative_core`, `conservativeWB_core`, `redLaws_core`, `p11_core`, …), and `status_tier1End_of` | none expected: through the transports |
| `Audit.lean` | the step-index report of `coreW` is expected unchanged (`ResU.UpdV` was already in the closure through `cC → wpG`). The Core pins are unchanged (no Core edit). Re-run both `run_meta` |
| `AxiomCheck.lean`, `Targets.lean`, `Status.lean` | import `Restricted.RunEnd`; `#print axioms` for every new theorem; new status entries |

### 5.4 Documents

**DESIGN.md** (line numbers as of a558a94):

- **§0, l.78-82 and l.100-107.** Add "the run-end relation `↭`" to "where W must change BoLo".
  Add `Upd` for OQ-9 to "a field of `SemWorld`". After "decide OQ-9 for (a)", add "which a fixed
  `↭` no longer excludes for a `Mut` lend: the run-end relation is the field `Upd` (§10)".
- **§1.0, l.117-121.** "The laws of §4.2 bound the relation from above at every index" becomes
  "bound the relation from above by W's runs at every index". Add: "W's runs end under `M.Upd`,
  Core's `↭` on the nil slice (`SliceShape`) and a field elsewhere. Of the conjuncts of done,
  `Adequate` bounds `M.Upd` from above, through `EffInterp` and `DataVals`, at a reachable leak
  (FIX-RUN-END §3), and the pin bounds it between nil indices. The rule-shaped conjuncts
  (`FramesW`, `SpanBorrows`, `I5`, `I1`, `P11`, the FL cases) read `M.Upd` on both sides and are
  not monotone in it, and no bound is recorded from them; their printed proofs consume `↭`'s
  borrow content, which at W is the laws of FIX-RUN-END §2.3 (d). `Arises`, `Exclusive`,
  `LifetimeSound` and the program-level conjuncts do not read it."
- **§1.1, l.226-230.** "`AdequateOfLaws`: adequacy follows from the laws of §4.2 with `UpdSeq` and
  `UpdReclaim`. Where `Upd` is Core's at every index those hold (`updSeq_of_core`,
  `updReclaim_of_core`) and FL is the only hard theorem. Otherwise they are W's own obligations,
  or `Adequate` is proved directly."
- **§1.3.**
  - l.421-433: "the wp's stop condition and its run-end relation `↭`".
  - l.452-480 and l.503-513: the code of §2.1, `held`'s docstring included.
  - l.482-483: "`↭` by `M.Upd`".
  - l.579-589: a bullet on `Upd`. It is pinned on the nil slice only. The pin puts Core's runs in
    W's, and it bounds ends from the nil slice to the nil slice; it does not bound W's runs. A
    world that carries a `Mut` lend open across a stop as a borrow cell needs `Upd` off the nil
    slice; one that carries it with the cell unfolded does not. The last bullet's "decide OQ-9
    for (a)" gets "which a fixed `↭` no longer excludes for a `Mut` lend".
  - l.591-600 (field table): add the row
    `| Upd | ResU.UpdV ρ π | OQ-9 (a Mut lend carried open as a borrow cell), OQ-44; pinned to Core's ↭ on the nil slice by SliceShape (the ← half the embedding; the → half bounds ends between nil indices, and fixes the reading of σ = [] that AGREE decision 10 asks about); bounded above by Adequate through EffInterp and DataVals (a reachable leak); read on both sides, and not monotonically, by FramesW, SpanBorrows, I5, I1, P11 and FL, whose printed proofs consume 6.27–6.29, 6.38, 6.39, 6.47–6.50 and the own-cell step (FIX-RUN-END §2.3 (d)); AdequateOfLaws asks UpdSeq, UpdReclaim |`.
    The `held`, `Fam` and `Stop` rows add: "a 6.65 `Mut` lend adds no 6.64 frame or record, so the
    frame and record lists these fields read do not see it, and `Fam` admits the configuration
    holding it (`TW.mutFold`); at Core's world the end holding it meets `Fam` and R-T1
    (`at02_held_end_core`)".
- **§1.4, l.604-617.** `coreW` gains `Upd`. The transports are unchanged.
- **§1.5, l.633.** "`Adequate M` from §4.2, `UpdSeq` and `UpdReclaim`, by `AdequateOfLaws`".
- **§1.6, l.711-718.** Imports add `LoopBorrow` (for `not_upd_of_new_mut`, `not_upd_of_new_imm`,
  `mutCell`).
- **D10, l.1196-1200.** Add: "A 6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not
  see it. A world that carries one open across a stop accounts for it through `Upd` and the index,
  either as a borrow cell in the run's resource or unfolded with the lend recorded in the index
  (OQ-9 (a), OQ-44). A 6.64 frame left open at a stop is excluded from the visible frames by
  `StopVisible` (`not_stop_imm_of_stopVisible`); where a world keeps it is OQ-9's question."
- **§4.1.** l.2007: the code of §2.3 (b). l.2024-2028: "it composes chained runs, platform answers
  and drive observations by `UpdSeq` (as `wpG_bind`) and reclaims by `UpdReclaim` (as
  `theorem32D`)".
- **§4.2.**
  - l.2038-2050: "Together they bound the relation from above" becomes "by W's runs". `EffInterp`
    bounds `F_Σ` by W's runs, which end under `M.Upd`. `M.Upd` is bounded from above by
    `Adequate` at a reachable leak, and pinned to `↭` on the nil slice: the `←` half is the
    embedding, the `→` half bounds ends between nil indices (FIX-RUN-END §2.2, §3).
  - l.2070-2078: the code of §2.2, and the laws of FIX-RUN-END §2.3 (b) and (d) with their status
    at `coreW` and at `carryW`.
  - l.2169-2183: `SliceShape` is still by `Iff.rfl`.
  - l.2187-2200: rewrite. An equivalence at σ = [] would put a tier-2 value in today's `cC`.
    That relation's runs end on the nil slice, with R-T1 and `↭`. Under OQ-9 (a) a run from
    σ = [] can end off it, where `M.Upd` is not pinned. LoopBorrow's "a borrow that `↭` lets
    outlive the run that opens it" is now expressible at W, as `Upd` off the nil slice: the
    run-end laws admit it for a `Mut` lend (`carryW`, FIX-RUN-END §4); the printed forms of 6.27
    and 6.50 at every index do not (FIX-RUN-END §2.3 (d)).
- **§5 I2.**
  - l.2416-2431: keep "decide OQ-9 for (a)" and add "which a fixed `↭` no longer excludes for a
    `Mut` lend; FIX-RUN-END §4".
  - l.2601-2608: add the evidence: `at02_held_end_core`, `at02_unfolded_end`,
    `at02_held_end_carry`, `at02_imm_end`, `not_stop_imm_of_stopVisible`.
  - l.2646-2683: the binder clauses of §2.3 (e).
- **§8.** l.3559 (AT02): "semantically R-T1" becomes "semantically `↭` (`at02_held_end_core`)".
  l.3561 and l.3574 (AT04, AT17, each a `Mut` lend through `withborU dFlag` open at a resuming
  stop): "semantically R-T1" becomes "semantically `↭`, by AT02's argument (not built)". l.3564
  (AT07): "R-T1: no lend in a continuation" becomes "`↭` for a `Mut` lend (`at02_held_end_core`);
  R-T1 and `↭` for a 6.64 frame (`at02_imm_end`, AT02's run): no lend in a continuation".
- **§9.** l.3600: item 2 adds `UpdRefl coreW`, `UpdOwn coreW`, `UpdSeq coreW`, `UpdReclaim coreW`,
  `UpdFrame coreW`, `UpdOutlives coreW`, `UpdLendBack coreW`. l.3623: "`AdequateOfLaws` (with
  `UpdSeq`, `UpdReclaim`)".
- **§10, l.3666-3667.** Replace with §6 below. l.3689-3692 (Q1): "with R-T1 at every stop and `↭`
  at every run end". Add Q4 (= AGREE decision 9) and Q5 (= AGREE decision 10).
- **§Corrections.** Add **C5**: "`wpGW`'s `↭` was a fixed conjunct. It is the field `Upd`, Core's
  on the nil slice (`SliceShape`), and `AdequateOfLaws` asks `UpdSeq` and `UpdReclaim`."
- **§Builder's notes.** Add the side result and the 6.64 configuration (§0).
- **§Sources.** Add [TR] 6.24–6.29, 6.34, 6.38, 6.39, 6.43, 6.47–6.50 and the p. 6 `wp` row;
  [CONF] 415:22-23; `Core/Demonic.lean` (`theorem32D`); `Core/Fundamental.lean` (`reclaim`,
  `withbor1U`, `withbor2U`); `Support/Model/Entailments.lean` (`updV_compS_own`); LoopBorrow
  `Obstruction.lean`; `Checks/RunEnd.lean`, `Checks/RunEndDesign.lean`.

**AGREE.md:**

- l.9-27: blocker 1 becomes "answered by FIX-RUN-END", with four lines, each for a `Mut` lend
  (an `Imm` lend carried open is not built):
  1. The run-end relation is the field `SemWorld.Upd`, and `wpGW` ends every run under `M.Upd`.
  2. `SliceShape` pins it to Core's `↭` on the nil slice. The pin puts Core's runs in W's runs,
     and it bounds ends from the nil slice to the nil slice; it does not bound W's runs, since a
     run picks its end index and one from σ = [] may end off the nil slice. Its `→` half fixes a
     reading of σ = [] (decision 10).
  3. What keeps a weak `Upd` from making done easy: the program-level guarantees are asserted of
     `J` and do not mention W; `Arises`, `Exclusive` and `LifetimeSound` do not read `Upd`; at the
     device, `Adequate` (with `EffInterp` and `DataVals`) excludes a reachable leak. The
     rule-shaped conjuncts read `Upd` on both sides, are not monotone in it, and no bound is
     recorded from them. Off the nil slice, no conjunct of done is shown to constrain `Upd`'s
     borrow content beyond `Adequate`'s leak bound.
  4. The lend-back laws (6.27–6.29, 6.38, 6.39, and 6.48 into the post, 6.50, at W) are stated
     beside done and hold where `Upd` is Core's at every index. Stated at every index, 6.27 and
     6.50 fail at every world that admits the runs OQ-9 (a) with the cell kept makes of AT02 (the
     held end, and the run that closes it), `carryW` among them. Their form for such a world is the
     open part of the field's specification (OQ-9 (a), OQ-44). `AdequateOfLaws` asks `UpdSeq` and
     `UpdReclaim`.
- The banner's count drops by the blocker.
- l.112-115: the W bullet lists `Upd`. Drop "(See the blocker …)".
- l.162: "`WLaws`, `UpdSeq`, `UpdReclaim` (`AdequateOfLaws`, OPEN)".
- Decisions: add
  - 9. "The run-end relation's laws `UpdSeq` and `UpdReclaim` are hypotheses of
    `AdequateOfLaws`, and `UpdRefl`, `UpdOwn`, `UpdFrame`, `UpdOutlives` and `UpdLendBack` are
    laws FL at W reads; none is a conjunct of done (FIX-RUN-END §2.3). Should done hold
    `UpdReclaim`, which would bound `Upd` from above in done itself? (The every-index
    `UpdOutlives` and `UpdLendBack` cannot go in done without excluding OQ-9 (a) with the cell
    kept.)"
  - 10. "`SliceShape`'s `Upd` pin is an equivalence. Its `→` half reads σ = [] as 'no lend carried
    open anywhere in the configuration', so a σ that counts only the lends the running
    computation carries must end, off the nil slice, a run that closes a lend a stored
    continuation carried (FIX-RUN-END §2.2). This is a constraint on OQ-44. Should the pin stay an
    equivalence, or keep only its `←` half (Core's run ends are W's), which drops the constraint
    and three checks and changes no derived result?"
- Decision 1 also gets the `↭` wording of Q1.

**README.md:**

- l.68-71: "and the run-end relation (`SemWorld.Upd`, Core's `↭` on the nil slice)".
- Status table: rows for the pin and the laws (`updRefl_core`, `updOwn_core`, `updSeq_core`,
  `updReclaim_core`, `updFrame_core`, `updOutlives_core`, `updLendBack_core`, PROVED AT σ=[];
  the `_of_core` forms, generic; `wpGW_of_wpG_nil`, generic); for the degenerate-world checks
  (`endState_prog`, `not_adequate_of_leak`, PROVED, generic; `not_adequate_leakW`, PROVED at the
  witness; `not_sliceShape_of_updTop`, PROVED, generic, a sanity check on the pin); for the
  run-end laws admitting an end that holds a `Mut` lend as a cell (`updRefl_carryW`,
  `updOwn_carryW`, `updSeq_carryW`, `updReclaim_carryW`, `at02_held_end_carry`, PROVED at the
  witness); for the printed forms excluding it (`not_updOutlives_of_opened`,
  `not_updMutBack_of_closed`, PROVED, generic); and for the 6.64 end (`at02_imm_end`, PROVED,
  every world meeting `SliceShape`). Each status is written only once its lemma is proved in the
  library.
- l.119-122: `carryW` and `leakW` under non-vacuity.

**Status.lean:**

- The docstring's second-wave row becomes "`AdequateOfLaws` (with `UpdSeq`, `UpdReclaim`) |
  OPEN".
- A section "The run-end relation" with `status_` theorems for §5.2.
- The unresolved-findings list records finding 1 as answered.

### 5.5 Outside this unit's write scope (flagged, not edited)

- **`docs/effects-state/BRIEF.md` §3.1–3.2.** "At every stop, `wpG` requires the open Imm frames
  and records to equal those at entry … so no internal lend spans a suspension." For a 6.64 frame
  open at a stop, R-T1 and `↭` both exclude the end at AT02's stop (`at02_imm_end`). For a `Mut`
  lend it is `↭` alone (`at02_held_end_core`; §0, side result). §3.2's "a Mut lend leaves no `ps`
  entry" stands.
- **`research/effects/src/foundations/well-bracketing.md`.** It makes the same statement. No
  status line changes, so the notebook is not edited by this unit. The register's P14 evidence
  line, "the lexical stop", should read "the lexical stop and `↭` (R-T1 and `↭` for a 6.64 frame,
  at AT02's stop; `↭` for a `Mut` lend)".
- **SPEC.** A W whose `Upd` is not Core's off the nil slice changes BoLo's `wp`. It needs a SPEC
  entry when the kernel adopts it (BRIEF §5, the critic's correction on the stop condition).

### 5.6 Interactions with findings 2–7 (noted, not fixed)

- **Finding 6.**
  - `FramesW` may decide OQ-9 for (a) if (b) cannot give the stated shape. The finding's concern
    was that, with `↭` fixed, (a) was excluded too, so `EndStateAt` could be unsatisfiable at
    every `M`. After this fix a fixed `↭` no longer excludes (a) for a `Mut` lend: the run-end
    laws admit an end that holds the lend as a cell (§4). Whether `FramesW` can be met under (a)
    is not established, and whether `FramesW` belongs in done is still finding 6's question.
  - The printed route to `FramesW` reads the lend-back laws, and their every-index forms fail at
    every world that admits the runs OQ-9 (a) with the cell kept makes of AT02 (§2.3 (d)). So
    under (a) with the cell kept, `FramesW` needs a proof off the printed route, or the laws' own
    forms for (a). This sharpens finding 6's concern; it is not fixed here.
  - As the verifier noted, `↭` no longer stops `MutFrameW` from being met by a lender that stops
    with the lend carried. That it can be met that way is not shown.
  - Keeping the laws of §2.3 (b) and (d) out of `WLaws` adds no device law to done.
- **Finding 3.** The route to `Conservative` and `ConservativeWB` at W now goes through
  `wpGW_of_wpG_nil`, which needs the `←` half of the `Upd` pin.
- **Finding 7.** `Upd` adds no step index. The audit of `coreW` is expected unchanged. The witness
  worlds are not W and are not audited, and the design check is outside the library.
- **I3 (`ShareCancel`), a conjunct of done.** Its closing clause reads `M.held` only: "the
  cancel's end holds nothing its start did not". A `Mut` lend carried open adds nothing to
  `held`, under either representation of (a). So the closing clause says nothing about `Mut`
  lends, and `ShareCancel`'s option-neutrality does not cover them. Noted only: the program-level
  `Soundness` (B4) still catches a cell that is never closed, as a non-empty final memory, and B5
  (`ReleasedOnceReuse`) a release through a reused location.
- **`CancelCloses`** (named-only, OQ-57). "A cancel ends every lend it holds" would have to read
  the index (and `Upd`) as well as `held`.
- **The minor finding on `StopVisible`** ("forces every lend that spans a stop into `held`").
  `not_stop_imm_of_stopVisible` is that finding for a 6.64 frame at AT02's stop. A `Mut` lend is
  not affected: it adds no frame. Not changed here.
- **Findings 2, 4 and 5.** No interaction.

---

## 6. The DESIGN §10 note

These two rows replace DESIGN l.3666-3667, and are in DESIGN §10. Every lemma of this design
they name is in the library (`Restricted/RunEnd.lean`, `Restricted/CoreLaws.lean`,
`Restricted/Corollaries.lean`); the others are Core's, LoopBorrow's or GhostEnd's.

| question | where it sits | how the end state stays open on it |
|---|---|---|
| OQ-9, OQ-10: lends across a stop, carried open in σ or ghost-ended | `SemWorld.Upd`, `.held`, `.Fam`, `.Stop`, `.Stk`; `MutFrameW`/`ImmFrameW` | **The run-end relation is a field, `Upd`.** A 6.65 `Mut` lend adds no 6.64 frame and no record, so the frame and record lists that `held`, `Fam` and `Stop` read do not see it, and `Fam` admits the configuration holding it (`TW.mutFold`). At Core's world the end at AT02's `Foo` stop holding it as a cell meets `Fam` and R-T1 (`at02_held_end_core`). Core's `↭` is what excludes it: `↭` keeps the borrows of `⦇ρ⦈` and `⦇ρ′ ● ρ⁺⦈` equal ("this definition embodies lexical borrowing", [CONF] 415:23; LoopBorrow `not_upd_of_new_mut`). So with `↭` fixed in `wpGW`, no world could stop holding the lend as a cell (`at02_runEnd`; `wpGW_at02`, at every world whose `Upd` is Core's at every index), and OQ-9 (a) for a `Mut` lend in that shape needs a changed `↭`. `Upd` is Core's `↭` on the nil slice (`SliceShape`). Off it, it is open. A world that carries a `Mut` lend open across a stop accounts for it through `Upd` and the index: as a borrow cell in the run's resource, or unfolded with the lend recorded in the index. Which one is OQ-9 (a)'s and OQ-44's question. OQ-9 (b), and (a) with the cell unfolded at the stop, are `Upd` at Core's value at every index. The run-end laws (the pin, `UpdRefl`, `UpdOwn`, `UpdSeq`, `UpdReclaim`) also admit an end that holds the lend as a cell: `carryW` meets them and admits AT02's held end (`at02_held_end_carry`). `carryW` is a witness for those laws only. The printed route's other `↭` lemmas at W, stated at every pair of indices (`UpdFrame`, `UpdOutlives`, `UpdLendBack`), hold where `Upd` is Core's at every index. `UpdOutlives` fails at every world that lets a run from `∅` end with a lend at the top of its end, and `UpdLendBack` at every world that lets a run that starts with a lend end with no cell there (`not_updOutlives_of_opened`, `not_updMutBack_of_closed`); AT02's held end and the run that closes it are such runs. So a world that carries a lend open as a cell needs its own forms of them off the nil slice; what they are, and whether such a world meets FL or done, is OQ-9 (a)'s open question. The `Upd` pin, with the `Fam` pin, reads σ = [] as "no lend carried open anywhere in the configuration": a constraint the end state places on OQ-44 (AGREE decision 10). A 6.64 `Imm` lend at AT02's stop, frame open, fails R-T1 and `↭` at the nil index (`at02_imm_end`, AT02's machine run), and `StopVisible` excludes its visible frame at every index (`not_stop_imm_of_stopVisible`); an `Imm` lend carried open is not built. The frames at W are stated in the printed rule's shape with stops (`O151AsStated`). If (b) cannot give that shape, they decide OQ-9 for (a), which a fixed `↭` no longer excludes for a `Mut` lend. Recorded, not assumed. |
| **The stop condition and the run-end relation at resuming rows** (beside OQ-58) | `SemWorld.Stop`, `.Upd`; `SliceShape`; `UpdSeq`, `UpdReclaim`; `UpdFrame`, `UpdOutlives`, `UpdLendBack` | R-T1 (`Core/EffDefs.lean:40`) is "our conjunct, not a printed row" (the brief). `↭` is printed ([TR] p. 5 row 18, p. 6's `wp`), and effects change "the wp and its stop condition". The end state pins both only between nil indices, where nothing is carried. The `Upd` pin's `←` half puts Core's runs in W's (`wpGW_of_wpG_nil`). Its `→` half bounds ends from the nil slice to the nil slice; it does not bound W's runs, since a run from σ = [] may end off the nil slice. What keeps a weak `Upd` from making done easy: the program-level guarantees are stated over `J` and do not mention W (`endState_prog`); `Arises`, `Exclusive` and `LifetimeSound` do not read `Upd`; at the device, `Adequate`, through `EffInterp` and `DataVals`, excludes a world whose `Upd` admits a reachable leak (`not_adequate_of_leak`, `not_adequate_leakW`). The rule-shaped conjuncts (`FramesW`, `SpanBorrows`, `I5`, `I1`, `P11`, FL) read `Upd` on both sides, are not monotone in it, and no bound is recorded from them. **Off the nil slice, no conjunct of done is shown to constrain `Upd`'s borrow content beyond `Adequate`'s leak bound; the lend-back laws, which carry that content in the printed proofs, are the open part of the field's specification.** Those proofs consume 6.27–6.29, 6.38, 6.39 (the lend comes back), 6.47–6.50 and the own-cell step; at W these are `UpdRefl`, `UpdOwn`, `UpdSeq`, `UpdFrame`, `UpdOutlives` and `UpdLendBack`, Core's where `Upd` is Core's at every index. `AdequateOfLaws` asks `UpdSeq` (6.48 then 6.49, as `wpG_bind` composes runs) and `UpdReclaim` (`reclaim` with the post empty). They hold where `Upd` is Core's at every index and at `carryW`, and they are not conjuncts of done (AGREE decision 9). An equivalence with today's `wpG` at σ = [] for computations at resuming rows would put every tier-2 computation from σ = [] in today's `cC`, with R-T1 at every stop and `↭` at every run end (§4.2). A W whose `Upd` is not Core's off the nil slice changes BoLo's `wp` and needs a SPEC entry when the kernel adopts it. |

---

## 7. Build plan, when the Lean is written

1. Edit `Defs/World.lean`, then `Statements/Device.lean` (the `Upd` conjunct of `SliceShape`;
   the laws of §2.3 (b) and (d)). Run `lake build Targets.Defs.World` and
   `lake build Targets.Restricted.Transport`, then `Targets.Restricted.CoreLaws`,
   `Targets.Restricted.Interface` and `Targets.Restricted.Composition`. Expected edit:
   `sliceShape_core` only.
2. Write the new `Restricted/RunEnd.lean` from `Checks/RunEnd.lean` and `Checks/RunEndDesign.lean`,
   restated at the library's `SemWorld`, and the `_of_core` forms in `Restricted/CoreLaws.lean`.
   They replace both checks, which are moved and restated, not deleted unread. Build
   `lake build Targets.Restricted.RunEnd`.
3. `Status.lean`, `AxiomCheck.lean`, `Targets.lean`, then `lake build Targets`, which runs the
   AxiomCheck `run_meta` and both `Audit` `run_meta`s. Grep for forbidden keywords.
4. Update the documents (§5.4). Commit only when told.

---

## 8. The implementation

**Where each change is.**

| file | what |
|---|---|
| `Defs/World.lean` | the field `SemWorld.Upd` after `Stop` (§2.1), `held`'s docstring, `wpGW`'s run-end conjunct `M.Upd i i' ρ ρ' π`, `coreW.Upd := ResU.UpdV ρ π`; the module docstring |
| `Statements/Device.lean` | the `Upd` conjunct of `SliceShape` (§2.2); `UpdSeq`, `UpdReclaim`, `UpdRefl`, `UpdOwn`, `UpdFrame`, `UpdOutlives`, `UpdMutBack`, `UpdImmBack`, `UpdLendBack`, beside `WLaws` (§2.3 (b), (d)); the module docstring |
| `Statements/Composition.lean` | `AdequateOfLaws` asks `UpdSeq M → UpdReclaim M →` |
| `Statements/Binder.lean` | the `Upd` clauses of `FreezeBinderLoc` (`↔`) and `FreezeBinderLife` (forward), beside the `Stop` clauses (§2.3 (e)) |
| `Restricted/CoreLaws.lean` | `sliceShape_core`'s `Upd` component; `coreW_upd`; `wpGW_of_wpG_nil`; `updRefl_of_core` … `updLendBack_of_core`; `updRefl_core`, `updOwn_core`, `updSeq_core`, `updReclaim_core`, `updFrame_core`, `updOutlives_core`, `updLendBack_core` |
| `Restricted/Corollaries.lean` | `endState_prog` |
| `Restricted/RunEnd.lean` (new) | §0's configurations, the pin's checks, the leak and `leakW`, `carryW`, the printed forms' exclusions, the 6.64 configuration |
| `Status.lean` | the table "The run-end relation", `AdequateOfLaws` (with `UpdSeq`, `UpdReclaim`), finding 1 answered, and `status_` theorems for the results above |
| `AxiomCheck.lean`, `Targets.lean` | `#print axioms` of every new theorem; the import of `Restricted.RunEnd` |

`Restricted/RunEnd.lean` imports `LoopBorrow.Obstruction` (for `not_upd_of_new_mut`,
`not_upd_of_new_imm`, `mutCell`), as DESIGN §1.6 records.

**Re-proved.** `sliceShape_core` is the only proved result whose proof changed: one more component,
`fun _ _ _ _ _ => Iff.rfl`. Every other proved result of the library elaborates unchanged against
the field, as §5.3 expected. The transports (`wpGW_core`, `wpGW_core_eq`, `ewpW_core`) hold by
unfolding at the reducible `coreW`. The generic step lemmas (`wpGW_mono`, `wpGW_step`,
`ewpW_fold`, `ewpW_unfold`, `ewpW_step`, `i5beta`, `wpGW_strip`, `redLaws_of_mono`) carry the
run-end conjunct by position. The generic composition results, every `*_core` result and
`status_tier1End_of` are unchanged. `Audit.lean`'s report of `coreW` and the Core pins are
unchanged.

**Departures from §5.2.** Each restates a result; no statement of §2–§4 changed.

- `at02_runEnd` is in the library as the verifier stated it. Its `↭` is a hypothesis, not a
  conjunct of `wpGW`, so it holds at every world; what does not survive the field is its use
  through `wpGW` at every world. Its nil-slice form is `at02_runEnd_nil`, as §5.2 plans.
  `wpGW_at02` is restated at every world whose `Upd` gives Core's `↭` at every index (the
  hypothesis `hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π → ResU.UpdV ρ π`), which is `wpGW` as it was
  with `↭` fixed. The two are the library's evidence for §6's "with `↭` fixed in `wpGW`, no world
  could stop holding the lend as a cell".
- `not_adequate_of_leak` concludes `¬ Adequate M`, as §3 states it, through
  `not_adequateRetAt_of_leak` (`¬ AdequateRetAt M Platform.none`, the check's form) and
  `platformNone_respects`. `not_adequate_leakW` concludes `¬ Adequate leakW`.
- `at02_held_end` and `at02_held_end_core` state the failure of `M.Upd` at the nil index (by the
  pin) beside `¬ ResU.UpdV`; `at02_unfolded_end` states that `M.Upd` holds there;
  `at02_imm_end` states the failure of `M.Upd` at its nil end index beside `¬ ResU.UpdV`.
- The check's `wpGWU_core` has no library form: there is one `wpGW`, and `coreW.Upd` is
  `ResU.UpdV` by `Iff.rfl` (`coreW_upd`). The check's `sliceShape_coreWU` and `coreWU_upd` are
  `sliceShape_core` and `coreW_upd`.
- `at02_imm_end`'s `M.Upd` conjunct reads the `→` half of the pin, so §2.2 lists it among the
  checks that do, and AGREE decision 10 names those checks rather than counting them.

**The two check files.** `Checks/RunEndDesign.lean` is replaced by the library and removed from
the tree. `Checks/RunEnd.lean`, the verifier's check, is kept unchanged and outside the library's
build: its `wpGW_iff_runFrame` states `wpGW` with `↭` fixed and does not elaborate against the
field, and each of its results is restated in `Restricted/RunEnd.lean`.

**Not established** (as before): no world is built that meets every law of `WLaws` and admits a
reachable leak (§3); no lemma shows that a weak `Upd` fails or meets any rule-shaped conjunct
(§2.3 (a)); `carryW` is a witness for the five run-end laws only, and whether a world that carries
a lend open as a cell meets FL or done is OQ-9 (a)'s open question (§4); an `Imm` lend carried
open is not built (§4).

---

## Unresolved review findings

The review of this design ended with two major findings. The design was revised in answer to
each; the revision was not reviewed again. Each is listed as the review left it, with the revision
that answers it.

1. **The recorded design text chose a representation for OQ-9 (a)** (§5.1's `held` docstring,
   §5.4's D10 edit, §6's OQ-9 row). The text to be written into the `held` docstring, D10 and
   DESIGN §10 read "a `Mut` lend carried open is a borrow cell accounted by `Upd` and σ, not a held
   frame" and "shows only as a borrow cell". §4 lists a third shape, (a) with the cell unfolded at
   the stop, in which the lend is kept only in the index and is not a borrow cell, and says that
   how σ carries lends is OQ-44's question. So the text picked the cell-kept representation,
   against §4's "No OQ-9 option is chosen" and the rule that the targets allow an option without
   choosing it. The Lean field is neutral; the defect was in the recorded text. *Fix asked:* say
   that a `Mut` lend open across a stop adds no 6.64 frame and no record, so `held`, `Fam` and
   `Stop` do not see it, and that, depending on the option, it is a borrow cell in the run's
   resource (accounted by `Upd` and the index) or is kept in the index with the cell unfolded,
   which is OQ-9's and OQ-44's question; drop "not a held frame". *Revision:* §2.1, §5.1 and
   §5.4's D10 edit read "A 6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not see
   it; a world that carries one open across a stop accounts for it through `Upd` and the index,
   either as a borrow cell in the run's resource or unfolded with the lend recorded in the index
   (OQ-9 (a), OQ-44)". §6's row reads "as a borrow cell in the run's resource, or unfolded with the
   lend recorded in the index. Which one is OQ-9 (a)'s and OQ-44's question." Neither "not a held
   frame" nor "shows only as a borrow cell" remains. `SemWorld.held`'s docstring, DESIGN D10 and
   DESIGN §10 carry the revised text.
2. **Two impossibility claims about a 6.64 (`Imm`) lend had no Lean behind them** (§0's side
   result, §5.4's AT07 edit, §5.5, §6's OQ-9 row): that R-T1 and `↭` each exclude an `Imm` lend
   open at a stop, and that relaxing `Stop` alone does not admit an `Imm` lend across a stop. The
   task allows an impossibility claim only as an elaborating `def … : Prop` or a discharged Lean
   configuration whose world arises in `TW`. *Fix asked:* either (a) build the configuration, an
   AT02-shaped end under 6.64 holding `c ↦ imm(α, v, ∅)` with the frame record in `ps′`, show that
   it arises in `TW`, and prove `¬ ResU.UpdV ∅ π` by `not_upd_of_new_imm` and that `M.Stop` fails
   at the nil index under `SliceShape`; or (b) reword every occurrence to "I have not derived that
   an `Imm` lend is excluded by R-T1 or `↭`, and have not verified that any obstruction is real",
   and drop the sentence about relaxing `Stop` alone. *Revision:* (a), at AT02's machine run.
   `at02_imm_end` (every world meeting `SliceShape`) ends AT02's run at `Foo` in the configuration
   a 6.64 lend gives: `c ↦ imm({α}, inj₁ (), ∅)`, with 6.64's record in the visible frames and in
   the index. It arises (`imm_arises`: `TW.alloc`, then `TW.immFrame`; `imm_tagged`). It meets
   every other conjunct of `RunFrame` at the nil index, and fails R-T1, `↭`
   (`not_updV_empty_immRes`, by `not_upd_of_new_imm`) and `M.Upd`. `StopVisible` excludes its
   visible frame at every index (`not_stop_imm_of_stopVisible`). Each claim is now about that end:
   "So relaxing `Stop` alone does not admit this end" (§0), "R-T1 and `↭` for a 6.64 frame
   (`at02_imm_end`, AT02's run)" (§5.4's AT07 edit), "R-T1 and `↭` both exclude the end at AT02's
   stop" (§5.5). The unwinding constant's term is the same for 6.64 and 6.65, so the end is AT02's
   machine run; AT02's callback reads through `withswap`, which a 6.64 lend does not type, and no
   6.64-typed program is built. No claim is made that R-T1 or `↭` excludes every `Imm` lend open at
   a stop, and an `Imm` lend carried open is not built (§4).
