# Scope: borrows held across suspension (#791)

Part of #771, the tree track. Branch `tree-791`, from `tree-core` (666485be). SPEC §62;
`structure.md` §4–§6; `scope-781.md` D2, D5, D14; `scope-806.md`; `scope-782.md`. This doc is for
review. No proof code lands until it is agreed.

**Kernel target.** Lends with a non-empty escrow, and reborrows of the escrow's contents, `imm`
and `mut`, at any depth (a reborrow of a reborrow), open and end at `twp`/`cerwpT`, with canonical
images. A stored task holding such a reborrow across a park stays resumable through the scheduler
headline on `tree-core` (`poolSchedAdequacyT`; #795's `PoolTJ` once it lands). No assumed-fact
hypotheses.

**Lean checks backing this doc.** Two scratch files, kept in `~/repos/scratch-archive/791/`, each
checked with `lake env lean` in this worktree, no errors, no `sorry`:
- `Check791.lean`: the record type, the typed world `TWC` with every constructor, `TemplCoh`,
  `TemplAtC`, `RecRRL`, and `retakes_of_le` (proved).
- `Check791Core.lean`: the statements `TwpReb`, `TwpRebEnd`, `TwpRebDeep`, `CerwpTMFrame` and
  `CerwpTMAntiFrame` as elaborating `def … : Prop`, with the definitions they need (`CellFoldT`,
  `opTableGT`, `MFPostT`, `codeP`, `OpTabT.MustResume`).

The spike (`reb-spike` 82e32697, `experiments/RebSpike/RebSpikeC.lean`) and Core's canonical-image
experiment (`reb-canon` 18b15971, `experiments/DtorUnwind/DtorUnwind/SI/TWNC.lean`,
`CanonDeep.lean`, `CanonRef.lean`) were read only. The chain-side frames across stops are on the
local branch `tree-inv` (92b6cc49), `experiments/DtorUnwind/DtorUnwind/SI/StopFrameN.lean` and
`AntiStopN.lean`.

## 0. Every open design item, starting from Core's answer

The rule for this section: Core (the chain world) already settles reborrows, deep reborrows,
canonical images and `mut` reborrows. Each item cites Core's answer first and ports it. A
tree-specific design appears only where a step of Core's answer does not carry over, and the
step is named.

| # | Item | Core's answer | Port | Lean check | Fence |
|---|---|---|---|---|---|
| O1 | Canonical image of a record | one template per record, a `Classical` choice: `tmpl r` (`TWNC.lean:42`), `canon r β = relRes r.R β (tmpl r)` (`TWNC.lean:49`) | **the template stored in the record** (`RecC.C`) | `TWC` elaborates | (b) below |
| O2 | Chain-view template (`rebDeep`, any depth) | `tmplD r S₀ u₀ w₀` (`TWNC.lean:82`), `canonD` (`TWNC.lean:90`), `TemplDAt` (`CanonDeep.lean:36`) | per-record `RecC.D : Loc → TRes`, keyed by the chain position | `viewWit`, `TmplDOK`, `TWC.rebDeep` elaborate | depth fence below |
| O3 | Two entries with one base carry one template | automatic: `tmpl` is a function of the record | invariant `TemplCoh` | `TemplCoh` elaborates; not proved | one entry per base |
| O4 | A typed image exists at `immFrame`, non-empty escrow, any code | `reborrow_vShape` (`Support/TypedWorld/ReborrowShapes.lean:36`): a typed value has a typed `↺` image | port at the codes, by induction on `KTy` | not checked | a decidable class of codes |
| O5 | The canonical image is typed at `β`, not only at the template's own lifetime | `canon_reb` (`TWNC.lean:68`), `relabel_reb` (`Core/Images.lean:918`), `reb_wit_stratum` (`Core/Images.lean:1068`); typing at `β` only for `ref S` records (`canon_ref`, `CanonRef.lean:22`) | port; extend `canon_ref` to each code former | `retakes_of_le` **proved** (the spike's `Retakes` premise is gone) | a decidable class of codes |
| O6 | `✓` of the image against an arbitrary frame (the piece the spike did not build) | `canon_escrowAgree` (`TWNC.lean:329`), `canonD_escrowAgree` (`CanonDeep.lean:210`), `rebReentryAgreeC` (`TWNC.lean:357`), from `TWNC.templ` (`TWNC.lean:246`) and `TWNC.templD` (`CanonDeep.lean:88`) | port as `TWC.templ` (`TemplAtC` at every record) | `TemplAtC` elaborates; not proved | none (a failure stops; §7) |
| O7 | `twp`-level premises for the reborrow end (`RebEndRecT` reads the world) | `TW.rebEnd`'s `RebEndRec` (`Core/World.lean:157`), read at one record | derive from the tag (`FrameLifeT`) and the lend cell's flattening (6.33) | not checked | keep `RebEndRecT` as a premise read at the run's resource and the tag |
| O8 | A `mut` reborrow | `withbor3` = Anti-Frame 6.66 then Mut Frame 6.65 (`withbor3_compatX`, `Core/Compatibility.lean:1109`; `wpTS_M_frameX`, `Core/FrameRules.lean:346`; `wpTS_M_antiFrameX`, `:550`). Across a stop: fold at the stop, lend again at the resume (`erwp_M_frame`, `StopFrameN.lean:320`); seal at the stop under the guard `CellFold`, open again at the resume (`erwp_M_antiFrame`, `AntiStopN.lean:257`); both together `erwp_withbor3` (`AntiStopN.lean:515`) | port to `cerwpT`: `CerwpTMFrame`, `CerwpTMAntiFrame`. **No `mut` records, no mask** | both statements elaborate; not proved | segment-local `mut` frames |
| O9 | `mut` lend whose lender is in another task | scoped join: the borrow moves to one child and comes back at the join (`reb-canon` d8d52e1b, `CrossProgM`) | rides on #795's join (`PoolTJ`) | not checked | the lender is the borrowing task |

### O1. Where the template lives

**Core's answer.** One typed image per record, chosen once (`tmpl r`, `Classical.choose` of
`TmplSpec r`), and every reborrow image the template re-taken at `β`. The world reads no choice.

**The literal port is already in the library**: `tmplT`, `tmplR`, `canonT`
(`Support/Model/Tree/World/Records.lean`), the `Classical` choice at the current tree.

**The step that does not carry over: `TWNT.reread`.** The chain world never re-reads. The tree
does, and `TemplAt` across a re-reading needs the new tree's choice to be the re-reading of the
old one (`templAt_reread`, `Templ.lean:112`, takes exactly that as its `htc` premise).
`tmplT K' Θ' r'` is a `Classical.choose` at the grown tree, unrelated to `tmplT K Θ r`. This was
not derived and no obstruction was verified: a statement about two unrelated `Classical.choose`
values has no Lean configuration either way. What is known is that the specification does not
pin the template down: Core's `reb_witness_choice` (`RebAcrossN.lean:139` on `reb-canon`) gives
two incompatible typed images of one escrow at `ref (thunk C)`. At the codes the analogue is
`ref (imm a 1)` (two images whose witnesses' `imm` cells have different lifetime sets). It was not
built here.

**What tree-core did instead, and why it fails.** It carried the choice in the world
(`TWd.tc`, `TcCarried`). Spike 1 (`reb-spike` e3ce7203, `RebSpike.lean`) is a Lean configuration
with every hypothesis discharged: `twp`'s start world carries an arbitrary choice
(`twp_tc_irrel`), and at the empty choice `tc0` an open `imm` lend with a non-empty escrow admits
no reborrow (`config_tc0`, `no_reb_tc0`, `tcCarried_pins`).

**Port.** Keep Core's per-record choice and store it where the re-reading carries it: in the
record. `RecC.C` is fixed by `immFrame` and re-read with the record (`RecRRL`). `canonC r β =
relResT r.b.R β r.C` is `canon` with `tmpl r` read off the record. Spike 2 checked this
(`reb_anyStart`, `canonC_wit`, `park_config`, `keepRelC_canon`). `templAt_reread` ports as is: its
`htc` premise becomes a clause of `RecRRL`.

**Alternative (b), structural template, for the user.** At the codes every former's
interpretation is exact in its resource (`vUnit`, `vRef`, `vImm`, `KTy.interp`'s `mut` clause,
`Support/Model/Tree/Reread.lean:385–405`, `Codes.lean`). So one typed image is definable without
choice: at a `ref` position `ℓ ↦ imm({α}, w, R∖ℓ)`, at a `mut` position `ℓ ↦ imm({α}, m.v,
m.wit)`, an `imm` position kept, recursion through `+` and `[a]`. It re-reads with the escrow, so
`TWNT` needs neither `tc` nor a record field. Not checked. What it gives up: it exists only while
records' types are codes. Core's choice exists because `ref (thunk C)` (and type variables, `μ`,
`⊗` with imprecise components) have no definable image. Lineage records take the payload type of
a `Mut` position as their type, so #790 (`Mut` at any semantic type) would put an imprecise type
on a record and force (a) after all. "Nothing merges that later PRs would throw away" therefore
favours (a). **Recommendation: (a).**

### O2. Chain views at any depth

**Core's answer.** `tmplD r S₀ u₀ w₀`, a choice keyed by the record, the position's type and value,
and the view's escrow `w₀`. **The step that does not carry over:** the key `w₀` is a resource,
and a re-reading changes it, so a stored function keyed by `w₀` would need re-keying at each
re-reading. That is `TcCarried`'s problem again, per record. **Port:** key by the chain position
`l₀`. Given the record, `S₀` and `u₀` are determined by `l₀` (`chain_unique_rec`,
`Core/Images.lean:1493`; tree: `chain_unique_recT`, `InvReb.lean:20`), and `w₀` is determined by
`TemplAtC` (the view at a root carries `C`'s witness, the view at a deeper position the parent's
`D`'s). So `D : Loc → TRes K` is the same information. Locations do not change under re-reading,
and `RecRRL` re-reads `D` pointwise.

Depth is not fixed. A reborrow of a reborrow is either `rebDeep` at a deeper chain position (the
witness comes from `D` of the parent position: `viewWit`), or `reb` at a lineage record (a `Mut`
position of the escrow; its own `C` and `D`). Both are uniform rules. Fence, if `TmplDOK` cannot be
kept: `rebDeep` only at root positions (`p₀ = none`), which gives up a reborrow of a deep
reborrow through `ref` positions and keeps the one through `Mut` positions (lineage). Stated on
configurations: `ChainT … (some _) …` excluded at `rebDeep`.

### O3. Coherence

**Core's answer.** None is needed: `tmpl` is a function of the record. **Port:**

```lean
def TemplCoh (rs : List (RecC K)) : Prop :=
  ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.b = r₂.b → r₁.C = r₂.C ∧ r₁.D = r₂.D
```

**Route.** An invariant of `TWC`, by its induction. `immFrame`: the new entries' bases are apart
from the old ones by `ex`/`ag` disjointness, the argument of `TWNT.exclUnique` (`EscBeneath.lean:50`)
read at the lent locations, and within `ds` the premise `TemplCoh ds` (any choice that is a
function of the base meets it). `immEnd`: sublists. `reread`: two re-read entries with one base
come from entries with one base (`RR.inj_of`, `Coherent.lean:400`, under `TWNT.mutOne`), and the
re-reading is a function (`RR.func`). With it, `ExclUniqueT` (`EscBeneath.lean:45`) stays a
statement about full records. **Fence:** "one entry per base" (`(rs.map RecC.b).Nodup`) as a
`TWC` invariant, which makes coherence trivial. It gives up nothing if duplicates never arise.

### O4. A typed image exists at the opening

**Core's answer.** `reborrow_vShape` (`Support/TypedWorld/ReborrowShapes.lean:36`), by induction on
the type: `box α ⟦T⟧ ⊨ ↺_α ⟦Imm̲ T⟧`. **Port:**

```lean
def TmplExists : Prop :=
  ∀ (K : WCactus) (Θ : CodeTy) (T : KTy) (v : BoCa.Val) (R : TRes K) (α : Life),
    (T.interp Θ).P K v R → R.InStratum (TSet.single α) → CovR (sem Θ) K R →
    ResUT.Valid R → ∃ C, TmplAt Θ α R T v C
```

The route is induction on `KTy` (six formers), each case `reborrow_vShape`'s. Not checked. **Fence:**
`immFrame` takes `TmplAt Θ α R T v C` as a premise (it does in `TWC`), and the lend rule is offered
at the codes where `TmplExists` is proved. The class is decidable on `KTy` (a predicate by
recursion); what it gives up is lending values whose code lies outside the class.

### O5. The canonical image typed at `β`

**Core's answer.** `canon_reb` makes `canon r β` an image at every `β` the escrow lies above, and
`canon_ref` types it at `ref S`. Core's `TWNC.reb` keeps the typing as a premise at other types.
**Port:** `canonC_typed : TmplAt Θ α R T v C → K.le β α → R.InStratum {β} →
((T.immReborrow β).interp Θ).P K v (relResT R β C)`, by induction on `KTy`, `canon_ref`'s proof at
`ref`. The spike's scope premise `Retakes` is **discharged**: `retakes_of_le` (`Check791.lean`,
proved) derives it from the template's own image at `α` (`ResUT.reb_src`) and `β ⊑ α`
(`ResUT.InStratum.mono`). `β ⊑ α` is what `RebRecLeT` gives at a non-empty escrow. **Fence:** as O4.

### O6. The image composes with any frame

The spike stopped here: at an arbitrary frame, `✓(fρ ● c)` needs every view of the frame at the
record's roots to carry the template's witness. **Core's answer.** `TemplAt` is an invariant of the
typed world (`TWNC.templ`, by the transfer lemmas `reb_like_back`, `frame_transfer`, `end_back`,
`lift_view`). From it the canonical image agrees with every typed world holding the record
(`canon_escrowAgree`), which is `[TR]` 6.55's `EscrowAgree` input. **Port:** `TWC.templ :
TWC K Θ W ps rs → ∀ r ∈ rs, TemplAtC W r`, with the tree's transfer lemmas (`Images.lean`,
`InvReb.lean`, same names), the `reread` case being `templAt_reread`/`templDAt_reread`
(`Templ.lean:112, 127`). No fence: if `TWC.templ` fails, `twp_reb` has no proof (§7).

### O7. The reborrow end at `twp`

`TWNT.rebEnd` asks `RebEndRecT K W' rs r.R β`, read at the whole end world. A run does not see the
world. **Route:** derive it inside `twp_update`'s step from `RecInv`. The tag `α` of `r` bounds
every view of the lineage (`FrameLifeT`), and `ag` of the lend cell carries `⦇R⦈` at `α` (6.33), so
a walk cell at `m` below `β ⊑ α` has a cell at `l₀` with a longer lifetime. Not checked. **Fence:**
`twp_rebEnd` takes a run-level premise, "the run's resource holds no view of `r`'s lineage
shorter than `β` that is not covered at `l₀`". It is stated on configurations and decidable on a
finite resource. What it gives up is ending a reborrow while a deeper reborrow of it, at a shorter
lifetime, is live elsewhere.

### O8. `mut` reborrows

**Core's answer.** A `mut` reborrow is `withbor3`: the Anti-Frame (6.66) opens the held `mut` cell
`ℓ ↦ mut(β, v, σ, P̂)` into `ℓ ↦ own(v) ● σ`, and a Mut Frame (6.65) lends `ℓ`, or a cell inside
`σ` (a boxed field), at a shorter lifetime. Every reborrow `TWNT` makes is `imm` (`KTy.immReborrow`
sends `Mut` to `Imm`, as printed `Imm̲`). Across a stop, Core's chain relation (`erwp`, `tree-inv`)
does at the stop what the printed proofs do at the return:
- the Mut Frame folds the borrow back at the stop (`ℓ ↦ mut` to `ℓ ↦ own ● χ`, by 6.27 at the top of
  `π`) and lends it again at the resume, by induction on the index (`erwp_M_frame`);
- the Anti-Frame seals the cell at the stop and opens it again at the resume, under the guard
  `CellFold` on the stop's share (content in the cell's family). The guard is produced by the
  inner Mut Frame's fold (`erwp_M_frameF`, `AntiStopN.lean:312`), or by a frame around the
  callback (`erwpG_frame`, `:440`). The tables are must-resume (`OpTabN.AFOK`, `LendOK`).

At a stop the flattening is therefore the one before the frame. That is why no record and no mask
is needed. It is also what `MutOne`, `InvKeptA` and `UpdA`'s ancestor cases expect: the `mut` cell
at a stop is the same stored cell, with its code, at the top of the share.

**Port.** Both rules at `cerwpT` (`Check791Core.lean`, elaborating):

```lean
def CellFoldT (l : BoCa.Loc) (A : KTy) : (w : TWd) → TRes w.K → Prop := fun w ρ =>
  ∃ (u : BoCa.Val) (χ R rest : TRes w.K), (A.interp w.Θ).P w.K u χ ∧
    ResUT.CompS (ResUT.single l (CellUT.ownOf u)) rest ρ ∧ ResUT.CompS χ R rest

def opTableGT (T : OpTabT) (G : (w : TWd) → TRes w.K → Prop) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧ G w ρk ∧ contShareT en F k w ls O K v Ψ ρk
```

`CerwpTMFrame` and `CerwpTMAntiFrame` are in §3. The tree-specific changes are three. The cell's
family is its location's code read at the world (`codeP`, E1), not `Φ l`'s `F k`. The resume is at
an extension, so the re-lent cell is the re-read one (`RC.mut_inv`). The lend's lifetime is a fresh
child (`twp_extend`), which is a proper tree extension.

**Fence:** `mut` frames scoped within a segment (the body's table has no stopping entry, a
decidable condition on `OpTabT`). It gives up writable borrows held across a suspension
(`async-field-await-mut.bc`'s shape).

### O9. A `mut` lend whose lender is in another task

Fold-at-stop needs the borrow at the top of the lender's `π` at its stop. When the lender parks
while a stored child holds the borrow, it is not there. **Core's answer** is the scoped join: the
borrow moves to exactly one child and comes back at the join. On the tree that is #795's join
(`PoolTJ`). It is in progress on `tree-795` (df252c64, `Core/TreePoolShare.lean`, `PoolTJ.deposit`)
and not on `tree-core`. It collects a joiner's `imm` copies. Whether it carries a `mut` borrow
moved to one child and back was not checked.
**Fence:** the lender is the borrowing task (same-task frames). The §4 instance is in that class.
This item is not part of #791's done-when unless the user says otherwise (choice 3).

### #790's constraints

1. **Is the template fixed to a code?** No. `C : TRes K` and `D : Loc → TRes K` are resources. Only
   `TmplAt`'s typing clause reads `T`, through `(T.immReborrow α).interp Θ`. `TWd.tc`, the one
   `KTy`-indexed object, is deleted. What #790 must change: lineage records at `Mut` positions take
   the payload's type as their type (`MutPosT … S`). With `Mut` at a semantic payload, `FrameBaseT.T`
   (or `TmplAt`'s typing clause) must read a semantic type. Under (a) that touches `TmplAt` only.
   Under (b) the structural template would stop existing (O1).
2. **Is re-reading generic in the location typing?** `RecRRL (Θx : LocTy)` is (`Check791.lean`).
   `RecRR Θ' := RecRRL (sem Θ')`. This doc proposes stating `RecsRR`, `SRecsRR` and `KeepRel` over
   `LocTy` in the same pass, since the record pass touches every one of them. Cost is small:
   their proofs read `RR` only.
3. **The index.** The design adds no index: templates are index-free resources, and at the codes
   their typing is index-free. Core's chain relation answers the index question one way #790's
   doc does not list. The cell invariants are families indexed by the step, `Φ : LocFam`, a
   parameter of `erwp` read at `F k` (`erwp_M_frame`'s `n ≤ j`, `F j`). That is a fourth reading
   beside #790's three: the index in the relation's location family, not in `TWd` or `WInv`. O8's
   port uses `codeP` (index-free). If #790 adopts Core's `LocFam`, `codeP`, `CellFoldT` and
   `MFPostT` become `F k` and the O8 proofs follow `erwp_M_frame`'s index handling verbatim. This
   neither blocks nor pre-empts #790.

## 1. The record change

**The type** (`Check791.lean`, `#check @RecC.mk : FrameRecT K → TRes K → (Loc → TRes K) → RecC K`).
In the library, done in place:
- today's `FrameRecT` is renamed `FrameBaseT`. Positions, chains, lineages (`SubRecT`, `LinPathT`,
  `DescRT`, `LinLocT`, `FrameLifeT`) and `TIT` stay on bases, unchanged;
- the new `FrameRecT` is

```lean
structure FrameRecT (K : WCactus) where
  b : FrameBaseT K   -- location, value, escrow, code
  C : TRes K         -- the root template, fixed at the opening
  D : BoCa.Loc → TRes K  -- the chain-view template at each chain position
```

  with `abbrev`s `FrameRecT.le/v/R/T := r.b.…`, so `r.le`, `p.R` read as before and the statements
  of `twp`, `EndT`, `cerwpT`, `contShareT`, `KeepRel`, `RecInv`, `SplitT`, `recMask`, R1–R4 and
  `poolSchedAdequacyT` keep their text;
- `RecRR Θ' r r'` becomes `RecRRL (sem Θ')`: base re-read, `RR` on `C`, and `RR` on `D` at every
  location;
- `TWd` loses `tc` (`TWd' := ⟨P, Θ⟩` in the check). The headlines' `w₀ P` becomes `⟨P, fun _ => none⟩`.

**`TWNT`** becomes `TWNT K Θ W ps rs` (no `TChoice`). The constructors are `TWC`'s in
`Check791.lean`, which elaborates (`#check @TWC.immFrame`, `@TWC.rebDeep`, `@TWC.reread` are
printed in the check's output). Against today's `TWNT`:
- `immFrame` gains `TmplAt Θ α R T v C`, `TmplDOK Θ α ⟨b, C, D⟩`, the same at every `d ∈ ds`, and
  `TemplCoh ds`; `ds`'s membership reads bases (`ds.map RecC.b`);
- `reb` reads `c = canonC r β` (was `canonTc tc r β`);
- `rebDeep` reads `c = canonDC r l₀ w₀ β = relResT w₀ β (r.D l₀)` (was `canonDTc tc S₀ u₀ w₀ β`);
- `immEnd` keeps the surviving entries (`d ∈ rs' ↔ d ∈ rs ∧ ∃ p ∈ ps', DescRT p.b d.b`);
- `reread` loses `TcCarried`. The re-read lists are `Forall₂ (RecRRC Θ')`, templates included;
- every other constructor is unchanged.

**Deep reborrows: the chain-view template and its coherence.** O2. `D l₀` is the template of the
view at chain position `l₀`. `TmplDOK` asks it to be a typed image of `viewWit r p₀ l₀` (from `C` at
a root, from the parent's `D` below). Coherence is `TemplCoh`'s second clause (O3).

**How `mut` reborrows fit.** O8: they need no record. `mut` cells have one holder (`MutOne`,
`TWNT.mutOne`). Folding at a stop returns the share to the flattening the frame started from, so
`UpdA`'s `mut` clauses and `InvKeptA` (`UpdAInv.lean:102`) see the stored cell with its code at both
ends. The ancestor cases (`Beneath`) arise at `imm` reborrows through `Mut` positions: `reb` at a
lineage record puts a view over a `mut` cell, and that cell then sits beneath the view.

## 2. What the record change touches

Statement changes only where the record type or the choice index appears. Sizes are estimates
of lines touched, mostly mechanical.

| File | Change | Statement changes? | Size |
|---|---|---|---|
| `World/Records.lean` | `FrameBaseT` rename; new `FrameRecT`; `RecRR` → `RecRRL`; `TWNT` without `tc`, constructors as `TWC`; `TChoice`, `canonTc`, `canonDTc`, `UsedT`, `TcCarried` deleted; `tmplT`/`canonT` kept only if (b) | yes (the definitions themselves) | 250 |
| `World/Templ.lean` | rewritten: `TemplAtC`, `TemplCoh`, `TWC.templ`, `TWC.templCoh`; `templAt_reread`/`templDAt_reread` kept with `htc` from `RecRRL`; `TcCarried.rec`, `tcCarried_refl`, `TcCoherent`, `tcCoherent_of_inj`, `tcCarried_exists`, `TWNT.templ_reread` deleted | yes | −150, +500 |
| `World/World.lean` | `TWd.tc` removed | `TWd` only | 10 |
| `World/Recs.lean` | `RecInv` without `w.tc`; `TaggedT` reads `p.b`; `RecsRR`/`SRecsRR` over `LocTy` | `RecInv`'s body | 40 |
| `World/TInv*.lean`, `InvBase`, `InvMid`, `InvReb`, `InvSimple`, `InvUses` | `TIT` stays on bases; `TWNT.inv`'s induction gains binders (spike: `TWC.inv`, 25 lines, by the same `tit_*` lemmas) | no | 120 |
| `World/Coherent.lean` (`TWNT.mutOne`), `EscBeneath.lean` (`TWNT.exclUnique`), `NoOwnUnder.lean`, `FdEsc.lean`, `FdEscBranch.lean`, `StepKeep.lean`, `ExtExtF.lean` (R4's `tc tc'` dropped), `Clause3.lean` | `TWNT` inductions gain binders; `exclUnique`'s `immFrame` and `reread` cases read `TemplCoh` | R4 loses `tc tc'` | 400 |
| **#806**: `World/UpdA.lean`, `UpdAFrame.lean` (`RecMaskClosed`, `recMaskClosed`), `UpdAInv.lean` (`InvKeptA`, `fdEsc_of_updA`), `UpdATrans.lean`, `UpdAGrow.lean`, `RecMask.lean`, `UpdX.lean` (`recMask`, `recMask_rr`) | read `p.le`, `p.R` through the abbrevs; `recMask_rr` reads `RecRRL`'s base clauses | no | 60 |
| `World/ExtF.lean` (`KeepRel`, `extFT`, `RelFT`) | `RecRR` → `RecRRL`; `KeepRel` over `LocTy` | the `LocTy` generalisation only | 50 |
| `Core/TreeWp.lean`, `TreeWpEff.lean` | `RecInv`'s `tc` gone from the proofs; `twp_updateW` added (the update whose continuation is chosen at the start world, as `twp_extend`) | no | 80 |
| `Core/TreeLend.lean` | `lendRec` gets `C := ∅`, `D := fun _ => ∅` (`tmpl_empty`); `twp_lendOpen`/`twp_lendEnd` generalised to non-empty escrows (§3) | the generalisation | 600 |
| `Core/TreeHeap.lean`, `TreeConsume*.lean`, `TreeHandle.lean`, `TreeCactus.lean`, `TreeStepKeep.lean`, `TreeResume.lean`, `TreePool*.lean`, `TreeSched*.lean`, `TreeBorrowEdges.lean`, `TreeSem*.lean`, `TreeHeadlines.lean` | anonymous constructors (`⟨l, v, R, T⟩`, about 20 sites); `TWNT … tc` hypotheses (about 195 occurrences in 33 files, by the spike's count) lose `tc` | `w₀ P` in the headlines; no other | 600 |

Totals: about 2.2k lines touched, about 0.5k of them new. Spike 2's estimate on `si-781d` was of the
same order: about 16 `TWNT` inductions, about 40 `RecRR` destructures, 20 constructors.

## 3. The theorem statements

All elaborate in `Check791Core.lean` against today's names. There the template is passed
explicitly (`C`, `D`); after the change it is `r.C`, `r.D`.

- **`twp_reb`** (`TwpReb`). At `(r, α) ∈ ls`, `β ⊑ α`, the run holding the view `ρ.get le =
  immOf s r.v r.R`, the run continues from `ρ₀ ● relResT r₁.R β r₁.C` at every extension. The
  continuation is Kripke in form because the image's definedness is known only at the start world,
  from `TWC.templ` (O6). The proof is a `twp_updateW` instance: `TWC.reb`; `RebRecLeT` from the tag
  and `ExclUniqueT.parent`; `✓` from `canon_escrowAgree`'s port; `UpdX` masked at the run's records.
  The image's cells are at `r`'s escrow locations, which the record's owner masks, and a reborrower
  that does not own the record has `imm` cells there, kept or given up (`UpdA`).
- **`twp_rebEnd`** (`TwpRebEnd`). The run gives back `c.restrictDom r.R.exclPart` for an image `c`
  of `r` at `β`. No world premise (O7).
- **`twp_rebDeep`** (`TwpRebDeep`), and `twp_rebEndDeep` likewise, at any chain position `l₀`, the
  image `relResT w₀₁ β (D₁ l₀)`.
- **Lends with a non-empty escrow**: `twp_lendOpen`/`twp_lendEnd` with `ℓ ↦ own(v) ● R` for `R` typed
  at `T` (`R ∈ Res_α`), the record `⟨⟨ℓ, v, R, T⟩, C, D⟩` with `C`, `D` from O4. The end's condition
  becomes `FdEsc ℓ R` (the general `immEnd_valid_of_fdEsc`), replacing `FdEsc ℓ ∅`. The records
  that leave are the record and its lineage.
- **`mut`**: `CerwpTMFrame` and `CerwpTMAntiFrame` (O8), and `cerwpT_withbor3`, `erwp_withbor3`'s
  port, as their composite. Still to add to `CerwpTMFrame`: the chain premise `ρb ∈ Res_{↓α}` (the
  frame outlives the lend). It is not in the elaborated text yet.
- **The template invariant and its preservation.** `TWC.templ : TWC K Θ W ps rs → ∀ r ∈ rs,
  TemplAtC W r`. `TWC.templCoh : TWC K Θ W ps rs → TemplCoh rs`. `TWC.tmpl : … → ∀ r ∈ rs,
  TmplAt Θ (tag) r.b.R r.b.T r.b.v r.C ∧ TmplDOK …`, kept by re-reading as `tmplSpec_rr` in the spike.
- **Resumability across a park.** No new headline: `poolSchedAdequacyT` as it stands. The new content
  is a stored share holding an image (or a sealed `mut` cell) that is a value of its type at the
  resume list. That is `keepRelC_canon` (spike) generalised, `canonC_rr` with `Retakes` discharged by
  `retakes_of_le`, at `KeepRel`. With #795, `PoolTJ` replaces `PoolT` in the instance, statement
  unchanged.

## 4. The hardest case, kept in

**Shape.** Under `HS` (`Core/TreePoolSpawn.lean`), through `poolSchedAdequacyT`, every premise
discharged:
1. Task B allocates `ℓ_B`, opens an `imm` lend of it (empty escrow or not), and parks.
2. Task A allocates `c ↦ own(loc k) ● k ↦ own(())` (code `ref (ref 1)`, so `k` is the boxed field).
   It opens a Mut Frame on `c` at a fresh child `α` (`twp_extend`, a proper tree extension). Then
   it takes a `mut` reborrow of the field: Anti-Frame on `c`, Mut Frame on `k` at a fresh child
   `α′ ⊏ α` (a second proper extension). That makes two levels: the borrow of the record, then the
   reborrow of its field.
3. A parks (`await`) holding the field's borrow. At the stop, `k` is folded and `c` is sealed
   (`CellFoldT` from the fold). The share is `c ↦ mut(α, …)`.
4. B resumes and ends its lend (`twp_lendEnd`, its condition from the resumer's guarantee).
5. A resumes at `KeepRel`, after the tree grew. `c` is opened again and `k` lent again, re-read.
   A ends the reborrow (Mut Frame end on `k`, Anti-Frame end on `c`), ends the outer Mut Frame and
   frees both.

This is #770's target shape at the codes, one step past it. `async-field-await-mut.bc` holds the
record's `mut` borrow across `await` and modifies the boxed field between awaits. Here the field's
own borrow is held across the `await`. One condition is spelled out: the outer borrow is A's
own. A lender in another task is O9. A companion instance exercises the `imm` side at depth 3:
A holds `reb r`, then `rebDeep` at a deeper chain position, then `reb` at a lineage record of a
`Mut` position (a view over a `mut` cell, `UpdA`'s ancestor case), across the same park, then ends
all three.

**What the instance needs.** O1–O8 except O9; `twp_extend` at a fresh child; the scheduler's
existing facts (`contShareT_resume`, `KeepRel.trans`, `stepKeepsFdEsc`).

## 5. Risks, ranked

| # | Risk | Lean check | Note |
|---|---|---|---|
| 1 | O8 at `cerwpT`: a frame rule must rewrite what a stop owes (`Ψ` is `cerwpT` itself), which the tree has never done ("frame rules as instances of capture", condition 20). `erwp_M_frame`'s induction on the index has to go through `cerwpT`'s well-founded definition and `contShareT`'s Kripke wand. A further subpoint: `CerwpTMFrame`'s `w.Θ l = some A` is at `w`, while the run starts at an extension where `l` (an `own` cell) may be re-typed, so the proof re-types it back at the start | statements elaborate | the largest unknown; Core's chain proofs are about 900 lines |
| 2 | O6, `TWC.templ`, at `reread` and `immEnd` with per-record templates | not checked | Core's proof is by the same transfer lemmas, which exist at the tree |
| 3 | O7, `RebEndRecT` from the tag | not checked | fence available |
| 4 | O4/O5 at `mut` and `box` positions: `d.R ∈ Res_α` for lineage records, needed for their template at `α`, rests on `Above` being transitive through a `mut` cell's witness | not checked | fence: a code class |
| 5 | O3 at `reread` (`RR.inj_of` needs `MutOne` of a world containing both escrows) | not checked | fence: one entry per base |
| 6 | #790 later puts semantic types on lineage records (O1) | — | (a) absorbs it in `TmplAt` |

**Size.** Record change 2.2k (§2). O2–O7 and the `imm` rules about 3k. The `mut` rules at `cerwpT`
2–3k. The two closed instances 1.5–2.5k. Total about 9–11k lines.

## 6. Not doing

- Fixing a depth: no statement names a depth, and no proof argues per level.
- `imm` only: O8 is in the done-when.
- An instance at `TWd.Ext.refl` only: both §4 instances open their lends at fresh children.
- Hypotheses on `twp_frame`, or on any headline.
- Per-location splits where the walks are needed (`UpdA` stays along the walks; D5).
- Routing around the template invariant: `twp_reb`'s `✓` comes from `TWC.templ`, never from a
  premise of the rule.
- A `mut` record or mask in place of Core's fold/seal at the stop (O8), unless the user picks it.
- Re-opening tree-core's D14 (`imm` lends open and end as two `twp_update` instances).

## 7. Kill criteria, set before the result

- **Proved** (every §3 statement, both §4 instances through `poolSchedAdequacyT`, axioms ⊆ the
  three) → build lands.
- **A design item fails as a Lean configuration** (every hypothesis discharged) → take that item's
  fence from §0 and report what it gives up. O6 has no fence: its failure stops the unit.
- **Undetermined** → report the exact step that did not follow, with the unspent hypotheses, the
  unused uniqueness results (`RR.func`, `RR.inj_of`, `chain_unique_recT`, `ExclUniqueT.parent`),
  and which of Core's lemmas cited in §0 are not yet ported.

## Choices for the user

1. **Template (O1):** (a) per-record `C`/`D` in the record (recommended; Core's per-record choice
   stored where the re-reading carries it), or (b) a structural template at the codes (no record
   change; it stops existing once a record's type is imprecise, which #790 brings).
2. **`mut` (O8):** port Core's fold/seal at the stop (recommended), or `mut` records with masks
   (D14's shape for `mut`, not Core's).
3. **Cross-task `mut` lender (O9):** outside #791 until #795's join lands (recommended), or in
   #791's done-when, which makes #791 wait on #795.
4. **Hardest case:** confirm §4's same-task two-level shape as #770's target. The other reading is
   a field borrow taken from a record lent by another task, which is O9.

## Appendix: R1 status (2026-11-04)

`Core/TreeMutFrame.lean` holds §3's `CerwpTMFrame` and `CerwpTMAntiFrame` as stated above, and
`not_cerwpTMFrame`: a Lean configuration, every hypothesis discharged, refusing `CerwpTMFrame` as
stated. The cause is not the stop. An `own` cell pins no code (`AgreeOn` reads `mut` cells only),
so the lender's run starts at extensions re-typing `ℓ`. The borrowed run is entered only where `ℓ`
is typed at `A` (`Cov.mut`). A frame condition reading `Θ ℓ` (`FOff`) admits the borrowed run
vacuously and refuses the lender's. This is §5 risk 1's subpoint, confirmed in Lean.

Candidate statement `CerwpTMFrameM` (elaborates; not proved): `F.Mono`, `Fb.Mono` and
`OpTabT.FdMono T` (a resume runs at `fdAt en v Fb O′`, and the resumed run re-lends there), plus
`ρ_b ∈ Res_D` with `K.DownOf D {α}` (§3's missing premise). It awaits the user's decision, since it
changes §3's text. The Anti-Frame side was not checked: its inner run may end at a world re-typing
`ℓ`. Whether that forces a closure premise on `Q` has not been derived either way.

**Next step, once the statement is agreed.** Prove the lender's side of the Mut Frame at any final
term at `twp`, the port of `rwpG_M_frameG` (`StopFrameN.lean` on `tree-inv`). That proof re-types
`ℓ` at the start (`TWd` with `Θ ℓ := A`, `F.Mono`). It enters through `TWNT.mutFold`, and needs
`TaggedT` across the fold, the lowering swap and `CovR` of the `mut` cell. It runs the borrowed
run, applies `ResUT.six27` at the end, folds, and exits through `TWNT.mutUnfold`. `↭` from `ρ₀` to
the folded end needs a six28 at `UpdA`, which does not exist yet. `InvKeptA`, `MaskDiff` and the
mask facts carry over (`l` is not in `recMask O₀`). Then comes `erwp_M_frame`'s strong induction at
`cerwpT`: a stop folds the cell into the share, and the resume re-lends at `w''` with `ℓ` re-typed.

### Why `CerwpTMFrameM` carries the frame premises (decided 2026-11-04)

Core's location family `Φ` is a fixed parameter of `erwp`. The tree's store typing lives in the
world, and `TWd.Ext` re-types every location the resource holds no `mut` cell at (`AgreeOn` reads
`HoldsMut`). A Mut Frame turns an `own` cell, which pins no code, into a `mut` cell, which pins its
location's code (`Cov.mut`). So the lender re-types `ℓ` at the start, and owes the frame condition
at the re-typed world. `not_cerwpTMFrame` is the configuration that rules out the statement
without it. Hence the four approved premises: `F.Mono`, `Fb.Mono`, `OpTabT.FdMono T`, and `houtb`.

They are met at the scheduler (`Core/TreeMutFrame.lean`):
- `fdMask_none_headline`: `fdMask ∅` meets the headline's `Fb` premise and is `Mono`.
- `TP_fdMono`: `park`'s table is `FdMono` (by `fdJoinT_fdMono`), and `fdAt` is `Mono` by `fdAt_mono`.

**Open: `park` is cancellable.** `not_mustResume_TP`: `enPark.q = .cancel`. So §4's park is at a
table that `OpTabT.MustResume` (Core's `LendOK.entry`) refuses. Core's chain proof needs
must-resume because a cancellable stop owes a cancel run (`contShareT`'s second clause). That run
ends without resuming and cannot hand the folded cell back. Core defers that case to a frame around
the lend (`StopFrameN.lean`'s header, "step 3"). It needs the user's decision before
`CerwpTMFrameM` can serve §4.

### Templates (decided 2026-11-04)

`tmplSpecT_two` (`Support/Model/Tree/World/TemplChoice.lean`): at `ref 1` over `m ↦ own(())`,
`m ↦ imm({β₁}, (), ∅)` and `m ↦ imm({β₂}, (), ∅)` both meet `TmplSpecT`, and no world re-reads both.
So which one `tmplT` picks at each tree is not fixed by the specification, which is the evidence for
option (a). Caveat: here the two differ only in the template's own lifetime, and the canonical
images agree (`canonT_view`). The witness-set variant (`ref (imm a 1)`, O1) is not built.

### Templates, the witness-set variant (2026-11-04)

`Core/TreeTemplChoice.lean`. Take the escrow at `ref (imm '3 1)`: `k ↦ own(loc j) ●
j ↦ imm({1, 2}, (), ∅)`. `●` unions `imm` lifetime sets, so the escrow lies above
`k ↦ own(loc j) ● j ↦ imm({aᵢ})` for `aᵢ = 1, 2`. Each part gives a template
`k ↦ imm({3}, loc j, j ↦ imm({aᵢ}))` meeting `TmplSpecT` (`tmplSpecT_two_wit`). `relRes` keeps the
witness, and `RC` keeps the lifetime sets in a witness. So at every `β` the two canonical images
have no common re-reading (`canon_two_wit`). The canonical images can differ. Option (a), the
per-record template, proceeds.

### `mut` and cancellable stops: option (b) (decided 2026-11-04)

`CerwpTMFrameC` (`Core/TreeMutFrame.lean`, elaborates; not proved) replaces `MustResume` with
`OpTabT.KeepsShare`: no non-abortive entry is unrestricted. At the tree a cancel is the
continuation's cancel branch, run at the same `Ψ` (`contShareT`'s second clause, #817's shape). So
the fold-and-re-lend induction treats it as a resume with no answer resource: the borrowed run's
cancel branch, re-lent, ends in `MFPostT l A Q`. Only an unrestricted entry, whose share is empty,
cannot hold the folded cell. `TP_keepsShare`: `park`'s table meets it.

**The Anti-Frame at the start and end worlds (not derived either way).** The borrowed run holds
`ℓ ↦ own(v) ● σ_P` and may end at a world re-typing `ℓ`. The outer run reseals `ℓ` as a `mut` cell,
which `Cov.mut` and `InvKeptA` read at `A`. So it either re-types `ℓ` back to `A`, owing `Q` there,
or needs the borrowed run to end with `ℓ` still at `A`. I have not built a configuration showing
the re-typing is forced. Two candidate shapes:
- a closure premise on `Q` (beyond the approved four: needs the user's OK);
- `MFPostTK`, `MFPostT` with `w.Θ l = some A`. This is closer to Core, where the cell's family `Φ ℓ`
  is fixed and the borrowed run cannot change it.

**Next step.** Prove `CerwpTMFrameC`. Start with the stop-free lender's side at `twp` (the port of
`rwpG_M_frameG`; see "R1 status" above), then the strong induction. Its stop case folds into the
share, and the resume and cancel cases re-lend at the re-typed world.

### Anti-Frame decided; where the build stops (2026-11-04)

The Anti-Frame uses `MFPostTK` (Core's fixed `Φ ℓ`), with no premise on `Q`. Its statement is
`CerwpTMAntiFrameK` (`Core/TreeMutFrame.lean`, elaborates; not proved). If proving it shows that a
real borrowed run must re-type `ℓ`, build that configuration and stop. Do not fall back to a
premise on `Q`.

**Next step, precisely: prove `CerwpTMFrameC`.**
1. **Lender's side at a final term, at `twp`** (port `rwpG_M_frameG`, `StopFrameN.lean` on
   `tree-inv`), in a new `Core/TreeMutFrameRun.lean`.
   - **Start.** Given the outer start world `w₀ ⊒ w`, form `w₀'` = `w₀` with `Θ ℓ := A`. It
     extends `w₀` on `ρf`, since `ρf` holds no `mut` cell at `ℓ`: `ℓ` is `own` in the run and the
     world is valid. Move `F` there by `F.Mono`. Re-read `BM` there; its `mut` cell is covered by
     `codeP w₀' A`.
   - **Entry.** Enter by `TWNT.mutFold`. Prove `TaggedT` across the fold (`mut_fold_ag`'s port),
     the lowering swap of `mut` for `own ● ρ_P` (`lower_swap_mut_own`'s port) and `CovR`.
   - **The borrowed run.** Apply it. `ResUT.six27` at its end finds `ℓ ↦ mut` at the top (`houtb`
     gives `Res_D`).
   - **Fold and exit.** Fold, and exit by `TWNT.mutUnfold`.
   - **`↭`.** Prove a six28 at `UpdA`: `UpdA BM ρ' fρ'` gives `UpdA ρ Y fY`. It does not exist
     yet and is the largest piece.
   - **The rest.** `InvKeptA`, `MaskDiff`, `NoneAt` and `SplitT` carry over: the records are
     unchanged, and `ℓ` is not in `recMask`.
2. **Strong induction on `n`** (port `erwp_M_frame`).
   - **Value.** A value ends as `MFPostT`.
   - **Stop.** At a stop, the borrow lies in the share. Fold it there (`extF_fold`'s port is
     `KeepRel` across the fold).
   - **Resume.** At a resume at `w''`, re-type `ℓ := A` again, move `fdAt en v Fb O′` by
     `fdAt_mono`, and apply the induction hypothesis.
   - **Cancel.** The cancel clause is the same as a resume with no answer.
3. **Anti-Frame** (`erwp_M_antiFrame`, `AntiStopN.lean`). The opening is `TWNT.mutUnfold`, the
   reseal is `TWNT.mutFold` read at `MFPostTK`'s `Θ ℓ = A`, and the stop's seal runs under
   `CellFoldT`.
4. **Then** the record change (option (a), `canon_two_wit`) and the rest of §0's order.
