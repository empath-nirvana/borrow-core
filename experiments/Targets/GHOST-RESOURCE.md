# Is there already a resource that is not lowered to the heap?

**The question** (2026-10-07). S6's probe (`Targets/I/GhostCoupling.lean`: `not_ghostCoupling`,
`lower_empty_eq`; TIER1-PLAN "Decision D5 applied") found that route 8.4 needs "an `own`-like
obligation that `ResU.Lower` does not lower to the heap, or `wpTS`'s run-end conditions read on the
run's steps". Do we already have, in BoLo as transcribed or in our extensions, a ghost or logical
resource that could carry S6's obligation? The obligation is created when a `lin`/`aff` `κ` is
captured at `[op]`, consumed at its resume or cancel, and must be gone at a run's end.

**Answer.** No. Nothing in `Paper/` or `Core/` can carry it. Every obligation BoLo's relation
enforces is an `own` cell. `own` cells bind a run only because `ResU.Lower` ties them to the real
heap. Every other component of the world is chosen existentially by whoever proves `wpTS`, so no
step of the run forces it into existence. The extensions that add ghost-like state (EffModelRel's
tokens, GhostEnd's and ProbeD1's lend stacks, Targets' `SemWorld`) are either outside BoLo's
relation or set to trivial values at Core's world.

The smallest extension that changes **no BoLo definition** goes the other way: lower the
obligation to the heap. `[op]`'s `κ` takes an ordinary `Ref 1` cell, and its resume (and, at `aff`,
its cancel) frees it. That is the pattern Core already uses for capabilities and reuse tokens
(§3). A real ghost cell kind changes printed rows 5.3, 5.25 and ↭/5.33 (§4).

Paths below are relative to `~/repos/borrow-core` (main). The cited lines are identical in
`~/repos/borrow-core-tier1`.

---

## 1. BoLo's resource algebra: nothing survives lowering

- **Cells.** `CellU` (`Paper/S5_Model/Definitions.lean:239`) has three kinds: `own v`, `imm`
  (lifetime set, value, witness/escrow `ρ`) and `mut` (lifetime, value, witness, predicate). Row
  5.3, `Cell_α ≜ own + imm + mut`, is `[as printed]` (line ~172). There is no fourth kind, and
  every cell sits at a `Loc`.
- **Lifetimes are labels, not tokens.** `Life := ℕᵒᵈ` (line 104). `LSet` (107) indexes `imm`/`mut`
  cells and the strata `Res_α`. BoLo has no lifetime-token resource: unlike RustBelt's `[κ]_q`,
  nothing is owned that stands for "lifetime α is alive". `box α`, `fresh` and `reborrow` (around
  lines 669, 678 and 1268) are predicates over cells.
- **Flattening and lowering.** `ResU.Flat ρ σ ≜ ∃ e a, ExS ρ e ∧ AgW ρ a ∧ e ● a = σ` (1679, row
  5.22). `ResU.Lower ρ m ≜ ∃ σ, Flat ρ σ ∧ ∀ l, m l = (σ.get l).map erase` (1694, row 5.25). This is
  an equation at **every** location, so the domain of the flattening is exactly the domain of the
  heap. Escrows (an `imm` cell's witness: 6.53–6.56's `ρ′`) and `mut` witnesses are pulled back
  into `σ` by `ex`/`ag` and lowered too. No component of a resource escapes `Lower`. The probe's
  `lower_empty_eq` (`GhostCoupling.lean:49`) machine-checks this at the empty heap: `Lower ρ ∅ →
  ρ = ∅`.
- **What is checked at a run's end.** `NoOwn ρ ≜ ρ|own = ∅` (1362, `[TR]` p. 6's `ρ⁺|own = ∅`),
  together with `ρ ↭ π` (`ResU.UpdV`, 1742; `UpdImm`/`UpdMut` compare only `imm`/`mut` cells). In
  a closed run, `↭` from `∅` rules out `imm`/`mut` cells in the leftover `ρp`. So `NoOwn` and the
  answer's relation leave nothing, and `adequacyD_val` (`Core/Demonic.lean:334`) gives the empty
  memory at the end. That is BoLo's only run-end obligation, and it is a statement about memory.

**Can it carry S6's obligation unchanged?** No. `[op]` (`Head.hop`,
`Paper/S3_Dynamics/Definitions.lean:502`) keeps the heap, so `Lower` makes no `own` cell appear.
`κ = kappa n H K` (438) is an ordinary λ-value, resumable any number of times.

**What BoLo already enforces.** If `K`'s frames own memory, `κ`'s share holds those `own` cells.
Dropping `κ` then leaks them and is rejected. S6's teeth R1–R3 own nothing, which is why they get
through. BoLo's linearity is linearity of resources (no leaked `own` cell), not a count of how many
times a resource-free value is used.

## 2. The typed world `TW` and its record lists

- `TW W ps rs` (`Core/World.lean:110`) is `[about ours]`, not a printed row. `ps` are 6.64 frames
  and `rs` their lineages. `ls : List SRec = FrameRec × Life` (`Core/FrameRecords.lean:159`) are
  tagged records. They are not cells, so in that sense they are the ghost part of our world;
  `Core/DelayApprox.lean:18` calls the existential `(…, ps', ls')` "its own ghost world".
- **They have the right shape.** `wpTS`'s conjuncts `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈
  ls)` (`World.lean:199`, and the same in `wpG`, `Core/EffDefs.lean:27–40`) say that a record
  created inside a run is ended before the run returns. That is a create, consume, and
  required-gone-at-run-end discipline. At a closed program `ls = []` (`cC_ret_eq`, `GhostCoupling.lean:68`),
  so an obligation recorded there *would* be checked.
- **Three reasons it cannot carry S6's obligation:**
  1. Every record is anchored to a heap cell. The only creators are `immFrame` (from `own l v`,
     `World.lean:115`) and `reb`/`rebDeep` (at an existing `imm` cell). `Tagged` (171) ties every
     `ls` entry to a `ps` record.
  2. The `↔` conjuncts forbid *net creation* inside a run. An entry created at `[op]` mid-run
     cannot be in `ls'`.
  3. The post-world `(ps', ls')` is existential, and nothing about it is read off the steps
     (`wpTS_of_headChain`, `GhostCoupling.lean:72`: a heap-preserving head step keeps any world).
     The prover can simply never record the capture.
- **Smallest change on this route:** a new `TW` constructor for an obligation record not tied to a
  cell, `wpG`'s `↔` relaxed at the `[op]` stop, and its removal tied to `κ`'s resume step. That
  changes Core's relation (`wpTS`/`wpG`), which D5 ("no change to … the relation") rules out, and
  it is the probe's second option, "run-end conditions read on the steps". `TW` is ours, so no
  printed BoLo row changes, but every `TW` induction in `Core/Invariant.lean`, `Reborrow*`,
  `FrameRules` and `Fundamental` would gain a case.

## 3. `Core/EffDefs.lean`: tables, `contShare`, `cancelOwed`

- `Table` (50), `opTable` (157), `cancelTab` (131), `cancelOwed` (138) and `contShare` (144) are
  **permissions, not debts**. `contShare` says only:
  - `q = unr → ρ = ∅`;
  - for every extension `ls'`, the share may be resumed at every answer in `PB`
    (`PB ─⋆ Φ ls' (K.plug w)`);
  - `q ≠ lin → cancelOwed`, i.e. the cancel run is safe.

  Nothing is owed. No component says "this must be used", and `cancelOwed` is offered, not
  required. The only thing that makes dropping a share fail is `own` cells inside `ρ` (§1).
- `KapRel`: not in Core (no match in `Core/`). `TabAtS` (`experiments/GhostEnd/GhostEnd/Stacked.lean:290`)
  is a stratum condition on `ρ` relative to a lend stack, a predicate rather than a carried resource.
- **Precedent for lowering a token to the heap.** Core already models non-memory obligations and
  capabilities as real cells:
  - `Core/Stdio.lean`: `stdin : Ref Input`, `stdout`/`stderr : Ref Output`, with harness
    `alloc`/`free`.
  - `Core/FoldReuse.lean:9–12`: "the reuse token is an owned `Ref 1`".
  - `Core/Dtor.lean:19`: `U(C & F 1)`'s destructor is `close`, which forces and projects to the
    second component, the cancel branch.

## 4. `[TR]` §5–6: lifetime tokens, `↭`, escrow (6.55), reborrow records

- **No lifetime tokens.** Lifetimes are the strata index (rows 5.1–5.9, transcribed above).
- **`↭`** (5.29–5.31: `UpdImm`, `UpdMut`, `UpdV`) preserves `imm`/`mut` cells by `FlatAt`. It says
  nothing about `own` cells, which are kept honest by `Lower` alone.
- **Escrow (6.53–6.56)** is the `imm` cell's witness: real cells moved under a borrow and lowered
  back through `ex`/`ag`.
- **Reborrow records** (6.150's `reb`/`rebEnd`) are ours (`TW`), anchored at `imm` cells (§2).

So `[TR]` has no ghost component. A cell kind that `Lower` skipped would be a new printed-row
variant: 5.3 gains a constructor, and 5.25 becomes "lower the non-ghost part". On its own that is
not enough. A ghost `own` cell that is not lowered is constrained by nothing in `wpTS`: `↭` ignores
`own`, and `Lower` would skip it. So any run could delete it, which is dropping `κ` again. It also
needs a persistence clause in `↭`/5.33 ("ghost cells persist except across the step that resumes
or cancels their `κ`"), which again reads the steps. Every lemma that cases on `CellU`, from 6.2
through 6.60 and on through 6.141–6.151, gains a case. *This paragraph is from reading the
definitions; I have not built that configuration in Lean.*

## 5. Experiments that add ghost-like state, and whether any reaches Core's relation

| experiment | what it adds | in Core's relation? |
|---|---|---|
| `EffModelRel/Own.lean`, `Cell.lean` (`EffCell.Tok`: `res`/`use`/`rsv`/`pl`) | multisets of ownership tokens; a ghost run `Tree.Safe`; `CancelOK`/`DropOK` for continuations | no: standalone, its own tree semantics, "imported by nothing" (README). It also bounds only what a dropped `κ` *owns*, not a use count |
| `GhostEnd` (`LStack`/`LEnt`, `TabAtS`) | a lend stack: each entry a `Loc` and a lifetime variable | no: a layer over Core. Each entry is a heap location's lend, and `TabAtS` is a predicate on `ρ` |
| `ProbeD1` (`σ`, `StackOK`, `FutOK`, `futS`) | the same lend stacks, with a future-world order | no: a probe world. Entries are lends |
| `Targets` `SemWorld` (`I/World.lean:59`: `held`, `Stop`, `share`; `B.BWorld`: `Stk`, `Fam`, `Upd`) | slots where a ghost index and a run-end check could live | at Core: `coreB.Stk = Unit` and `Fam = TW ∧ Tagged` (`B/World.lean:66`), `coreW.held = ([],[])`, and `Stop` = `wpTS`'s two `↔` conjuncts (`I/World.lean:165–169`). A non-trivial `Stk`/`Stop` is a new relation, and it still needs `Stop`/`Upd` to read the steps (§2.3) |

## 6. Run-end conditions beyond `NoOwn`

`wpTS` (`World.lean:186–199`) and `wpG` (`EffDefs.lean:27–40`) end with:
- `NoOwn ρp`;
- `UpdV ρ π`;
- `TW`/`Tagged` at the post-world;
- the two `↔` conjuncts over `ps`/`ls`;
- `Q`.

The `↔` conjuncts are the only run-end condition beyond memory (§2). `ewpTS`'s stops add only what
`opTable`/`cancelTab` allow: `NoOwn` again on abandoned errors and continuations (`EffDefs.lean:124–135`, 163–167).

---

## The smallest extension: lower the obligation to the heap (no BoLo definition changes)

**Change** (all `[spec §19]`, "no printed counterpart"):
- `kappa` (`Paper/S3_Dynamics/Definitions.lean:438`) and `Head.hop` (502).
  - At a non-`unr` operation, `[op]` hands the clause `κ` together with a fresh `c = alloc ()`.
    For example, `kappa` becomes `let c = alloc () in λs. case s {resume: free c; … | cancel: …}`,
    so the allocation goes through the ordinary `alloc` redex and the allocator (`ARun`,
    `Core/Alloc.lean:88`).
  - Resume frees `c`.
  - At `aff`, cancel frees `c`. At `lin`, cancel does not free it, matching `contShare`'s
    `q ≠ lin` gate.
  - The machine needs `q` at the operation, carried in the payload or in the clause table.
- `contShare` (`EffDefs.lean:144`): at non-`unr` operations the share holds `ptoOwn c ()`.

**Why this carries S6's obligation.** BoLo's own run-end check catches each tooth:
- R1, an `aff` capture dropped: `c` leaks, so `NoOwn` and the empty end memory fail.
- R2, a capture resumed twice: the second `free c` is stuck.
- R3, a `lin` capture cancelled: `c` leaks.

None of R1–R3 would be in Core's relation, which is exactly what `not_ghostCoupling` showed was
missing.

**What it re-proves.**
- **Unchanged:** no BoLo row (5.3, 5.22–5.33) and no `[TR]` 6.x lemma. The cell is handled by the
  existing 6.141 alloc and 6.142 free machinery and by `TW.alloc`/`TW.free`. The borrow
  guarantees stand as proved.
- **Re-proved:**
  - Core's effect fragment: `EffWp`'s `[op]` step lemmas (`ewp_handle`, `ewp_handle_vals`),
    `handleV_compatC` and the `[handle]` compatibility cases (`EffRules`), `EffCancel`,
    `EffBorrow` (a new `own` cell inside a share that spans stops), and `fundamentalC`'s effect
    cases.
  - `adequacyC`/`adequacyD`, with statements unchanged.
  - The `Targets`/`GhostEnd` probes that unfold `kappa`.
- **The design cost is to surface, not settle.** One allocation per `lin`/`aff` capture conflicts
  with "effect handling is erased" (resume-once = call) and with the zero-cost target, unless the
  backend erases an unread `Ref 1` alloc/free pair. That is a backend erasure lemma, not a change to
  the borrow calculus.

**The ghost alternative** (§4) is strictly larger. It changes printed rows 5.3 and 5.25 and `↭`/5.33,
needs a step-indexed persistence rule, and re-opens every `CellU` case of 6.2–6.151.

**Machine-checked vs. read.**
- Machine-checked (probe): `lower_empty_eq`, `cC_ret_eq` and `not_ghostCoupling`.
- From reading the definitions, not built in Lean:
  - the claim that the post-world is unconstrained by heap-preserving steps (§2.3; but see
    `wpTS_of_headChain`);
  - the claim that a non-lowered ghost cell could be deleted by any run (§4);
  - the claim that the heap route rejects R1–R3.

  I have not verified any obstruction beyond the probe's.
