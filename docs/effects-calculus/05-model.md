# 05 · The semantic model: one Kripke world

This section defines the model of the effect calculus: the world `W = (ρ, ls, σ)` and its
order, the resources that arise at `W`, the generalised `wp` and its stop condition, protocol
tables and `ewp`, the continuation obligations, the logical relation over `W`, and models and
comodels read semantically. It states the model lemmas with their proof routes, writes out the
first probe of OQ-9 (a 6.64 frame), OQ-44's probe (a 6.65 frame) and OQ-58's probe, and maps every
relation family built beside the kernel onto `W`.

Notation, ids and the open-question register are those of [00-structure.md](00-structure.md).
This section owns D-W, D-ORD, D-ARISE, D-WPG, D-STOP, D-TABLE, D-OPTAB, D-CANCELTAB,
D-TABLEOK, D-EWP, D-EWPP, D-SHARE, D-KAP, D-OWED, D-REL, D-SEM, D-MODEL, D-COMODEL, D-DTOR,
D-BIN, and T-MONO, T-NIL, T-STOP, T-ARISE, T-FRAME, T-SUMOK, T-MODEL, T-COMODEL, T-DEF. It carries
OQ-8, OQ-9, OQ-10, OQ-11, OQ-19, OQ-31, OQ-56 and OQ-61, and raises OQ-44 to OQ-46, OQ-57, OQ-58
and OQ-63 (§13);
every question is boxed in [99](99-open-questions.md).

**How to read this section.** Every definition is written twice where it matters: its form at
`W`, and its instance at `σ = []`, which is the kernel's existing definition by `rfl` where the
definition reads no extension of the world, and only by T-NIL's per-row proof where it does
(OQ-58). Every claim about
code cites `file:line` in this worktree, or `branch:file:line` for the unmerged branches
`gfp`, `gfp-arising` and `borrow-callbacks`. Where OQ-8 (quantifier placement) or OQ-9 (open
frames across a stop) changes a definition, both candidates are written out and the default is
named; at OQ-9 (b) the relation has further candidate clause sets (§7, §8). Nothing here is a
machine-checked obstruction: a missing lemma is "not built".

---

## 0. The kernel model this section extends

The kernel already has a Kripke model with one world component beside the resource. Stated
once, so that every definition below can say exactly what it changes.

- **Resource.** `ρ : WRes`, BoLo's resource algebra (`Paper/S5_Model`). The future-world
  quantifier for `ρ` is `─⋆` and `wpG`'s frame quantifier `∀ ρf`, as in BoLo
  (`Core/EffDefs.lean:28`; reading in `borrow-callbacks:docs/effects-tr/17-borrow-callbacks.md`
  §17.3).
- **Record list.** `ls : List SRec`, records of `[TR]` 6.64 frames tagged with their frame
  lifetime (`SRec := FrameRec × Life`, `Core/FrameRecords.lean:159`). Its order is `Ext`
  (`Core/FrameRecords.lean:172-174`): records relevant to `ρ` are kept, and records strictly
  longer-lived than any borrow cell of `ρ` are unchanged. `Ext.refl`, `Ext.trans`
  (`Core/Wp.lean:142, 138`).
- **Typed world.** `TW W ps rs` (`Core/World.lean:110-167`): the configuration is reached from
  `∅` by the printed proofs' operations; `ps` are the 6.64 frames taken and not ended, `rs`
  their lineages. Its invariant is `TI` (`Core/Invariant.lean:1836`), `TW.inv`
  (`Core/Invariant.lean:2702`).
- **`wpG`** (`Core/EffDefs.lean:27-40`): `[TR]` p. 6's `wp` over tagged typed worlds, ending at
  any term. `ps` is universally quantified inside it (`:28`) and is not a world component. At
  the final term, whatever it is, `ps' ↔ ps ∧ ls' ↔ ls` (`:40`).
- **The relation.** `vCE`, `cC`, `cB` (`Core/Relation.lean:119, 154, 192`). The `Ext` quantifier
  sits at `U` only (`:127-128`); `⊸` (`:156-157`) and `∀` (`:161-162`) quantify over resources
  through `─⋆`; `F` is `wpTS` (`:155`); `F_Σ` is `ewpTS` at `opTable` (`:165-168`).
- **Continuation obligations.** `contShare` (`Core/EffDefs.lean:144-149`), `KapRel`
  (`Core/EffRules.lean:569-578`), `cancelOwed` (`Core/EffDefs.lean:138-140`): each quantifies
  over `ls'` with `Ext ls ls' ρ`.

**What is missing for the full calculus** (audit C1, M4): no world component for a lend open
across a suspension, no monotonicity lemma for the relation, and an arising condition for
stacks that lives as a guard inside relation families built beside the kernel (§9).

---

## 1. The world

### D-W: the world `W = (ρ, ls, σ)`

- **Form.**

  ```
  W  ::= (ρ, ls, σ)
  ρ  : WRes                                   BoLo's resource
  ls : List SRec                              records of open 6.64 frames, tagged (as built)
  σ  : List OEnt                              the open-lend component, innermost first
  OEnt ::= ⟨ℓ, x, T, k, R, α⟩
           ℓ : Loc            the lent place
           x : LifeVar        the variable the lend's binder names (see representation note)
           T : VTy            the payload type
           k ∈ {mut, imm v}   6.65 lend, or 6.64 frame at the value it fixed
           R : Nm → Bool      the lend's row: the names whose stops cross this lend
           α : Life           the lend's lifetime
  ```

  Well-formedness `Wf W`: the lifetimes of `σ` are strictly decreasing inward
  (`List.IsChain (· < ·)`, innermost first, so the innermost is the shortest; `Life = ℕᵒᵈ`);
  the variables of `σ` are distinct; every `imm` entry's frame record, with tag `α`, is a member
  of `ls`. That the `imm` part of `σ` is a selection of `TW`'s own `ps`, not new data, is enforced
  where `ps` is in scope, by D-WPG's premise `∀ e ∈ σ, e.imm → frameOf e ∈ ps`.

  A world-indexed predicate is `P : List SRec → List OEnt → WProp`; the separation connectives
  act on `ρ` with `(ls, σ)` fixed. `P_W` abbreviates `P ls σ ρ` for `W = (ρ, ls, σ)`.

- **Reading.** `σ` is the stack of lends open around the current term whose frames lie outside
  it, between the term and the handler that will receive its stops. It is GhostEnd's lend stack
  (`LStack`, `experiments/GhostEnd/GhostEnd/Stacked.lean:93-107`) with the lifetime vector
  folded into the entries (`αs` is a separate index there, `:110-112`). The same lends, seen
  from the run that suspends, are the frames a stop leaves open and hands to its continuation:
  `ps' ∖ ps` for 6.64 frames under OQ-9 (a). What `σ` must hold to serve both readings, and
  whether it is a selection of `TW`'s `ps`, is OQ-44.

- **Representation note.** Entries carry the binder's variable `x` because a re-lend (OQ-9 (b))
  changes the lifetime the callback's `δ` reads at `x`: GhostEnd extends `δ` by the stack at the
  lifetime vector (`extS`, `Stacked.lean:110-112`). Whether entries carry variables or lifetimes
  only, with `δ` binding the variables, is representation, recorded as open in
  `borrow-callbacks:docs/effects-tr/17-borrow-callbacks.md` §17.7; it is boxed in OQ-8, decided by
  which representation states criterion (iii) at the chosen candidate.
- **Uses.** O-W, O-LIFE, O-ARISE.
- **Today.** `ρ`, `ls` as built. `σ` exists only as a relation parameter in experiments
  (`Stacked.lean:237`, an index in `borrow-callbacks:experiments/GhostEnd/GhostEnd/Extend.lean:62`)
  and implicitly inside `wpG`'s frame quantifier (`Core/EffDefs.lean:28-29`). Status:
  **changed** (`σ` made a component).
- **Slices.** Typing never mentions `σ` (03); the machine never mentions it (04); laws are stated
  at every `W` (06, OQ-11); compatibility lemmas are stated at every `W` (07).
- **Depends on.** Nothing.
- **Open.** OQ-44 (content of `σ`), OQ-9 (what an entry means across a stop), OQ-3 (whether a
  handler site is an entry), OQ-8 (representation of `x`).
- **Obligation.** None by itself. Every lemma that mentions `ls` today must be restated at
  `(ls, σ)` and shown to hold at `σ = []` unchanged (T-NIL). **Mechanical**; the step most likely
  not mechanical is the `Mut`/`Imm` payload restriction (OQ-46).

---

## 2. The order

### D-ORD: `W ⊑ W'`

- **Form.** At a resource `ρ`, `(ls, σ) ⊑_ρ (ls', σ')` iff

  ```
  Ext ls ls' ρ                                            (1) records, as built
  ∧ ∃ τ σ₁. σ' = τ ++ σ₁ ∧ Relend(σ₁, σ)                  (2) fresh entries inside
  ∧ Wf (ρ, ls', σ')                                       (3) nesting order kept
  ∧ ∀ e ∈ τ. ρ ∈ Res_{e.α}                                (4) the new lends are below ρ
  ∧ ∀ e ∈ τ. e.x ∉ vars σ₁                                (5) an extension rebinds nothing
  ```

  where `Relend(σ₁, σ)` holds iff `σ₁` and `σ` agree in every component except the lifetime, and
  `σ₁`'s lifetimes are pointwise `⊑` `σ`'s and in nesting order: GhostEnd's `ReLend`
  (`Stacked.lean:158`). Under OQ-9 (a) `Relend` is equality (`σ₁ = σ`); under OQ-9 (b) it is
  `ReLend`. Condition (4) reads the resource `ρ` at which the order `⊑_ρ` is taken, the resource
  of the world being extended: every new entry's lifetime lies below it. It is 6.64/6.65's `И`:
  the frame's resource lies above the fresh lifetime (the `fresh` premise of `wpG_I_frameX`,
  `Core/EffWp.lean:80-83`, whose proof takes H4 below it). Condition (5) is `Extend.lean:94`'s side
  condition `e'.x ∉ σ.map LEnt.x`, minus its second disjunct, which belongs to the `∀` clause
  (D-REL).

  The order is on `(ls, σ)` at a given `ρ`; this is the definition, and `W ⊑ W'` abbreviates
  `(ls, σ) ⊑_ρ (ls', σ')` at `W = (ρ, ls, σ)`. The resource does not evolve along `⊑`: BoLo's
  resource evolution is `─⋆` composition together with `↭` (`UpdV`) inside `wp`, which every
  clause already contains, and the order never restates it.

- **Facts.** Reflexive (`τ = []`, `Relend` reflexive, `Ext.refl`, `Core/Wp.lean:142`).
  Transitive (`Ext.trans`, `Core/Wp.lean:138`; `++` associative; `ReLend` transitive; (4) at the
  later resource because a later extension's entries are below the earlier ones by (3)). Stable
  under splitting the resource: `Ext.left`, `Ext.right` (`Core/Wp.lean:130, 134`). New records at
  a lifetime `α` with `ρ ∈ Res_α` are an `Ext` step (`ext_add`, `Core/Wp.lean:466`).
- **Uses.** D-W, O-ORD.
- **Today.** `Ext` only (`Core/FrameRecords.lean:172`). The stack order is spread across
  `ReLend` (`Stacked.lean:158`), the extension `τ ++ σ` (`Extend.lean:93-94`) and the per-lemma
  hypotheses `hTL`, `hβ`, `hσx`/`hσT`, `e.x ∉ σ` (audit m5). Status: **changed**.
- **Slices.** Read by D-REL's Kripke clauses, D-SHARE, D-KAP, D-OWED, D-TABLEOK, D-MODEL.
- **Depends on.** D-W.
- **Open.** OQ-8 (which clauses quantify over it), OQ-9 (`Relend` equality or `ReLend`), OQ-44.
- **Obligation.** Reflexivity and transitivity: **mechanical**. The single step most likely not
  mechanical: (4) after a re-lend, since a `ReLend` lowers `σ`'s lifetimes and (4) must still hold
  of entries added before it.

### T-MONO: one monotonicity lemma

- **Form.**

  ```
  ∀ A δ v W W'.  W ⊑ W'  →  𝒱⟦A⟧_W δ v  ⊨  𝒱⟦A⟧_W' δ v
  ∀ Γ δ γ W W'.  W ⊑ W'  →  𝒢⟦Γ⟧_W δ γ  ⊨  𝒢⟦Γ⟧_W' δ γ
  (candidate (b) of OQ-8 only)  ∀ C δ e W W'.  W ⊑ W'  →  𝒞⟦C⟧_W δ e  ⊨  𝒞⟦C⟧_W' δ e
  ```

  one induction on value types, environments `η` required monotone (an admissibility condition
  on candidates, as #245 item 7 asks: "world-indexed, frame-closed, borrow-preserving,
  stratified").
- **Proof route.**
  - `1`, `0`, `int`, `opq`, `unk`: no world.
  - `⊗`, `⊕`, `!`, `[@a]`, `Ref`, `fam`: componentwise.
  - `U C`: the clause is a Kripke universal over `⊑` (both candidates), so monotone by
    transitivity of D-ORD.
  - `Imm a A`, `Mut a A`: the stored predicate is read at `ls₀`, the members of `ls` strictly
    longer-lived than the cell (`ptoMutS`, `ptoImmS`, `Core/Relation.lean:43-54`). The cell is a
    borrow cell of `ρ` at `b`, so `CellIn ρ b` and `Ext`'s second conjunct
    (`Core/FrameRecords.lean:174`) leaves every record strictly longer-lived than `b` unchanged:
    `ls₀` is the same at `ls'`. So these clauses are monotone in `ls` by the definition of
    `Ext`. Their monotonicity in `σ` is OQ-46.
  - `μX. A`: induction inside the least fixed point; the candidate is quantified jointly over the
    mode and the list (`Core/Relation.lean:144-148`), so over `(ls, σ)` here.
  - `tvar`: the environment's candidate, monotone by admissibility.
  - At candidate (a) of OQ-8 the computation relation is not monotone and need not be: a
    computation is consumed at the world it is given, and every value that stores one does so
    under `U`, which is Kripke. At candidate (b) the `⊸` and `∀` clauses are Kripke, and `𝒞` is
    monotone by transitivity (reading of
    `borrow-callbacks:docs/effects-tr/17-borrow-callbacks.md` §17.6).
- **Today.** Not built; Core has `Ext.refl`/`Ext.trans` only. GhostEnd's `Extend.lean` names the
  missing lemma ("Kripke monotonicity of `gRLk`", `Extend.lean:39-41`).
- **Depends on.** D-ORD, D-REL.
- **Open.** OQ-8, OQ-46.
- **Obligation.** **Mechanical** at `Imm`/`Mut` in `ls` (by `Ext`'s definition, above) and at
  every value former. **Unknown** at `σ` inside `Mut`/`Imm` payloads (OQ-46). The single step most
  likely not mechanical otherwise: `μ`, whose candidate must be shown monotone inside the
  fixed point.

---

## 3. Resources that arise

### D-ARISE: arising at `W`, and the table as a `TW` invariant

- **Form.** A configuration arises at `W` when it is a `TW` world: `TW fρ ps (rsOf ls)` and
  `Tagged fρ ps ls` (`Core/World.lean:110, 171`), with the `imm` entries of `σ` among `ps`. The
  table at `W` is GhostEnd's `TabAtS` with the lifetimes taken from the entries:

  ```
  TabAt_W(ρ)  ≜  (σ = e :: _  →  ρ ∈ Res_{↓ e.α})
               ∧ (σ = _ ++ [e']  →  ∀ k ψ. k ∉ places σ → ρ(k) = ψ → ψ ∈ CellRes_{e'.α})
  ```

  every borrow cell is at a lifetime `⊒` the innermost lend, and every one away from the stack's
  places is strictly above the outermost (`TabAtS`, `Stacked.lean:290-292`; `TabAt` at one lend,
  `experiments/GhostEnd/GhostEnd/Table.lean:39-40`). At `σ = []` it holds of every resource
  (`tabAtS_nil`, `gfp-arising:experiments/GhostEnd/GhostEnd/Arising.lean:251`).

  **The intended change, and what it needs.** The intent is that `TabAt_W` is a property every
  arising configuration at `W` has, and every part of it, not a premise the relation's clauses
  assume. That needs a lemma that derives it from `TW`, T-ARISE.0 below. Preservation of `TabAt`
  by a run (T-ARISE's first line, the shape of `wpG_tabAt`, `Table.lean:87`) does not do it: it
  carries a precondition through a run. Until T-ARISE.0 is proved, D-SEM keeps `TabAt_W(ρ)` as a
  premise and both clause sets keep `guard_W`, so in substance the guard is a guard, as today.
  Whether T-ARISE.0 is achievable, and then whether the clauses still carry the guard
  (`guardS`, `Arising.lean:169`) or lose it, is OQ-45.
- **Uses.** D-W, O-ARISE.
- **Today.** `TW` as built. `TabAtS` as a guard at `U`, `⊸`, `∀` in `vRLa`/`cRLa`
  (`Arising.lean:173-203`), and as a hypothesis of `GFPAt` (`Stacked.lean:305-310`). Status:
  **intended change** from a guard to an invariant, in force only once T-ARISE.0 is proved.
- **Slices.** 07: once T-ARISE.0 holds, every compatibility lemma receives `TabAt_W` from it, not
  from its hypotheses; until then from D-SEM's premise.
- **Depends on.** D-W.
- **Open.** OQ-45, OQ-44.
- **Obligation.** See T-ARISE.

### T-ARISE: the table is preserved by every run, at returns and at stops

- **Form.**

  ```
  T-ARISE.0 (theorem tabAt_of_TW):
    ∀ fρ ps ls σ ρ.  TW fρ ps (rsOf ls) → Tagged fρ ps ls → (∀ e ∈ σ, e.imm → frameOf e ∈ ps) →
      PartOf ρ fρ → HeldUnderTW ρ ps σ → TabAt_{(ρ,ls,σ)}(ρ)
  ```

  every part `ρ` of an arising frame that a term holds under the stack `σ` (`HeldUnder`: its
  borrow cells are views the stack's lends handed it, or lie away from the stack's places) has the
  table. Route: induction on `TW`'s constructors, `[TR]` 6.50 (`tabAt_updV`, `Table.lean:80`) at
  each world operation. `PartOf` and `HeldUnderTW` are the statement's names. `HeldUnderTW ρ ps σ`
  is defined from `ps` and `σ` alone, as a constraint on which frame records the part holds:
  every borrow cell of `ρ` is inside a frame record of `ps` whose lend is an entry of `σ` (a view
  the stack handed it) or at a location no entry of `σ` lends. Stated with a premise that `TW` does
  not carry (a free-standing `HeldUnder ρ σ`), the lemma would relocate the guard into a premise
  rather than derive it; OQ-45 records this. **Unknown** (OQ-45).

  ```
  ∀ W e Q ρ.  TabAt_W(ρ)  →  wpG_W e Q ρ  →  wpG_W e (λ W' t ρ'. TabAt_W'(ρ') ∧ Q W' t ρ') ρ
  ∀ ρ₁ ρ₂ ρ.  ρ₁ ● ρ₂ = ρ  →  (TabAt_W(ρ) ↔ TabAt_W(ρ₁) ∧ TabAt_W(ρ₂))
  start:  a lend opened at a fresh α below ρ, with its view composed in, satisfies TabAt at e :: σ
  ```

  `W'` at a value is `W`; at a stop it is the world D-STOP hands the table.
- **Proof route.** At one entry this is built: `wpG_tabAt` (`Table.lean:87`) from `tabAt_updV`
  (`Table.lean:80`, `[TR]` 6.50 at `↓α` and at each location away from `ℓ`) and `tabAt_comp`
  (`Table.lean:67`); `wpG_tabAtS_one` (`Arising.lean:112`); the start: `tabAt_start`
  (`experiments/GhostEnd/GhostEnd/StackStep.lean:360`), `tabAtS_start_one` (`Arising.lean:120`).
  At a stack: parts and whole is `tabAtS_comp` (`Arising.lean:83`); preservation needs
  `tabAt_updV` at the innermost entry's `↓α` and at the outermost entry's `α`, which is 6.50
  (`updV_outlives`, `updV_outlives_at`, used at `Table.lean:82-83`) applied twice. At a stop under
  OQ-9 (a), the world grows by `τ`, and `TabAt` at `τ ++ σ` follows from the start lemma at each
  entry of `τ`.
- **Today.** One entry only (`wpG_tabAt`, `wpG_tabAtS_one`). The audit's M5: coverage at one
  entry, placement as a guard. T-ARISE.0: not built at any depth.
- **Depends on.** D-ARISE, D-WPG, D-STOP.
- **Open.** OQ-45, OQ-9.
- **Obligation.** **Mechanical** at a stack at returns (6.50 twice, no new mathematics). The step
  most likely not mechanical: the stop under OQ-9 (b), where a re-lend lowers `σ`'s lifetimes and
  `TabAt` at the lowered vector must follow from `TabAt` at the old one; `tabAt_mono`
  (`Table.lean:56`) is that fact at one entry.

---

## 4. The generalised `wp` and the stop condition

### D-WPG: `wpG_W`

- **Form.** `wpG_W(τ) e Q ρ`, where `W = (ρ, ls, σ)`, `τ : List OEnt` is the list of open 6.64
  frames this run holds the closing obligation for (empty except for a resumed continuation or a
  cancel run under OQ-9 (a)), and
  `Q : List SRec → List OEnt → List OEnt → Expr → WProp` receives the post-run record list, the
  outer stack, the frames the stop added, and the final term (the remainder of the verbatim
  conjuncts follows `wpG`'s):

  ```
  wpG_W(τ) e Q ρ  ≜
    ∀ ρf fρ ps. ρf # ρ → ρf ● ρ = fρ → TW fρ (frames τ ++ ps) (rsOf ls) → Tagged fρ (frames τ ++ ps) ls →
    (∀ e ∈ σ, e.imm → frameOf e ∈ ps) →
    ∀ A k. ∃ ρ' ρp fρ' fρ'p π t μ μ' ps' ls' τ'.
      ρ' # ρf ∧ ρf ● ρ' = fρ' ∧ ρp # fρ' ∧ ⌊fρ⌋ = μ ∧ fρ' ● ρp = fρ'p ∧ ⌊fρ'p⌋ = μ' ∧
      (∃ k'. ARun A k μ e k' μ' t) ∧ ρ' ● ρp = π ∧ ρ ↭ π ∧ NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      Stop(τ, ps, ps', ls, ls', t, τ') ∧ Q ls' σ τ' t ρ'
  ```

  Every conjunct except `Stop`, the arguments `Q` receives, and the premise
  `∀ e ∈ σ, e.imm → frameOf e ∈ ps` is `wpG`'s verbatim (`Core/EffDefs.lean:27-40`). That premise
  is what makes `σ`'s `imm` entries a selection of `TW`'s own `ps` (O-W): the run is quantified only
  over frame lists that hold the stack's open 6.64 frames. At `σ = []` it is vacuous, so
  `wpG_W([])` at `σ = []` is still `wpG`. which is `[TR]` p. 6's `wp` (row 5.33, repaired in
  `Core/World.lean:186-199`). `frames τ` is the 6.64 frame records of `τ`'s `imm` entries.
  `Stop` is D-STOP.

  **Two stacks.** `σ` is the stack of lends opened outside this run and still open around it;
  `τ` is the stack of frames this run must close. The term sits under `τ ++ σ`, and D-ARISE's
  `TabAt` and D-REL's clauses read that stack. `σ` never contains `τ`'s entries, so at a value,
  where `Stop` forces `τ' = []` and closes `τ`, `Q` receives `(ls', σ)` with `τ`'s entries popped
  from the stack and their lineages `lin(τ)` removed from `ls'` (D-STOP's value clause). At a stop,
  the continuation's stack is `τ' ++ σ`, `τ'` being its closing obligation. `τ` is an index
  beside `W`; that is a defect against 00 §0.2 item 1 and is boxed as OQ-57.

  `valPost Q ls' σ τ' t ≜ ∃ v. ⌜t = v ∧ τ' = []⌝ ⋆ Q ls' σ v`.
- **`σ = []`, `τ = []` instance.** With D-STOP's default (unchanged) `Stop`, `τ' = []` at every final
  term, and `wpG_W([])` at `σ = []` is `wpG` by definition. `wpTS = wpG ∘ valPost`
  (`wpTS_iff_wpG`, `Core/EffWp.lean:43`).
- **Uses.** D-W, D-ARISE, D-STOP.
- **Today.** `wpG` (`Core/EffDefs.lean:27`). Status: **changed at `Stop`**, at the arguments `Q`
  receives, and by the index `τ`.
- **Slices.** 04 supplies `ARun` and the head steps; nothing else of the machine is read.
- **Depends on.** D-W, D-STOP.
- **Open.** OQ-9, OQ-10, OQ-57.
- **Obligation.** Every lemma about `wpG` in `Core/EffWp.lean` restated at `wpG_W(τ)`: `wpG_mono`
  (`:58`), `wpG_step` (`:868`), `wpG_bind` (`:878`), `wpG_here` (`:962`), `wpG_head` (`:973`),
  `wpG_ramify` (`:978`), `wpG_frame` (`:1005`), `wpG_garbage` (`:730`), and the three frames
  `wpG_I_frameX` (`:75`), `wpG_M_frameX` (`:363`), `wpG_M_antiFrameX` (`:567`). **Mechanical** at
  `τ = []` (the proofs never inspect the final term, `Core/EffWp.lean:12-15`). The step most likely
  not mechanical: `wpG_bind` at `τ ≠ []`, where the inner run's stop hands frames to the outer
  context's continuation.

### D-STOP: the stop condition relativised to the table

This is a **kernel definition change**. Its text is written as the SPEC entry it requires; no
kernel work starts before that entry is accepted. It is the candidate of OQ-10 (a), conditional
on OQ-9 (a). The default, if OQ-9 and OQ-10 are unresolved, is the stop condition unchanged and
R-T1.

> **SPEC entry (draft): the stop condition of `wpG`.**
>
> *Current.* At every final term `t`, `ps' ↔ ps ∧ ls' ↔ ls` (`Core/EffDefs.lean:40`).
>
> *Proposed.* With `τ` the frames the run holds the closing obligation for:
>
> ```
> Stop(τ, ps, ps', ls, ls', t, τ')  ≜
>   t is a value:      τ' = [] ∧ ps' ↔ ps ∧ ls' ↔ ls ∖ lin(τ)
>   t is not a value:  ps' ↔ frames τ' ++ ps ∧ frames τ' ∩ ps = ∅ ∧ ls' ⊇ ls ∖ lin(τ) ∧
>                      every record of ls' not in ls ∖ lin(τ) descends from a frame of τ'
> ```
>
> where `lin(τ)` is the records of `τ`'s lineages and `ps` excludes `frames τ` (the run starts at
> `frames τ ++ ps`, D-WPG). At a value the run has closed every frame it held and opened, exactly
> as `[TR]`'s `wp` does: `τ`'s frames leave `ps`, their lineages leave `ls`, and the post receives
> the outer stack `σ`, which never held `τ`'s entries (D-WPG, *Two stacks*), so the stack and `ls`
> stay consistent with D-W's `Wf`. At `τ = []` this is the current clause, so `wpTS` is unchanged. At a stop the frames still open, `τ'`, are handed to the table, which states
> what the continuation owes them (D-SHARE, D-OWED, D-OPTAB); the table receives `τ'` as an
> explicit argument (D-TABLE). An abortive entry of a table and `cancelTab` admit only `τ' = []`
> (D-OPTAB, D-CANCELTAB), so at an abortive table the stop condition is the current one.
>
> *Why.* The current clause is `[TR]`'s value-time condition kept at stops. It forbids a stop to
> leave a 6.64 frame open (`ps' ↔ ps`), and it forbids a resumed run to close a frame opened before
> the stop, since that frame is then in the pre-configuration's `ps` and must still be there at the
> value. Both halves are T1 for 6.64 frames.
>
> *What it does not reach.* 6.65 and 6.66 leave `ps` unchanged (`TW.mutFold`, `TW.mutUnfold`,
> `Core/World.lean:135-144`). For a 6.65 lend, closure at a stop comes from applying
> `wpG_M_frameX` (`Core/EffWp.lean:363-371`), whose conclusion ends `α` at whatever final term
> the run reaches; GhostEnd keeps 6.65 lends open across stops over the current `wpG`, as
> resources owed through `RelendableN` (`Stacked.lean:170-174, 200-206`). So the proposed clause
> concerns 6.64 frames; how a 6.65 lend open across a stop is recorded is OQ-44.
>
> *Conservativity.* T-STOP.

- **Uses.** D-WPG, O-TAB.
- **Today.** `Core/EffDefs.lean:40`. Status: **changed; SPEC entry required**.
- **Slices.** 04 is unaffected (no step changes). 07: every compatibility lemma at a row.
- **Depends on.** OQ-9's probe (§12.1).
- **Open.** OQ-9, OQ-10, OQ-44, OQ-57; R-T1 by default.
- **Obligation.** **Unknown.** The first probe is §12.1.

**`τ` as an index beside `W`.** D-STOP needs the closing obligation `τ`, which D-WPG, D-EWP and
D-TABLE carry as an explicit index. 00 §0.2 item 1 makes that a defect to report; it is OQ-57,
whose settling statement is:

```lean
/-- OQ-57: the closing obligation can be carried by the world's entries. -/
def ClosingInW : Prop :=
  ∀ (τ σ : List OEnt) (ls : List SRec) (e : Expr) (Tb : TableW) (Q : PostW) (ρ : WRes),
    Disjoint τ σ →
    (ewpW τ ls σ e Tb Q ρ ↔
       ewpC ls (τ.map (·.withCloser .thisRun) ++ σ.map (·.withCloser .outer)) e Tb Q ρ)
```

`ewpC` is D-EWP with no `τ` index, reading the obligation off the entries' `closer` field (OQ-57
(b)); `withCloser`, `TableW`, `PostW` are names the settling experiment defines.

**The alternative that keeps the stop.** OQ-9 (b), capture rebasing, needs no change to
`wpG`. Its single-lend instances are built over the current `wpG` at every monotone table: 6.65
(`ewpTS_M_frameR`, `experiments/GhostEnd/GhostEnd/Relend.lean:117`), 6.64 (`ewpTS_I_frameR`,
`experiments/GhostEnd/GhostEnd/ImmLend.lean:175`), 6.66 (`ewpTS_M_antiFrameR`,
`experiments/GhostEnd/GhostEnd/Frames.lean:89`). At a stop the lend ends as at a return, the
continuation is owed the owner and a callback lent again at a lifetime fresh at resumption
(`Relend.lean:20-34`). The cost moves into the relation: the callback must be re-lendable, which is
the `U` clause `RelendableS` (`Stacked.lean:163-167`) and the order's `ReLend`. Under (b), `σ` is
the stack of lends to re-lend, not open frames in `ps`, and D-STOP is not adopted.

### T-STOP: conservativity of D-STOP

- **Form.**

  ```
  (1) ∀ W e Q.  wpG_W([]) e (valPost Q)  =  wpTS ls e Q                  at σ = []
  (2) ∀ W e Q.  ewp_W e Table.bot Q  ↔  wpTS ls e Q
  (3) ∀ Tb.  Tb.Abortive  →  ewp_W e Tb Q  ↔  wpG_W([]) e (ewpPost Tb Q)   with τ' = [] at every stop
  ```

- **Proof route.** (1) by definition: at a value D-STOP is the current clause at `τ = []`, and
  `wpTS_iff_wpG` (`Core/EffWp.lean:43`). (2) is `ewp_bot` (`Core/EffWp.lean:772`), whose proof
  never reads the stop clause. (3) is `ewp_abortive` (`Core/EffWp.lean:811`) once every abortive
  table forces `τ' = []` (D-OPTAB's abortive half, D-CANCELTAB). With (3), the abortive frame
  lemmas `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU` (`Core/EffWp.lean:828, 842,
  854`) carry over unchanged.
- **Today.** `ewp_bot`, `ewp_abortive` for the current stop.
- **Depends on.** D-STOP, D-EWP, D-OPTAB, D-CANCELTAB.
- **Open.** OQ-10.
- **Obligation.** **Mechanical.** The step most likely not mechanical: (3)'s use inside
  `ewp_unwind` (`Core/EffBorrow.lean:58`), which reads the stop's resource through `Table.withFr`.

---

## 5. Tables and `ewp`

### D-TABLE: protocol tables

- **Form.** A table receives the pre-stop world and the frames the stop added, explicitly:

  ```
  Table_W  :=  List SRec → List OEnt → List OEnt → Expr → Cont → WProp
  Cont     :=  List OEnt → List SRec → List OEnt → Expr → WProp
  ```

  `Tb (ls', σ) τ' t Φ` reads: the configuration stopped at `t`, with record list `ls'`, outer stack
  `σ`, and the 6.64 frames `τ'` the stop left open, is allowed, with every continuation it owes in
  `Φ`. A continuation `K[w]` owed is read as `Φ τ' (ls'', σ'') K[w]`: at a later world, holding the
  closing obligation for `τ'`. `Mono`, `Abortive`, `bot` as built, with the arguments added:
  `Tb.Mono ≜ (Φ ⊆ Φ') → Tb W τ' t Φ ⊨ Tb W τ' t Φ'`; `Tb.Abortive ≜ Tb W τ' t Φ ⊨ Tb W τ' t Φ'`;
  `Table.bot ≜ ⊥`.
- **`σ = []`, `τ' = []` instance.** `Table` (`Core/EffDefs.lean:50`), `Table.Mono` (`:53`),
  `Table.Abortive` (`:58`), `Table.bot` (`:65`), with the two extra arguments at `[]`.
- **Uses.** D-W. **Today.** As built at `[]`. Status: **changed** (signature).
- **Depends on.** D-W. **Open.** OQ-57.
- **Obligation.** None.

### D-OPTAB: the protocol table of a row

- **Form.** For `T = ⟦Σ⟧δ : OpTab` with entries `en = ⟨q, abort, P_A, P_B⟩`, `P_A, P_B :
  List SRec → List OEnt → Val → WProp`:

  ```
  opTable T (ls, σ) τ' t Φ  ≜
      ∃ K n i v en. ⌜t = K[perform (n,(i,v))] ∧ ¬HasHnd n K ∧ T n i = en ∧ ¬en.abort⌝
                    ⋆ en.P_A(ls, τ' ++ σ) v ⋆ share T en n (ls, σ) τ' K Φ
    ∨ ∃ K n i v en. ⌜t = K[raise (n,(i,v))] ∧ ¬Catches n K ∧ T n i = en ∧ en.abort ∧ τ' = []⌝
                    ⋆ (en.P_A(ls, σ) v ∧ NoOwn) ⋆ NoOwn
  ```

  `τ'` is an argument: the frames the stop added (D-STOP), passed by D-WPG. The argument is read
  under the stack it was performed under, `τ' ++ σ`. The abortive half admits no open frame: the
  raise has already passed every finaliser frame of the region, since `Catches` holds at every
  `ubind` and `cfin` frame (`Paper/S3_Dynamics/Definitions.lean:397-407`), and an abandoned
  continuation holds nothing owned. The non-abortive half hands `τ'` to `share`.
- **`σ = []`, `τ' = []` instance.** `opTable` (`Core/EffDefs.lean:157-167`): by definition up to
  `share`, whose own `σ = []` instance is proved per row (`share_nil`, OQ-58).
- **Uses.** O-INT, K-OP, K-RAISE, D-SHARE.
- **Today.** As built; reads `W`. Monotone at every `T` (`opTable_mono`, `Core/EffWp.lean:951`).
- **Slices.** 02 supplies `⟦Σ⟧δ` (`effTab_effOf`, `Core/EffRules.lean:49`).
- **Depends on.** D-TABLE, D-SHARE, D-STOP.
- **Open.** OQ-24 (`NoOwn` payload; R-NOOWNERR), OQ-57.
- **Obligation.** `opTable_mono` at `W`: **mechanical** (the proof is the monotonicity of `share`
  in `Φ`).

### D-CANCELTAB: the table of a cancel run

- **Form.**

  ```
  cancelTab T N (ls, σ) τ' t _  ≜  ∃ K err. ⌜t = K[raise (0,(0,(N, err)))] ∧ ¬Catches 0 K ∧ τ' = []⌝
                                    ⋆ (errOk T N (ls, σ) err ⋆ NoOwn)
  ```

  with `errOk` (`Core/EffDefs.lean:122-127`) re-indexed. A cancel run stops only at the cancel
  itself, having unwound every frame that catches it, and leaves no frame open: with `τ' = []`,
  D-STOP's stop clause gives `ps' ↔ ps`, so the frames `τ` the cancel run was handed (D-OWED) are
  closed.
- **`σ = []` instance.** `cancelTab` (`Core/EffDefs.lean:131-134`); abortive
  (`cancelTab_abortive`, `Core/EffWp.lean:1013`).
- **Uses.** K-CANCEL. **Today.** As built. **Depends on.** D-TABLE. **Open.** OQ-21 (the error
  policy), OQ-9 (that a cancel run closes the frames it was handed).
- **Obligation.** None at the definition. Its use is §12's probe.

### D-TABLEOK: the tables a borrow may lend across

- **Form (candidate).** For a lend of variable `x`,

  ```
  TableOK_x(Tb)  ≜  Tb.Mono                                                   (1)
                  ∧ ∀ W W' τ' t Φ. W ⊑ W' → Tb W τ' t Φ ⊨ Tb W' τ' t Φ        (2)  hTL
  and for Tb = opTable T:
                  ∀ n i en. T n i = en → en.q ≠ lin →
                    ∀ W τ' K Φ.  share T en n W τ' K Φ  ⊨
                      ∀ N. n ∈ N → hndNames K ⊆ N →
                        ewp_W(τ') (K[raise (0,(0,(N, none)))]) (cancelTab T N) ⊥   (5)
  and for every Tb:  Tb.Irred                                                  (6)
  under R-CLOSEDOP (OQ-56), for Tb = opTable T, in addition:
                  ∀ n i en. T n i = en →
                      P_A, P_B do not read x                                   (3)
                    ∧ P_A outlives every lifetime                              (4)

  TableOK(Tb)  ≜  ∀ x. TableOK_x(Tb)
  ```

  (1) holds of every `opTable T` (`opTable_mono`, `Core/EffWp.lean:951`). (2) is the hypothesis
  `hTL` of `ewpTS_I_frameR` (`ImmLend.lean:176`), which the audit (m5) reads as a slice of the
  world order. (3) and (4) are `Row.Unwind`'s conditions without its abortive-only conjunct
  (`Core/EffBorrow.lean:133-135`; their uses `Row.Unwind.tab_extend` `:145`, `Row.Unwind.out`
  `:160`), extended to `P_B` because a resumed continuation receives the answer after the lend has
  been handed on or re-lent. They are R-CLOSEDOP, a named restriction, and are not part of the
  full class; without them an entry may be lifetime-polymorphic (03 K-BOR, *The full class*), and
  what replaces (3)-(4) is `LifetimePolyOpTableOK`'s conclusion (OQ-56). (5) says that the share a
  non-linear entry demands of a stopped context, holding the open frames `τ'`, gives the cancel run
  of that context at `ewp(τ')` against `cancelTab`, which admits only a stop with `τ' = []`, so the
  frames are closed (D-OWED, D-CANCELTAB); it is `owed` read off `share`. Whether it holds is OQ-9,
  and the formula is fixed only up to OQ-9's choice (under OQ-9 (b) `τ' = []` always and (5) is
  `owed` at `[]`). (6) is
  `Irred` (06 §1.4: every term a stop of `Tb` allows is irreducible), which the backward half of
  a law's unary interchange needs; `opTable T` and `cancelTab T N` have it, since neither stops at
  a redex (`Core/EffDefs.lean:131-167`).
- **Instances.** `Table.Abortive` tables satisfy (1)-(5) with (5) vacuous: today's `*U` rows
  (`Row.Unwind`). The empty row: today's pure constants. A row whose every entry is linear and
  resuming (`LinResume`, `experiments/GhostEnd/GhostEnd/Body.lean:141`) satisfies (5) vacuously:
  GhostEnd's stack steps (`stack_step_other` `StackStep.lean:392`, `stack_step_imm` `:1003`). An
  affine row needs (5) (`ResumeAff`, `opTableO`, `experiments/GhostEnd/GhostEnd/Drop.lean:44, 49`).
- **Uses.** D-OPTAB, D-ORD. **Today.** Not built. Status: **new**.
- **Slices.** 03: K-BOR's side condition `BorOK_x Σ`, whose interpretation this is.
- **Depends on.** D-ORD, D-OPTAB, D-OWED.
- **Open.** OQ-9 (conjunct (5)), OQ-56 (conjuncts (3)-(4)), OQ-7, OQ-2.
- **Obligation.** (1), (3), (4), (6) **mechanical**; (2) **mechanical** once `share` is monotone
  along `⊑`; (5) **unknown** (OQ-9).

### D-EWP: `ewp_W(τ)`

- **Form.** One least fixed point indexed by the closing obligation, written in `Prop` as today:

  ```
  ewpStep Tb Q P τ (ls, σ) e  ≜
      wpG_{(ρ,ls,σ)}(τ) e (λ ls' σ τ' t. valPost Q ls' σ τ' t ∨ Tb (ls', σ) τ' t P)
  ewp_W(τ) e Tb Q ρ  ≜
      ∀ P : Cont. (∀ τ₀ W₀ e₀ ρ₀. ewpStep Tb Q P τ₀ W₀ e₀ ρ₀ → P τ₀ W₀ e₀ ρ₀) → P τ (ls, σ) e ρ
  ewp_W  ≜  ewp_W([])
  ```

  The fixed-point variable `P` carries `τ`, and a table hands `P` its own `τ'`, so a continuation
  resumed with frames `τ'` is read through `ewp(τ')` at every unfolding, and frames still open at a
  second stop of the resumed run are handed on again by that stop's `τ'`.
- **`σ = []`, `τ = []` instance.** `ewpStep`, `ewpTS` (`Core/EffDefs.lean:68-75`): under D-STOP's
  default every stop has `τ' = []`, so `P` is only ever applied at `[]`, and `ewp_W([])` at `σ = []`
  is `ewpTS` by definition.
- **Facts carried.** `ewp_ind`, `ewp_fold`, `ewp_unfold` (`Core/EffWp.lean:754, 759, 765`),
  `ewp_bot` (`:772`), `ewp_of_wp` (`:785`), `ewp_mono` (`:795`), `ewp_abortive` (`:811`), each by
  its existing proof, generalised over `τ`.
- **Uses.** D-WPG, D-TABLE. **Today.** As built over `wpG` at `τ = []`.
- **Depends on.** D-WPG. **Open.** OQ-10, OQ-57.
- **Obligation.** **Mechanical**: none of the cited proofs reads `ls` or the final term's frames.

### D-EWPP: the partial-correctness relation at a `div` row (only under OQ-15 (b))

- **Form.** A run segment with no termination demand, and its greatest fixed point over stops:

  ```
  wpGP_W(τ) e Q ρ  ≜
    ∀ ρf fρ ps. ρf # ρ → ρf ● ρ = fρ → TW fρ (frames τ ++ ps) (rsOf ls) → Tagged fρ (frames τ ++ ps) ls →
    (∀ e ∈ σ, e.imm → frameOf e ∈ ps) → ∀ A k μ. ⌊fρ⌋ = μ →
      (∀ k' μ₁ e₁. ARun A k μ e k' μ₁ e₁ → Final e₁ ∨ ∃ k'' μ₂ e₂. AStep1 A k' μ₁ e₁ k'' μ₂ e₂)   (safe)
    ∧ (∀ k' μ' t. ARun A k μ e k' μ' t → Final t →
         ∃ ρ' ρp fρ' fρ'p π ps' ls' τ'.  [wpG_W's conjuncts at (μ', t)] ∧ Stop(τ, ps, ps', ls, ls', t, τ')
                                          ∧ Q ls' σ τ' t ρ')                                            (post)

  ewpP_W(τ) e Tb Q ρ  ≜  ∃ P : Cont. (∀ τ₀ W₀ e₀ ρ₀. P τ₀ W₀ e₀ ρ₀ → ewpStepP Tb Q P τ₀ W₀ e₀ ρ₀) ∧ P τ (ls, σ) e ρ
  ewpStepP Tb Q P τ (ls, σ) e  ≜  wpGP_{(ρ,ls,σ)}(τ) e (λ ls' σ τ' t. valPost Q ls' σ τ' t ∨ Tb (ls', σ) τ' t P)
  ```

  `wpGP_W` takes `wpTSD`'s every-run quantifier (`Core/Demonic.lean:223`: every run from every
  configuration `wpTS` quantifies over) and replaces its conclusion, "every run continues to a
  value", by safety at every reachable configuration and the post at every final one: partial
  correctness. `Final t` is a value or a stop (04 §5.1); `AStep1` is the allocator step
  (`Core/Demonic.lean:117`). `ewpP_W` is the greatest fixed point of the same step functional
  shape as D-EWP, because a partial-correctness run may resume a continuation infinitely often. A
  `div` entry in a row adds no table entry: `Div = {}` (03 §9.2).
- **Relation to `ewp_W`.** At every row, `ewp_W(τ) e Tb Q ⊨ ewpP_W(τ) e Tb Q` (total implies
  partial: a run that terminates is safe, and by determinism, `AStep1.deterministic`,
  `Core/Demonic.lean:117`, the final configuration `wpG` exhibits is the one every run reaches); the
  converse fails at a diverging `e`. D-REL reads `𝒞⟦F_Σ R⟧_W` by `ewpP_W` when `div ∈ Σ`, by `ewp_W`
  otherwise.
- **A second family.** `ewpP_W` beside `ewp_W` is a second wp family, which 00 §0.2 item 1 makes a
  defect: it is recorded in OQ-63, whose option (b) makes the two one definition with a mode and
  whose settling statement is:

  ```lean
  /-- OQ-63 (b): every fact of D-EWP and every frame of T-FRAME holds at both modes by one proof. -/
  def EwpModeUniform : Prop :=
    ∀ (m : Mode), FactsCarried (ewpMode m) ∧ FramesLifted (ewpMode m)
  ```

  (`Mode`, `ewpMode`, `FactsCarried`, `FramesLifted` are names the settling experiment defines:
  `ewpMode .total = ewp_W`, `ewpMode .partial = ewpP_W`.)
- **Uses.** D-WPG, D-STOP, D-TABLE. **Today.** Not built; `wpTSD` (`Core/Demonic.lean:223`) is a
  total-correctness every-run form. Status: **new**, only under OQ-15 (b).
- **Depends on.** D-WPG. **Open.** OQ-15, OQ-63.
- **Obligation.** T-FRAME and T-STOP at `ewpP_W`, and `handle_compatC` at it (K-HDIV under (b)):
  **unknown**. The step most likely not mechanical: the coinduction at a stop whose continuation
  is resumed under a lend opened before the stop.

### T-FRAME: `[TR]` 6.64, 6.65, 6.66 and 6.150 lifted once

- **Form.** At every `TableOK_x` table `Tb`, every `τ` and every depth of `σ`, the four printed
  frames hold over `ewp_W(τ)` with their printed premises and boxed postconditions verbatim. Each
  printed `wp(e){·}` is read as `ewp_{W'}(τ)(e){Tb}{·}`; `P̂` is a predicate on values (at a typed
  instance, `𝒱⟦T⟧_W δ`):

  ```
  6.64  (Paper/S6_3_FrameAndAntiFrame/Lemmas.lean:67, wp_I_frame :81)
    ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Imm α P̂ ─⋆ ewp_{W·e_α}(τ)(e){Tb}{[α](ℓ ↦ v ─⋆ P̂(v) ─⋆ Q̂)})
      ⊨ ewp_W(τ)(e){Tb}{Q̂}

  6.65  (:242, wp_M_frame :256)
    P̂ ⊨ [β]P̂   →
    ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ ─⋆ ewp_{W·e_α}(τ)(e){Tb}{[α] ∀v′. ℓ ↦ v′ ─⋆ P̂(v′) ─⋆ Q̂})
      ⊨ ewp_W(τ)(e){Tb}{Q̂}

  6.66  (:455, wp_M_antiFrame :469)
    ℓ ↦ Mut α P̂ ⋆ (∀v. ℓ ↦ v ─⋆ P̂(v) ─⋆ ewp_W(τ)(e){Tb}{∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ ─⋆ Q̂)})
      ⊨ ewp_W(τ)(e){Tb}{Q̂}

  6.150 (Paper/S6_7_WeakestPreconditionRules/Lemmas.lean:1157, wp_reborrow)
    RebEscrow P̂   →
    ℓ ↦ Imm α (Иβ. ↺_β P̂) ⋆ (Иβ. ∀v. P̂(v) ─⋆ ewp_W(τ)(e){Tb}{[β]Q̂})
      ⊨ ewp_W(τ)(e){Tb}{Q̂}
  ```

  `W·e_α` is `W` with the new lend `e` (place `ℓ`, lifetime `α`) as its innermost entry. Under
  OQ-9 (a) a stop inside the body hands `e` to `Tb` in its `τ'` (for 6.64; for 6.65, OQ-44); under
  OQ-9 (b) the stop ends the lend and the continuation is owed a re-lend at a lifetime fresh at
  resumption. This is the piece `bodyS`/`OpenS` of `Stacked.lean:209-226` at `e :: σ`.

  **Hypotheses the lift must spend.**
  - 6.65's premise `P̂ ⊨ [β]P̂`, taken at every value and every world (as `wpTS_M_frameX` takes it at
    every record list, `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean:248-250`).
  - 6.150's `RebEscrow P̂` (`[restricted]`, `docs/adjudications.md` §12.61) and its `И` freshness
    of `β`.
  - The `И` freshness of `α` at 6.64 and 6.65, which D-ORD's condition (4) states as a slice of
    the order.
  - **Added hypothesis** (not printed): `Q̂` stable along `⊑`, the `W`-form of
    `wpTS_I_frameX`'s `hQ` along `Ext` (`Core/EffWp.lean:77`), needed because the postcondition is
    read at the world a stop extends. It is not a printed hypothesis; it is T-MONO's at the
    postcondition, and its scope is the postconditions D-REL produces.
  - `TableOK_x Tb`, conjuncts (1), (2), (5) and (6) at a resuming table; (3)-(4) under R-CLOSEDOP.
- **Proof route.** By induction on the least fixed point (`ewp_ind`), applying the printed frame
  at `wpG` at each unfolding (`wpG_I_frameX`, `wpG_M_frameX`, `wpG_M_antiFrameX`,
  `Core/EffWp.lean:75, 363, 567`; `wpTS_reborrow` for 6.150), which never inspect the final term.
  This is the technique of `ewpTS_M_frameR` (`Relend.lean:117-133`): induction on `Relend` with
  `wpG_M_frameX` at each unfolding, "so each resumption re-applies 6.65 as printed"
  (`Relend.lean:24-26`). Depth: one induction on `|σ|`, the step `σ → e :: σ` being GhostEnd's
  commutation lemmas (`stack_step_other`, `stack_step_reborrow`, `stack_step_imm`,
  `StackStep.lean:392, 563, 1003`), with the split `σ = σ_in ++ σ_out` at a handler (audit M8). No
  per-depth instance. Each borrow row consumes the halves its printed proof names: 6.172 (withbor1)
  6.64; 6.173 (withbor2) 6.65; 6.174 (withbor3) 6.66, then 6.60, then 6.65
  (`Paper/S6_8_FundamentalProperty/Lemmas.lean:1462-1466`); 6.175 (withload) 6.150.
- **Today.** Abortive half in Core (`Core/EffWp.lean:828-854`); resuming halves at one lend in
  GhostEnd (above); the stack step at linear-resume tables; 6.150 not lifted (audit m6).
- **Depends on.** D-EWP, D-TABLEOK, D-ORD; OQ-9 decides the form of the body's world.
- **Open.** OQ-9, OQ-3 (handler between lenders; R-MID by default), OQ-7, OQ-44, OQ-57.
- **Obligation.** **Unknown** for 6.150 (untranscribed at a resuming table) and for affine
  tables. **Mechanical** for 6.64-6.66 at linear-resume tables at depth 1 (built). The step most
  likely not mechanical at depth: the split at a handler between lenders, which `AllCross`
  (`StackStep.lean:182`, discharged only by constant `true`) currently excludes.

### T-SUMOK: `TableOK` is closed under row sum

- **Form.** `TableOK_x(opTable T) → TableOK_x(opTable T') → (T, T' disjoint) →
  TableOK_x(opTable (T ⊕ T'))`, where `⊕` is iterated `OpTab.ext` (`Core/EffDefs.lean:117-118`).
- **Proof route.** (1) holds of every `opTable` (`Core/EffWp.lean:951`). (3)-(5) are conditions on
  each entry, so they hold of the sum because every entry of `T ⊕ T'` is an entry of `T` or of
  `T'`. (2) follows from `share`'s monotonicity along `⊑`, which does not depend on the row.
- **Today.** Not built.
- **Depends on.** D-TABLEOK.
- **Open.** OQ-9 (if (5) is not pointwise in the row, the closure fails).
- **Obligation.** **Unknown** until OQ-9 fixes (5). (1)-(4) and (6) are pointwise in the row or
  row-independent, so closure at them is mechanical. (5) as written quantifies over each entry, but
  its `cancelTab T N` and its `ewp` read the whole table `T`: a cancel run under a sum row may stop
  at an entry of the other summand. Whether (5) at `T` and at `T'` gives (5) at `T ⊕ T'` is not
  derived.

---

## 6. Continuation obligations

The three obligations are legitimately distinct (audit §4.4): `share` is about a stopped
context, `KapRel` about a reified `κ`, `owed` about the cancel run. All three change in the same
way: the `Ext` quantifier becomes `∀ W' ⊒ W`, and, under OQ-9 (a), they receive the frames `τ'`
the stop left open.

### D-SHARE: the stopped context's share

- **Form.**

  ```
  share T en n (ls, σ) τ' K Φ ρ  ≜
      (en.q = unr → ρ = ∅ ∧ τ' = [])
    ∧ ∀ (ls'', σ'') ⊒_ρ (ls, σ).
        (∀ w. (en.P_B(ls'', τ' ++ σ'') w ─⋆ Φ τ' (ls'', σ'') K[w]) ρ)
      ∧ (en.q ≠ lin → owed T n (ls'', σ'') τ' K ρ)
  ```

  `Φ τ'` is the continuation read with the closing obligation for `τ'` (D-TABLE's `Cont`); every
  variable is bound: `τ'` is the table's argument, passed by `opTable`. At `unr` a copied
  continuation may hold no open frame, by the same reason it holds no resource.
- **`σ = []`, `τ' = []` instance.** `contShare` (`Core/EffDefs.lean:144-149`) with `Ext ls ls' ρ`
  for the order, equal by T-NIL: the quantifier over `⊒` at `σ = []` ranges over non-empty
  extensions, so the equality is proved per introduction row, and that proof is **unknown**
  (OQ-58).
- **Uses.** D-ORD, D-OWED, D-STOP. **Today.** As built. Status: **as built; quantifier changed**.
- **Depends on.** D-ORD.
- **Open.** OQ-8 (the quantifier sits here under candidate (a)), OQ-9, OQ-57, OQ-58.
- **Obligation.** Monotone in `Φ` and along `⊑`: **mechanical**.

### D-KAP: a reified continuation's obligation

- **Form.** A reified `κ` holds the frames `τ` its stop left open:

  ```
  KapRel Tout Qout en (ls, σ) τ κ ρ  ≜
      (en.q = unr → ρ = ∅ ∧ τ = [])
    ∧ ∀ (ls', σ') ⊒_ρ (ls, σ).
        (∀ w. (en.P_B(ls', τ ++ σ') w ─⋆ ewp_{(ls',σ')}(τ) (resume κ w) (opTable Tout) Qout) ρ)
      ∧ (en.q ≠ lin → ewp_{(ls',σ')}(τ) (cancel κ) (opTable Tout) (λ _ _ v. ⌜v = ()⌝) ρ)
  ```

- **`σ = []`, `τ = []` instance.** `KapRel` (`Core/EffRules.lean:569-578`), equal by T-NIL, proved
  per introduction row, **unknown** (OQ-58), as `share`.
- **Uses.** D-ORD, D-EWP. **Today.** As built. **Depends on.** D-ORD, D-EWP.
- **Open.** OQ-8, OQ-28 (bound of a stored `κ`), OQ-58.
- **Obligation.** `vC_kTy_of_kapRel` (`Core/EffRules.lean:1053`) at `W`: **mechanical** at
  candidate (a) of OQ-8 (it reads `KapRel`'s quantifier into `kTy`'s `U` clause). At candidate (b)
  the `⊸` clause of `kTy`'s resume entry also quantifies, so `KapRel`'s quantifier must cover both.

### D-OWED: the cancel run's obligation

- **Form.**

  ```
  owed T n (ls, σ) τ K ρ  ≜  ∀ N. n ∈ N → hndNames K ⊆ N →
      ewp_{(ls,σ)}(τ) (K[raise (0,(0,(N, none)))]) (cancelTab T N) ⊥ ρ
  ```

  The cancel run starts holding the closing obligation for the frames `τ` the stop left open, and
  `cancelTab` admits only a stop with `τ' = []`, at which D-STOP's stop clause forces those frames
  closed (D-CANCELTAB). So `owed` says: running `K`'s finalisers innermost first closes every frame
  `K` holds, LIFO, with a `NoOwn` leftover.
- **`σ = []`, `τ = []` instance.** `cancelOwed` (`Core/EffDefs.lean:138-140`), by definition (no
  quantifier over worlds).
- **Uses.** D-CANCELTAB, D-EWP, D-DTOR. **Today.** As built. **Depends on.** D-CANCELTAB.
- **Open.** OQ-9 (frames), OQ-57.
- **Obligation.** **Unknown**: §12.1's probe is exactly this obligation at one 6.64 frame.

### D-DTOR: the destructor of a context

- **Form.** For a context `K`, its destructor `D_K` (O-FIN, owner 04) is the nested stack `K°`
  of its finaliser frames, innermost first: `D_K⟨e⟩ ≜ K°[e]` at `e` a raise or a cancel, and the
  sequential form `D_K ▷ e` at an `e` that may return (O-FIN), each finaliser running under the
  frames outside it. Its semantic content at `W`:

  ```
  Cancel_W(τ, T, N, K)  ≜  ewp_W(τ) (K[raise (0,(0,(N, none)))]) (cancelTab T N) ⊥
  ```

  `owed` is `Cancel_W` at the continuation of a stopped operation, for every region `N` holding
  its name and its handlers. An abortive stop's abandoned continuation needs no `Cancel`: it holds
  no finaliser frame (`Catches` at every `ubind`, `Paper/S3_Dynamics/Definitions.lean:404`) and
  nothing owned (D-OPTAB).
- **Unary content of L-W.** `Cancel_W(T, N, K)` is the semantic reading of `cancel κ ≡ D_K ▷
  return ()` (L-W, owner 06): the cancel run is the run of `D_K`, LIFO, to a `NoOwn` leftover.
- **`σ = []` instance.** `cancelOwed`'s body; `cancel_frame` (`Core/EffRules.lean:168`),
  `ewp_ccatch` (`:580`), `cancel_then` (`:342`).
- **Uses.** O-FIN, D-CANCELTAB. **Today.** Stated per use, not once. Status: **changed** (stated
  once).
- **Depends on.** D-CANCELTAB, D-EWP. **Open.** OQ-7 (finalisers at a non-abortive table;
  R-FINAB), OQ-21.
- **Obligation.** **Mechanical** at abortive finaliser rows (built). **Unknown** under OQ-9 (a),
  where a finaliser closes a frame opened before the stop.

---

## 7. The relation

### D-REL: `𝒱⟦A⟧_W`, `𝒞⟦C⟧_W`, `𝒢⟦Γ⟧_W`

One clause per former of O-TY, at `W = (ρ, ls, σ)`. The block is one `mutual` definition,
structurally recursive on the type (T-DEF). Clauses that do not read `σ` are today's with
`ls` replaced by `(ls, σ)`; they are marked **=**. The clauses that differ are marked **Δ** and
written in full.

```
𝒱⟦1⟧_W δ v              = ⌜v = ()⌝                                                    =
𝒱⟦A ⊗ B⟧_W δ v          = ∃ v₁ v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦A⟧_W δ v₁ ⋆ 𝒱⟦B⟧_W δ v₂          =
𝒱⟦0⟧_W δ v              = ⊥                                                           =
𝒱⟦A ⊕ B⟧_W δ v          = (∃ v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦A⟧_W δ v₁) ∨ (… inj₂ …)              =
𝒱⟦!A⟧_W δ v             = ρ = ∅ ∧ 𝒱⟦A⟧_W δ v                                           =
𝒱⟦[@a] A⟧_W δ v         = atLife δ a (λα. box α (𝒱⟦A⟧_W δ v))                           =
𝒱⟦Ref A⟧_W δ v          = ∃ ℓ v'. ⌜v = ℓ⌝ ⋆ ℓ ↦ v' ⋆ 𝒱⟦A⟧_W δ v'                        =
𝒱⟦Imm a A⟧_W δ v        = atLife δ a (λα. ∃ℓ. ⌜v = ℓ ∧ CohE (rsOf ls) ℓ A δ⌝
                                         ⋆ ptoImmS ℓ α (ls,σ) (λ W₀. 𝒱°⟦A⟧_W₀ δ))       Δ (OQ-46)
𝒱⟦Mut a A⟧_W δ v        = atLife δ a (λα. ∃ℓ. ⌜v = ℓ⌝ ⋆ ptoMutS ℓ α (ls,σ) (λ W₀. 𝒱⟦A⟧_W₀ δ))  Δ (OQ-46)
𝒱⟦Unk⟧, 𝒱⟦int w⟧, 𝒱⟦opq k⟧                                                            =
𝒱⟦X⟧_W δ v              = η(X).P W v                                                  =
𝒱⟦μX. A⟧_W δ v          = NoMut ∧ Cl ∧ ∀P. (𝒱⟦A⟧[P/X] ⊆ P) → P W v   (P over worlds)     =
𝒱⟦fam L⟧_W δ v  (= [L]) = ∃ ℓ c. ⌜v = arr ℓ c⌝ ⋆ ⊛_{m<c} 𝒱⟦L⟧_W δ (ℓ+m)               =
𝒱⟦U C⟧_W δ v            = ∀ W' ⊒ W. 𝒞⟦C⟧_W' δ (force_C v)                              Δ (OQ-8)

𝒞⟦F A⟧_W δ e            = wpG_W([]) e (valPost (λ W'. 𝒱⟦A⟧_W' δ))                       = (wpTS)
𝒞⟦F_Σ R⟧_W δ e          = ewp_W e (opTable ⟦Σ⟧δ) (λ W'. 𝒱⟦R⟧_W' δ)                      Δ (reads D-STOP)
𝒞⟦A ⊸ C⟧_W δ e          = see the two candidate clause sets below                      Δ (OQ-8)
𝒞⟦C & D⟧_W δ e          = 𝒞⟦C⟧_W δ (e (inj₁ ())) ∧ 𝒞⟦D⟧_W δ (e (inj₂ ()))               =
𝒞⟦⊤⟧_W δ e              = ⊤                                                           =
𝒞⟦∀'x ⊏ c. C⟧_W δ e     = see the two candidate clause sets below                      Δ (OQ-8)
𝒞⟦νX. C⟧_W δ e          = NuOk → ∃R. R ⊆ 𝒞ᴮ[R/X]⟦C⟧ ∧ R W e   (R over worlds)          =

𝒢⟦Γ⟧_W δ γ              = ⌜LiveWithin Γ γ⌝ ⋆ ⊛_{x live} 𝒱⟦Γ(x)⟧_W δ γ(x)              =
```

`fam L` is the array type, written `[L]`; its clause is today's `vCE` clause at `.fam`
(`Core/Relation.lean:149`) read at `W`, and T-MONO's "componentwise" case is this clause. `Imm̲`
(the view `withload` hands its callback) is not a former but the type metafunction
`VTy.immReborrow` (`Core/Types.lean:1447`), so the relation reads its result type and needs no
clause of its own. `𝒱°` is the observable view (today's `b = false`, `Core/Relation.lean:113-118`):
`U` positions relaxed to `⊤`. `ptoImmS`, `ptoMutS` at a world store the predicate at `W₀ = (ls₀, σ₀)`, the
members of `ls` and of `σ` strictly longer-lived than the cell; `σ₀` is OQ-46. Every former is
read at `W`; none falls back to the `σ = []` relation. This is the difference from every relation
family built beside the kernel, which fall back to the kernel's `vC` under `Imm`, `Mut`, `μ`, `ν`,
`[L]` and type variables (audit M1; e.g. `Stacked.lean:249`).

**The two candidate clause sets of OQ-8.** Until OQ-8 is settled, both are carried. They differ
only at `U`, `⊸` and `∀`. The arising guard (D-ARISE, OQ-45) is written `guard_W P ≜ TabAt_W →
P` and is present in both as in `vRLa`/`cRLa` (`Arising.lean:173-203`) unless OQ-45 removes it.

```
Candidate (a), CBPV points (audit §3.3):
  𝒱⟦U C⟧_W δ v        = guard_W (∀ W' ⊒ W. 𝒞⟦C⟧_W' δ (force_C v))
  𝒞⟦A ⊸ C⟧_W δ e      = ∀ v. 𝒱⟦A⟧_W δ v ─⋆ guard_W (𝒞⟦C⟧_W δ (e v))
  𝒞⟦∀'x ⊏ c. C⟧_W δ e = ∀ α. ⌜α ⊏ ⟦c⟧δ⌝ ─⋆ guard_W (𝒞⟦C⟧_W δ[x↦α] (e ()))
  share, KapRel, owed : ∀ W' ⊒ W   (D-SHARE, D-KAP, D-OWED)

Candidate (b), binder clauses (#287):
  𝒱⟦U C⟧_W δ v        = guard_W (∀ W' ⊒ W. 𝒞⟦C⟧_W' δ (force_C v))
  𝒞⟦A ⊸ C⟧_W δ e      = ∀ W' ⊒ W. ∀ v. 𝒱⟦A⟧_W' δ v ─⋆ guard_W' (𝒞⟦C⟧_W' δ (e v))
  𝒞⟦∀'x ⊏ c. C⟧_W δ e = ∀ W' ⊒ W. (τ's entries: x or not free in C)
                           ∀ α. ⌜α ⊏ ⟦c⟧δ_W'⌝ ─⋆ guard_W' (𝒞⟦C⟧_W' δ[x↦α] (e ()))
  share, KapRel, owed : ∀ W' ⊒ W
```

Candidate (b)'s `∀` clause is `cRLk`'s (`Extend.lean:92-96`), with `(τ, αt)` folded into `W'`.
Its `U` and `⊸` clauses are what §17.6 recommends and `vRLk` does not yet have: `vRLk`'s `U`
clause stays at `σ` (`Extend.lean:63-65`) and its `⊸` clause quantifies over resources only
(`:86-87`). At `U` both candidates quantify over `⊑`: the kernel already places a Kripke
quantifier there (`Core/Relation.lean:127-128`).

**The clause set of OQ-9 (b), capture rebasing.** Under OQ-9 (b) the stop is unchanged, a lend
ends at a stop as at a return, and the continuation is owed a re-lend at a lifetime fresh at
resumption. Every relation family built for that reading has its `U` clause as `RelendableS`
(`Stacked.lean:163-167`; `vRLs` at `:238-239`; `vRLk` at `Extend.lean:63-65`), which a plain
`∀ W' ⊒ W` does not contain: it splits the resource into the views the stop dropped (`vwS`) and a
part strictly above the outermost lend (`stratS`), and quantifies over `Ext` and over `ReLend`
with the views handed back. Read at `W`:

```
Candidate (b)-rebase, the U clause:
  𝒱⟦U C⟧_W δ v  =  guard_W (Relendable_W (λ W'. 𝒞⟦C⟧_W' δ (force_C v)))
  Relendable_W P ρ  ≜  ∃ ds ρz ρn. ρz ● ρn = ρ ∧ vw_W(ds) ρn ∧ strat_W ρz ∧
                         ∀ W' ⊒ W.  ReLend_{W'}(W)  →  (vw_{W'}(ds) ─⋆ P W') ρz
```

where `vw_W(ds)` is `vwS` at `W`'s stack with the dropped-flags `ds`, `strat_W` is `stratS` at the
outermost lifetime of `W`'s stack, and `ReLend_{W'}(W)` is D-ORD's condition (2) at `Relend =
ReLend`. Its `⊸` and `∀` clauses are those of OQ-8's chosen candidate: OQ-9 (b) composes with OQ-8
(a) by taking (a)'s `⊸`/`∀` and this `U`, and with OQ-8 (b) by taking (b)'s `⊸`/`∀` (the `∀`
clause being `cRLk`'s, `Extend.lean:92-96`) and this `U`. `share` and `KapRel` take the same
`Relendable_W` in place of `∀ W' ⊒ W` (GhostEnd's `RelendableN`, `Stacked.lean:170-174`, is the
`share` form). Whether the hand-back `vw_{W'}(ds) ─⋆ …` is derivable from `∀ W' ⊒ W` plus D-ORD's
`Relend` is not derived, so the three clause sets are carried until OQ-8 and OQ-9 are settled.

- **`σ = []` instance.** See T-NIL. Every **=** clause is today's clause at `(ls, [])`, by
  definition. Every **Δ** clause is today's clause conjoined with obligations at extensions, so it
  equals today's clause only if those obligations are discharged at every introduction row
  (OQ-58).
- **Uses.** D-W, D-ORD, D-ARISE, D-WPG, D-EWP, D-OPTAB, D-SHARE.
- **Today.** `vCE`, `cC`, `cB`, `effTab`, `effRet`, `effRetE` (`Core/Relation.lean:119-204`).
  Status: **changed** (re-indexed).
- **Slices.** 03 fixes the formers; 07 proves one compatibility lemma per rule at this relation.
- **Depends on.** D-ORD, D-ARISE, D-EWP.
- **Open.** OQ-8, OQ-9, OQ-45, OQ-46, OQ-31, OQ-58.
- **Obligation.** The definition: **mechanical** (T-DEF). Its use: T-NIL, T-MONO, T-FP (07).

### D-SEM: semantic typing at every world

- **Form.**

  ```
  Δ; Γ ⊨ e : C  ≜  ∀ δ γ W ρ.  Δ.Models δ  →  Wf W  →  σ.WF Δ  →  TabAt_W(ρ)  →
                     𝒢⟦Γ⟧_W δ γ ρ  →  𝒞⟦C⟧_W δ (γ e) ρ
  ```

  `σ.WF Δ` is `LStack.WF` (`Stacked.lean:295-296`): entries' variables in `Δ` and distinct. Under
  candidate (b), §17.6 cost 3 notes that a transported context may meet entries named by later
  binders; whether the condition becomes freshness is boxed in OQ-8, with the representation of
  `x` (D-W).
- **`σ = []` instance.** `SemC` (`Core/Relation.lean:228-229`): `Wf`, `σ.WF Δ` and `TabAt`
  hold trivially at `[]` (`tabAtS_nil`, `Arising.lean:251`). This is `gfpAt_nil_iff`'s content
  (`Stacked.lean:593`) and `gfpAtA_nil_iff`'s (`Arising.lean:354`), for their relations.
- **Uses.** D-REL. **Today.** `SemC`; `GFPAt` (`Stacked.lean:305`), `GFPAtA` (`Arising.lean:234`).
  Status: **changed**.
- **Depends on.** D-REL, D-ARISE. **Open.** OQ-8, OQ-45.
- **Obligation.** None at the definition; T-FP is 07's.

### T-NIL: Core is the `σ = []` instance

- **Form.** Core's definitions are re-pointed: each is shown equal to the model's definition at
  `σ = []`, by `rfl` where the definition reads no extension of the world and by a per-row proof
  where it does; then every Core theorem keeps its statement. The per-row proof is **unknown** at
  `U`, `share` and `KapRel` (OQ-58), so no section claims these equalities by definition.

  | Core object | definition at `σ = []` | `_nil` lemma | form |
  |---|---|---|---|
  | `wpG` (`Core/EffDefs.lean:27`) | `wpG_W([])` | `wpG_nil` | definitional, given D-STOP at `τ = []` |
  | `wpTS` (`Core/World.lean:186`) | `wpG_W([]) ∘ valPost` | `wpTS_nil` | `wpTS_iff_wpG` (`Core/EffWp.lean:43`) |
  | `Table`, `Mono`, `Abortive`, `bot` (`Core/EffDefs.lean:50-65`) | D-TABLE at `[]` | `table_nil` | definitional |
  | `ewpStep`, `ewpTS` (`:68-75`) | D-EWP at `[]` | `ewp_nil` | definitional |
  | `opTable` (`:157`) | D-OPTAB at `[]` | `opTable_nil` | definitional given `share_nil` (`τ' = []` holds at `[]` under the default stop) |
  | `cancelTab`, `errOk` (`:122-134`) | D-CANCELTAB at `[]` | `cancelTab_nil` | definitional |
  | `contShare` (`:144`) | D-SHARE at `[]` | `share_nil` | to be proved per introduction row, `new ⊆ old` mechanical, `old ⊆ new` **unknown** (OQ-58): `∀ W' ⊒ W` at `[]` ranges over `τ ≠ []` |
  | `KapRel` (`Core/EffRules.lean:569`) | D-KAP at `[]` | `kapRel_nil` | as `share_nil`: `old ⊆ new` **unknown** (OQ-58) |
  | `cancelOwed` (`Core/EffDefs.lean:138`) | D-OWED at `[]` | `owed_nil` | definitional (no quantifier) |
  | `vCE` (`Core/Relation.lean:119`) | D-REL at `[]` | `vC_nil` | **=** clauses definitional; `U`: `old ⊆ new` **unknown** (OQ-58) |
  | `cC`, `cB` (`:154, 192`) | D-REL at `[]` | `cC_nil`, `cB_nil` | definitional at candidate (a) except through `U`; `⊸`, `∀`: `old ⊆ new` **unknown** at (b) |
  | `effTab`, `effRet`, `effRetE` (`:170-185`) | D-REL at `[]` | `effTab_nil` | definitional |
  | `gDenC` (`:224`) | `𝒢` at `[]` | `gDen_nil` | follows from `vC_nil` |
  | `SemC` (`:228`) | D-SEM at `[]` | `sem_nil` | follows from `cC_nil`, `gDen_nil`, `tabAtS_nil` |

  **The `U` clause at `[]`.** Today: `∀ ls'. Ext ls ls' ρ → cC C ls' δ (force v)`
  (`Core/Relation.lean:127-128`). At `W = (ρ, ls, [])`: `∀ (ls', σ') ⊒_ρ (ls, []). 𝒞⟦C⟧_{(ls',σ')}
  δ (force v)`, where `σ' = τ` may be non-empty. So the new clause is today's (the instance
  `τ = []`) conjoined with obligations at every `τ ≠ []`. Elimination is unaffected (instantiate
  `τ = []`, as `all_elimK` does at `∀`, `Extend.lean:110-115`). Introduction is the obligation:
  every Core proof that builds a `U` value must discharge the extensions. The introduction sites:
  the `thunk` rows (`Core/Compatibility.lean`), `fixSelf` in `bounded_fix`
  (`Core/BoundedFix.lean:107-110`, which uses `Ext.refl`), `vC_kTy_of_kapRel`
  (`Core/EffRules.lean:1053`), the clauses in `handle_compatC` (`:1121, 1145, 1153`, which use
  `ext_empty'`, `:691`).

  This holds at **both** candidates of OQ-8, since both quantify over `⊑` at `U`. OQ-8's criterion
  (i) reads it as a property of `vRLk` (no `σ = []` lemma); it is a property of any clause that
  quantifies over stack extensions at `σ = []` (recorded in OQ-8). The kernel conclusion
  survives exactly when `old ⊆ new` is proved at the introduction rows. If it fails, the kernel's
  `vCE` thunk clause is strictly strengthened: Core's relation changes meaning, `fundamentalC`
  and every Core theorem do not transfer, and they are re-proved through T-FP at `W` under E-W
  (audit M2). This is OQ-58, a first probe run next to OQ-9's:

  ```lean
  /-- OQ-58: a thunk in today's relation at ls is in the new U clause at (ρ, ls, []), i.e. it is
  forced correctly at every one-entry extension. Proved per introduction row. -/
  def NilAgreesU : Prop :=
    ∀ (C : CTy) (δ : LSub) (ls : List SRec) (f : Val) (ρ : WRes),
      vC true (.thunk C) ls δ f ρ →
      ∀ (e : OEnt) (ls' : List SRec), OrdW ρ ls [] ls' [e] →
        cCW C ls' [e] δ (forceE C (.val f)) ρ
  ```

  `OrdW` is D-ORD and `cCW` D-REL at `W` (names the settling experiment defines). The universal form is expected
  to fail in general (it is `old ⊆ new` for every thunk, not only introduced ones); the probe is
  its instances at the `thunk`, `fixSelf`, `vC_kTy_of_kapRel` and handler-clause rows, each with
  every hypothesis discharged, and a refutation is a thunk built by one of those rows at which it
  fails.
- **Proof route.** **=** clauses by `rfl`. **Δ** clauses: `new ⊆ old` by instantiating
  `τ = []`, `Relend = id`; `old ⊆ new` per introduction row, from T-FP at `W` for the row's
  premises.
- **Today.** The GhostEnd `_nil` lemmas are `propext` equalities of sibling families:
  `vRLs_nil`, `cRLs_nil`, `gRLs_nil` (`Stacked.lean:501, 540, 588`), `vRLa_nil`, `cRLa_nil`
  (`Arising.lean:260, 300`). `vRLk` has none (`Extend.lean`, whole file).
- **Depends on.** D-REL, D-STOP (default at `τ = []`).
- **Open.** OQ-8 (criterion (i)), OQ-11, OQ-58.
- **Obligation.** **Mechanical** at the **=** clauses and at the definitional rows. **Unknown** at
  `old ⊆ new` for the `U` clause (both candidates) and the `⊸`/`∀` clauses (candidate (b)).

### T-DEF: the relation is defined without a step index

- **Form.** `𝒱`, `𝒞`, `effRet` at `W` are one `mutual` block, `termination_by structural` on the
  type. `W`'s components and the extensions `W' ⊒ W` are data universally quantified to the left
  of a clause, never relations. `ewp`, `μ` and `ν` are least and greatest fixed points written in
  `Prop`. Nothing is stored in the world.
- **Proof route.** As `Stacked.lean` (structural with `σ` a parameter, `:237-273`) and
  `Extend.lean` (structural with `σ` an index growing at `∀`, `:62-105`); the elaborator checks
  it. The five cut-offs of OQ-31 (TR §16.5) keep it so.
- **Today.** `vRLs` structural (#282, `Stacked.lean:5-28`); `vRLk` structural (`Extend.lean:62-105`).
- **Depends on.** D-REL. **Open.** OQ-31.
- **Obligation.** **Mechanical**.

---

## 8. OQ-8: the settling statements

OQ-8 is boxed in the register (99); this records the Lean statements that settle it, in
the terms of this section. The candidates are six clause sets over `W`: (a), (b0) and (b) of OQ-8,
each with the `⊸`/`∀`/`U` clauses as §7 writes them, and each composed with OQ-9 (b)'s
`Relendable_W` at `U` (the "-rebase" sets of §7). (b0) is `vRLk`/`cRLk` exactly as built
(`borrow-callbacks:experiments/GhostEnd/GhostEnd/Extend.lean:62-105`: `U` clause `RelendableS` at
the fixed stack, `⊸` over resources only, `∀` over extensions `τ ++ σ`), which is already a
"-rebase" set, so the six are (a), (b), (a)-rebase, (b)-rebase, (b0), and (b0) without
`RelendableS` (its `U` replaced by `∀ W' ⊒ W`). Each is written in an experiment with every row of
the rule set as an enumerated `sorry` (audit M6).

```lean
/-- Two placements coincide at every world. Stated for every pair of candidates. -/
def QuantPlacementAgrees (X Y : Candidate) : Prop :=
  ∀ (C : CTy) (δ : LSub) (ls : List SRec) (σ : List OEnt) (e : Expr) (ρ : WRes),
    Wf ρ ls σ → TabAtW σ ρ → (cCW X C ls σ δ e ρ ↔ cCW Y C ls σ δ e ρ)

/-- Criterion (i): a candidate at σ = [] is the kernel's relation. -/
def NilAgrees (X : Candidate) : Prop := ∀ C δ ls e ρ, cCW X C ls [] δ e ρ ↔ cC C ls δ e ρ

/-- Criterion (iii): the withbor row's starting point at a candidate, through its U clause. -/
def CallbackExt (X : Candidate) : Prop :=
  ∀ σ δ y c T D ls f ρf e α ρv ρ,
    vCW X (.thunk (.all y c (.arr (.mut (.var y) T) D))) ls σ δ f ρf →
    FreshLend e y α σ ρf →
    ptoMutS e.l α (ls, σ) (fun W₀ => vW T W₀ (δ.extend y α)) ρv →
    ResU.CompS ρf ρv ρ →
    cCW X D ls (e :: σ) (δ.extend y α) (.app (.app (forceE _ (.val f)) (.val .unit)) (.val (.loc e.l))) ρ
```

The payload predicate is D-REL's `𝒱⟦T⟧` at the stored world `W₀ = (ls₀, σ₀)` (OQ-46's default (a):
the entries of `σ` strictly longer-lived than the cell), not the kernel's `vC`, so the probe tests
D-REL at `W` and falls back to no `σ = []` relation. At (b0), `CallbackExt (b0)` is the existing
`callback_ext` (`Extend.lean:131`), which reads the payload at the kernel's `vC` with no stack: that
is (b0) as built, and it agrees with the statement above exactly where OQ-46 (b) is taken
(`σ₀ = []`). `CallbackExt (a)` is `callback_ext` with the `U` clause doing what `cRLk`'s `∀`
clause does there: force the callback at the extended world, then instantiate `∀` and `⊸` at that
same world. It is a reading that the CBPV placement suffices for the `withbor` row; it is not
proved. A **separating configuration** is a closed derivation and world at which the conclusion
of T-FP holds at one candidate and fails at the other, every hypothesis discharged.

Criteria (ii) and (iv) are T-MONO and the `thunk`, `lam`, `allI` rows (`lam_RLa`,
`allI_RLa`, `Arising.lean:478, 815`, at the fixed-stack relation). The pairs `QuantPlacementAgrees`
is stated at: (a)/(b) (the audit's question), (b0)/(b) (whether §17.6's added `U` and `⊸`
quantifiers change the relation `vRLk` already has), (a)/(a)-rebase and (b)/(b)-rebase (whether
OQ-9 (b)'s hand-back `vw_{W'}(ds) ─⋆ …` is derivable from `∀ W' ⊒ W` plus D-ORD's `Relend`, §7),
and (a)-rebase/(b0).

---

## 9. Retirement map

What each relation family and stacked piece becomes in `W`. Every retirement is conditional on
the re-index (decision 20: a generalisation lands with the deletion of its instances,
`docs/decisions.md:47-49`), and nothing is deleted before it.

| piece | where | becomes in `W` | fate |
|---|---|---|---|
| `vRL`, `cRL` | `experiments/GhostEnd/GhostEnd/Bridge.lean:221, 231` | on the fragment it reads, D-REL's OQ-9 (b) clause set (§7) at the one-entry world `[e]`; it reads only `.thunk` (over `.ret`/`.arr` bodies at the external row `S`) and `.tensor` among value formers, falls back to the kernel's `vC` at every other value former, and reads `True` at every other computation former (`&`, `⊤`, `∀`, `ν`, the `.eff` chain) | retire, after inclusion (i) below |
| `vRLg`, `cRLg`, `RelendableG` | `experiments/GhostEnd/GhostEnd/RLCompat.lean:508, 518, 498` | `vRL` with the table as a guard: on the same fragment, D-REL's (b)-rebase clause set with `guard_W` at `[e]` | retire, after inclusion (i') below |
| `vRLs`, `cRLs`, `effRetS`, `gRLs` | `Stacked.lean:237, 252, 268, 284` | D-REL's OQ-9 (b) clause set with OQ-8 (a)'s `⊸`/`∀`, `σ` fixed (its `U` is `RelendableS`, `:238-239`) | retire, after equivalence (ii) below |
| `vRLa`, `cRLa`, `effRetA`, `gRLa`, `guardS` | `gfp-arising:experiments/GhostEnd/GhostEnd/Arising.lean:173, 189, 206, 222, 169` | D-REL's OQ-9 (b) clause set with `guard_W` (OQ-45) and OQ-8 (a)'s `⊸`/`∀` | retire, after equivalence (iii) below |
| `vRLk`, `cRLk`, `effRetK` | `borrow-callbacks:experiments/GhostEnd/GhostEnd/Extend.lean:62, 81, 100` | D-REL's OQ-9 (b) clause set (its `U` is `RelendableS`, `Extend.lean:63-65`) with OQ-8 (b)'s `∀` (`:92-96`) and a resource-only `⊸` (`:86-87`) | retire, after equivalence (iv) below; its content survives as candidate (b) if OQ-8 picks (b) |
| `LEnt`, `LKind`, `LStack` | `Stacked.lean:93-107` | `OEnt`, `σ` (D-W), the lifetime folded in | promote as D-W |
| `extS` | `Stacked.lean:110` | `δ` at a world: `δ` extended by `σ`'s variables at their lifetimes | promote (D-W representation) |
| `ReLend` | `Stacked.lean:158` | `Relend` in D-ORD under OQ-9 (b) | promote conditionally |
| `depth`, `tabK` | `Stacked.lean:115, 118` | computed from entries' rows `R` | promote |
| `TabAt`, `TabAtS`, `tabAtS_comp`, `wpG_tabAt`, `wpG_tabAtS_one`, `tabAt_start` | `Table.lean:39, 87`; `Stacked.lean:290`; `Arising.lean:83, 112`; `StackStep.lean:360` | `TabAt_W` (D-ARISE), T-ARISE | promote |
| `RelendableS`, `RelendableN` | `Stacked.lean:163, 170` | the `U` clause at `W` and `share`'s continuation, under OQ-9 (b) | promote conditionally |
| `ghostS`, `stopS`, `dropS`, `vwS` | `Stacked.lean:188, 200, 145, 132` | what a stop owes the lenders it crosses: D-SHARE's content under OQ-9 (b) | promote conditionally |
| `bodyS`, `openFS`, `OpenS` | `Stacked.lean:209, 215, 221` | `ewp_W` at `σ` (D-EWP); `bodyS_nil_iff` (`:476`) is `ewp_nil` | promote |
| `AllCross` | `StackStep.lean:182` | removed by the split `σ = σ_in ++ σ_out` at a handler (T-FRAME), or R-MID | retire |
| `LinResume`, `ResumeAff`, `opTableO` | `Body.lean:141`; `Drop.lean:44, 49` | instances of D-TABLEOK's conjunct (5) | retire as predicates; keep as instances |
| `GFPAt`, `GFP`, `GFPAtA`, `GFPA` | `Stacked.lean:305, 312`; `Arising.lean:234, 238` | T-FP at `W` (07) | retire |
| `gfpAt_nil`, `gfpAtA_nil`, `segment_fundamental` | `Stacked.lean:613`; `Arising.lean:374`; `experiments/GhostEnd/GhostEnd/Segment.lean:30` | T-NIL; `fundamentalC` | retire |
| `Open`, `Relend`, `OpenD`, `RelendI`, `AntiRelend`, `NestRelend`, `NestRelend₂` | `Body.lean:63`; `Relend.lean:57`; `Descend.lean:125`; `ImmLend.lean:128`; `Frames.lean:68`; `Nested.lean:103, 285` | `ewp_W` at depth 1 and 2 (subsumed by `OpenS`, audit §2.2) | retire defs; promote the frame lemmas built on them |
| `ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`, `stack_step_*`, `nested_relend`, `nested₂_relend` | `Relend.lean:117`; `ImmLend.lean:175`; `Frames.lean:89`; `StackStep.lean:392, 563, 1003`; `Nested.lean:164, 352` | T-FRAME's instances | promote |
| `FrameThaws`, `FrameThawsD`, `StopSafe`, `RBody`, `KernelInvariant`, `O151AsStated`, `CloL`, `KapRelR`, `URelend`, `Relendable` | `Typed.lean:361, 166, 180`; `Values.lean:365`; `Kernel.lean:47`; `Open.lean:76`; `Callee.lean:45`; `Bridge.lean:114, 133`; `RLCompat.lean:77` | no counterpart (superseded by `OpenS`, audit §3.5) | retire |
| `not_gfp`, `not_gfpAt_below` | `gfp:experiments/GhostEnd/GhostEnd/Below.lean:282, 196` | the configuration T-ARISE excludes (`below_excluded`, `Arising.lean:446`) | do not merge under a `not_` name (audit §3.5) |
| `contShare`, `KapRel`, `cancelOwed` | `Core/EffDefs.lean:144, 138`; `Core/EffRules.lean:569` | D-SHARE, D-KAP, D-OWED at `[]` | keep, re-indexed |
| `wpG`, `ewpTS`, `opTable`, `cancelTab`, `vCE`, `cC`, `cB`, `SemC` | Core, cited above | D-WPG, D-EWP, D-OPTAB, D-CANCELTAB, D-REL, D-SEM at `[]` | keep, re-indexed (T-NIL) |

**The equivalences each retirement needs.** A family retires only when it is shown to be the
clause set it is claimed to become. Each is written as an enumerated `sorry` in the experiment
that states D-REL, with its `_nil` instance:

```lean
-- (i): on vRL's fragment, D-REL's OQ-9 (b) clause set at the one-entry world is included in vRL,
-- and the two agree there. vRL's own index is (S, x, T, δ, l) and a lifetime α, not a stack entry;
-- e is the entry built from them (place l, variable x, payload T, row S, lifetime α).
theorem vRebase_le_vRL : ∀ S x T δ l A α ls v ρ, RLFragment S A →
    vRebase [entryOf S x T l α] δ A ls v ρ → vRL S x T δ l A α ls v ρ := sorry
theorem vRL_eq_rebase_frag : ∀ S x T δ l A α ls v ρ, RLFragment S A →
    (vRL S x T δ l A α ls v ρ ↔ vRebase [entryOf S x T l α] δ A ls v ρ) := sorry
theorem vRL_nil        : ∀ δ A ls v ρ, vRebase [] δ A ls v ρ ↔ vC true A ls δ v ρ := sorry
-- (i'): vRLg, the same at the guarded clause set.
theorem vRLg_eq_rebaseG_frag : ∀ S x T δ l A α ls v ρ, RLFragment S A →
    (vRLg S x T δ l A α ls v ρ ↔ vRebaseG [entryOf S x T l α] δ A ls v ρ) := sorry
theorem vRLg_nil       : ∀ δ A ls v ρ, vRebaseG [] δ A ls v ρ ↔ vC true A ls δ v ρ := sorry
-- (ii): vRLs at σ is the OQ-9 (b) clause set with OQ-8 (a)'s ⊸/∀.
theorem vRLs_eq_rebase : ∀ σ δ A αs ls v ρ, vRLs σ δ A αs ls v ρ ↔ vRebaseA σ αs δ A ls v ρ := sorry
-- vRLs_nil exists (Stacked.lean:501); it becomes the instance of vRL_nil at this clause set.
-- (iii): vRLa is (ii)'s clause set with guard_W.
theorem vRLa_eq_rebase : ∀ σ δ A αs ls v ρ, vRLa σ δ A αs ls v ρ ↔ vRebaseAG σ αs δ A ls v ρ := sorry
-- vRLa_nil exists (Arising.lean:260).
-- (iv): vRLk is the OQ-9 (b) clause set with OQ-8 (b)'s ∀ and a resource-only ⊸.
theorem vRLk_eq_rebase : ∀ σ δ A αs ls v ρ, vRLk σ δ A αs ls v ρ ↔ vRebaseB σ αs δ A ls v ρ := sorry
theorem vRLk_nil       : ∀ δ A ls v ρ, vRLk [] δ A [] ls v ρ ↔ vC true A ls δ v ρ := sorry
```

`vRebase`, `vRebaseG`, `vRebaseA`, `vRebaseAG`, `vRebaseB` are the clause sets of §7 at the stated
choices; `RLFragment S A` (the value types `vRL` reads: `.thunk` of a `.ret`/`.arr` body at row
`S`, closed under `.tensor`) and `entryOf` are names the experiment that states D-REL defines.
`vRLk_nil` is the statement `vRLk` lacks today; at the `U` clause it is OQ-58's question at
`RelendableS`.

What is known and what is not, per family. `vRL` and `vRLg` (`Bridge.lean:221-240`,
`RLCompat.lean:508-527`): a full `↔` with D-REL is excluded **by their definitions**, not unknown,
because `cRL`/`cRLg` read `True` at `&`, `⊤`, `∀`, `ν` and the `.eff` chain (`| _, _, _, _ => fun
_ => True`), so at `A = U(∀…)` or `U(C & D)` they hold where D-REL states a real clause; and the row
is an external parameter `S` read through `opTable (Row.tab S δ)`, not the type's own row. Hence
the fragment restriction and the one-way inclusion. On the fragment, each `↔` is **mechanical**
except at the kernel fallback under `Imm`, `Mut`, `μ`, `ν`, `[L]` and type variables inside a
`.tensor` component. `vRLs`, `vRLa`, `vRLk`: each `↔` reads the families' fallback to the kernel's
`vC` at those formers (audit M1; `Stacked.lean:249`) against D-REL's reading of every former at
`W`, so each is **unknown** at those formers and **mechanical** elsewhere.

---

## 10. Models, comodels and runners in `W`

### Sources read for this section

- **Ahman & Bauer, *Runners in action*, ESOP 2020** (arXiv 1910.11629, fetched for this section).
  §2.2 Def. 1: "A runner R for a signature Σ is given by a carrier set |R| together with, for each
  op ∈ Σ, a co-operation op_R : A_op → (|R| ⇒ B_op × |R|)". The induced map `r_X` "transforms
  (static) computation trees into state-passing maps", and the continuation "appears precisely
  once as the head of the outermost application. In terms of programming, this corresponds to
  linear use in a tail-call position." Def. 2: a T-runner gives, for each op, `op_R : A_op → T
  B_op`. Prop. 3: monad morphisms `Tree_Σ(−) → T` are in one-to-one correspondence with T-runners
  for Σ. Thm 7 (Finalisation): "A well-typed run factors through finalisation"; "unless some
  enveloping runner sends a signal, finalisation with F is guaranteed to take place".
- **Katsumata, Rivas & Uustalu, *Interaction laws of monads and comonads*, LICS 2020** (arXiv
  1912.13477, fetched for this section). §2.1: a functor-functor interaction law is two
  endofunctors `F`, `G` with maps `φ_{X,Y} : F X × G Y → X × Y` natural in `X` and `Y`;
  "computations over a set of values X are elements of F X … Machine behaviors over a set of
  states Y are elements of G Y". §4 (Runners): "a (stateful) runner of T [is] an object Y with a
  family θ of maps θ_X : T X × Y → X × Y natural in X" satisfying unit and multiplication laws;
  monad-comonad interaction laws are in bijection with `D`-coalgebraic runner specs. §3 defines a
  monad-comonad interaction law as a monad `T`, a comonad `D` and maps `ψ_{X,Y} : T X × D Y →
  X × Y` compatible with `η`, `µ`, `ε` and `δ` (diagrams (1), four conditions); a stateful runner
  (§4) has the unit and multiplication conditions only.
- Plotkin & Pretnar (LMCS 2013), Møgelberg & Staton (LMCS 2014), Plotkin & Power (MFPS 2008):
  [via `docs/effects-tr/12-sources.md`], as marked there (every computation type a model;
  capabilities as comodels; a theory with a constant has only the empty comodel).

What a comodel means for a capability is OQ-19 (default (a): state-access semantics, no runner
construct, no `finally`). Runners are cited for the duality and the shape of the interaction law;
nothing below adopts a runner construct.

### D-MODEL: `IsModel`

- **Form.** A model of the effect `n : E` (with row `Σ_in = n:E ⊕ Σ`, `n ∉ Σ`) at carrier
  `(Tout, Qout)` is a pair `(h_ret, hs)` such that, at every world:

  ```
  IsModel_{n,E}(Tout, Qout)(h_ret, hs)  ≜
      (∀ W τ v. Qin_W v ⊨ ewp_W(τ) (h_ret v) (opTable Tout) Qout)
    ∧ ∀ i en. ⟦n:E⟧ n i = en → ∃ c. clauseAt hs i = c ∧
        (¬en.abort → ∀ W τ τ' v κ. en.P_A_W v ⋆ KapRel Tout Qout en W τ' κ ⊨ ewp_W(τ) (c (v, κ)) (opTable Tout) Qout)
      ∧ (en.abort  → ∀ W τ v. en.P_A_W v ⊨ ewp_W(τ) (c v) (opTable Tout) Qout)
    ∧ ∀ m i. m ≠ n → Tin m i = Tout m i
  ```

  These are exactly `ewp_handle`'s hypotheses (`Core/EffRules.lean:615-624`), named and read at
  `W`. The clause runs outside the region, continuing the handler's own run, which holds its own
  obligation `τ`; `κ` holds the frames `τ'` its stop left open (D-KAP). `Φ` in the audit's form ("closed under `opTable Σ` stops at every future world") is the
  carrier `ewp_W(·)(opTable Tout) Qout`.
- **Uses.** K-MODEL, D-KAP, D-EWP.
- **Today.** Not named; the hypotheses `hret`, `hop` of `ewp_handle`. Status: **new** (as a
  name).
- **Slices.** 02: the syntactic form (`clausesTy`, `retTy`, `kTy`, `Core/EffRules.lean:976-994`);
  06: L-HRET, L-HOP, L-HFWD, L-HUNIQ.
- **Depends on.** D-KAP, D-EWP. **Open.** OQ-11 (stated at `W`), OQ-3.
- **Obligation.** None at the definition.

### T-MODEL: every computation type is a model; handling is initial; graded algebraicity

- **Form.**

  ```
  (M1) ∀ C W. 𝒞⟦C⟧ is closed under stops of opTable ⟦Σ⟧ at W:
         en.P_A_W v ⋆ share ⟦Σ⟧ en n W [] K (λ τ W' t. 𝒞⟦C⟧^τ_W' t) ⊨ 𝒞⟦C⟧_W (K[perform (n,(i,v))])
       (𝒞⟦C⟧^τ the clause read with closing obligation τ; at F_Σ R it is ewp_W(τ))
       for C = F_Σ R by ewp_fold; for A ⊸ C, C & D, ∀ pointwise.
  (M2) IsModel_{n,E}(Tout,Qout)(h_ret,hs) →
         ∀ W e. ewp_W e (opTable Tin) Qin ⊨ ewp_W (hnd_n (h_ret,hs) e) (opTable Tout) Qout
       (existence of the homomorphism out of the least fixed point; uniqueness is L-HUNIQ, binary).
  (M3) an operation stopped under K at qualifier q owes K's share scaled by q (D-SHARE:
       unr → ∅; q ≠ lin → owed, D-OWED), and K's destructor when weakening applies (D-DTOR).
  ```

- **Proof route.** (M1) at `F_Σ` is `ewp_perform_here` (`Core/EffRules.lean:100`) generalised from
  the empty context to `K` with its share; at the other formers by their clauses. (M2) is
  `ewp_handle` (`Core/EffRules.lean:615-688`) with its hypotheses read as `IsModel`; its five-case
  induction on the least fixed point is the existence half of initiality (audit M11 asks it to be
  read so; the proof is unchanged). (M3) is the definition of `share`; re-deriving `let_compatC`'s
  side conditions (`:896`), `then_compatC` (`:928`) and `kTy`'s cancel entry (`:976-982`) from it
  is 06's L-ALG and 07's.
- **Today.** `ewp_handle` as a case analysis; no `IsModel`. Plotkin-Pretnar's "every computation
  type is a model" [via 12-sources] is the statement (M1).
- **Depends on.** D-MODEL, D-SHARE, D-OWED, D-DTOR.
- **Open.** OQ-11, OQ-4 (uniqueness), OQ-3 (a handler site as a world entry).
- **Obligation.** (M1), (M2) at `σ = []`: **mechanical** (built). At `W` under OQ-9 (a): **unknown**
  at (M2)'s `[op]` case, where the clause receives `κ` holding frames `τ'` and may run inside
  lends of its own before resuming (§12, the second companion configuration).

### D-COMODEL: `IsComodel`

- **Form (default of OQ-19).** A comodel of `n : E` at state `S`, answering in row `Σ'`, is a
  family of co-operations on the payload, `c_i : U(S ⊗ A_i ⊸ F_{Σ'}(S ⊗ B_i))` (the type 02
  K-COMODEL and 03 K-CAP use), such that, at every world:

  ```
  IsComodel_{n,E,Σ'}(S)(c)  ≜  ∀ i en W s v. ⟦n:E⟧ n i = en → ¬en.abort →
      𝒱⟦S⟧_W s ⋆ en.P_A_W v  ⊨
        ewp_W (force c_i (s, v)) (opTable ⟦Σ'⟧) (λ W'. 𝒱⟦S⟧_W' ⊗ en.P_B_W')
  ```

  The `Mut 'l S` view is not an argument of the co-operation. At a capability call
  `withswap m (λs. force c_i (s, v))` (03 K-CAP), `[TR]` 6.66 (AntiFrame) at the cell of `m`
  supplies `𝒱⟦S⟧` of the payload taken out and takes `𝒱⟦S⟧` of the payload put back, so that
  `IsComodel` over `𝒱⟦S⟧` gives the call's `ewp` over `𝒱⟦Mut 'l S⟧`. At `Σ' ≠ ∅` that needs
  `withswap` at a row (OQ-20 (c)).

  The comodel meets the same `opTable ⟦n:E⟧` entries as a model of `n : E`: `P_A` in, `P_B`
  out. That is TR D4.6's "one protocol per effect for both models and comodels"
  (`docs/effects-tr/12-sources.md` §12.3 item 3). An abortive entry has no co-operation: a theory
  with a constant has only the empty comodel (Plotkin-Power 2008 [via 12-sources]).
- **Reading against the sources.** At `Σ' = ∅` the co-operation is Ahman-Bauer's Def. 1: a
  carrier `|R|` (the payload `S`) with pure co-operations `op_R : A_op → (|R| ⇒ B_op × |R|)`, which
  is `S ⊗ A ⊸ F(S ⊗ B)`. At `Σ' ≠ ∅` the co-operation is effectful over a carrier, which is not
  Def. 1 (pure, with a carrier) nor Def. 2 (a T-runner, `op_R : A_op → T B_op`, with no carrier):
  it is Ahman-Bauer's kernel-monad runner of §3 (a runner whose co-operations are kernel code over
  `Σ'` with state `C`), or Katsumata-Rivas-Uustalu's R-residual runner (arXiv 1912.13477: a
  monad map `T → St_{R,Y}` into the residual monad's state monad). Both sources were fetched
  (below); the R-residual reading is this section's match, marked [I].
- **Uses.** K-COMODEL, K-CAP, K-SWAP, O-COMODEL.
- **Today.** Not built: `withswap` calls are checked against no table (audit C2). The capability as
  a borrow: `handle` is `withbor` form (2), typed (`translate_typed`,
  `experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`) and safe (`effect_safety`,
  `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:55`), an instance of the shift
  schema (`handle_is_shift`, `Safety.lean:115`; `shiftTy`, `experiments/Shifts/Shifts.lean:17`).
  Status: **new**.
- **Slices.** 02 (form), 03 (K-CAP, K-SWAP), 06 (L-STATE, L-INTER, L-TENSOR).
- **Depends on.** D-OPTAB, D-REL. **Open.** OQ-19, OQ-1, OQ-20 (a callee that performs;
  R-PURESWAP), OQ-29.
- **Obligation.** None at the definition.

### T-COMODEL: running a computation against a capability meets the protocol

- **Form.**

  ```
  IsComodel_{n,E,Σ'}(S)(c) →
    ∀ W e. ewp_{W·e_l} e (opTable (⟦n:E⟧ ⊕ ⟦Σ'⟧)) Q  ⊨  ewp_{W·e_l} (run_c e) (opTable ⟦Σ'⟧) Q
  ```

  where `W·e_l` is the world with the lend of the state cell as its innermost entry and `run_c e`
  replaces each `perform_n` by a `withswap` call of the co-operation on the lent cell (the
  translation of `experiments/HandlersAsBorrows`, `Translate.lean:182-184`). At `Σ' = ∅` this is
  the free-model universal property applied to the `St_S`-structure `op_M` (A-B §2.2, the text
  before Def. 2): the co-operations determine the homomorphism `r_X` out of the free model, "linear
  use in a tail-call position", and T-COMODEL says its target is `ewp` at the residual row. At
  `Σ' ≠ ∅` the co-operation is neither A-B's Def. 1 nor Def. 2 (D-COMODEL), and the reading is
  through A-B's kernel-monad runner (§3.1) or KRU's residual runners, marked [I]. A-B's Prop. 3
  (monad morphisms `Tree_Σ(−) → T` correspond to carrier-free `T`-runners) does not back it
  directly.
  Running against a comodel is the tensor of a model and a comodel used for operational semantics
  (Plotkin & Power, MFPS 2008 [via 12-sources]).
- **The runner laws.** The borrow constant's result type is the shape of Katsumata-Rivas-
  Uustalu's `φ : F X × G Y → X × Y`: `withbor` form (2) takes the source `Ref S` and a callback
  and returns `Ref S ⊗ T₂` (`shiftTy … true`, `experiments/Shifts/Shifts.lean:17-20`), the
  answer paired with the final state. A stateful runner must respect the monad's unit and
  multiplication (KRU §4); in the kernel these are L-RUN's run-return and run-bind (06 §5), the
  comodel's counterparts of L-HRET and L-HUNIQ. These are the runner laws, not the axioms of a
  monad-comonad interaction law, which also constrain the comonad's counit and comultiplication
  (KRU §3, diagrams (1)); those comonad-side conditions are not stated here (OQ-19). L-INTER is a different law (answering/control
  commutation).
- **Proof route.** By induction on the least fixed point of `e`'s `ewp`: a stop at `n` is replaced
  by the co-operation's run, given by `IsComodel`, then the continuation by the induction
  hypothesis; a stop at `Σ'` passes outward, as in `ewp_handle`'s forwarding case
  (`Core/EffRules.lean:661-674`). The lend's frame is T-FRAME at `⟦Σ'⟧`.
- **Today.** Not built. `effect_safety` proves the translated program safe by BoLo's own
  adequacy (`Safety.lean:55-57`), not against a table.
- **Depends on.** D-COMODEL, T-FRAME, D-TABLEOK (the residual row lends across the cell's
  borrow).
- **Open.** OQ-1 (whether this makes the comodel a derived form), OQ-19, OQ-20.
- **Obligation.** **Unknown** at a residual row that is not abortive (it needs T-FRAME at a
  resuming `TableOK` table). **Mechanical** at an abortive or empty residual row (the `*U` frames).

---

## 11. The binary relation (conditional)

### D-BIN: `≈` over pairs of worlds

- **Form (conditional on OQ-4).** `W₁ ≈_g W₂` relates two worlds along a partial bijection `g`
  on locations, with `𝒱≈⟦A⟧_{W₁,W₂} δ v₁ v₂` and `𝒞≈⟦C⟧` by the same clauses as D-REL, the `F`
  and `F_Σ` clauses reading two runs whose final heaps are related along an extension of `g`. The
  renaming relation of `experiments/TwoRun` (`HeapRel`, `run_sim`,
  `experiments/TwoRun/TwoRun/Sim.lean:253`) is its candidate core; `freshRun_det`
  (`experiments/TwoRun/TwoRun/Fresh.lean:255`) gives determinism up to a permutation of
  locations.
- **Uses.** D-W, D-REL. **Today.** None on Core (audit T16). Status: **new, conditional**.
- **Slices.** 06 (binary halves), 07 (T-2RUN, T-BINFP, T-SOUND).
- **Depends on.** D-REL. **Open.** OQ-4, OQ-5.
- **Obligation.** Not started; OQ-4's option (b) first checks which laws follow from `run_sim` and
  a unary fact without `≈`.

---

## 12. The probes of OQ-9 and OQ-44, written out

The first unknown (OQ-9, critic 4) is whether **open 6.64 frames** handed to a continuation are
closed on every path. D-STOP's proposed clause concerns 6.64 frames, the `TW.immFrame` records in
`ps`; 6.65 and 6.66 leave `ps` unchanged (`TW.mutFold`, `TW.mutUnfold`, `Core/World.lean:135-144`).
So the first probe is a 6.64 lend, where `ps' ↔ frames τ' ++ ps` bites. The 6.65 configuration is
OQ-44's probe and comes second. Each is written so that it can be stated in an experiment without
further design; the names below that are not existing declarations are the experiment's, listed
after each statement.

### 12.1 First probe (OQ-9): a 6.64 lend open at an affine stop, cancelled

**The configuration.** `withbor1U` (`withbor1UTy`, `Core/EffBorrow.lean:185-187`; term
`withborUE d`, `:200-202`) lends `r = ℓ : Ref A` as `Imm 'x A` (a 6.64 frame) to a callback that
performs an **affine** operation of name `n` while the lend is open. A handler of `n` around the
whole receives the stop, and its clause cancels `κ`.

```
E         ≜  [(aff, B, 1)]                                 -- one operation op_0 : B ↠^aff 1
body d r v ≜ withborUE d r (λ_. λm. perform (n, (0, v)) ; return ())
h_ret     ≜ λu. return ()
c         ≜ λp. let (v', k) = p in (cancel k ; return ())  -- the clause cancels κ
e_probe n d r v ≜ hnd (n, (h_ret, c)) (body d r v)
```

The callback is typed at `∀'x ⊏ ⊓Δ. Imm 'x A ⊸ F_{n:E}(['x] 1)`. The stopped context `K` contains
the `ubind` frame of `withborUE` (`thenE`, `Core/EffRules.lean:923`), so `HasHnd n K = false` but
`K` holds a finaliser frame. Today the term is not typed, because `withbor1U` requires `Row.Unwind`
(abortive only, `Core/EffBorrow.lean:133-135`).

**The one-table stop.** At `K[perform (n, (0, v))]`, D-STOP's stop clause with `τ = []` and
`τ' = [e]`, `e = ⟨ℓ, x, A, imm w, R, α⟩` the 6.64 entry of the lend, `α` its fresh lifetime, `w`
the value it fixed:

```
ps' ↔ frames [e] ++ ps    ∧    frames [e] ∩ ps = ∅    ∧    ls' ⊇ ls    ∧
every record of ls' not in ls descends from frames [e]
```

and the table `opTable (OpTab.ext n 0 en OpTab.empty)` receives `(ls', σ) [e] t Φ`.

**The statement.**

```lean
/-- OQ-9, first probe: a 6.64 frame open at an affine stop is closed by the cancel run. -/
def OpenFrameCancel : Prop :=
  ∀ (n : UInt32) (en : OpEntW) (A B : VTy) (δ : LSub) (d : Expr) (r v : Val)
    (ls : List SRec) (ρ : WRes),
    n ≠ 0 →
    rowTabW (Row.ofEff n [(.aff, B, .unit)] 0) δ n 0 = some en →   -- en is ⟦n:E⟧ n 0
    en.abort = false → en.q = .aff →
    IsDtor d A →                                                    -- d frees r and its payload
    ((ex fun ℓ => ⌜r = .loc ℓ⌝ ⋆ ex fun w => ptoOwn ℓ w ⋆ vW A (ls, []) δ w)
       ⋆ en.PA ls [] v) ρ →                                         -- source, and v ∈ en.P_A at W
    ewpW [] ls [] (e_probe n d r v) (opTableW OpTab.empty)
      (fun _ _ u => ⌜u = Val.unit⌝) ρ
```

The source and the payload are separate resources; `v ∈ en.P_A` and the payload `w ∈ 𝒱⟦A⟧` are
read at `W = (ρ, ls, [])`, the world outside the lend at which they are supplied, by D-REL at `W`
(`vW`), not by the kernel's `vC`: D-REL falls back to no `σ = []` relation. At `σ = []` the two
coincide only by T-NIL (OQ-58), so a probe stated with `vC` would test the kernel's relation, not
D-REL's. The handler's inner table is
`opTableW (OpTab.ext n 0 en OpTab.empty)`, which `ewp_handle` at `W` reads off `e_probe`'s body row
`Row.ofEff n [(.aff, B, .unit)] 0`; the outer table is the empty row's. `NoOwn` of the leftover is
part of `wpG_W` (D-WPG), so the post needs only the value. Experiment names: `vW` (D-REL's `𝒱` at
`W`), `OpEntW` (D-OPTAB's
entry, `P_A, P_B : List SRec → List OEnt → Val → WProp`), `rowTabW` (K-INT at `W`), `ewpW` (D-EWP at
the relativised stop, its first argument `τ`), `opTableW` (D-OPTAB), `IsDtor d A` (`d` is the
source's finaliser, `dtorE`, `Core/EffBorrow.lean:14-17`), `e_probe` (the function above). The
claim is the universal form; a refutation is a concrete instance with every hypothesis discharged.

**What it must show.** At the stop the 6.64 frame is open (`τ' = [e]` under OQ-9 (a), or ended and
owed as a re-lend under (b)). The clause runs `cancel κ`, which by `ewp_kappa_cancel`
(`Core/EffRules.lean:529`) is `ccatch (hnd H K[raise (0,(0,(N, none)))])`, run at `ewp(τ' = [e])`
(D-OWED). The raise reaches the `ubind` frame, where the lend ends (the frame's `TW.immEnd`,
`Core/World.lean:151`) and `[finalise-cancel]` runs `d r`, freeing the source, LIFO; the run ends at `ccatch` with `τ' = []`, so D-STOP's stop clause closes `e`, with a `NoOwn` leftover
(`ewp_ccatch`, `:580`). It reports an obstruction only as `¬ OpenFrameCancel` with every hypothesis
discharged.

**The two companion configurations**, stated the same way once the first is settled:

1. **Abortive drop.** The operation is abortive (`raise`). The `ubind` frame catches it first
   (`Catches` at `ubind`, `Paper/S3_Dynamics/Definitions.lean:404`) and runs `d`; the stop reaches
   the table with `τ' = []`. `def OpenFrameRaise : Prop`. This is today's `*U` path
   (`ewp_unwind`, `Core/EffBorrow.lean:58`) and should be mechanical.
2. **Resume between lenders.** A lender `L₁` (outer), the handler `H` of `n`, a lender `L₂`
   (inner, a 6.64 lend), a perform of `n` inside `L₂`. `H`'s clause opens a lend `L₃` of its own
   (fresh lifetime `α₃`, below `α₂` by D-ORD (3)) and resumes `κ` inside it. `κ` closes `L₂` when
   it returns, while `L₃` is still open. `def ResumeBetweenLenders : Prop` states that the run
   closes `L₂` then `L₃` with `NoOwn` and every 6.64 exit applied in an order the printed frame
   admits. This configuration is the one OQ-3 and R-MID name; it is where LIFO is at stake.

**Reading, not a claim.** Under OQ-9 (b) the first probe looks mechanical: the lend ended at the
stop (`ewpTS_I_frameR`'s stop case, `ImmLend.lean:175`), the owner is in the continuation, and the
cancel run's `[finalise-cancel]` meets an owned source. Under (a) the cancel run must apply 6.64's
exit inside the cancel run, at a point the printed proof does not split at. I have not derived
either and have not verified that any obstruction is real.

### 12.2 OQ-44's probe: a 6.65 lend open at an affine stop, cancelled

The same configuration with `withbor2U` (`withbor2UTy`, `Core/EffBorrow.lean:189`), the lend a
6.65 `Mut 'x A`. A 6.65 lend adds no `ps` entry, so D-STOP's clause does not see it; what a stop
must record of it is OQ-44.

```lean
/-- OQ-44: a 6.65 lend open at an affine stop is closed by the cancel run, and the stop
records it in τ' as a mut entry. -/
def OpenMutFrameCancel : Prop :=
  ∀ (n : UInt32) (en : OpEntW) (A B : VTy) (δ : LSub) (d : Expr) (r v : Val)
    (ls : List SRec) (ρ : WRes),
    n ≠ 0 →
    rowTabW (Row.ofEff n [(.aff, B, .unit)] 0) δ n 0 = some en →
    en.abort = false → en.q = .aff → IsDtor d A →
    ((ex fun ℓ => ⌜r = .loc ℓ⌝ ⋆ ex fun w => ptoOwn ℓ w ⋆ vW A (ls, []) δ w)
       ⋆ en.PA ls [] v) ρ →
    ewpW [] ls [] (e_probeM n d r v) (opTableW OpTab.empty) (fun _ _ u => ⌜u = Val.unit⌝) ρ

/-- Every 6.65 lend a resuming stop leaves open is in the τ' the table receives. -/
def MutLendRecorded : Prop :=
  ∀ e τ' ps ps' ls ls' t, MutLendOpenAt e t → StopW [] ps ps' ls ls' t τ' → e ∈ τ'
```

`e_probeM` is `e_probe` with `withborUE d r` at `withbor2U`'s callback type; `MutLendOpenAt`,
`StopW` are the experiment's names (D-STOP at `W` with OQ-44's chosen record of 6.65 lends). Under
OQ-44 (b) a `TW` constructor records the 6.65 frame and `MutLendRecorded` becomes a statement about
`ps' ∖ ps`; under (a) and (c) it is a statement about `τ'` alone.

---

## 13. Open questions raised here

Boxed in [99](99-open-questions.md):

- **OQ-44**, what the open-lend component `σ` holds: 6.65 lends leave `ps` unchanged, the
  records of open 6.64 frames are already in `ls`, and under OQ-9 (b) `σ` is a stack of lends to
  re-lend. D-W is written at its default (a).
- **OQ-45**, whether the arising guard `guard_W` stays in the `U`, `⊸` and `∀` clauses once
  `TabAt_W` is a `TW` invariant.
- **OQ-46**, the world `σ₀` at which a stored `Imm`/`Mut` payload is read.
- **OQ-57**, the closing-obligation list `τ` as an index beside `W` (D-WPG, D-EWP, D-TABLE),
  recorded as a defect against 00 §0.2 item 1, with `def ClosingInW : Prop` (§4).
- **OQ-58**, whether Core is the `σ = []` instance at `U`, `share` and `KapRel`, with
  `def NilAgreesU : Prop` (T-NIL), a first probe beside OQ-9's.
- **OQ-63**, the partial-correctness `ewpP_W` (D-EWPP) as a second wp family beside `ewp_W`,
  recorded as a defect, with `def EwpModeUniform : Prop`.

Carried from 02 and 03: OQ-61 (the interpretation of a self-referential signature as a least
table, K-SELFROW), OQ-45 (now recording that a free-standing `HeldUnder` premise would relocate the
guard, T-ARISE.0).

The refinement of OQ-8's criterion (i) found here (both candidates quantify over `⊑` at `U`, so
neither has a definitional `σ = []` lemma at a row that introduces a `U` value) is boxed as OQ-58
and cited from OQ-8's box. OQ-56 (operation types that mention the lend) is carried for
D-TABLEOK's conjuncts (3)-(4).

---

## 14. Report lists (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed** at the tables this section needs:

- `[TR]` 6.150 (reborrow, with its `И` freshness) at a resuming table: not lifted (audit m6);
  T-FRAME's 6.150 half is unknown until it is.
- `[TR]` 6.50 at a stack: used at one entry (`tabAt_updV`, `Table.lean:80`), not at two
  lifetimes of a stack (T-ARISE).
- `[TR]` 6.64 at an `Imm` table beyond `ewpTS_I_frameR`; 6.65's `↭` steps line by line (audit,
  "Unspent and untranscribed items").
- `[TR]` 6.172-6.174 (the `withbor` rows) at `W`: transcribed in `Paper/` at the kernel's
  relation, cited as the model for `callback_ext` and `CallbackExt`, not lifted.
- 6.65's printed proof split into an entry half and an exit half usable at different points: not
  printed, and needed under OQ-9 (a) only (§12, reading).

**Printed hypotheses the lifts must spend** (T-FRAME): 6.65's `P̂ ⊨ [β]P̂`; 6.150's `RebEscrow P̂`
and the `И` freshness of `β`; the `И` freshness of `α` at 6.64 and 6.65 (D-ORD (4)). None is spent
yet, since no lift at a resuming table at `W` is built. D-TABLEOK's conjuncts (3)-(4) carry
`Row.Unwind`'s closed-in-lifetimes conditions (`Core/EffBorrow.lean:133-135`) as R-CLOSEDOP;
conjunct (2) is `ewpTS_I_frameR`'s `hTL` (`ImmLend.lean:176`), named as a slice of D-ORD.

**Uniqueness and functionality results not used.** `head_det_eff` (`Core/Steps.lean:596`) and
`freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`) are not used by the unary model; the
second is D-BIN's candidate core. `ResU.CompS.functional` is used by GhostEnd's stack lemmas and
would be by T-FRAME's depth induction; `dropC_disj` (`RelendableS` closed under `⋆`) is not built
(#282 report).

**Hypotheses added.** One, to T-FRAME's lifted forms: the postcondition `Q̂` stable along `⊑`,
the `W`-form of `wpTS_I_frameX`'s added `hQ` (`Core/EffWp.lean:77`), scoped to the postconditions
D-REL produces (T-MONO). D-STOP is a change to our own kernel definition, written as a SPEC entry
(§4). D-ORD's conditions (4) and (5) are 6.64/6.65's `И` and `Extend.lean:94`'s freshness side
condition.
