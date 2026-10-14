# BoxedKappa: a handler clause that receives `κ : [@d] K`

Build with `lake build BoxedKappa`. There is no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`, and every declaration's axioms are within
`[propext, Classical.choice, Quot.sound]` (`lake env lean experiments/BoxedKappa/scripts/Axioms.lean`).
The library does not import this directory. It imports `Core.Fundamental` and three `Support.Model`
files, and adds no definition to Core.

## The question

`VOutlivesR` has no case for `U C`, and `[handle]` gives a clause its continuation as a bare
`kTy Σ R q B F`, so a continuation never has a `[@d]` type. BOXED-κ is the variant of `[handle]`
whose clause receives `κ : [@d] K`. The relation reads `[@d] K` as `vC K` and the resource in
`Res_{δ(d)}` (`box α P ρ = P ρ ∧ ρ.InStratum α`). So the rule needs the continuation's share at
every stop of the handled computation to lie in `Res_{δ(d)}`.

## Results

| Deliverable | Lean name | File | Status |
|---|---|---|---|
| 1. Stop lemma, semantic | `ewp_stratify` | `BoxedKappa/Stop.lean` | proved |
| 1. Stop lemma at `SemC` | `stop_sem` | `BoxedKappa/Stop.lean` | proved |
| 1. Stop lemma at `CDerives` | `stop_lemma` | `BoxedKappa/Stop.lean` | proved |
| 2. `[handle]` at the stratified table | `ewp_handleS` | `BoxedKappa/Handle.lean` | proved |
| 2. BOXED-κ at clause values | `ewp_handle_valsB` | `BoxedKappa/Handle.lean` | proved |
| 2. BOXED-κ, variable form | `handle_compatCB` | `BoxedKappa/Handle.lean` | proved |
| 2. BOXED-κ, value form (`effHandleV`'s) | `handleV_compatCB` | `BoxedKappa/Handle.lean` | proved |
| 3. Necessity of the answer-type condition | — | — | not determined |

### 1. The stop lemma

`opTableS α T` is `opTable T` with one more conjunct at each non-abortive stop: the continuation's
share is in `Res_α`. It is below `opTable T` (`opTableS_le`, `ewpS_ewp`). `SemCS Δ Γ M Σ A d` is
`SemC` at `F_Σ A` with `opTableS δ(d)` in place of `opTable`: at every substitution, every run, and
every stop of every resumption, the share is in `Res_{δ(d)}`.

    theorem stop_lemma (hder : CDerives Δ Γ M (.comp (CTy.effOf S A)))
        (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d

`Row.AnsOutlives Δ d S` is `∀ o ∈ S, o.abort = false → VOutlives Δ d o.B`.

**No new invariant is needed. An existing one carries the stratum.** `wpG` has the conjunct
`ResU.UpdV ρ π`: `↭` from the run's start resource `ρ` to `π = ρ' ● ρp`, where `ρ'` is the
resource at the stop. `↭` keeps `Res_α` (`ResU.updV_inStratum`, `[TR]` 6.50 read at `Res_α`).
So a run that starts in `Res_α` ends in `Res_α` (`wpG_inStratum`), and the share is a `●`-factor of
the stop's resource. At a resumption, the next run starts at the share `●` the answer, so it is in
`Res_α` when the answer is (`ewp_stratify`, by induction on `ewpTS`'s fixed point). At the typed
level, the context's resource is in `Res_{δ(d)}` by `gSepC_outlives` (6.60 folded over `Γ`, as
`[]I` uses it). An answer whose type outlives `@d` is in `Res_{δ(d)}` by `vC_outlives`.

Each part of the hypothesis is used:

- `Δ ⊨ Γ_M ⊐ @d` puts the start resource in `Res_{δ(d)}`.
- `Δ ⊨ @d` (part of `CtxOutlives`) gives `δ(d)`.
- The answer-type condition gives `OpTab.AnsIn`.
- `hder` gives `SemC` (`fundamentalC`).

**T1 is not a premise.** Core enforces it already: a lend's callback is typed at the pure row
(`axWithbor*Ty`) or at a row of abortive operations (`Row.Unwind`). The proof does not use T1
either. `wpG`'s `↭` already rules out a lend that is open at a stop: such a lend's borrow cell
would be in the stop's flattening and not in the start's. That last point is not machine-checked
as a separate statement. It explains why the proof needs no T1 premise. It also means lifting T1
would have to change `wpG`, not only the typing.

**The premise is weaker than the one the brief proposed.** Only the answer types of non-abortive
operations are required. An abortive operation's answer type is `0`, and it never resumes.

**Scope.** `opTableS` constrains the stops of the handled computation's own table. A cancel run of
a captured continuation (`cancelOK`) is read at the entry's cancel obligation, not at `Φ`, and is
left unstratified. BOXED-κ needs only the share at the stop.

### 2. BOXED-κ

`clausesTyB Σ R d E fs` is `clausesTy` with each capturing clause at
`!U(A ⊗ [@d] (kTy Σ R q B F) ⊸ F_Σ R)`. Abortive clauses are unchanged.

    theorem handleV_compatCB
        (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
        (hc : SemV Δ Γ₁ H (.tensor (retTy S A R) (clausesTyB S R d E fs)))
        (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
        (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))
        (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S)) :
        SemC Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R)

`handle_compatCB` is the same at `hndTerm` (`h_ret` and the clauses as variables).

**Derivation.** It comes from `stop_sem` and a re-run of `ewp_handle`'s proof at the stratified
table (`ewp_handleS`). `ewp_handle` cannot be used as a black box. Its clause hypothesis receives
`KapRel` only, so the share's stratum is lost by the time the clause sees it. `ewp_handleS` is
`ewp_handle`'s proof with the extra conjunct passed to the clause. At a linear or affine operation,
`κ` also holds its cell. That cell is an `own` cell, which is in every stratum
(`ResU.inStratum_single_own`). From `KapRel`, `vC_kTy_of_kapRel` gives `vC K κ`, and the stratum
conjunct makes it `vC ([@d] K) κ` (`ewp_handle_valsB`).

### The final premise of BOXED-κ

These are in addition to `[handle]`'s premises, with the clauses at `clausesTyB`. The handled
computation `e : F_{E_n ⊕ Σ} A` under `Γ₂` must satisfy:

1. `Δ ⊨ Γ₂ ⊐ @d`, which includes `Δ ⊨ @d`;
2. every non-abortive operation of `E_n ⊕ Σ` has an answer type that outlives `@d`. This covers
   both the handled operations and the forwarded ones, because a forwarded operation's answer comes
   back into `e`'s continuation, which a later handled operation may capture.

No T1 premise, and nothing else.

### 3. Necessity of the answer-type condition: not determined

Neither (a) nor (b) is machine-checked.

**What is checked.** The condition enters only through `OpTab.AnsIn` in `ewp_stratify`: the
answers' **resources** must lie in `Res_{δ(d)}`. The answer **types** are just one way to obtain
that (`vC_outlives`).

**Why (b) is not easy.** A typed handler cannot make an out-of-stratum answer from nothing:

- its clauses have persistent contexts (`clausesTy` is a tuple of `!`, holding `∅`);
- `↭` never mints a borrow cell;
- borrows are created only by lends whose callbacks resume nothing (T1);
- subsumption to a shorter `Imm`/`Mut` keeps the cell at its original lifetime (`ptoImmS_antitone`,
  `ptoMutS_antitone`).

So the answer-type condition could be redundant at the level of resources. One route still gets
through, which is why (b) is not claimed.

**Candidate typed witness for (a)** (believed; nothing about it is checked in Lean). Inside a lend
`withbor r (Λ'x. λ(b : Imm 'x I32). …)`, with `@d` from the enclosing `Δ`, so `'x ⊏ @d`:

- An outer state-passing handler of `getB : 1 ↠^lin Imm 'x I32`, answer type
  `U(Imm 'x I32 ⊸ F R')`, is applied to the initial state `b`. Its clause answers `getB` with a
  copy of the state.
- Inside it, an inner handler of `get : 1 ↠^lin Imm 'x I32` and `tick : 1 ↠^lin 1`, at outer row
  `[getB]`. The `get` clause performs `getB` and resumes with the answer.
- `M = let y = perform get () in perform tick (); return y`, with `Γ_M = ∅` (it outlives `@d`).
  `get`'s answer type `Imm 'x I32` does not outlive `@d`.
- At `M`'s `tick` stop, the continuation holds `y`, an `imm` cell at `δ('x) ⊏ δ(d)`.

The step from a model-level argument to a Lean theorem is not built. The argument for why any
share justifying the resumption must hold that cell goes like this:

- `↭` fixes the flattening's `imm` cells exactly.
- A `{δ('x)}` cell at `ℓ` in a stratified share is impossible.
- If the share lacks it, the resumed run's end cannot hold any `imm` cell at `ℓ`.
- But `M`'s answer `y : Imm 'x I32` needs one.

Turning this into a Lean contradiction means instantiating `wpG`'s universally quantified world
with a valid typed world (`TW`, `Tagged`, records coherent with an `imm` lend at `ℓ`). The other
route is to build the program's semantics around the hypothesised `SemCS M` and contradict
adequacy.

**Believed, not checked.** In every candidate witness, `κ`'s type mentions `'x`, through the outer
row or the state type. So the boxed `κ` cannot be moved out of `'x`'s lend by typing, and the
failure is in the model (`[@d] K` would be an empty type at that `κ`), not in safety. A premise of
the form "`Σ` and `R` outlive `@d`" might replace the answer-type condition. That is a hypothesis
only.

## What remains

- Deliverable 3, either way. The model-level argument above is the plan for (a).
- BOXED-κ is not a `CDerives` rule. Adding it would add one case to `fundamentalC`, which is
  `handleV_compatCB`, and one to each inversion in `Inversions.lean`.
