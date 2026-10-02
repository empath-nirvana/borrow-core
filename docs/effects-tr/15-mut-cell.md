# §15 The `Mut` cell with a rebased continuation (candidate result)

[← §12 Sources and novelty](12-sources.md) · [index](README.md) · next: [§16 Does the chain bottom out?](16-regress.md)

Issue #251. This section attempts the central lemma of #245's brief head on: a `Mut` cell whose
witness holds a suspended continuation, closed under resume and drop. It works in BoLo's real
setting, the **kernel lift**: the full carrier `Res` with `imm` and `mut` cells and lifetimes,
borrow-core's typed world (record lists `ls`, `Ext`, `Tagged`), and SPEC §19's `ewpTS` with
protocol tables. That is §9.3's setting, not the own-fragment of §§4–5 (L4.1 is not used here).

It is a **candidate result**. Nothing here is mechanised and the kernel is unchanged. Each step
cites the [TR] number or the `Core/` or `Paper/` declaration it uses. A step that is not derived
is marked open, with its exact statement.

## 14.0 The result in brief

1. **The lemma holds** (T14.5) for every continuation in the kernel's relation that is
   *rebased*: its resource is in `Res_c`, the stratum strictly above `'c`. Resume is `d_callMut`.
   Drop is `close`, which runs the continuation's cancel, and that cancel disposes of every owned
   cell exactly once. The one new proof is a coinduction (T14.4). It shows that the kernel's
   continuation value `kappa n H K`, under a handler whose `yield` clause returns it, is an affine
   closure `Aff^c` (§22). Every other step is an existing lemma.
2. **Rebasing costs nothing.** No relabelling is needed. [TR]'s `↭` already keeps every lifetime a
   run opens out of what the run hands back, at a stop as at a return (L14.1). [TR] 6.147
   (`wpTS_box`), through 6.50 (`updV_outlives`), puts each new suspension back in `Res_c`
   (L14.2). Internal lifetimes are abstracted by the continuation's obligation, which is
   universally quantified over the resumer's record list. They never appear in the witness.
3. **Producing such continuations.** The kernel's typing produces rebased continuations from
   every body that does not suspend inside a borrow it opened (T14.6). That is SPEC §19's present
   rule (T1, #172). A body whose **lend spans a `yield`** (an internal lifetime still open at a
   suspension) is **open** (O14.1). O14.1 is §9.3's O3 at the kernel's tables. Its exact step: the
   continuation's obligation has to be re-established at the resumer's record list. Re-folding the
   lend at its old lifetime needs `RefoldKripke`, which is refuted (`refoldKripke_false`), at a
   list that arises (`refold_fails_at_consumer_frame`). Re-opening it at a fresh lifetime needs
   the callback's remainder at that lifetime. 6.65's premise does not give it, and the existing
   relabelling (`relabel_reb`, `relabel_obs`) moves only `imm` views at data types (O14.2).
4. **The tripwire (T15) does not reappear** (L14.9). The cell's invariant is defined by recursion
   on types, with `ν` read through a monotone operator. Reaching the cell from inside its own
   witness is excluded by the *strict* stratum of `Mut_α` ([TR] p. 4). A non-strict stratum is
   exactly where the negative occurrence would come back (`no_nonstrict_stratum`, the same Cantor
   argument as phase B's `no_negative_domain`).
5. **Corollaries** (§15.7). T1 for the *resumer* (resuming while holding a lend) is bookkeeping:
   it is the `withswap` discipline. Generator objects, capabilities across `yield`, task queues
   and handler state follow for bodies with no spanning lend. T1 for the *continuation* (a lend
   spanning a `yield`) is O14.1 itself. Nothing here discharges it: one route is refuted by a
   machine-checked lemma, and the other is not derived.

---

## 14.1 Setting

**Definition D14.1 (strata).** [TR] p. 4, at borrow-core's carrier (`WRes`, D4.1). `Life = ℕᵒᵈ`:
a smaller number lives longer, `⊤ = 0`.

    Mut_α ≜ {(β ⊐ α, v, ρ ∈ Res_β, P̂ : Val → SProp_β) | P̂(v)(ρ)}      Res_α ≜ Loc ⇀ Cell_α

- `ρ ∈ Res_α` (`ResU.InStratum`, `[α]` of [TR] p. 6) says that every borrow cell of `ρ` has lifetime
  strictly above `α`.
- `[@c] T` is membership in `Res_{δ(c)}`, and the box modality is strict (SPEC §23, *The box
  rule*).
- `ptoMutS ℓ α ls P` (`Core/Relation.lean`) is `ℓ ↦ Mut α P̂` with three parts: a cell
  `mut(b, u, σ, Q)` with `α ⊑ b` and `σ ∈ Res_b`; its predicate `Q` read at `ls₀`, the members of
  `ls` strictly longer-lived than `b`; and `P` lying in `Res_b` at every list (`hunif`).

**Definition D14.2 (the cell and its invariant).** The cell has type `Mut @a ([@c] U(Aff^c A B))`
(SPEC §22, `affBox`). Its resource is

    ptoMutS ℓ_c δ(a) ls (λ ls₀. vC true (affBox c A B) ls₀ δ)

so its witness `ρ̄` is in `Res_b ∩ Res_{δ(c)}`, and the content `v` satisfies `𝒱⟦[@c] U(Aff^c A B)⟧`.
By `cC_aff_iff` (`Core/Aff.lean`) this is the **invariant at `'c`**:

- `@ρ̄ ⊐ δ(c)`;
- at every list `ls'` with `Ext ls ls' ρ̄`:
  - for every `a ∈ 𝒱⟦A⟧`, the call `v (inj₁ ()) a` runs to a `B` and a rest that satisfies the
    invariant again;
  - `v (inj₂ ())` runs to `()`.

`A` is closed (`A.Cl 0`), as §22's positivity asks.

**Definition D14.3 (the generator handler and its continuation).** The body `M` performs one
control operation `yield : B_y ↠ A` on the name `n`. Its entry `en_y` (SPEC §19 `OpEnt`) has the
following fields:

| field | value | meaning |
|---|---|---|
| `q` | `aff` | resumed at most once, or cancelled |
| `abort` | `false` | a resuming operation |
| `PA` | `vC B_y` | the argument relation |
| `PB` | `vC A` | the answer relation |

The handler is

    H_gen ≜ hndVal n hr hs
      hr  ≜ λ_. return (inj₂ (), done)             (the body returned)
      hs  ≜ [ λ(b, κ). return (inj₁ b, κ) ]        (the yield clause returns the continuation)

and `gen(M) ≜ hnd H_gen M`.

- `B ≜ B_y ⊕ 1`.
- `done` is the closed affine closure that answers `(inj₂ (), done)` at every call and `()` at
  `close`. It is derivable by `d_mkBox` at the state `1`, so `fundamentalC` puts it in `vC (affBox c A B)`.
- The handler is deep. At a stop the machine reifies `κ = kappa n H_gen K` (`Core/EffRules.lean`).
  It has two branches, `κ (inj₁ ()) w` (`ewp_kappa_resume`: run `hnd H_gen K[w]`) and
  `κ (inj₂ ())` (`ewp_kappa_cancel`: run the cancel under `ccatch`). These are exactly
  `Aff^c`'s eliminations `call` and `close`, in the same encoding (`cC_aff_iff`'s
  `.app (.app e (inj₁ ())) a` and `.app e (inj₂ ())`). This is the representation #251 asks for:
  resume is `call`, cancel is `close`.

**Definition D14.4 (the generator's postcondition).** `Q_gen` is the greatest fixed point of

    F(Q)(ls, v)  ≜  (∃ b κ'. v = (inj₁ b, κ')  ∧  vC B_y ls δ b ⋆ KapRel ∅ Q en_y ls κ')
                 ∨  (v = (inj₂ (), done)  ∧  vC (affBox c A B) ls δ done)

`KapRel Tout Qout en ls κ` is the relation of `κ`'s type at an operation's entry
(`Core/EffRules.lean`):

    (q = unr → ρ = ∅)  ∧  ∀ ls', Ext ls ls' ρ →
        (∀ w. (PB ls' w ─⋆ ewpTS ls' (κ (inj₁ ()) w) (opTable Tout) Qout) ρ)
      ∧ (q ≠ lin → ewpTS ls' (κ (inj₂ ())) (opTable Tout) (λ_ v. ⌜v = ()⌝) ρ)

`F` is monotone, because `Q` occurs only as an `ewpTS` postcondition (`ewp_mono`). So the
greatest fixed point exists, written in `Prop` as for `nuRel`, and needs no step index. Any fixed
point would do. The table `∅` is `OpTab.empty`: the generator's calls perform nothing outside it.
At the empty table `ewpTS` is `wpTS` (`cC_effOf` at the empty row, through `ewp_bot` and
`opTable_empty`).

**Definition D14.5 (rebased continuation).** A continuation `κ` with resource `ρ̄`, at the list
`ls`, is **rebased at `c`** when two things hold:

1. **stratum:** `ρ̄ ∈ Res_{δ(c)}`. Every borrow cell `ρ̄` holds is strictly longer-lived than
   `'c`: the witness's stratum is its external footprint only.
2. **obligation:** `KapRel ∅ Q_gen en_y ls κ ρ̄`.

*Internal lifetimes are abstracted* in this sense:

- `ρ̄` holds no cell at a lifetime opened inside the handler's extent (L14.1).
- Any lend the continuation re-opens when resumed is opened inside the obligation, which holds at
  *every* `ls'` with `Ext ls ls' ρ̄`. So the lend's lifetime is chosen at the resumer's list,
  fresh for it.

The definition fixes no internal lifetime, and the world records none (the brief's "don't track
suspended lifetimes in the world", #245).

**Definition D14.6 (resume and drop).**

- **Resume** is `callMutE i j` (`d_callMut`, `Core/AffRules.lean`):
  1. `withswap` the witness out ([TR] 6.66 in the proof of `withswap_compatX`, `wpTS_M_antiFrameX`);
  2. call it at `a` (`κ (inj₁ ()) a`), which resumes `K` under `H_gen` up to the next `yield` or
     the end of the body;
  3. swap the rest in.
- **Drop** is `close`: `κ (inj₂ ())`, which is cancel. It is reached as the destructor of the cell's
  content (`hasDtor_aff`, `hasDtor_affBox`; SPEC §12 class 2) or by `d_closeBox`.

## 14.2 Rebasing is forced by `↭`

**Lemma L14.1 (a suspension holds no internal cell).** Take a `wpG` run from `ρ`, ended at a
return or a stop `t` with resource `ρ'` and leftover `ρ⁺`.

1. A lend opened during the run, and not ended by `t`, has no cell in `ρ'`. Such a lend is a
   `mut` or `imm` cell at its location `ℓ`, at the lend's own lifetime.
2. If `ρ ∈ Res_α` then `ρ' ∈ Res_α`.

*Proof.* `wpG`'s conjunct `ResU.UpdV ρ (ρ' ● ρ⁺)` is [TR] p. 5's `↭`. At each location its clauses
fix the flattened `mut` cell by `(ℓ, α, P̂)` and the flattened `imm` cell by `(ℓ, β, v, ρ)`.

1. Opening a lend at `ℓ` changes the flattened cell at `ℓ`. An `own` cell becomes `mut(α, …)` or
   `imm({α}, …)` (6.65, 6.64), and a `mut(x, …)` cell becomes `mut(α, …)` under a reborrow (6.66,
   then 6.65). So a run whose result held the lend's cell would break `↭`.
   - The `mut` and `imm` cases are `not_upd_of_new_mut` and `not_upd_of_new_imm`, and the general
     kind-level statement is `upd_borrow_top`. All three are machine-checked
     (`experiments/LoopBorrow`).
   - The lend's cell cannot hide in the leftover `ρ⁺` either: `↭` reads the flattening of
     `ρ' ● ρ⁺`.
2. This is [TR] 6.50 (`updV_outlives`) followed by `outlives_comp`. ∎

**Lemma L14.2 (re-rebasing).** If `ρ ∈ Res_{δ(c)}` and `wpTS ls e Q ρ`, then
`wpTS ls e (λ ls' v. [δ(c)] (Q ls' v)) ρ`. The same holds for `ewpTS` at `opTable ∅`.

*Proof.* [TR] 6.147 (`wp[]`) at the typed world, `wpTS_box` (`Core/Wp.lean`). Its proof is 6.50
(`updV_outlives`, `Paper/S6_2_NonStandardLemmas/Lemmas.lean`) on `wpG`'s `↭` conjunct, followed by
`outlives_comp` to keep the part `ρ'` of `ρ' ● ρ⁺`. At `∅`, `ewpTS = wpTS` (D14.4). ∎

So each time a resumed continuation suspends again, its new share is back in `Res_{δ(c)}`,
provided the run began there. This is the whole of "re-rebase at the next suspension". It needs no
new machinery.

## 14.3 The lemma

**Lemma L14.3 (the generator handler).** Let `ewpTS ls M (opTable T_y) (λ_ _. vC 1) ρ`, where
`T_y = OpTab.ext n 0 en_y OpTab.empty`. Then `ewpTS ls (gen M) (opTable ∅) Q_gen ρ`.

*Proof.* `ewp_handle` (`Core/EffRules.lean`) with `Tin = T_y` and `Tout = ∅`.

- `hret`: `hr ()` returns `(inj₂ (), done)`. `ewp_val`, the right disjunct of `F(Q_gen) =
  Q_gen`, and `done ∈ vC (affBox c A B)` (D14.3).
- `hop` at `en_y` (non-abortive): the hypothesis is `(vC B_y ls δ b ⋆ KapRel ∅ Q_gen en_y ls κ) ρ`.
  The clause returns `(inj₁ b, κ)`, which is the left disjunct of `F(Q_gen) = Q_gen` with the same
  resources. `ewp_val`. ∎

**Theorem T14.4 (a rebased continuation is a bounded affine closure).** Assume:

- (H1) `en_y.q = aff`;
- (H2) `ρ̄ ∈ Res_{δ(c)}`;
- (H3) `KapRel ∅ Q_gen en_y ls κ ρ̄`;
- (H4) `Δ ⊢ A ⊐ @c` (SPEC §23's `VOutlives`, strict at the `Imm`/`Mut` rules) and `A.Cl 0`.

Then `vC true (affBox c A B) ls δ κ ρ̄`.

*Proof.* The box clause of `vC` asks two things.

- **The stratum.** This is (H2).
- **The thunk.** `vC true (affT c A B) ls δ κ ρ̄`: at every `ls'` with `Ext ls ls' ρ̄`,
  `cC (affC c A B) ls' δ κ ρ̄`.

The thunk is by `aff_coind` (`Core/Aff.lean`) with the candidate

    R ≜ R_κ ∪ nuRel (affBody c A B) δ
    R_κ(ls, e, ρ) ≜ ∃ κ. e = κ ∧ ρ ∈ Res_{δ(c)} ∧ KapRel ∅ Q_gen en_y ls κ ρ

`R_κ` holds of `κ` at every such `ls'`, by (H2) and (H3) with `Ext.trans`, since `KapRel` is
Kripke. It remains to show `R ⊆ nuF (affBody c A B) δ R`.

- **`nuRel` part:** `nuRel_out`, then `nuF_mono` along `nuRel ⊆ R` (`Core/NuRel.lean`).
- **`R_κ` part:** the two clauses of `cC_aff_iff`'s unrolling, with `U X` read at `R`.
  1. **call.** Let `a` and `r_a` satisfy `vC A ls δ a r_a`, and compose `ρ ● r_a`.
     - (H3)'s resumption conjunct at `ls' = ls` (`Ext.refl`) gives
       `ewpTS ls (κ (inj₁ ()) a) (opTable ∅) Q_gen (ρ ● r_a)`, which is `wpTS` by D14.4.
     - `r_a ∈ Res_{δ(c)}` by (H4) and 6.60 (`vC_outlives`, `Core/RelationFacts.lean`).
       `ρ ∈ Res_{δ(c)}` by `R_κ`. So `ρ ● r_a ∈ Res_{δ(c)}` (`outlives_comp`).
     - L14.2 gives the postcondition `[δ(c)] Q_gen`.
     - Unfold `Q_gen = F(Q_gen)` at the result `(v, ρ'')`.
       - **Left disjunct**, `v = (inj₁ b, κ')` with `ρ'' = ρ_b ● ρ_κ'`:
         - `vC B_y ls'' δ b ρ_b` gives `vC (B_y ⊕ 1)`.
         - `ρ_κ' ∈ Res_{δ(c)}`, because it is a part of `ρ'' ∈ Res_{δ(c)}` (`outlives_comp`).
         - `KapRel ∅ Q_gen en_y ls'' κ' ρ_κ'`, and `KapRel` is Kripke.

         So `κ'` is in `thunkR R` (`Core/Relation.lean`) at `ls''`, through `R_κ`. The boxed rest
         `[@c] U X` holds: the stratum, then `thunkR R`.
       - **Right disjunct**, `(inj₂ (), done)`: `done ∈ vC (affBox c A B)`, which is `nuRel` behind
         the box. So it is in `R`.

     Together these give `vC (B ⊗ [@c] U X)` read at `R`.
  2. **close.** (H1) gives `q ≠ lin`, so (H3)'s cancel conjunct at `ls` gives
     `ewpTS ls (κ (inj₂ ())) (opTable ∅) (λ_ v. ⌜v = ()⌝) ρ`. That is `wpTS` to `vC 1`. ∎

**Theorem T14.5 (the `Mut`-cell lemma).** Let `ℓ_c` hold a cell as in D14.2 whose content is a
rebased continuation (D14.5) under (H1) and (H4). Then:

1. **Resume.** For `m : Mut @a ([@c] U(Aff^c A B))` at `ℓ_c` and `a ∈ 𝒱⟦A⟧`, `callMutE` runs to
   `(m, b)` with `b ∈ 𝒱⟦B⟧`, and afterwards the cell satisfies D14.2's invariant again. If the
   call reached a `yield`, the new content is a rebased continuation.
   - The resumed continuation re-opens, inside its obligation, whatever it re-opens, at the
     resumer's list (D14.5).
   - The new suspension is re-rebased by L14.2.
   - The cell is swapped back by `withswap`.
2. **Drop.** Dropping the content runs `close`. The run ends at `()` with nothing owned left. Each
   owned cell of the witness `ρ̄` is disposed of by that run exactly once, in one of two ways:
   - it is freed;
   - it is stored into the payload of an external borrow that `ρ̄` held. Its lender then owns it,
     and the borrow is forgotten by [TR] 6.148.

*Proof.*

1. By T14.4 the content is in `vC (affBox c A B)`. `d_callMut` is a `CDerives` derivation, so
   `fundamentalC` gives its semantic typing at every closing substitution in `𝒢⟦Γ⟧`, including one
   that maps the borrow to `ℓ_c` and the argument to `a`. Its derivation is `withswap`, `[]E` and
   `d_callAff`, so its soundness is `withswap_compatX` (6.66 inside), `cC_aff_iff`'s call clause
   and the `[]I` of the rest. The rest is the call clause's `[@c] U X` at T14.4's candidate `R`.
   - At a `yield` it is in `R_κ`: a rebased continuation.
   - At the body's end it is `done`.
2. **Drop.** `close` is T14.4's close clause: a `wpTS` run with postcondition `⌜v = ()⌝`. So its
   final resource is `∅`, and its leftover `ρ⁺` has `ρ⁺|own = ∅` (`wpG`).
   - The run starts from `ρ̄` and ends owning nothing. `↭` constrains only borrow cells, so each
     `ℓ ↦ own(_)` of `ρ̄` is either freed or moved into the witness of a `mut` cell that `↭` keeps.
     That cell is in `⦇ρ̄⦈` at its start, so it is a borrow `ρ̄` held of an external owner.
   - Each own cell goes once. Own cells of composable resources are disjoint (6.41), and the run
     never gets stuck (`wpG`), so no location is freed twice. None is left in `ρ⁺` as `own`.
   - The cancel run itself is `ewp_kappa_cancel` then `ewp_ccatch`. It unwinds `K`'s frames
     innermost first, running their finalisers (SPEC §19 [finalise-cancel]).
   - The content is consumed by `close`. `not_persistent_affBox` and `not_affine_aff` leave no
     copy that could be resumed or cancelled again. ∎

T14.5 is the lemma #251 states. Every step is an existing lemma except two things written here:
the candidate `R` with its two clauses (T14.4), and `Q_gen` (D14.4).

## 14.4 Producing rebased continuations

T14.5 is about any rebased continuation. Whether lifetime stratification survives continuations
turns on which bodies *produce* one.

**Theorem T14.6 (production without a spanning lend).** Assume:

- `Δ; Γ ⊢ M : F_Σ 1` in the kernel, with `Σ = {yield : B_y ↠ A}` at `aff`;
- `Δ ⊢ Γ ⊐ @c` and (H4);
- `γ ∈ 𝒢⟦Γ⟧δ` at `ρ`.

Then the run of `gen(M)γ` ends in `Q_gen ∧ [δ(c)]`. Its `inj₁` results carry rebased
continuations.

*Proof.*

- `fundamentalC` and `cC_effOf` give `ewpTS ls Mγ (opTable (Row.tab Σ δ)) (vC 1) ρ`. Then L14.3.
- `ρ ∈ Res_{δ(c)}` by 6.62 at `Δ ⊢ Γ ⊐ @c`. L14.2 adds `[δ(c)]` to the postcondition, and T14.4's
  call case then reads off a rebased `κ`. ∎

The hypothesis T14.6 does *not* need is "no lend open at a suspension". The kernel already
guarantees it: a borrow's callback may perform only abortive operations (SPEC §19, *Which
operations cross a borrow's scope*, `Row.Unwind`). So no `yield` happens inside a borrow, and every
lifetime the body opens has ended before it suspends. This is T1 as the kernel states it (#172).

**Definition D14.7 (candidate rule `[gen]`).**

    Δ; Γ ⊢ M : F_{yield : B_y ↠ A (aff)} 1      Δ ⊢ Γ ⊐ @c      Δ ⊢ A ⊐ @c      A.Cl 0
    ─────────────────────────────────────────────────────────────────────────────────────────
    Δ; Γ ⊢ gen_c M : F((B_y ⊕ 1) ⊗ [@c] U(Aff^c A (B_y ⊕ 1)))

- `H_gen`'s clause boxes `κ` at `@c`. The kernel cannot type that today: `κ : U(…)` has no outlives
  rule (SPEC §22, `aff_not_outlives`), so `[]I` refuses it. That is the reason for a rule.
- Its compatibility lemma is T14.6 followed by T14.4.
- It is one `CDerives` rule and adds no index. Under the growth discipline it needs a SPEC entry
  before it lands, and none is made here.

**Open problem O14.1 (a lend spanning a suspension).** Does [TR] 6.65 (Mut Frame) hold with `ewpTS`
at a table with a *resuming* entry? Written at the typed world:

    ptoOwn ℓ v ⋆ vC T ls δ v ⋆
      fresh (λα. ptoMutS ℓ α ls (vC T · δ) ─⋆
        ewpTS ls e (opTable T') (λ ls'' v'. box α (∀w. ptoOwn ℓ w ─⋆ vC T ls'' δ w ─⋆ Q ls'' v')))
    ⊨  ewpTS ls e (opTable T') Q

This is `wpTS_M_frameX` with `ewpTS … (opTable T')` for `wpTS`, where `T'` has an entry with
`abort = false`. At an abortive-only `T'` it is mechanised: `ewpTS_M_frameU`
(`Core/EffWp.lean`). The same question stands for 6.64 (`wpTS_I_frameX`), 6.66 and 6.150. Then
§19's `withbor`, `withload` and the block borrows could take a callback row with a resuming
operation, and a `yield` could sit inside a borrow the generator opened.

*Where a proof meets the open step.* Follow 6.65's proof (the H-numbers are [TR]'s, pp. 24–25) up
to a stop of the callback at `α`. The premise's `ewp` gives the stop share `ρ_κ` with the cell
`ℓ ↦ mut(α, v', χ', P̂)`. The conclusion's run began without that cell, so by L14.1 its stop share
must hold the lend unfolded: `ρ_κ/ℓ ● ℓ ↦ own(v') ● χ'`, by 6.27 at `Res_{↓α}` (`six27_down`) and
6.28. The conclusion then owes `KapRel` at the **unfolded** share, at every `ls'` with
`Ext ls ls' (unfolded)`. Two routes, and neither closes:

1. **Refold at the old `α`.** `wpTS_M_refold` (`experiments/LoopBorrow`) re-pushes the saved lend for
   one run at any depth. Using the premise's resumption at the refolded share needs
   `Ext ls ls' (folded)` from `Ext ls ls' (unfolded)`: that is `RefoldKripke`.
   - `refoldKripke_false` refutes it.
   - `refold_fails_at_consumer_frame` builds a tagged typed world that reaches the failing list: a
     resumer that, after the stop, borrows a cell of its own at `γ` with `α ⊏ γ ⊏ ⊤` and resumes
     inside that borrow. A `'c`-bounded resumer has `γ ⊏ δ(c)`, but so may `α` be, and nothing
     orders `γ` against `α`.
   - So this route fails at that step, machine-checked.
2. **Re-open at a fresh `α′`** below every record of `ls'` and below the payload's stratum, as 6.65's
   entry does (H4, `exists_fresh`, `↓(γ ⊓ β)`). The cell is re-created by 6.65's H12–H17 (6.24 via
   `six24`, 6.25, 6.8), not relabelled. But the callback's **remainder** `K.plug w` is then owed at
   `α′`. The premise's `fresh` quantifies the callback **from its start**, at each `α`. It says
   nothing about the remainder of a run begun at `α` and resumed at `α′`. **This is the step not
   derived.**

I have not derived the lifted lemma and have not verified that any obstruction is real. A third
route, a register of open lends in `wpTS` (LoopBorrow's "dormant lend"), is a model change. #245's
brief rules it out ("don't track suspended lifetimes in the world"), and its soundness is not
verified.

**Open problem O14.2 (relabelling at `U`).** This would close route 2 of O14.1.

*Statement.* Let `v` be a value of a type `U C`, or of any type without an outlives derivation
(`⊸`, `∀`, `U`). Let `vC (U C) ls δ v ρ` hold, where `ρ` holds the cells of pending internal frames
at `α₁ ⊐ … ⊐ αₙ`. Let `ρ̄ = unfold(ρ)`, let `Ext ls ls' ρ̄`, and let `α′₁ ⊐ … ⊐ α′ₙ` lie below
every record of `ls'` and every external cell of `ρ̄`. Then

    vC (U C) ls'' δ' v (fold_{α′}(ρ̄))

where:

- `fold_{α′}` re-creates each `mut` frame cell at `α′ᵢ` (6.65's entry) and re-takes each `imm`
  image at `α′ᵢ` (`relRes`);
- `ls''` is `ls'` with each internal `imm` frame's records added at `α′ᵢ` (`AddAt`);
- `δ'` is `δ` with the internal lifetime variables sent to `α′`.

*Why it would suffice.* O14.2 applied to the premise's continuation share, which is a value at
`κ`'s type, gives the remainder at `α′`. The rest of 6.65's proof then runs at `α′`. Its 6.27
needs `@(rest) ⊐ α′`, which the fresh choice gives. This is a sketch, not a proof.

*What exists.* The existing relabelling (§15.5) proves O14.2's conclusion only for `imm` views at
data types. `relabel_obs`'s `thunk` case is the observable view, `True` (`vC_obs_aff`), so it
transports nothing at `U`.

## 14.5 How rebasing instantiates the existing machinery

| declaration | what it does | in this section |
|---|---|---|
| `updV_outlives` (6.50), `wpTS_box` (6.147) | a run from `Res_α` ends in `Res_α` | **the whole of rebasing** for T14.5: L14.2 re-rebases every new suspension |
| `upd_borrow_top`, `not_upd_of_new_mut` (LoopBorrow) | a run hands back only borrow cells its start had | internal lifetimes never reach the witness (L14.1) |
| `relRes`, `relabel_reb` (`Core/Images.lean`) | `c₀ ∈ reb_{β₀}(R)` and `R ∈ Res_β` give `relRes R β c₀ ∈ reb_β(R)` | **an instance only inside O14.1's route 2**, for a pending `Imm` frame's image: `R` is the owner escrow `ℓ ↦ own(v) ● χ`, `β₀ = α`, `β = α′`, with `R ∈ Res_{α′}` because `α′` is below the payload's stratum. `π`, `b` and the domain are kept |
| `relabel_obs` (`Core/RelationFacts.lean`) | the image's relation at `Imm̲ 'x T`, at the same list, for `β` below every record (`hβls`) | an instance for the views a resumed continuation holds **at data types**, with `β = α′` fresh for the resumer's list |
| `ResU.Reb` up to `π` | `π` assigns each view cell its piece of the owner | `π` decomposes the owner and does not abstract lifetimes. Every relabelling keeps it, and nothing here instantiates it |
| — | transport of a `U`-value (the callback's remainder, or a closure capturing an internal borrow) to fresh lifetimes | **no instance.** `relCell` fires only at `imm` cells, and a frame's `mut` cell is not a reborrow image (6.65 makes it fresh). This is O14.2 |

So #251's expectation is half met. Rebasing the **witness** is an instance of existing results:
6.50 and 6.147, not the relabelling lemmas. Re-instantiating the **continuation** at fresh
internal lifetimes would use `relabel_reb` and `relabel_obs` for its data views. The
continuation's code-level remainder has no instance. That is O14.1 and O14.2.

## 14.6 The tripwire (T15)

**Lemma L14.9 (no negative occurrence).** The disguise: the cell's invariant quantifies over
continuations whose relation ranges over worlds containing that same cell. It does not reappear, in
either sense.

1. **Definition.**
   - `vC` is defined by recursion on types (`vC_ind`).
   - At `ν` it is the union of post-fixed points of `nuF`. `nuF` is monotone because `X` occurs
     only positively (`nuF_mono`, `NuOk`), and an observation's argument is closed (`A.Cl 0`). An
     argument mentioning `X`, which would be the type-level negative occurrence, is outside
     `NuOk` (SPEC §22, *Open*).
   - `Q_gen` (D14.4) is a fixed point of a monotone operator.
   - `wpTS` quantifies over frames `ρ_f` of the carrier `Res`. The carrier is built before any
     predicate, by well-founded recursion on `Life = ℕᵒᵈ`: `Cell_α` refers only to `SProp_β`,
     `β ⊐ α` (D14.1). So a frame that contains `ℓ_c ↦ mut(b, …, P̂_c)` is an element of a set
     already defined, not a recursive occurrence of `P̂_c`.
2. **The knot.** No run of the resumed continuation can reach `ℓ_c`.
   - The witness `ρ̄` is in `Res_b`, so it holds no borrow cell at `b` or below.
   - Every borrow of `ℓ_c` is at `b` or below: the cell itself, and its reborrows, which 6.65 and
     6.122 make at lifetimes `⊏ b`.
   - While the cell is lent, no resource owns `ℓ_c`. 6.65 moves the owner into the cell (H13–H17).
   - During a call, `ℓ_c`'s owned cell belongs to `withswap`'s frame, not to the callback
     (6.66's `ℓ ↦ v`). By 6.119 (M-ex), nothing else holds it.
   - So Landin's knot (a stored continuation that reads its own cell) cannot be tied. ∎

**Where it would reappear.** It would reappear at a non-strict stratum: a witness with cells at the
cell's own lifetime. Then a stratum contains its own predicates. `no_nonstrict_stratum`
(`experiments/Outlives`, SPEC §23 *Left as printed*) refutes such strata by Cantor's argument,
which is phase B's `no_negative_domain` at the model's strata.

Rebasing places the witness strictly above `'c` (D14.5.1). Because SPEC §23 keeps `[]I` strict at
the `Imm`/`Mut` rules (`not_vC_outlives_le`), (H4) cannot admit an answer whose cells sit at `'c`
itself. The tripwire therefore stays excluded wherever T14.5 applies. O14.1 does not touch it,
since every route there keeps the witness unfolded and in `Res_{δ(c)}`.

## 14.7 Corollaries

**C14.1 (T1 for the resumer is bookkeeping).** Resuming a stored continuation while holding a
lend needs no T1 premise. The resumer may resume inside any borrows of its own, at any list.

- T14.5's resume is `d_callMut`, sound at every list and frame.
- The content's obligation is Kripke along `Ext` (D14.5). The resumer's lends are framed.
- The only discipline is that at resume the content is swapped *out*: owned by the callback, the
  owner's cell held by `withswap` (#245's "at resume the cell must be in the owned tag").

**C14.2 (T1 for the continuation is O14.1).** A `yield` inside a borrow the generator opened, with
the lend spanning the suspension, is exactly O14.1. Neither route of O14.1 discharges it:

- the same-lifetime refold fails (route 1);
- a fresh lifetime needs O14.2.

The bookkeeping that *does* exist is the per-observation lend: re-borrow at each resume, so the
lend ends before the `yield` and begins again after it. LoopBorrow covers it with no new rule. It
covers the lend only. A view or closure derived from it cannot survive the `yield`
(`not_lendingYield_mut`, `not_lendingYield_imm`).

**C14.3 (generator objects).** Take `gen_c M` (D14.7) stored in a cell `Mut @a ([@c] U(Aff^c A
(B_y ⊕ 1)))`.

- `next` is `d_callMut`.
- Dropping it is `close`, which finalises once (T14.5).
- A finished generator is `done`.
- This holds for every body with no spanning lend (T14.6).

**C14.4 (capabilities across `yield`).** A capability may be held across a `yield` in three ways:

| the capability is | holds across `yield` | why |
|---|---|---|
| **owned** (`Cap(ℓ, s)`, an `own` cell; or the `run` frame of an owning lend, §9.1 item 3) | yes | it has no lifetime |
| **borrowed from outside** at `'x ⊐ 'c` | yes | `Δ ⊢ Γ ⊐ @c` in D14.7, so 6.62 puts it in `Res_{δ(c)}` |
| **borrowed inside the generator** across the `yield` | open | O14.1 |

**C14.5 (task queues).** A queue is a family of cells of `[@c] U(Aff^c A B)`. Polling a task is
`d_callMut` on its cell (C14.1: the scheduler may hold lends while it polls). A finished task is
dropped by `close`. Tasks are disjoint because their witnesses are separate owned resources
(6.41). Tasks whose bodies have no spanning lend are covered.

**C14.6 (handler state).** Consider a parameterised handler whose state cell stores a continuation.
The clause owns the cell while the body is suspended and lends it while the body runs. That is
T14.5 with the state cell as `ℓ_c`. A continuation stored there is rebased by L14.2, as at any
other suspension.

## 14.8 Status and transcription

| result | statement | status |
|---|---|---|
| L14.1 | a suspension holds no internal cell | proved here; kind-level part machine-checked (`upd_borrow_top`) |
| L14.2 | re-rebasing | [TR] 6.147 at the typed world, mechanised (`wpTS_box`) |
| L14.3 | the generator handler | proved here, an instance of `ewp_handle` |
| T14.4 | a rebased continuation is a bounded affine closure | proved here, by `aff_coind` |
| **T14.5** | **the `Mut`-cell lemma: resume and drop** | **proved here** |
| T14.6 | production without a spanning lend | proved here, from `fundamentalC` |
| D14.7 | the rule `[gen]` | candidate; its compatibility is T14.6 + T14.4; needs a SPEC entry |
| L14.9 | T15 excluded | proved here |
| O14.1 | a lend spanning a suspension (§9.3 O3 at the kernel's tables) | **open**: route 1 fails, machine-checked (`refoldKripke_false`, arising by `refold_fails_at_consumer_frame`); route 2's step not derived |
| O14.2 | relabelling at `U` | open; holds for `imm` views at data types (`relabel_reb`, `relabel_obs`) |

**What a mechanisation writes.**

1. `Q_gen` as a fixed point in `Prop`, on the model of `nuRel`.
2. T14.4's candidate `R_κ ∪ nuRel`, with its two clauses.
3. L14.3 as one application of `ewp_handle`.
4. L14.1's lifetime clause, extending `upd_borrow_top`.

Everything else is cited by name: `cC_aff_iff`, `aff_coind`, `nuF_mono`, `nuRel_out`,
`KapRel`, `ewp_kappa_resume`, `ewp_kappa_cancel`, `ewp_ccatch`, `cC_effOf`, `wpTS_box`,
`updV_outlives`, `outlives_comp`, `vC_outlives`, `d_callMut`, `withswap_compatX`,
`hasDtor_affBox`, `not_persistent_affBox`, `fundamentalC`. No `CDerives` index is added. D14.7
is one rule.

**Hypotheses, and where each is spent.**

| hypothesis | spent in |
|---|---|
| (H1) `aff` | T14.4's close clause |
| (H2) | the box and the call's stratum |
| (H3) | both clauses |
| (H4) | the call's stratum, through 6.60 |
| `A.Cl 0` | `cC_aff_iff` and `aff_coind` |
| `Δ ⊢ Γ ⊐ @c` (T14.6) | 6.62 at the first run |

**Not covered here.**

- Forwarded effects (`Tout ≠ ∅`). Their `Aff` would be §22's effectful closure, whose relation
  clause is not stated in `Core/Aff.lean`.
- Multi-shot continuations (`q = unr`). `KapRel` asks `ρ = ∅` there, and the closure is
  persistent, not affine.
- The relevant qualifier (open in SPEC §19).
