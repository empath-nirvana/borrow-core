# §17 Borrow callbacks: premises, constants and the fresh binder

[← §16 Does the chain bottom out?](16-regress.md) · [index](README.md)

Issue #286. This section analyses #284 and #285 (`experiments/GhostEnd`, branch `gfp-arising`) and
grounds them in the literature. One part is mechanised: `experiments/GhostEnd/GhostEnd/Extend.lean`
(§17.5). Each claim either cites its source or is marked as a reading. **Verified** means the cited
passage was read in the fetched text of the paper. **Unverified** means it was not.

---

## 17.0 The answer in brief

1. **What the literature does.** None of the surveyed proofs reads a binder as "fresh". In every
   Kripke model surveyed, the `∀` and `→` clauses quantify over **every future world** and every
   instantiation available there, never only over fresh ones. The fresh name, region, lifetime or
   location is created in **the compatibility lemma of the construct that introduces it**. That
   lemma extends the world and then uses the premise, or the callback's `∀` clause, at the
   extended world. This works because those clauses already range over every future world.
   Whether the construct is a typing rule with a premise or a constant with a rank-2 type makes no
   semantic difference (§17.2).
2. **BoLo does the same** (§17.3). In `[TR]` 6.172–6.174, `withbor` is a constant. The clause
   `𝒱⟦∀'a ⊏ @b. T⟧` quantifies over every `α ⊏ @bδ`, and nothing in it says fresh. The fresh
   lifetime comes from `И` inside Mut Frame (6.65), which builds `ℓ ↦ M_α`. The proof then ends
   *"Follows from ∀E-compat and ⊸E-compat"*. BoLo's only world is the resource. The future-world
   quantifier for it is `─⋆` (and `wp`'s frame), so the callback's `⊸` clause already covers the
   resource with the new borrow composed in.
3. **What D16.1 lacks** (§17.4). D16.1 has two world components, the resource and the lend stack
   `σ`. The arising guard (#285) makes the `U`, `⊸` and `∀` clauses depend on `σ`, but their
   quantifiers still range over resource extensions only. That is a Kripke relation with half a
   future-world quantifier. `not_gfp` (#284) and `below_excluded` (#285) are the two sides of that
   gap.
4. **#286's hypothesis is right in substance, with one correction.** Reading the callback at
   `σ·y` is the standard semantics, but it is not special to the bounded-fresh binder. It is the
   Kripke quantifier over future worlds, taken over the product order
   `(ρ, σ) ⊑ (ρ ● ρ′, τ ++ σ)`. The fresh lend is one such future world, and the instance `τ = []`
   is D16.1's own clause.
   - **It closes the row's starting point.** `callback_ext` in Lean: a callback read at `σ`,
     applied to the view of a fresh lend, is in `cRL_{σ·y}` (§17.5).
   - **It is structural.** The block elaborates under `termination_by structural`, with `σ` an
     index that grows only at `∀`.
   - **It mirrors 6.65.** The row picks the fresh lifetime and builds the view, then instantiates
     the callback's `∀` and `⊸`. That is what 6.172 does.
5. **Verdict: a right answer, not a design choice** (§17.7).
   - Neither "callbacks as premises" nor "a special fresh-binder clause" is the answer.
   - The clauses that receive a value from outside quantify over future (resource, stack) worlds.
     These are the three the guard touches: `U`, `⊸` and `∀`.
   - The borrow row creates the lend.
   - Premise against constant is not a real alternative. Both need the same lemma: the context
     read at `σ` must be read at `σ·y`, which is Kripke monotonicity (§17.6).
   - What is left to choose is representation only (§17.7).

---

## 17.1 The question

The findings, in the vocabulary of `experiments/GhostEnd/README.md` steps 3h–3k:

- **3j, `not_gfp`.** D16.1 reads a value at the stack `σ`. Its `∀` clause instantiates `'y` below
  the stack, and its `⊸` clause then hands the function an argument (the inner view `k ↦ M_3`) that
  no run at `σ` can reach. GFP fails at `[x]` on `Λ. λn. return (thunk (return n))`.
- **3k, the guard.** That argument fails the table at `σ` (`not_tabAtS_innerView`), and every run
  at `σ` keeps the table (`wpG_below_not_arises`). Guarding `U`, `⊸` and `∀` by `TabAtS σ` removes
  the refutation, and `lam` and `allI` are then proved.
- **3k, what is not settled.** With the guard, a callback read at `σ` is obliged on no argument
  holding a cell below the stack (`below_excluded`). A borrow constant hands its callback exactly
  such a view. So the `withbor` row (#275) must read the callback at `σ·y`, and D16.1 has no clause
  that does.

Step 3j named two repairs outside the list: borrow rules whose callback is a premise, and a clause
that reads values at an extended stack. #286 asks whether a third reading, the bounded-fresh `∀`
read as Kripke world extension, is simply the standard semantics.

## 17.2 The literature

The table summarises each construct. Notes and verification status follow it.

| construct | typing form | `∀` / `→` clause | where the fresh thing is created |
|---|---|---|---|
| Wadler `let!` (1990) | rule, two body premises (§4) | no semantics in the paper | nothing is allocated |
| Tofte–Talpin `letregion` | rule, body premise | (consistency relation, not a Kripke LR; unverified) | (unverified) |
| Thamsborg–Birkedal masking (ICFP 2011) | rule `T-MASKING`, body premise (Fig. 1) | `→`: all `w′ ⊒ w` (Fig. 4) | Lemma 6.4 (Masking) picks `r ∉ |w|`, `w →reg(r) w′`, `R′ = R[ρ ↦ r]` |
| Birkedal–Sieczkowski–Thamsborg (CSL 2012) | rule, body premise | Kripke | Lemma 5 (Masking) takes a region from the world's reserve |
| Fluet–Morrisett `runRGN` (JFP 2006) | rank-2 constant in Haskell (§2); in FRGN a form whose premise is a callback `v : ∀γr. RGNHandle γr → RGN γr τ` (Fig. 7) | syntactic soundness, no LR | the operational rule picks fresh names and applies `v` to them |
| `runST`, Launchbury–Peyton Jones (PLDI 1994) | rank-2 constant `(∀β. ST β α) → α` | denotational (secondary) | — |
| `runST`, Timany et al. (POPL 2018) | **a construct, not a constant**: rule Trunst, premise `Ξ, X ∣ Γ ⊢ e : ST X τ` | `∀`: every relation and every region name `r` (Fig. 7); Iris's resources play the future world | Lemma 3.2 allocates a fresh region (`regions ≡∗ ∃r. region(r, …)`), then instantiates the premise with `⟦1⟧` and `r` |
| λ_Rust `newlft` (POPL 2018) | rule F-newlft, continuation premise (Fig. 4) | the semantic judgment quantifies over every lifetime substitution `γ` (§7) | the proof of F-newlft applies LftL-begin, taking `α := α₀ ⊓ κ̄` |
| L³ (FI 2007) | `new : ∃ρ.(Cap ρ τ ⊗ !Ptr ρ)`, no scoped form | `∀ρ` ranges over **all** locations (Fig. 4); the extended model adds future store typings (Fig. 7, Lemma 4.4) | the `New` case of Theorem 3.1: "Choose `ℓ ∉ dom(…)`" |
| Pitts–Stark (HOOTS 1998) | `let x = ref V in M` | `E(r)`, `K(r)` and `→` range over all `r′ ⊵ r` (Def. 4.2, 4.6) | the `ref` case of Prop. 4.8 uses `r′ ⊗ id_ℓ` with weakening (Lemma 4.3) |
| Ahmed–Dreyer–Rossberg (POPL 2009) | ordinary `ref` | `→` and `∀`: all `(j, W′) ⊐ (k, W)`; `∀` also over all relations (Fig. 4) | the `ref` compatibility adds an island `w_ref`; Lemma 4.1 is closure under extension |
| Neis–Dreyer–Rossberg `new α ≈ τ` (ICFP 2009) | rule E-NEW, body premise (Fig. 1) | `∀`: all `(k′, w′) ⊒ (k, w)` and all semantic types there (Fig. 2) | the `new` compatibility lemma extends `η`, `ρ` with `α ↦ (α₁, α₂)`, "highly reminiscent of the proof of compatibility for ref" (§4.3) |
| Dreyer–Neis–Birkedal (ICFP 2010) | ordinary `ref` | `∀` and `→`: all `W′ ⊒ W` (Fig. 3) | allocation adds islands |

**Verification.**

- **Verified** for Wadler (§4), Fluet–Morrisett, Thamsborg–Birkedal, Birkedal–Sieczkowski–Thamsborg,
  Timany et al., Jung et al., Ahmed–Fluet–Morrisett, Pitts–Stark 1998, Ahmed–Dreyer–Rossberg,
  Neis–Dreyer–Rossberg, and Dreyer–Neis–Birkedal Fig. 3.
- **Timany et al., checked twice.** Their §1.3 says *"we treat the stateful operations as
  constructs in the language rather than as special constants"*. Lemma 3.2's proof sketch says
  *"Using (5) with regions we know there exists a fresh semantic region r … We then instantiate
  our assumption by the unit relation ⟦Ξ ⊢ 1⟧∆ and r"*. It drops `X` at the end because `X` is not
  free in `τ`. #286's description of this paper as treating `runST` as a constant is therefore
  corrected: the constant is Launchbury–Peyton Jones's.
- **Unverified** (not read in primary form): Tofte–Talpin 1994/1997, Calcagno–Helsen–Thiemann 2002,
  Helsen–Thiemann 2000, Banerjee–Heintze–Riecke 1999 (characterised only through Fluet–Morrisett
  §1 and §7), Launchbury–Peyton Jones 1994 (type only, as quoted by others), the ν-calculus paper
  (MFCS 1993), Gabbay–Pitts, and Benton–Leperchey 2005. Dreyer et al. POPL 2010 was read only in
  part.

**The pattern.** Every verified Kripke model has the same three parts.

- **The binder clause is a universal over future worlds and instantiations.** It is never
  restricted to fresh instantiations: Timany's `r ∈ ℤ⁺` is arbitrary, L³'s `ℓ` is any location,
  ADR's `∀` ranges over all relations.
- **One lemma creates the fresh thing.** The construct's compatibility lemma allocates it, extends
  the world, and feeds the extended world to the premise or the callback.
- **The binder is dropped afterwards** because it is not free in the result type. Examples are
  Timany's last step and `ρ ∉ FRV(Γ, τ)` in masking.

The construct's form does not change this. Premise-style proofs apply the induction hypothesis at
the extended world (Thamsborg–Birkedal Lemma 6.4, NDR's `new`, F-newlft). Callback-style proofs
apply the callback's `∀` and `→` clauses there (Timany's `runST` instantiates a `∀X`, and BoLo's
6.172, below). Both rely on the clauses holding at *every* future world. In the premise style the
context must be valid at the extended world, and the Kripke monotonicity lemma provides that
(ADR Lemma 4.1, Pitts–Stark Lemma 4.3, L³ Lemma 4.4).

**Answer to #286's question 1:** neither (a) nor (b) as stated. The standard answer is (c):

- the binder is the ordinary Kripke universal over future worlds and instantiations;
- the scoped construct's compatibility lemma creates the resource and extends the world;
- monotonicity transports everything else into the extended world.

## 17.3 How BoLo proves `withbor`

**The form.** `withbor` is a constant: `Derives.withbor2Ax`, typed
`Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂` (`Paper/S2_Statics`, row 2.45). Its
fundamental-property case is the semantic typing of the constant, `[TR]` 6.172–6.174
(`Paper/S6_8_FundamentalProperty`, `withbor1_compat` to `withbor3_compat`).

**The binder.** `[TR]` p. 4 gives `𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ['a↦α](v ())`
(`Paper/S4_LogicalRelation`, row 4.5). This is a plain universal over every lifetime below the
bound. It contains no freshness condition and no world.

**Where freshness lives.** `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` (`[TR]` p. 6, row 18; `fresh` in
`Paper/S5_Model`). It says the current resource lies above `α`, which is freshness relative to the
world. Mut Frame (6.65, p. 24) is

    ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ –⋆ wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}) ⊨ wp(e){Q̂}

and its proof (H4) takes `α ⊏ γ ⊓ β` below everything the frame holds and builds the fictional cell
`ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`.

**The row.** 6.172 (p. 45, read in the PDF) and 6.173 run as follows.

1. Apply Imm or Mut Frame.
2. *"Apply ИR on LHS. Fix α ⊏ ⨅δ by И-mono. Apply –⋆R."*
3. Fold the borrow into `𝒱⟦Imm 'a T₁⟧δ['a↦α]` (*"using that 'b does not occur free in T₁ or
   T₂"*).
4. *"Follows from ∀E-compat and ⊸E-compat."*

In Lean, `withbor2_compat` picks the bound `a₂ ⊓ m` (`⋔r` at the callback's resource `@ρ₂`, then
`⋔-mono` to `⊓Δδ`). It then instantiates `hvf α` (the `∀` clause) and applies the callback's `⊸`
clause to `ℓ ↦ M_α`.

**Reading 6.65 as a world extension.** This is a reading, not a claim of the paper. BoLo's world
is the resource. In BI's Kripke resource semantics, `P ─⋆ Q` holds at `ρ` when `Q` holds at
`ρ ● ρ′` for every `ρ′ ⊨ P`. So `─⋆` is the quantifier over future worlds of the resource
preorder, and `wp`, which is universal in the frame `ρ_f`, is too. Mut Frame extends the world by
composing `ρ_m` in. The callback's `⊸` clause (`∀v′. 𝒱⟦T₁⟧ ─⋆ ℰ⟦T₂⟧`) covers that extension
because it is a `─⋆`.

So 6.65 is the pattern of §17.2 exactly:

- the binder is a plain universal;
- the constant's lemma creates the fresh lifetime and the borrow;
- the callback's own clauses, which range over the future world, take it from there.

BoLo needs no monotonicity lemma, because its single world component is quantified by `─⋆`
everywhere.

## 17.4 What D16.1 lacks

D16.1's world has two components: the resource `ρ`, and the lend stack `σ` with its lifetimes
`αs`. Its clauses quantify over resource extensions through `─⋆` and `wpG`, as BoLo's do. **No
clause quantifies over stack extensions.** The stack is "a fixed parameter of the block"
(`Stacked.lean`).

- **Before the guard,** no clause read the stack's position relative to its argument. So a value
  at `σ` was obliged on everything, including arguments that only arise at `σ·y`, and `not_gfp`
  exhibits one that cannot be met at `σ`.
- **After the guard,** the clauses read the stack (`TabAtS σ αs` at `U`, `⊸` and `∀`), but their
  quantifier still ranges over resource extensions alone. The resource extension that composes in
  a fresh view is paired with the old stack, under which the guard rejects it. That is
  `below_excluded`.

The two steps are one phenomenon. A clause that reads a world component must quantify over that
component's future values, or values cannot be used after the world grows. Every Kripke model in
§17.2 has this rule, and every one of their `→`/`∀` clauses says "for all `W′ ⊒ W`". The guard is
the right restriction (3k shows the witness does not arise). What it lacks is the Kripke
quantifier that comes with any world-relative condition.

## 17.5 The hypothesis, tested

**The clause.** `Extend.lean` defines `vRLk`/`cRLk`/`effRetK`. They are `vRLa`/`cRLa`/`effRetA`,
the guarded relation, except at `∀`:

    cRL_σ (∀'x ⊏ c. C) αs e ≜ ∀τ αt.  |αt| = |τ|  →  αt ++ αs in nesting order  →
                               τ's variables fresh for σ, each the bound x or not free in C  →
                               ∀α.  ⌜α ⊏ c⌝  ─⋆  guard_{τ++σ}  cRL_{τ++σ} (C)[x ↦ α] (αt ++ αs) (e ())

**Results** (Lean, standard axioms only).

| question | result | declaration |
|---|---|---|
| Structural? | Yes. The `mutual` block elaborates under `termination_by structural` on the type. `σ` is now an index that grows only at `∀`. `τ` and `αt` are universally quantified data to the left, not relations, so nothing occurs negatively at the same type. §16.5's T15 table is unchanged. | `vRLk`, `cRLk`, `effRetK` |
| Elimination weakened? | No. `τ = []` is `cRLa`'s clause. | `all_elimK` |
| Does it close the row's starting point? | Yes. Take a callback in `cRL_σ` at `∀'y ⊏ c. Mut 'y T ⊸ D`, applied to the view `ℓ′ ↦ M_α` of a fresh lend `e` (with `e.x = y`) opened at `α` below the stack. The application is in `cRL_{e·σ} D` at `α :: αs`. That is the piece at `σ·new` that `StackStep.lean` folds back to `σ`. | `callback_ext` |
| ... at one entry, every hypothesis discharged? | Yes. Both tables at `[e]` follow from the callback's resource lying above `α`, as 6.172–6.174 discharge `⋔` by `⋔r` at `@ρ₂`, and from the view being the entry's own (`tabAtS_start_one`). | `callback_ext_one` |

**What is not shown.** I have not derived either of these and have not verified that any
obstruction is real.

1. **The rest of #275's row.** It converts `cRL_{σ·new}` at the callback's type (an answer in
   `effRetK (e :: σ)` at `['y] B`, the substitution `δ[y ↦ α]` varying with the re-lend) into the
   callback form `OpenS … (cbQ …)` that `stack_step_other`/`stack_spans_mut` consume. It needs
   `OpenS` monotone in its answer relation, `effRetK`'s congruence in `δ` (as `vRLa_congr`), and
   the answer `[α](vRL B)` read as `ghostS`. This is the half of #275 that step 3h called
   "`relend_of_openD` at a stack". The extension reading supplies its premise, which step 3j found
   missing ("#275 has no induction hypothesis to start from").
2. **GFP at this relation.** See §17.6.

**Does it mirror 6.65?** Yes, step for step:

| BoLo (6.172–6.173) | stacked row with `callback_ext` |
|---|---|
| Mut Frame's `И` picks `α ⊏ γ ⊓ β` below the frame | the row picks `α` below the head of `αs` and the bound (`stack_step_other`'s `γ = b ⊓ head αs′`) |
| it builds `ρ_m = ℓ ↦ mut(α, …)` | 6.65 at the stack builds the view `vwE e true α` |
| `⋔r` at `@ρ₂`: the callback's resource is above `α` | `TabAtS [e] [α] ρf` from `ρf ∈ Res_α` |
| `∀E-compat` at `α` | the `∀` clause at `τ = [e]`, `α` |
| `⊸E-compat` at `ℓ ↦ M_α` | the `⊸` clause at `e·σ`, the view |
| the world grows by `ρ_m ●`, which `─⋆` already covers | the world grows by `ρ_m ●` and `e ::`, which the `∀` clause now covers |

The one difference is the last row. BoLo's world has no second component, so `─⋆` is enough.

## 17.6 Premise against constant; what GFP then owes

**The same obligation either way.** Suppose `withbor` took its callback as a premise
(`Δ, y ⊏ ⊓Δ; Γ, m : Mut 'y T ⊢ M : D`). The row would apply the induction hypothesis at `σ·y` to
`M`, with the context `Γ` read at `σ`. GFP's hypothesis at `σ·y` asks for `gRL_{σ·y} Γ`, so the
row needs `gRL_σ Γ ⊨ gRL_{σ·y} Γ`. That is Kripke monotonicity along stack extension.

§16.4's sketch, *"applies the induction hypothesis to its callback's premise at `σ·(ℓ′, y, T′, k′)`"*,
presupposes this step without naming it. (This is a reading of the sketch, not a mechanised
claim.)

With the constant and the extended `∀` clause, the same lemma appears in `allI`. To prove the
clause at `τ = [e]`, `allI` applies the induction hypothesis at `e·σ`, with the context read at
`σ`. So the choice of typing form moves the obligation between rows without removing it. This
matches §17.2, where both styles depend on monotonicity.

**Where monotonicity comes from.** This is a reading, not mechanised. With only `∀` extended,
monotonicity of a context value at `U` or `⊸` would need computation-level monotonicity, including
D16.1's piece `OpenS` at `σ` into `OpenS` at `e·σ`. The standard construction avoids that. Give
**every clause that receives a value from outside** the future-world quantifier, so that
monotonicity holds by construction:

- `U`: `RelendableS` at every `τ ++ σ`;
- `⊸`: the argument at every `τ ++ σ`;
- `∀`: as above.

These are the three clauses the guard touches. Monotonicity is then an induction on value types:

- `⊗`, `⊕`, `!`, `[@a]` and `Ref` are componentwise;
- the leaves read `δ_{τ++σ}` only at variables that `τ` does not rebind (`vC_congr`, given the
  freshness side condition);
- `U` and `⊸` hold by transitivity of `++`.

The work moves to `thunk`, `lam` and `allI`, each proved at every extension from the induction
hypothesis at `τ ++ σ`. GFP's motive already quantifies over `σ`.

**Costs.**

1. `vRL_[]` is no longer `vC`. At `[]` the extended clauses ask for behaviour at every lend opened
   later, so `GFPAt []` is stronger than `fundamentalC`. Whether it still yields adequacy by the
   route `gfpAt_nil_iff` gives is not checked.
2. The row conversion of §17.5 item 1 remains.
3. `GFPAt`'s `σ.WF Δ` requires every entry's variable to be in `Δ`. At `allI` the extension
   `[e]` has `e.x = x`, the rule's own variable, so the condition holds there. A transported
   context may meet entries named by later binders. Either the condition is relaxed to freshness,
   or entries carry lifetimes only and `δ` carries the binding. That is representation (§17.7).

## 17.7 Verdict

**This is a right answer, not a design choice.**

- **It is fixed by the relation D16.1 already is.** D16.1 is a Kripke relation over a product
  world: the resource and the stack. The arising guard, which 3k showed to be the right
  restriction, reads the stack component at `U`, `⊸` and `∀`. In the standard semantics (every
  model in §17.2, and BoLo's own `─⋆` for its one component), a clause that reads a world
  component quantifies over that component's future values. So those three clauses quantify over
  stack extensions `τ ++ σ` as well as resource extensions.
- **The fresh-binder reading is the special case the row needs.** The `withbor` row instantiates
  the `∀` clause at the extension `[e]` that it creates itself, exactly as 6.172 instantiates
  `𝒱⟦∀⟧` at the lifetime 6.65's `И` creates. The binder is not given a "fresh" semantics. The
  world extension happens in the borrow constant's row, as in every surveyed proof.
- **Premise against constant is not a real choice.** Both need context monotonicity along stack
  extension (§17.6). The literature uses both forms over the same semantic machinery. Timany et
  al. even use a construct where Launchbury–Peyton Jones use a constant. Keeping the borrow
  operations as constants (the kernel's and BoLo's form) costs nothing.

**What is genuinely open, and only representation:**

- whether stack entries carry syntactic lifetime variables (D16.1's `LEnt.x`, so `σ.WF Δ` and a
  freshness side condition on extensions) or lifetimes only, with `δ` binding the variables;
- whether `U` and `⊸` get the stack quantifier explicitly, or monotonicity is proved for them
  instead. The first is standard and makes monotonicity free.

**Recommended next step.**

- Restate the guarded relation with the future-stack quantifier at `U`, `⊸` and `∀`.
- Prove the monotonicity lemma for value types.
- Redo `thunk`, `lam` and `allI` at extensions.
- Prove #275's conversion (§17.5 item 1), starting from `callback_ext`.

## 17.8 Report lists

- **Printed hypotheses not spent.** None. `callback_ext` spends the callback's `∀` and `⊸` clauses
  and both guards. `callback_ext_one` spends `ρf ∈ Res_α` on both tables, as 6.172 spends `⋔r`.
- **Uniqueness and functionality results.** None needed: no step compares two decompositions.
- **Printed lemmas in the run-up that are untranscribed at a resuming table.** 6.150 (↺), as for
  steps 3g–3k. 6.172–6.174 are transcribed in `Paper/` at the kernel's relation. They are cited
  here as the model, not lifted to the stack.
- **Hypotheses added.**
  - `callback_ext` takes `e.x ∉ σ.map LEnt.x`, which follows from the presupposed rule's freshness
    (`stackFresh_of_fresh`). It also takes the two tables at `e·σ`. At one entry both are
    discharged (`callback_ext_one`).
  - The `∀` clause's side condition (`τ`'s variables fresh for `σ`, each the bound variable or not
    free in the body) makes sure an extension rebinds nothing the body reads.
