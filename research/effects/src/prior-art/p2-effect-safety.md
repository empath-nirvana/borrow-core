# Prior art: P2, effect safety and the row algebra

This note surveys the literature on one System A property, P2. It ends in a menu of options with trade-offs; it does not recommend one. The property is stated in [P2](../properties/effect-safety.md): a well-typed program performs no unhandled operation, the static effect over-approximates the dynamic one, and no part of the row algebra (subeffecting, masking, handling, row-variable instantiation) can hide or erase a performed effect.

**Verification marks.** **[V]** means I read the statement in the primary source's full text for this note; the quote is copied from it. **[U]** means I did not verify it, and it is cited from secondary material or from memory. Theorem numbers follow the version named in the sources list. Where an author version numbers differently from the ACM version, both are given.

---

## 0. Summary of the menu

The menu has two independent parts: **what the row algebra is** (rows R1–R6) and **how P2 is stated and proved** (routes S-a to S-g). Section 5 has the detail.

### 0.1 The algebra and representation

| | option | Yoshioka conditions it must meet | buys | costs | fit with our decisions |
|---|---|---|---|---|---|
| **R1** | **Simple rows over static per-site names, no masking** (today: `orowRF`, SPEC §19) | Def 5.1 (1)(2). (3) does not apply: there is no lift. (4) is met trivially: a label has no type arguments, since `Ξ n` is one signature | the smallest algebra; already proved lawful and safe (`rowAlgSafe_orowRF`); instances and no accidental handling come from static names | fails (3) as soon as `mask`/lift is added, by the shape of Thm 7.2. One tail variable, so no `ρ₁ ⊙ ρ₂` (Yoshioka Table 2). The "(3), (4) don't apply" argument is prose, not Lean | matches decision 62 and SPEC §19 as built |
| **R2** | R1 with **conditions (3) and (4) as checked conjuncts** (a guard) | (1)(2), plus a Lean statement that no lift exists and that dispatch reads the whole label | a future feature (mask, generic sites, lifetime-parametric operations) cannot silently invalidate S1 | small: two definitions and two easy lemmas at our instance | none against |
| **R3** | **Rémy rows with lacks constraints / presence** (Links; Hillerström–Lindley) | (1)(2) (simple rows) | `[handle]`'s `n ∉ Σ` becomes a kinding fact that survives instantiating `ρ`; E6's `PolyUseLacks` is exactly this shape; presence polymorphism | `RowCon` needs a lacks set (its `adm` field can already carry one); kinding rules; still one tail | compatible; row variables stay in the kernel |
| **R4** | **Scoped rows** (Koka, Leijen 2017; `EAScpR`) | (1)(2)(3); (4) only in the erasable variant `EAEScpR` (Thm 7.9; §7.3) | masking/lift are sound (Thm 7.4); re-entry typed by counting occurrences; Core's first-match `Row.find` already reads rows innermost-first | `∼` changes from first-match equality (which collapses duplicates) to "swap distinct labels only"; `[handle]` removes one occurrence; adds the (3) proof obligation; not needed while names are static | compatible; useful only if masking or dynamic instances are wanted |
| **R5** | **Capabilities** (System C/Ξ; HandlersAsBorrows) | the conditions become facts about capability sets / lifetimes: nothing is below `∅`, and ending one handler's lifetime discharges no other | effect safety is "no undelimited label", an outlives fact (B7, 6.60); E6 holds by construction; handler extents are lifetimes | storing effectful values needs boxes (OQ-28); collides with the reason SPEC §19 gives against generative labels; blurs the A/B separation (the notebook allows it only as an optional realisation) | as a **proof route** for an unchanged S3, compatible; as a **replacement** for rows, it conflicts with decision 62 |
| **R6** | **Modal effects, Met(X)** (Tang et al. 2025; Tang–Lindley 2026) | TL Def 3.5 validity conditions (1)(2), Yoshioka's restated | one theorem for any effect structure; rows and capabilities both encode; Met was built for annotation-light code (the E1 axis) | a modal kernel; local labels; all evidence is paper proofs | a different kernel, not a row option |

### 0.2 Statement and proof route

| | route | shape | buys | costs |
|---|---|---|---|---|
| **S-a** | progress-at-ε, every reachable configuration (today's S3 `EffSafe`) | Yoshioka Lemma 5.5/5.7 style, read over runs | the literature's standard strength; teeth already proved (`not_der_unhandled`) | covers only machine steps (`S.Reach`, which takes no `io` step), so not the run after a platform answer (§6.2) |
| **S-b** | terminating-only (Bauer–Pretnar Cor. 4.2) | "a terminating computation … calls an operation in Δ" | weakest; free from S-a | says nothing of divergent runs; too weak where div is codata |
| **S-c** | typing lemma: faulty terms untypable (Koka Lemma 4.b) | `⊢ X_op[op(v)] : τ \| ε ⇒ l ∈ ε` | static, no runs; Leijen: "effect types cannot be discarded (except through handlers)" | needs syntactic subject reduction to yield a run theorem; Core types semantically |
| **S-d** | capability form (System C Cor. 9 / Cor. 4.8) | "never results in an undelimited label" | label-centric, row-free; fits R5 | needs labels or capabilities in the machine |
| **S-e** | **corollary of the fundamental lemma plus adequacy** (Biernacki et al. 2018 Thm 9, 2020 Thm 2; Zhang–Myers Thm 2; our Core `effSafe_tier1`) | `FL ∧ adequacy ⇒` S-a | Core's route today; no syntactic preservation needed; the same route reaches W | effect safety has no named relation-free proof; it inherits FL's world |
| **S-f** | **a generic A-level theorem**: S1 plus abstract typing rules imply S3 (Yoshioka's and Met(X)'s actual contribution) | `RowAlgebra ∧ TypingRules ⇒ EffSafe`, over any `EffectSystem` | S1 becomes load-bearing rather than "teeth"; a new instance gets S3 from S1 | A needs `perform`/`handle`/`sub`/`let` typing rules, against A's minimal formers |
| **S-g** | **trace over-approximation under every runner** | S-a over `RReach R`, or "every `io` event on a run of a program at ε is an operation of ε" | states the brief's "static over-approximates dynamic" on the observable trace; the property P13 lowering preserves | a preservation fact for platform answers (`R.Respects` must give typed answers) |

**Where our current target sits (§6):** R1, stated through S-a, realised through S-e at Core σ=[]. S1 is Def 3.5 + Def 5.1 + `RowSig` + `SubClosed`. Conditions (3) and (4) are dismissed in prose (RESTRUCTURE §1.5). Neither R2's guard nor S-g's runner form is stated.

---

## 1. Canonical statements

### 1.1 Bauer–Pretnar 2014, *An effect system for algebraic effects and handlers* (LMCS 10(4:9)) [V]

Dirt `Δ` is "a finite set Δ of operations", each of the form `ι#op` with `ι` an **effect instance**. Subtyping on dirty types is set inclusion: `A ⩽ A′ ∧ Δ ⊆ Δ′ ⇒ A ! Δ ⩽ A′ ! Δ′`.

- **Theorem 4.1 (Progress & Preservation).** "Progress: If ⊢ c : A ! ∆ then either there exists a computation c′ such that c ⇝ c′, or c is of the form val e for some expression e, or c is of the form ι#op e (x. c′) for some ι#op ∈ ∆. Preservation: If ⊢ c : C and c ⇝ c′ then ⊢ c′ : C." Proved in Twelf (`progress.elf`, `preservation.elf`).
- **Corollary 4.2 (Safety).** "A terminating computation of type A ! ∆ returns a value of type A, or calls an operation in ∆. In particular, a terminating computation of type A ! ∅ does not call any operations and returns a pure value of type A."

Operations are in generic-effect form `ι#op e (x. c′)`, with the continuation explicit. So "stopped at an operation" is a syntactic head form; there is no evaluation context to search. The dirt is per operation (not per signature) and per instance, the same granularity as our `(n, i)` row keys.

### 1.2 Pretnar 2015, *An introduction to algebraic effects and handlers* (MFPS tutorial) [V]

**Theorem 4.2 (Safety).** "If ⊢ c : A ! ∆ holds, then either: c = return v for some ⊢ v : A, or c = op(v; y. c′) for some op ∈ ∆, or c ⇝ c′ for some ⊢ c′ : A ! ∆." This is one-step progress-and-preservation in a single statement. The handler rule's side condition is quoted in the text: an unhandled operation "must also appear in ∆′ as it may also be called in the handled computation (and thus also in continuations of handled operations)".

### 1.3 Leijen 2017, *Type directed compilation of row-typed algebraic effects* (POPL; MSR TR 2016) [V, TR version]

Rows use scoped labels: "the type system also allows duplicate labels, where an effect ⟨exc, exc⟩ …".

- **Theorem 1 (Semantic soundness).** "If · ⊢ e : τ | ϵ then either e ⇑ or e ⟼ v where · ⊢ v : τ | e."
- **Lemma 4 (Faulty expressions are not typeable).** "b. If Γ ⊢ X_op[op(v)] : τ | ϵ, with op ∈ Σ(l), then l ∈ ϵ." Leijen's gloss: "It is a powerful lemma though as it states that effect types cannot be discarded (except through handlers)."

The technique is subject reduction plus untypability of faulty expressions, not progress: "we use the latter technique since it turns out that for proving state isolation this technique works better". `X_op` ranges over contexts with no handler for `op`. Note that Thm 1 is stated at any `ϵ`, so an unhandled operation at a non-empty `ϵ` counts as "faulty" only when `l ∉ ϵ`.

### 1.4 Hillerström–Lindley 2016, *Liberating effects with rows and handlers* (TyDe) [V]

Rows are Rémy-style, with presence types `P ::= Pre(A) | Abs | θ`, and a row kind that tracks labels.

- **Definition 3.2.** "computation term N is normal with respect to effect E, if N is either of the form return V, or E[do ℓ W], where ℓ ∈ E and ℓ ∉ BL(E)." Here `BL(E)` is the labels bound by handlers in the context `E`.
- **Theorem 3.3 (Type Soundness).** "If ⊢ M : A!E, then there exists ⊢ N : A!E, such that M ⇝⁺ N ↛, and N is normal with respect to effect E." The core calculus is terminating, so this is stated with an existential normal form.

### 1.5 Biernacki, Piróg, Polesiuk, Sieczkowski [V]

- **2018, *Handle with care* (POPL).** Introduces `lift`, written `[e]_l`, which "dynamically creates a new occurrence" of a label and skips the nearest handler for `l`, with freeness counted: `(n+1)−free(l, [E]_l)`. **Theorem 9 (type-soundness):** "For any expression e, if Σ; ·; · ⊢ e : 1 / ⟨⟩ and e →∗ e′ ↛, then e′ is a unit value (e′ = ())." It is obtained "as a corollary of the fundamental property" (Theorem 8) of a logical relation.
- **2019, *Abstracting algebraic effects* (POPL).** Explicit coercions on rows, including swap: "the coercion ε₁ ↔ ε₂ (swap)" exchanges handlers for the first two occurrences. Effects are abstract (existential), and type erasure is proved semantics-preserving. **Theorem 2.7 (Type Soundness):** "If ∆; · ⊢ e : τ / ⟨⟩ and ∆; e →∗ ∆′; e′ ↛, then there exists v such that e′ = v."
- **2020, *Binders by day, labels by night* (POPL).** Lexically scoped handlers give effect instances. **Theorem 2 (Type Soundness):** "For any well-typed program e its evaluation does not get stuck, i.e., if ·; ·; · ⊢ e : τ / ι and e →∗ e′ ↛, then e′ ∈ Val." It comes from **Theorem 1 (Fundamental)**: "Any well-typed expression e logically approximates itself".

### 1.6 Zhang–Myers 2019, *Abstraction-safe effect handlers via tunneling* (POPL) [V]

**Theorem 2 (Type Safety).** "If ∅ | ∅ | ∅ | ∅ ⊢ t : [T]∅ and t −→∗ t′, then either there exists v such that t′ = v or there exists t′′ such that t′ −→ t′′." It "falls out as an easy corollary of Adequacy and Parametricity". Here effect safety is part of a binary result, and abstraction safety (P12, our E6) comes from the same relation.

### 1.7 System C: Brachthäuser, Schuster, Lee, Boruch-Gruszecki 2022, *Effects, capabilities, and boxes* (OOPSLA) [V, author version]

- **Definition 8 (Undelimited Label).** "A statement s contains an undelimited label l, if it has the form H_l[cap_l(v⃗)]."
- **Corollary 9.** "Starting from an empty context reducing a well-typed program ∅ ⊢ s : τ | ∅ never results in an undelimited label." (The notebook and survey cite this as "Cor. 4.8", presumably the ACM numbering. I verified the author PDF, which numbers it Corollary 9.)
- **Lemma 4 (Labels are delimited).** "If ∅ ⊢ E[cap_l(v⃗)] : τ | ∅ … then E = E′[#_l{H} with h]."
- The gloss: "Effect safety means that applications of a capability with label l only occur in a context that contains a delimiter at l." The dangerous step is `(ret)`: "This is the very point where effect safety could be violated", and it is made safe because "only boxed values can leave delimiters". It is mechanised in Coq (locally nameless).

### 1.8 Yoshioka, Sekiyama, Igarashi 2024, *Abstracting effect systems for algebraic effect handlers* (ICFP; arXiv 2404.16381v1) [V]

This is the generic statement our S1 transcribes.

- **Def. 3.5.** An effect algebra `⟨Σ_eff, ⊙, 0, (−)↑, ∼⟩`, a partial monoid under `∼`, with substitution a homomorphism. `ε₁ < ε₂` means `ε₁ ⊙ ε ∼ ε₂` for some `ε`.
- **Def. 5.1 (Safety Conditions).** "(1) For any L, (L)↑ < 0 does not hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠ L′, then (L)↑ < ε′." The gloss: "Condition (1) disallows the subeffecting to hide an invoked effect label L as if it were not performed. Condition (2) means that, if an expression invoking a label L is given an effect ε, and an effect handler for a different label L′ handles the expression, then the information of L still remains in the effect ε′".
- **Lemma 5.5 (Progress).** "If ∅ ⊢ e : A | ε, then one of the following holds: e is a value; e −→ e′ for some e′; or e = E[op_l S T v] for some … such that 0−free(l S, E)."
- **Lemma 5.7 (Effect Safety).** "If Γ ⊢ e : A | 0, then there exist no E, l, S, op, T, and v such that both e = E[op_l S T v] and 0−free(l S, E) hold."
- **Theorem 5.8 (Type-and-Effect Safety).** "If ∅ ⊢ e : A | 0 and e −→∗ e′ ↛, then e′ = v for some v." **Theorem 5.9:** `EA_Set`, `EA_SimpR` and `EA_ScpR` meet (1) and (2).
- **Def. 7.1 (lift coercions).** "(3) If (L)↑ ⊙ ε₁ ∼ (L₁)↑ ⊙ ··· ⊙ (Lₙ)↑ ⊙ (L)↑ ⊙ ε₂ and L ∉ {L₁, …, Lₙ}, then ε₁ ∼ (L₁)↑ ⊙ ··· ⊙ (Lₙ)↑ ⊙ ε₂."
- **Theorem 7.2.** "The effect algebras EA_Set and EA_SimpR do not meet safety condition (3). Furthermore, there exists an expression that is well typed under EA_Set and EA_SimpR and gets stuck." The witness is `handle_Exc [raise_Exc Unit ()]_Exc with h`, typed at `{}` using `{Exc} ∪ {Exc} ∼ {Exc}`.
- **Theorem 7.4.** `EA_ScpR` and `EA_MSet` meet (1)–(3). The reason given: "⊙ScpR in EAScpR is not idempotent". **Theorem 7.5:** type-and-effect safety with lift under (1)–(3).
- **Def. 7.6 (type erasure).** "(4) If (l S₁)↑ < ε and (l S₂)↑ ⊙ ε′ ∼ ε, then S₁ = S₂."
- **Theorem 7.7.** "The effect algebras EA_Set, EA_MSet, EA_SimpR, and EA_ScpR do not meet safety condition (4). Furthermore, there exists an expression that is well typed under these algebras and gets stuck." The witness is `Writer Int` / `Writer Bool` swapped by commutativity: "The proof of Theorem 7.7 relies on the commutativity of ⊙".
- **Example 7.8, Thm 7.9.** The erasable variants allow swapping only labels with different names, and meet (1), (2) and (4). Cost: "ρ₁ ∪ ρ₂ ∼ ρ₂ ∪ ρ₁ do not hold in erasable sets". **§7.3:** "only EA_EScpR satisfies these conditions", meaning (1)–(4).
- **Table 2.** "Multiple effect variables": ✓ for sets and multisets, ✗ for simple and scoped rows.

### 1.9 Modal effects: Tang, White, Dolan, Hillerström, Lindley, Lorenzen 2025 (OOPSLA, Met) and Tang–Lindley 2026 (POPL, Met(X)) [V]

- **Met, Def. 4.2 (Normal Forms).** "a value V or of the form M = E[do ℓ V] for ℓ ∈ E and n−free(ℓ, E)". **Theorem 4.3 (Progress)** and **Theorem 4.4 (Subject Reduction)** "together give type soundness and effect safety".
- **Met(X), Def. 3.5 (Validity Conditions).** "(1) if E ⩽_X · then E = ·, and (2) if ℓ ⩽_X ℓ′, E and ℓ ≠ ℓ′ then ℓ ⩽_X E." The text says these follow Yoshioka et al., and "together ensure that if a label ℓ is a subtype of an effect context E, then it must syntactically appear in the effect context E". **Theorems 3.7 and 3.8** (progress, subject reduction) hold "for any effect structure X satisfying the validity conditions".
- Effect structures: simple rows `R_simp` ("distinct labels without any effect variable"), scoped rows `R_scp` ("potentially duplicated labels"), and sets `S`. System Fε (Koka) encodes into `Met(R_scp)` and System C into `Met(S)`. The comparison: "System C generates fresh runtime labels for effect handlers, whereas System Fε does not" (§2.5.4). §6.3 adds that "the first-class handler names of Koka offer no extra expressiveness over the second-class local labels of Met(X)". §6.4 sketches Rémy rows as an effect-kind extension, "R = {Row L | L} where L is a label set and denotes all labels that must not be in the row".

### 1.10 How the statements differ

| axis | variants |
|---|---|
| strength | terminating-only (Bauer–Pretnar Cor. 4.2; Links Thm 3.3); every stuck end (Yoshioka Thm 5.8; Biernacki; Koka Thm 1 with ⇑); every reachable configuration (System C Cor. 9; our S3) |
| which row | only `0` (Yoshioka Lemma 5.7; Biernacki Thm 9 at `⟨⟩`); any `ε`, stops in `ε` (Bauer–Pretnar 4.1; Pretnar 4.2; Links Def. 3.2; Met; our `StopsIn ε`) |
| granularity | per operation and instance (Bauer–Pretnar `ι#op`); per label (Koka, Yoshioka, Links); per capability (System C); per `(n, i)` (ours) |
| where it lives | a typing lemma (Koka Lemma 4.b); a run theorem from progress and preservation (Bauer–Pretnar, Yoshioka, System C, Met); a corollary of a logical relation (Biernacki 2018/2020, Zhang–Myers, our Core) |
| the algebra | built in (most); a parameter with conditions (Yoshioka; Met(X)) |
| the platform | none: closed programs, pure semantics, everywhere. Ours alone adds runners (S2), see §6.2 |

---

## 2. How each system realises and proves it

| system | representation | key lemmas | technique | mechanised |
|---|---|---|---|---|
| Eff (Bauer–Pretnar) | sets of `ι#op`, inclusion subtyping | Thm 4.1 progress + preservation | syntactic | Twelf [V, stated in the paper] |
| Koka 2017 | scoped rows, `[eq-swap]` for distinct labels | Lemma 1 subject reduction; Lemma 4 faulty untypable | syntactic, no progress | paper |
| Links | Rémy rows with presence | Thm 3.1 subject reduction; Thm 3.3 | syntactic; abstract machine simulation (Thm 4.2) | paper |
| λH/L (Biernacki 2018) | scoped rows with `lift` | Thm 8 fundamental | logical relation; soundness as corollary | paper (the Coq status of this one is not verified) [U] |
| Biernacki 2020 | lexically scoped instances | Thm 1 fundamental | logical relation | paper [U on mechanisation] |
| Zhang–Myers | tunnelled effects | Thm 1 parametricity; Lemma 6 adequacy | logical relation | paper |
| System C | capability sets, second-class blocks, boxes | Lemma 4 labels delimited; Thm 3 progress; Thm 5 preservation; Lemma 7 | syntactic; the danger is `(ret)`, defused by boxing | Coq [V, stated] |
| λEA (Yoshioka) | abstract effect algebra | Lemmas 5.5–5.7 | syntactic, over the algebra's conditions | paper |
| Met(X) | effect structure + modalities + local labels | Thms 3.7, 3.8 | syntactic, "do not use ad-hoc case analysis on shapes" of effect collections | paper |
| **our Core** | first-match lists of `(n, i, q, A, B)`, static names | `fundamentalC`, `adequacyD`, `ewp_bot`; `effSafe_tier1` from FL, `FamEmpty`, `AdequateEvery` | semantic (Kripke logical relation, `ewpTS` least fixed point) | Lean, Core σ=[] |

**The handler case decides effect safety in every proof.** Koka's Lemma 4.b: "since op ∉ h the handler discharges some effect l′ with l ≠ l′ … and thus l ∈ ϵ′". This is exactly Def. 5.1 (2). Yoshioka's abstraction shows that (1) and (2) are all the progress proof uses of the algebra, plus (3) when lift is present and (4) when dispatch ignores type arguments.

---

## 3. Pitfalls and counterexamples

1. **An algebra that lets subeffecting hide a label** (Yoshioka Example 5.2, condition (1)): "∅ ⊢ op_l v : A | 0 can be derived … However, the operation call is not handled." Our `c1_of_rowSig` derives (1) from one signature object, and `not_der_unhandled` is the teeth.
2. **Handling one label erases another** (condition (2)): if `(l)↑ < (l′)↑`, then `handle_{l′} op_l v` is typed at `0`.
3. **Masking/lift with an idempotent algebra** (Thm 7.2). Sets and simple rows collapse `L ⊙ L` to `L`, so after `[e]_L` the handler for `L` appears to discharge both occurrences. Biernacki 2018's `n−free` counting is the operational side of the same fact.
4. **Dispatch that ignores type arguments, with a commutative algebra** (Thm 7.7). `Writer Int` and `Writer Bool` swap, so the inner handler receives an `Int` where it expects a `Bool`. The fix is to swap only distinct names (Ex. 7.8). The cost is that row variables no longer commute.
5. **Duplicate labels.** In scoped rows, handling removes one occurrence. In simple rows it may remove all, and that is safe only without lift. Yoshioka: removing `Exc` from `⟨Exc | ⟨Exc | ⟨Choice⟩⟩⟩` "can be ⟨Choice | ⟨⟩⟩" in simple rows, but only `⟨Exc | ⟨Choice⟩⟩` in scoped rows.
6. **Values escaping their handler** (System C §4.4; Met "escaping the scope of their handler"). Returning a closure over a capability or a label is where effect safety can fail. Boxes or absolute modalities record the capture.
7. **Accidental handling** (Zhang–Myers). This is an abstraction failure, not an effect-safety failure, but it is fixed by the same choices: instances, tunnelling or capabilities. SPEC §19 gives it as a reason for static names.
8. **Generative labels and reuse.** SPEC §19 (our own reasoning, "not built in Lean") argues that a freed and reused label could route an escaped continuation's operation to the wrong handler. Generative-label calculi avoid this by confining labels to their scope (Met(X) local labels, "cannot escape"; System C boxes).

---

## 4. Effect safety in the presence of borrows and lifetimes

- **Capabilities as lifetimes.** In System C, effect safety *is* a scoping theorem: Lemma 4 says every capability application sits under its delimiter. The survey reads this as "no capability is used after its handler frame has been popped. That is your outlives check" (survey A2). Conditions (1) and (2) become "nothing can be subsumed into the empty set" and "ending one handler's lifetime cannot discharge another's" (survey A2; this is the survey's synthesis, not a printed theorem).
- **Müller, Schuster, Starup, Ostermann, Brachthäuser 2023, *From capabilities to regions* (OOPSLA) [V].** A typed translation from System Ξ (second-class capabilities) to Λcap (regions with subregion evidence). It "connects the lexical scopes of the definition sites of capabilities in System Ξ with corresponding regions in Λcap", and "exposes the precise relation between the second-class property and the structure given by regions". Results: Thm 3.6 (typability preservation, from sound lifting environments, Lemma 3.5) and Thm 3.7 (evaluation). For us, this is formal evidence that a handler's dynamic extent can be a region, i.e. a lifetime. It is not an effect-safety theorem itself; effect safety transfers along the typability-preserving pipeline.
- **Rows say nothing about lifetimes** (survey §2 P6). In a row system, effect safety and lifetime soundness are separate theorems.
- **Our setting.** In BoLo a borrow is a lifetime-polymorphic second-class value: the `withbor` callback receives `'l` and `&'l T`, and cannot let it escape (6.60 outlives). So BoLo already has System C's mechanism. The notebook's HandlersAsBorrows experiment (`handle` as `withbor`, `effect_safety`, `handle_is_shift`, at the PAPER layer) is that reading. It is recorded as an optional realisation ([System A](../system-a.md): "Borrow-derived routes are optional").
- **The overlap point is I4** (answering effects are borrows). An answering handler is a lend, so its operations are calls on a borrowed capability, and for them P2 is B7. Control operations under static names are not borrows today: `Row.Unwind` and the T1/`↭` stop conditions are what forbid lends spanning resuming operations (BRIEF §3.1).
- **A lifetime-shaped instance of pitfall 4 to check.** SPEC §19 says "Operation types are closed in lifetimes, so every instance of a site has one protocol" and relies on this for re-entry of one static name. BRIEF §3.8 records that "neither `effPerform` nor `effHandle` requires it. Only `Row.Unwind` and `EffLeaf` do." If an operation type could mention a lifetime bound outside its site, two re-entrant instances of one name would carry different lifetime instantiations. That is Def. 7.6's shape, with lifetimes as the type arguments. `fundamentalC` covers both rules, so no stuck run can come of it at Core σ=[]. The question matters for the A-level reading, where `orowAlg`'s label has the single signature `Ξ n`, and at W. I have not built such a configuration and have not verified that it arises.

---

## 5. The menu

### 5.1 Representation (R)

**R1. Simple rows over static per-site names, no masking.** This is today's `orowRF`.
- *Statement:* S1 = `EffAlg.Laws` (Def 3.5) ∧ `EffAlg.Safe` (Def 5.1) ∧ `RowSig` ∧ `SubClosed`, with the algebra `orowAlg Ξ`: a closed first-match prefix plus an optional tail, `⊙` partial as for `EA_SimpR`, and `∼` meaning equal tails and equal first-match lookup.
- *How it relates to `EA_SimpR`:* by direct calculation from `Targets/Instance/Rows.lean` (not machine-checked), `orowAlg`'s `∼` contains `EA_SimpR`'s collapse rule and its swap rule for distinct names, because `RowEq` compares `Row.find` lookups. Instantiating Def. 7.1 at `ε₁ = (l)↑`, `n = 0`, `ε₂ = 0` gives `(l)↑ ⊙ (l)↑ ∼ (l)↑ ⊙ 0`. Condition (3) would then demand `(l)↑ ∼ 0`, which `RowSig` refutes. So **R1 cannot take a `mask`/lift without changing `∼`.**
- *Condition (4):* `orowAlg.Lab` is a name, and `lift n = Row.ofEff n (Ξ n) 0`. A label has no type arguments, so (4)'s premise forces `S₁ = S₂` trivially. The bridge's `orowAlg.WF` ties Core's row entries to `Ξ`.
- *Costs:* the bridges (`rowAlgebra_ourInst`, `effSafe_of_core`) are open. With one tail, `⊙` is undefined on `⟨…|ρ₁⟩ ⊙ ⟨…|ρ₂⟩` (Yoshioka Table 2). A function combining two independently-polymorphic callbacks must use one `ρ` plus `SubClosed` at each use. Whether `[sub]` reaches under a thunk (`U(F_ε A) ≤ U(F_ρ A)`) is a question about Core's value subtyping that I have not checked.
- *Buys:* the least proof burden; `rowAlgSafe_orowRF` is already proved. Static names give instances and E6 without masking (SPEC §19: "Distinct instances are distinguished lexically, as in Effekt's System Ξ").
- *Interactions:* E1/E2 need effect polymorphism (`not_noColouring_of_monoCallback`), which the tail variable supplies. P12's E6 is met by site freshness: decided (decision 57); to be checked by the elaborator (not built; P12 menu §6.2 (1)). P13: dispatch is by static name, so erasure is a direct call, branch or state machine per site.

**R2. R1 plus conditions (3)/(4) as checked guards.**
- *Statement:* add to S1 either (a) Yoshioka's conditions verbatim, guarded by instance flags (`HasLift → Cond3`, `DispatchErases → Cond4`), or (b) the facts that make them inapplicable, as conjuncts: `NoLift` (no former reinstates a label past its nearest handler), and `OneSigPerName` (dispatch by name reads a fixed signature, `∀ n, sig n` independent of the context). The second is where the lifetime question of §4 would surface.
- *Costs:* a few definitions and easy lemmas at our instance.
- *Buys:* RESTRUCTURE §1.5's prose ("Ours has no masking, and its labels are names without type arguments") becomes a statement that a later change must re-prove. Good-faith reading is unaffected.
- *Interactions:* generic sites (`Yield[T]`, `Fail[E]` at the surface) are elaborated per instance (SPEC §18: "elaborated once per assignment of its effects"). `OneSigPerName` is the kernel-side statement that this elaboration must respect. It is also a P13 obligation.

**R3. Rémy rows with lacks constraints / presence types.**
- *Statement:* as R1, but a row variable carries the set of names it lacks, and `[handle]`'s `n ∉ Σ` is checked against `Σ`'s prefix and its tail's lacks set. Optionally, presence `Pre(A) | Abs | θ` per label, as in Links.
- *Costs:* `RowCon` gains a lacks set. Its `adm : OpSig → Prop` can already express `o.n ∉ L`, so this may be a specialisation rather than new structure. The kinding rules must be preserved by substitution (Def 3.5's homomorphism clause, with `WF` indexed by lacks).
- *Buys:* `n ∉ Σ` survives any instantiation of `ρ`. E6's `PolyUseLacks` ("every ε without `li`") is exactly a lacks-kinded quantifier, so the A-level schema and the kernel rule coincide. Presence polymorphism helps handler composition (Hillerström–Lindley §2).
- *Interactions:* still simple rows, so the same conditions as R1 apply (Yoshioka Thm 5.9 covers `EA_SimpR`), and masking still needs R4.

**R4. Scoped rows (Koka).**
- *Statement:* `∼` is generated by `⟨L₁ | ⟨L₂ | ε⟩⟩ ∼ ⟨L₂ | ⟨L₁ | ε⟩⟩` for `L₁ ≠ L₂`, with no collapse. `[handle]` removes one occurrence, and S1 adds Def. 7.1. If dispatch ever erases type or lifetime arguments, the erasable variant (Ex. 7.8) is needed, and only `EA_EScpR` meets (1)–(4) (§7.3).
- *Costs:* the S1 proof grows by (3). `orowAlg`'s `∼` changes from lookup equality to an inductive equivalence. `[handle]`'s `n ∉ Σ` becomes unnecessary, and its removal changes Core's rule. Core's `Row.find` first-match reading already agrees with "innermost occurrence first".
- *Buys:* sound `mask`/lift (Thm 7.4), so a handler may skip its own instance. Re-entry of one site is typed by occurrence count instead of by the same-protocol argument. This is the standard if the kernel ever adopts dynamic, Koka-style instance selection.
- *Interactions:* with static names, this buys nothing E1–E10 asks for. It is an option to keep if generative or nested same-site instances (SPEC §19's "a site per level, which static names cannot give", L2 #173) are pursued.

**R5. Capabilities (System C / Ξ; via HandlersAsBorrows).**
- *Statement (S-d):* "every reachable configuration has no undelimited name: no `H_n[perform_n v]` without an enclosing `handle_n`". Effect safety is read through lifetimes: a handler opens a lifetime, operations are calls on a capability borrowed at it, and P2 is the instance of B7 (6.60) at capabilities.
- *Two ways to take it:*
  - (a) as a **proof route** for an unchanged S3: rows stay, and the bridge proves S3 by showing that every row entry is backed by a live lend. This is the notebook's "borrow-derived route".
  - (b) as a **replacement** for rows. This conflicts with decision 62 ("of course we have row variables in the kernel").
- *Costs:* storing an effectful value needs a box with a lifetime bound (OQ-28; System C boxes). Control operations are not lends today (the T1/`↭` stop, BRIEF §3.1), so (a) covers answering effects (I4) before control ones. SPEC §19's argument against generative labels must be met by scope confinement ("a scope-indexed thunk with no elimination to plain `U`", a T2 former we do not have).
- *Buys:* E6 by construction, P2 and P9 from one mechanism, and handler extents as lifetimes (Müller et al.). With answering effects as borrows, P2 for them is already B7.
- *Interactions:* the no-colouring axis is good: lifetime polymorphism instead of row polymorphism for called-only callbacks (foundations/second-class.md: "effect polymorphism without row variables for callbacks that are only called"). P12 by construction. For P13, Effekt's capability-passing compiles through regions to iterated CPS (Müller et al.).

**R6. Modal effects (Met(X)).**
- *Statement:* Thms 3.7 and 3.8 at an effect structure meeting TL Def 3.5. Our effect structure would be R1's or R3's algebra, with local labels for instances.
- *Costs:* a modal kernel (absolute and relative modalities on every function type). This is a different kernel, not a row choice, and the evidence is paper proofs only.
- *Buys:* rows and capabilities as encodings in one theorem. Met's stated aim is effect tracking without "extensive effect annotations" on existing code, which is the E1 axis.
- *Interactions:* decision 62's rows would become the effect structure of a modal kernel. This needs the user.

### 5.2 Statement and proof route (S)

- **S-a (today), progress-at-ε over reachable configurations.** It is as strong as System C Cor. 9, and stronger than Bauer–Pretnar Cor. 4.2. Its content at `0` comes from `RowSig` (`StopsIn 0` is empty).
- **S-b, terminating-only.** It follows from S-a and adds nothing. It is listed because Bauer–Pretnar and Links state it this way.
- **S-c, a static typing lemma.** Koka's Lemma 4.b at our instance would read `der Γ (plug K (perform l i v)) (F ε A) ∧ catches K l = false ⇒ has ε l i`. It is useful as a named lemma inside S-f. On its own it needs syntactic subject reduction, which Core lacks (RESTRUCTURE §1.5: the final value "may be a location, which its typing types semantically and not syntactically").
- **S-d, the capability form.** See R5.
- **S-e, corollary of the fundamental lemma (today, Core).** `effSafe_tier1` from FL, `FamEmpty` and `AdequateEvery`. It is the route of Biernacki 2018 (Thm 9 from Thm 8), Biernacki 2020 (Thm 2 from Thm 1) and Zhang–Myers (Thm 2 from Thm 1 and Lemma 6). It reaches W when FL does, and at W it is the only route available, since there is no syntactic preservation.
- **S-f, a generic A-level theorem.** Prove `RowAlgebra ∧ TypingRules ⇒ EffSafe` over any `EffectSystem`, which is Yoshioka Lemma 5.7 abstractly. Today S1 and S3 are separate (S) conjuncts, and S1's effect on S3 is only through `not_der_unhandled`.
  - *Buys:* S1 then carries S3's weight, as in Yoshioka and Met(X), and a second instance (or a changed row form under OQ-13) gets S3 by proving S1.
  - *Costs:* A gains typing rules for `perform`, `handle`, `[sub]` and `[let]`, against its design of "only the formers that its (S) properties and its (E) programs need" (System.lean header). It also needs an A-level subject reduction or relation, which A does not have.
- **S-g, trace over-approximation under every runner.** See §6.2.
  - *Statement:* `∀ R, R.Respects → ∀ e ε A, der [] e (F ε A) → ∀ c, RReach R (rinit R e) c → IsVal c.1 ∨ (∃ ev c', RStep R c ev c') ∨ StopsIn ε c.1`. Or the event form: every `.io l i v w` on an `RPath` from `rinit R e` has `has ε l i`.
  - *Costs:* runner answers must preserve typing, which is `Respects`'s job.
  - *Buys:* the brief's "the static effect over-approximates the dynamic one" on the observable trace, and a clean target for P13 (a lowering must emit only `ε`'s operations).

### 5.3 Masking, lift and instances: the sub-question

| choice | algebra needed | E6 / P12 | cost |
|---|---|---|---|
| static per-site names, no mask (today) | R1 or R3; Def 5.1 only | by site freshness | re-entry relies on "one protocol per name" (§4) |
| `mask`/lift | R4 (Def 7.1); erasable R4 if dispatch erases arguments | by mask, counted (Biernacki 2018) | Def 7.1 proof; Koka's own limit, quoted in docs/effects-scoping.md: `mask` needs "the exact number and order of handlers" |
| generative labels / local labels | a label kind separate from rows (TL §6.4: "local labels as sets and global labels as scoped rows") | by construction | scope confinement (T2 former); SPEC §19's reuse argument |
| capabilities | R5 | by construction | boxes; OQ-28 |

---

## 6. Where our current target sits

### 6.1 Position

- **Representation:** R1. `orowRF` is fixed in done until OQ-13's remaining question (RESTRUCTURE.md, "Done is fixed at `orowRF`"). Names are static per site, and there is no masking.
- **S1:** `RowAlgebra = Laws ∧ Safe ∧ RowSig ∧ SubClosed`, which is Def 3.5 + Def 5.1, plus one signature object (Kammar), plus subeffecting as a typing rule. Proved at the algebra: `rowAlgSafe_orowRF`, `rowLink_orowRF`. Open at our instance: `rowAlgebra_ourInst`. Conditions (3) and (4) are dismissed in prose (RESTRUCTURE §1.5), which is R1, not R2.
- **S3:** S-a, `EffSafe`: every `S.Reach` configuration is a value, steps, or `StopsIn ε`. It is open at our instance (`effSafe_of_core`). Core's form `EffSafe tier1` is proved at σ=[] by S-e.
- **Teeth:** `not_der_unhandled` and `c1_of_rowSig`, proved at every instance.
- **E6:** `Tunnel` with `PolyUseLacks`, an R3-shaped quantifier stated at A. At the kernel, `RowCon` carries a class and `adm` but no explicit lacks set.

### 6.2 Observations from reading, with no Lean checks run

1. **S3 does not cover runs after a platform answer.** `EffSafe` quantifies over `S.Reach`, the machine's own steps. `NoIO` says the machine never takes an `io` step, so every configuration after the first `RStep.io` is outside S3. S2 (`Safety`) covers those runs only as "never stuck" under runners with `Answers R ε`. A runner answering a strict superset of `ε` is not excluded from S2's quantifier. By reading, neither S2 nor S3 then says that a later unhandled operation lies in `ε`. I have not built an instance showing that the conjunction is weaker than S-g, and I have not verified that any gap is real. S-g is the candidate statement if the user wants the over-approximation clause on the trace. The literature offers no precedent: every cited statement is for closed programs without a platform.
2. **Conditions (3)/(4) are prose.** R2 would make them statements. By calculation (§5.1, R1), adding a lift to `orowAlg` breaks (3), which is Thm 7.2's shape.
3. **One tail variable** limits rows to `⟨prefix | ρ⟩` (Yoshioka Table 2). No (E) program is known to need `ρ₁ ⊙ ρ₂`. RESTRUCTURE notes that `timeout`'s schema "compose[s], and the second's row is below the composite", which goes through `SubClosed`.
4. **The lifetime-parametric operation question** (§4) belongs to R2's `OneSigPerName` and to B7. It is a question for W, not a claimed obstruction.

### 6.3 Inventory for this property

- **Untranscribed literature results in the run-up:**
  - Yoshioka Lemma 5.5 (progress at `ε`) and Lemma 5.7 have no A-level counterparts as lemmas (S-f).
  - Koka's Lemma 4.b has no counterpart (S-c).
  - System C's Lemma 4 has no counterpart (R5/S-d).
- **Unused results we have:** Core's first-match `Row.find`, which already reads rows innermost-first and would serve R4; and `RowCon.adm`, which could carry R3's lacks set.

---

## Sources

Verified for this note, from full text:

- Bauer, Pretnar. *An effect system for algebraic effects and handlers.* LMCS 10(4:9), 2014. Thm 4.1, Cor 4.2. https://arxiv.org/abs/1306.6316
- Pretnar. *An introduction to algebraic effects and handlers. Invited tutorial paper.* MFPS 2015, ENTCS 319. Thm 4.2. https://www.eff-lang.org/handlers-tutorial.pdf
- Leijen. *Type directed compilation of row-typed algebraic effects.* MSR-TR-2016-29 (the POPL 2017 paper's TR). Thm 1, Lemma 4. https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/algeff-tr-2016-1.pdf (POPL version: https://doi.org/10.1145/3009837.3009872, not read)
- Hillerström, Lindley. *Liberating effects with rows and handlers.* TyDe 2016. Def 3.2, Thm 3.3. https://homepages.inf.ed.ac.uk/slindley/papers/links-effect.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Handle with care: relational interpretation of algebraic effects and handlers.* POPL 2018. Thms 8, 9. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl18.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Abstracting algebraic effects.* POPL 2019. Thm 2.7. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf
- Biernacki, Piróg, Polesiuk, Sieczkowski. *Binders by day, labels by night: effect instances via lexically scoped handlers.* POPL 2020. Thms 1, 2. https://ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf
- Zhang, Myers. *Abstraction-safe effect handlers via tunneling.* POPL 2019. Thms 1, 2, Lemma 6. https://cs.uwaterloo.ca/~yizhou/papers/abseff-popl2019.pdf
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki. *Effects, capabilities, and boxes.* OOPSLA 2022. Author version: Def 8, Cor 9, Lemma 4, Thms 3, 5. https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf (ACM: https://doi.org/10.1145/3527320. The "Cor. 4.8" numbering cited elsewhere in the notebook is not verified.)
- Yoshioka, Sekiyama, Igarashi. *Abstracting effect systems for algebraic effect handlers.* ICFP 2024. arXiv v1: Defs 3.5, 5.1, 7.1, 7.6; Lemmas 5.5, 5.7; Thms 5.8, 5.9, 7.2, 7.4, 7.5, 7.7, 7.9, 7.10; Table 2. https://arxiv.org/abs/2404.16381 ; https://doi.org/10.1145/3674641
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen. *Modal effect types.* OOPSLA 2025. arXiv v3: Def 4.2, Thms 4.3, 4.4. https://arxiv.org/abs/2407.11816
- Tang, Lindley. *Rows and capabilities as modal effects.* POPL 2026. Defs 3.2–3.6, Thms 3.7, 3.8, §§2.4, 2.5.4, 6.3, 6.4. https://arxiv.org/abs/2507.10301
- Müller, Schuster, Starup, Ostermann, Brachthäuser. *From capabilities to regions: enabling efficient compilation of lexical effect handlers.* OOPSLA 2023. Lemma 3.5, Thms 3.6, 3.7. https://pure.au.dk/ws/files/404551780/3622831.pdf ; https://doi.org/10.1145/3622831

Cited without verification [U]:

- Brachthäuser, Schuster, Ostermann. *Effects as capabilities* (System Ξ). OOPSLA 2020.
- Xie, Cong, Ikemori, Leijen. *First-class names for effect handlers.* OOPSLA 2022. Its rank-2 scope safety is not read for this note.
- Osvald, Essertel, Wu, González Alayón, Rompf. *Gentrification gone too far? Affordable 2nd-class values for fun and (co-)effect.* OOPSLA 2016.
- Whether Biernacki et al. 2018/2020 are mechanised.

Local sources:

- `experiments/Targets/Targets/A/EffAlg.lean`
- `A/Soundness.lean` (S1, S3)
- `A/System.lean` (`Reach`, `RStep`, `NoIO`)
- `A/NonVacuity.lean` (`not_der_unhandled`, `c1_of_rowSig`)
- `A/Expressiveness.lean` (`Tunnel`)
- `Instance/Rows.lean` (`orowAlg`, `RowLink`)
- `Base/Rows.lean` (`RowCon`, `RowEq`)
- `RESTRUCTURE.md` §1.5
- `~/repos/borrow-core/SPEC.md` §18–§19 ("Names: which handler handles an operation", `[handle]`)
- `docs/effects-state/BRIEF.md` §3
- `research/effects/survey.md` A2, §1.8, §1.11, §2 P6
