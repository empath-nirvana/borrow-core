# 06 · The equational theory

This section states every law of the effect calculus (the `L-` ids of 00 §4) as a theorem over
the kernel: the machine of 04, the relation of 05 at the world `W`, and the typing judgement of
03. It also fixes the notions of equality the laws are stated in (O-EQ, which 00 §1 assigns to
this section). Laws come first: a construct of 02 or 03 is specified by the laws here together
with its rule, and a construct with no law entry is incomplete (00 §0.2 item 4).

Each law has up to four parts.

- **Binary form.** The equation, over contextual equivalence `≡` (§1.2).
- **Unary half.** What the law says about the kernel relation: an interchange of the two sides
  under every `ewp_W` specification (§1.4), or the `ewp_W` fact that the construct's
  compatibility lemma uses. It is proved, or to be proved, over D-EWP at `W` with no binary
  relation.
- **Route.** How the binary form is to be had: by **joinability** under one allocator (§1.3)
  with the step-inclusion obligation (§1.5), which is TwoRun's operational route and needs no
  binary relation; or by the binary relation `≈` (D-BIN), which waits on OQ-4.
- **Today.** Where any form of the law exists, kernel or experiment, cited `file:line`.

Entries use 00 §2's template. The fields *Binary*, *Unary* and *Route* are added after *Form*,
because 00 §8 asks this section for each of them per law.

Throughout, `n, m` are names with `n ≠ m` where both appear, `i` an operation index, `V, v`
values, `K` an evaluation context (`Kont`, `Paper/S3_Dynamics/Definitions.lean:384-420`), and

    op_{n,i}(V; y.M)  ≜  (λy. M) (perform_{n,i} V)          (the algebraic form of K-OP)
    hnd_n H M         ≜  hndE (hndVal n h_ret hs) M,  H = (h_ret, hs),  c_i the i-th clause of hs
    κ_n(H, K)         ≜  kappa n H K                    (Paper/S3_Dynamics/Definitions.lean:438)
    resume κ w ≜ κ (inj₁ ()) w        cancel κ ≜ κ (inj₂ ())
    ⊥_N               ≜  ⊥(N, none) = raise (cancelVal N none)  (a cancel of the region N, 04 §1)

`hndE`, `hndVal`, `clauseAt` and `cancelVal` are the kernel's (`[op]`, `[ret]`, `[unwind]`:
`Paper/S3_Dynamics/Definitions.lean:499-512`).

---

## 1. O-EQ: the equalities the laws are stated in

### O-EQ: equivalences
- Form: the four notions of §1.1-§1.4, and the binary relation `≈` of D-BIN as §1.6 requires it.
- Uses: O-JDG, O-TY, O-W, O-WP, O-EWP, O-REL, K-RUN, D-BIN.
- Today: none in Core. The only equivalence anywhere in the project is EffModelRel's `CtxEq`
  over a sibling calculus with no resources and no machine (`experiments/EffModelRel`; audit §2.1
  row S2). Every "law" in Core is a one-directional `Steps` fact about specific terms
  (`Core/Handlers.lean:76, 133, 153, 167, 211, 229`). New.
- Slices: contexts and judgements 03; runs and determinism 04; `≈` 05 (D-BIN); `T-2RUN`,
  `T-BINFP`, `T-SOUND` 07.
- Depends on: K-RUN (`AStep1.deterministic`, `Core/Demonic.lean:117`), T-ADEQ, T-FP.
- Open: OQ-4, OQ-11, OQ-47, OQ-43.
- Obligation: the definitions are mechanical. The step-inclusion theorem (§1.5) is **unknown**.

### 1.1 Typed program contexts

A program context `𝒞` is a term with one hole `[·]`, anywhere (under binders, in thunks, in
clauses). Its typing judgement

    𝒞 : (Δ; Γ ⊢ C) ⇒ (Δ'; Γ' ⊢ C')

holds when replacing the hole, read as a free computation constant typed `Δ; Γ ⊢ [·] : C`,
gives a `CDerives` derivation of `Δ'; Γ' ⊢ 𝒞[·] : C'`; one rule per `CDerives` rule with the hole
in one premise. A **closing** context has `Δ' = ∅`, `Γ' = []` and `C' = F_∅ G`, `G` a ground type
(built from `1`, `0`, `⊕`, `⊗`, `I32`, `I64`, booleans), so that its values hold no location.

`CDerives` has no hole judgement today (`Core/Fundamental.lean:60`). It is 03's judgement read
with one more axiom, the hole; it adds no rule to the calculus. Typed contexts are part of O-EQ
(00 §1).

### 1.2 Contextual equivalence `≡` and refinement `≲`

An **observation** of a closed `e : F_∅ G` under an allocator `A` is the value it reaches:

    Obs_A(e) = v   iff   ARun A 0 μ∅ e k' μ∅ (return v) for some k'

`μ∅` the empty memory. T-ADEQ (`adequacyD`, `Core/Demonic.lean:312`) gives, at every closed
well-typed `e`, a run under every allocator that ends at a value at the empty memory, and
`AStep1.deterministic` (`Core/Demonic.lean:117`) makes it the only run under that allocator. So
`Obs_A` is a total function on closed well-typed programs at `F_∅ G`. Under OQ-15 (a), the
default, termination is not observed, because every closed computation at `F_∅ G` terminates
(T-TOTAL, `Core/Totality.lean:40`); a looping `main` is observed one prefix at a time (SPEC §14
*The totality theorem*), and a law about div computations is stated at their observations
(L-DIV). This observation therefore depends on totality, which is not a goal (01 §4, U13): O-EQ
is among the things OQ-15 blocks. Under OQ-15 (b) a closed computation at `F_{div} G` may
diverge, `Obs_A(e) ∈ G_v ∪ {⇑}` is partial, and `≡` observes divergence: `M ≲ N` iff for every
closing context and allocator, `Obs_A(𝒞[M]) = v` implies `Obs_A(𝒞[N]) = v`, and `𝒞[M]⇑` implies
`𝒞[N]⇑`. Every law's binary form is then re-read at that observation (03 §9.2).

    Δ; Γ ⊢ M ≲ N : C   iff   Δ; Γ ⊢ M : C,  Δ; Γ ⊢ N : C,  and for every closing
                             𝒞 : (Δ; Γ ⊢ C) ⇒ (∅; [] ⊢ F_∅ G) and every allocator A,
                             Obs_A(𝒞[M]) = Obs_A(𝒞[N])
    Δ; Γ ⊢ M ≡ N : C   iff   M ≲ N and N ≲ M

Because `Obs_A` is total and single-valued, `≲` and `≡` coincide; `≲` is kept for laws whose
two sides are typed at different contexts (L-SUM absorption), where only one direction is typed.

The allocator is quantified outside the observation: two sides are compared under the same
allocator. A law whose two sides allocate in different orders (L-NU's ν/ν, L-STATE at a cell
allocated on one side only) needs the allocator to be invisible, which is TwoRun's
`freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`) and `fresh_run_image`
(`…/Sim.lean:274`) on fresh runs with no array step; OQ-43.

A row is a meta-index of the judgement (O-JDG; OQ-13). `≡` at `C = F_Σ A` compares
computations that may stop at `Σ`'s operations: the closing context supplies their handlers.

### 1.3 Joinability `⇣`

Two closed configurations are **joinable under `A` up to a relation `D`** when

    (μ, M) ⇣_A^D (μ, N)  iff  ∃ M' N' μ' k.  ARun A k₀ μ M k μ' M'  ∧  ARun A k₀ μ N k μ' N'  ∧  M' D N'

with the same allocation count `k₀` at the start and `k` at the end. `D` is `=` unless the law
names another: **deletion of plain frames** (L-ALG0, L-W), **relation of captured continuations**
(L-ALG, L-HFWD, L-NAH). A law is **reduction-shaped** when for every closing substitution `γ` of
its free variables and every memory, `M[γ] ⇣_A^D N[γ]` under every `A`. The reduction-shaped
laws are L-HRET, L-HOP, L-HFWD, L-ALG, L-ALG0, L-GEN, L-W, L-BETA, L-FIX, L-TAIL, the reduction
instances of L-EXC and L-YIELD, L-NAH given its unary premise, the β laws of §1A, L-CC, and L-TO
(its right unit and associativity joinable after capture, as L-ALG).

### 1.4 Unary interchangeability `≅_W`

The unary half of a law is stated in this form:

    M ≅_W N   iff   ∀ τ Tb Q.  TableOK Tb ∧ Tb.Irred  →  ( ewp_W(τ)(M){Tb}{Q} ⟺ ewp_W(τ)(N){Tb}{Q} )

    TableOK Tb  ≜  ∀ x. TableOK_x Tb          (D-TABLEOK, at every lend variable)

    Tb.Irred  ≜  every term a stop of Tb allows is irreducible: Tb (ls, σ) τ' t Φ ρ → ¬ ∃ μ μ' t'. Step1 μ t μ' t'

and its open form: `Δ; Γ ⊢ M ≅ N : C` iff for every `δ ∈ ⟦Δ⟧`, every `W`, and every `γ` with
`𝒢⟦Γ⟧_W δ γ`, `M[γ] ≅_W N[γ]` at the tables `⟦Σ⟧δ` of `C`'s rows. One direction (`⇐`) is the
**forward interchange**, the other (`⇒`) the **backward interchange**. `≅` implies that `M` and
`N` are in `𝒞⟦C⟧_W δ` together, since `𝒞⟦F_Σ A⟧` is `ewp` at `opTable ⟦Σ⟧δ`
(`cC_effOf`, `Core/EffRules.lean:73`).

`opTable T` and `cancelTab T N` stop only at `K[perform …]` with `K` free of the name, and at
`K[raise …]` with `K` catching nothing of the name (`Core/EffDefs.lean:131-167`); neither is a
redex, so both tables are `Irred`. `Irred` is needed only for the backward interchange: a run
`wpG` exhibits from a redex cannot end at the redex itself. `Irred` is conjunct (6) of
D-TABLEOK (05).

### 1.5 Step inclusion: the operational route (TwoRun)

Two metatheorems, owned here (00 §5.4), carry a reduction-shaped law to its unary half and to
`≡` without a binary relation. T-2RUN's law clause (07) is T-SI2 applied with determinism up to
renaming.

**T-SI1 (step interchange).** If `∀ μ. Head μ M μ N` and `M.allocs = false`, then `M ≅_W N` at
every `W`.
- Forward: `ewp_step` (`Core/EffWp.lean:936`) and `wpG_head` (`Core/EffWp.lean:973`); they do not
  inspect the term the run ends at, so they hold at every `W` once D-STOP changes only the stop
  (T-NIL, T-STOP).
- Backward: not built. From `wpG_W(M){Φ}` at a redex `M`, every exhibited run either takes the
  step to `N` (`AStep1.deterministic`) or ends at `M`; the second is excluded when `Φ` admits
  only values and `Irred` stops. **Mechanical**; the one step likely to be non-mechanical is
  peeling the first step off `ARun` inside `wpG`'s existential with the frame resources
  unchanged.

**T-SI2 (reduction in context is equivalence).** If a law is reduction-shaped (§1.3) with `D`
one of the named relations, then `M ≡ N` at the law's typing.
- Route: the relation "equal up to replacing instances `M[γ]` by `N[γ]`, closed under `D`" is a
  stuttering simulation of the machine under a fixed allocator. A step of the left side away from
  an instance is matched by the same step on the right (`Step1` is a context closure of `Head`,
  `Paper/S3_Dynamics/Definitions.lean:549`). A step at an instance is matched by the join. Both
  sides end at the same observation, since a closed `F_∅ G` run is total and deterministic
  (T-TOTAL, `AStep1.deterministic`).
- This is TwoRun's technique: `run_sim` (`experiments/TwoRun/TwoRun/Sim.lean:253`) is a
  simulation of the machine along a function, with no logical relation and no step index.
- **Unknown**: the closure of the replacement relation under substitution of an instance into a
  thunk that is later copied under `!` (`unr`), and under capture of an instance into `κ` by an
  outer `[op]`. OQ-47.

When T-SI2 holds, every reduction-shaped law's binary form follows from its join alone, and
OQ-4's option (b) carries those laws with no binary relation. The laws that compare two runs whose
reads differ (L-STATE, L-TENSOR) need, in addition, the read footprint of a well-typed callback,
`ReadFootprintTyped` (`experiments/TwoRun/TwoRun/Read.lean:81`), which is not derived; its untyped
form fails (`not_readFootprint`, `…/Read.lean:185`, at `peekE`, a term `CDerives` does not type).

### 1.6 What the laws need of `≈` (D-BIN)

The laws that are not reduction-shaped (L-HUNIQ, L-HFUSE, L-HCORR, L-STATE's equations,
L-TENSOR, L-ND, L-ETA's binary half, L-HIDE's binary half, L-INTER, L-NU, L-REN's binary half,
L-RUN's run-unique, the η laws of §1A)
need, of D-BIN (05):
1. `≈` is a relation over pairs of worlds `(W₁, W₂)`, indexed by D-REL's types, with one
   compatibility lemma per `CDerives` rule (T-BINFP);
2. it is sound for `≡` (T-SOUND);
3. at a `Mut` cell it relates the cell's contents by a relation chosen per cell (Ahmed, Dreyer &
   Rossberg, POPL 2009 [via 12-sources, TR §13.4, content recalled there]), which L-HIDE's binary
   half needs and EffModelRel's equality at ground states cannot give (TR §13.4, D13.11);
4. at an affine operation it compares destructor traces, and at a linear one it does not (the
   moded observation of #279's external input [via #279]), which L-ETA, L-INTER and ν/op need
   (TR §13.3 P13.9, §13.5, O1 at `experiments/EffModelRel/EffModelRel/Ownership.lean:93`).

Whether `≈` is in scope is OQ-4 (audit Q4). Its default is (b): every law is stated in its
binary form here, the reduction-shaped ones are carried by T-SI2, and the binary half of the rest
is marked not proved.

### 1.7 Laws over `W`

Each law below is stated over `W` (OQ-11 option (a)). Two cases.

- **Reduction-shaped laws** read the machine only. Their binary form does not mention `W`. Their
  unary half is T-SI1, whose forward direction is already world-independent (`wpG_step`,
  `Core/EffWp.lean:868`). They survive the re-index by T-NIL and T-STOP: **mechanical**.
- **Laws whose unary half inspects a stop** (L-ALG, L-ALG0, L-W, L-HFWD, L-BOR, L-HIDE) read the
  table's continuation obligation (`contShare`, `KapRel`, `cancelOwed`). At `σ = []` the existing
  lemmas are their unary halves. At `σ ≠ []` they depend on the form of D-STOP (OQ-10) and on
  where the future-world quantifier sits (OQ-8): **unknown**, and each entry marks it.

---

## 1A. Base laws: the theory the effect laws extend

Algebraicity and the handler laws are extensions of the base theory of the calculus, the β and η
laws of every former and the monad laws of `to` (Plotkin & Pretnar state the handler laws over
such a base; graded algebraicity generalises `to`'s associativity). These are stated here, each
with the same fields. "Reduction-shaped" laws get their binary form from T-SI2 (§1.5); η laws and
the right unit at an effectful `M` are not reduction-shaped and need `≈` (OQ-4) or a join after
capture. Every unary half below is an interchange `≅_W` (§1.4) at every `TableOK` table.

### L-TO: the monad laws of `to`
- Form.

      (left unit)   return V to x. N            ≡  N[V/x]
      (right unit)  M to x. return x            ≡  M
      (assoc)       (M to x. N) to y. P         ≡  M to x. (N to y. P)          x ∉ fv(P)

  at `F_Σ`, with K-LET's graded side condition on the context each continuation captures.
- Binary: as above.
- Unary: left unit is T-SI1 at the `beta` step. Right unit and associativity: both sides stop at
  the same operations with continuation shares that differ by a plain frame, `(λx. return x)[·]`
  or the regrouping of `(λy.P)[(λx.N)[·]]` into `(λx. (λy.P) N)[·]`, so the interchange is
  `ewp_frame_plain` (`Core/EffRules.lean:193`) read twice, as for L-ALG.
- Route: left unit reduction-shaped (one `beta`), T-SI2. Right unit and associativity are joinable
  after capture, with `D` relating the two captured continuations (§1.3, as L-ALG); at a value they
  are reduction-shaped. T-SI2 with that `D`.
- Today: the `beta` step (`Paper/S3_Dynamics/Definitions.lean:446`); `bind_compatC`
  (`Core/Compat.lean:179`) for the pure case. Not stated as laws. New.
- Depends on: T-SI1, T-SI2; L-ALG's capture-relating `D`.
- Open: OQ-47, OQ-11.
- Obligation: left unit **mechanical**; right unit and associativity **mechanical** given
  T-SI2 at the capture-relating `D`, which is **unknown** (OQ-47).

### L-UF: thunk and force
- Form. `force (thunk M) ≡ M` (β, at every `C`); `thunk (force V) ≡ V` at `U C` (η).
- Binary: as above. Unary: β by T-SI1 (`forceE`'s steps, `Core/Relation.lean:64-67`); η has no
  unary content beyond `𝒱⟦U C⟧`'s clause reading `force`.
- Route: β reduction-shaped, T-SI2; η needs `≈` (a value compared under every context that
  forces it), OQ-4.
- Today: not stated. New. Open: OQ-4, OQ-47. Obligation: β **mechanical**; η **unknown**.

### L-LAM: functions
- Form. `(λx. M) V ≡ M[V/x]` (β); `λx. M x ≡ M` at `A ⊸ C`, `x ∉ fv(M)` (η).
- Binary/Unary: β by T-SI1 at `beta`; η by `≈`.
- Route: β T-SI2; η OQ-4. Today: `beta` step. Obligation: β **mechanical**; η **unknown**.

### L-AMP: computation records
- Form. `πᵢ ⟨M₁, M₂⟩ ≡ Mᵢ` (β); `⟨π₁ M, π₂ M⟩ ≡ M` at `C & D` (η).
- Route: β T-SI2 (the `case` steps of the encoding, `Core/Relation.lean:158-160`); η OQ-4.
- Obligation: β **mechanical**; η **unknown**.

### L-PAIR: tensors
- Form. `let (x, y) = (V, W) in M ≡ M[V/x, W/y]` (β); `let (x, y) = V in M[(x, y)/z] ≡ M[V/z]`
  at `A ⊗ B` (η).
- Route: β T-SI2 (`letpair`); η OQ-4. Obligation: β **mechanical**; η **unknown**.

### L-CASE: sums
- Form. `case inⱼ V {inₖ x. Mₖ} ≡ Mⱼ[V/x]` (β); `case V {inⱼ x. M[inⱼ x/z]} ≡ M[V/z]` at
  `A ⊕ B` (η).
- Route: β T-SI2 (`case₁`, `case₂`); η OQ-4. Obligation: β **mechanical**; η **unknown**.

### L-BANG: the `!` modality
- Form. β: eliminating a promoted value gives the value (`bangE`, `Core/Fundamental.lean:133`); η
  at `!A`. `copyBang`/`forgetBang` are the structural rules L-P relies on.
- Route: β T-SI2; η OQ-4. Obligation: β **mechanical**; η **unknown**.

### L-ALL: lifetime abstraction
- Form. `(Λ'x. M) [] ≡ M` at an instance (β); `Λ'x. (M []) ≡ M` at `∀'x ⊏ c. C` (η). Lifetimes
  are ghost, so β is one `beta` step on the unit argument.
- Route: β T-SI2; η OQ-4. Obligation: β **mechanical**; η **unknown**.

### L-NUB: codata introduction and elimination
- Form. `out (in M) ≡ M`, `in (out M) ≡ M` at `νX. C` (`nuIn`/`nuOut` act on the same term,
  `Core/Fundamental.lean:331-334`); the coiteration laws are L-DIV's.
- Route: both are identities on terms: **as built**.

### L-CC: commuting conversions
- Form. For a plain `K` under L-ALG's side condition:
  `K[case V {inⱼ x. Mⱼ}] ≡ case V {inⱼ x. K[Mⱼ]}` and `K[let (x, y) = V in M] ≡ let (x, y) = V in K[M]`.
- Route: reduction-shaped (the left side's `case`/`letpair` step happens inside `K`; the right
  side's at the top), T-SI2. Obligation: **mechanical** given T-SI2.

---

## 2. Algebraicity

### L-ALG: graded algebraicity
- Form. For `K` **plain** (no handler frame, catches no name, no handler names:
  `∀m. K.HasHnd m = false`, `∀m. K.Catches m = false`, `K.hndNames = []`,
  `Paper/S3_Dynamics/Definitions.lean:386-420`), `y ∉ fv(K)`, and an operation
  `op_{n,i} : A ↠^q B` of `Σ`:

      Δ; Γ_K, Γ ⊢  K[op_{n,i}(V; y.M)]  ≡  op_{n,i}(V; y. K[M])  : F_Σ R

  under the **graded side condition** on `Γ_K` (the free context of `K`), read from `q` as a
  grade (O-QUAL):

      q = lin : none          q = aff, or op abortive : Γ_K Drops          q = unr : Γ_K persistent

  This is `[let]`'s side condition (`let_compatC`'s `hW`, `hU`, `Core/EffRules.lean:897`) and
  `ewp_frame_plain`'s (`hW`, `hU`, `Core/EffRules.lean:198-200`). The context enters every
  continuation additively (Staton, POPL 2015 §2 [via #235]), is dropped where the continuation
  may be weakened, and is contracted where it may be copied (Tang, Hillerström, Lindley & Morris,
  POPL 2024 §2.2 [via #235]).
- Binary: as above.
- Unary: `ewp_frame_plain` (`Core/EffRules.lean:193`) is the unary half at `σ = []`. An `ewp` of
  `M` at `opTable T`, with `K`'s context `Fr` beside it, gives an `ewp` of `K[M]`: at a perform,
  `Fr` joins the continuation's share (empty at `unr`); at a cancel or an abortive stop, `Fr` is
  left behind holding nothing owned. It is the "op stopped under `K` at grade `q` owes `K`'s
  share scaled by `q`" of 00 §4. The interchange form `K[op(V;y.M)] ≅_W op(V; y.K[M])` is the
  same lemma read twice: both sides stop at the same operation with the same continuation share,
  `Fr` inside `κ` on the left and inside the closure `λy. K[M]` on the right.
- Route: joinable after capture. Neither side steps until an outer `[op]` of `n` captures it,
  with context `K_out[K[(λy.M)[·]]]` on the left and `K_out[(λy.K[M])[·]]` on the right. At
  `resume … w` both reach `hnd_n H K_out[K[M[w/y]]]` in the same number of `beta` steps. At
  `cancel` the cancel passes `K` on the left (it catches nothing) and the closure on the right,
  and both reach the same `ccatch` configuration up to the deleted plain frame. So `D` relates
  `κ_n(H, K_out∘K∘(λy.M)[·])` with `κ_n(H, K_out∘(λy.K[M])[·])`. Binary form by T-SI2.
- Uses: K-OP, K-LET, K-CTX, K-KONT, K-GRADE, O-QUAL, D-SHARE, D-OPTAB.
- Today: the `[op]` step reifies `K` (`Paper/S3_Dynamics/Definitions.lean:502`), so the
  operation floats past `K` by construction; the unary half is `ewp_frame_plain`, used by
  `let_compatC` (`Core/EffRules.lean:896`). The four encodings the audit lists (`[let]`,
  `[then]`, `kTy`, `contShare`; audit M12) are this law at four frames. EffModelRel's `alg_bind`,
  `alg_app`, `alg_prj1`, `alg_prj2`, `alg_iapp` (`experiments/EffModelRel/EffModelRel/Laws.lean:67,
  76, 85, 90, 96`) are its binary form in a sibling calculus. Changed (stated once).
- Slices: `[let]` 03; `[op]` 04; `contShare` and T-MODEL's M3 05; T-COMPAT of `[let]` 07.
- Depends on: K-CTX, D-SHARE; L-W for the cancel half at non-plain frames.
- Open: OQ-11, OQ-16 (the `unr` grade), OQ-8 (the share's quantifier at `σ ≠ []`), OQ-47, OQ-65
  (R-ALGPLAIN).
- Obligation: unary half at `σ = []` **as built**. At `W`: **unknown** (the share of a stop that
  leaves frames open, OQ-10). Binary: T-SI2, **unknown**.

**At a non-plain frame.** A finaliser frame `ubind(N, D)`, a handler frame of another name, or a
borrow frame is not plain. There the law splits.
- A handler frame of `m ≠ n` is L-HFWD.
- A finaliser frame is L-HOP plus L-W: `κ`'s cancel entry runs the frame's finaliser, and no
  term `op(V; y. K[M])` carries that finaliser, because the kernel has no operation form with an
  explicit cancel continuation.
- A borrow frame is plain at run time (the lend is ghost, 05) and is L-BOR's resuming half.

So L-ALG's binary form is stated at plain frames, at handler frames of other names (L-HFWD) and at
borrow frames (L-BOR), not at finaliser frames: that is the named restriction R-ALGPLAIN, the
default of OQ-65, whose option (b) writes the derived form `op(V; y.M | D)` that would carry the
finaliser. The general statement is the unary one: the share of every frame on the path, scaled by
`q`, plus `D_K` under weakening (T-MODEL M3, 05).

### L-ALG0: algebraicity at arity 0, destructor form
- Form. Let `K` contain no handler frame of `n`, no `ccatch` and no `cfin` frame. Write `K°` for
  `K` with its plain frames deleted, a stack of finaliser frames `ubind(N_j, D_j)`, `j = 1`
  innermost. Define `D_K⟨e⟩ ≜ K°[e]`. Then

      K[raise_{n,i} V]  ≡  D_K⟨raise_{n,i} V⟩

  and, when every `D_j ()` answers `()` without raising, `D_K⟨raise_{n,i} V⟩ ↦* raise_{n,i} V`
  having run `D_1 (), …, D_k ()` in that order (LIFO). `D_K⟨e⟩ = K°[e]` is used only at a raise or
  a cancel, where each frame's `[finalise]` or `[finalise-cancel]` fires; at an `e` that returns,
  `K°[e]` would run the frames' continuations `N_j` by `[then]` (04:187), not their finalisers. For
  an `e` that may return, the sequential form `D_K ▷ e` (O-FIN) runs `D_1 (), …, D_k ()` LIFO, each
  under the frames outside it, a finaliser's raise superseding and finalised outward, and then `e`
  outside all of them. When some `D_j ()` raises `m`, its raise
  supersedes `raise_{n,i} V` and is finalised by the frames outside `j` (SPEC §19 *Cancels*,
  last bullet but one). Congard, Munch-Maccagnoni & Douence (ESOP 2026, arXiv 2510.23517,
  abstract read for this section) frame the problem as the strength of `T(− ⊕ E)` and introduce
  destructors `δ : A → TI`. That arity-0 algebraicity in the linear setting needs a destructor for
  every type, and that this restores the strength, is this section's inference [I] from that
  abstract, not a statement of the paper.
- Binary: as above.
- Unary: `opTable`'s abortive branch owes no continuation (`Core/EffDefs.lean:163-167`), and an
  abortive stop under a plain frame leaves `Fr` behind with nothing owned (`ewp_frame_plain`'s
  raise case, `Core/EffRules.lean:237-242`). Under a finaliser frame, `ewp_frame_then`
  (`Core/EffRules.lean:369`) runs `D` on the frame before the raise goes on. Together these are
  `K[raise V] ≅_W D_K⟨raise V⟩` at `σ = []`.
- Route: reduction-shaped up to deletion of plain frames. `[finalise]`
  (`Paper/S3_Dynamics/Definitions.lean:517`) discards the plain frames between the raise and its
  catcher in one step on both sides, and `[unwind]` (`:508`) discards the rest. Binary form by
  T-SI2.
- Uses: K-RAISE, K-THEN, K-CTX, O-FIN, D-DTOR.
- Today: `[finalise]`; `then_compatC` (`Core/EffRules.lean:928`); EffModelRel `alg_ab_bind`,
  `alg_ab_app`, `alg_dtor` (`experiments/EffModelRel/EffModelRel/Laws.lean:102, 107, 114`; the
  last proves one frame); the TR's T7.3 on paper, any context (`docs/effects-tr/07-laws.md` §7.1).
  `abort_passes` and `loop_abort` (`Core/Handlers.lean:153, 229`) are its form in the withdrawn
  sum encoding (decision 52; audit M10). Changed.
- Slices: `[then]` 03; `[finalise]` 04; D-DTOR 05; T-FIN 07; branch lowering 08.
- Depends on: D-DTOR (`D_K` is `K°`, O-FIN).
- Open: OQ-7 (finalisers at non-abortive rows), OQ-21 (what a finaliser performs and the policy
  for its raise), OQ-24 (an abortive payload that owns: today `NoOwn`), OQ-47.
- Obligation: unary at `σ = []` **as built** (two lemmas). Binary: T-SI2, **mechanical** given
  T-SI2; the one non-mechanical step is the deletion relation's closure under `[cfin-raise]` when a
  finaliser raises a name of the region.

### L-GEN: generic effect and algebraic operation
- Form.

      op_{n,i}(V; y.M)  ≡  (λy. M) (perform_{n,i} V)          (definition)
      perform_{n,i} V   ≡  op_{n,i}(V; y. return y)

  The first is the definition of the algebraic form. The second is L-ALG at the plain frame
  `(λy. return y)[·]`, whose context is empty, followed by one `beta` step after resumption.
  Generic effects, algebraic operations and, in the linear setting, state access operations are
  three equivalent presentations (Plotkin & Power, ACS 2003; Møgelberg & Staton, LMCS 2014,
  §8.1.1 and Thm 8.1 [via #235]). The third is L-STATE's form, for a capability.
- Binary, Unary, Route: those of L-ALG at an empty frame. **Mechanical** given L-ALG.
- Uses: K-OP, K-LET.
- Today: not stated. `op_tail` (`Core/Handlers.lean:76`) is the generic-effect form of one
  answering operation. New.
- Slices: 03 (no new rule).
- Depends on: L-ALG.
- Open: OQ-1 (whether the state-access presentation of an answering operation is the same law).
- Obligation: **mechanical**.

---

## 3. Handler laws

A handler `H` of `n : E` into `F_Σ R` is a model (O-MODEL): `h_ret : retTy Σ A R`, the clauses
`hs : clausesTy Σ R E` (`Core/EffRules.lean:989, 994`), each `!`, a clause at a resuming
operation receiving `κ : kTy Σ R q B` (`Core/EffRules.lean:976`). The body is typed at
`n:E ⊕ Σ` with `n ∉ Σ` (`handle_compatC`, `Core/EffRules.lean:1092`).

### L-HRET: handler return
- Form. `hnd_n H (return V)  ≡  h_ret V`.
- Binary: as above.
- Unary: `hnd_n H (return V) ≅_W h_ret V`. Forward: `wpG_head` at `[ret]`, as `ewp_handle`'s
  return case uses it (`Core/EffRules.lean:642-644`). Backward: T-SI1.
- Route: one `[ret]` head step (`Paper/S3_Dynamics/Definitions.lean:499`), allocation-free.
  Binary by T-SI2.
- Uses: K-HND, K-STEP, K-MODEL.
- Today: the step; EffModelRel `h_ret` (`experiments/EffModelRel/EffModelRel/Laws.lean:148`) in
  the sibling; `return_resumes` (`Core/Handlers.lean:167`) for the withdrawn encoding. Changed
  (stated over `hnd`).
- Slices: `[handle]` 03; `[ret]` 04; T-MODEL 05; T-ELAB 08 (every surface schema meets it).
- Depends on: T-SI1, T-SI2.
- Open: OQ-47.
- Obligation: **mechanical** given T-SI1 and T-SI2.

### L-HOP: handler operation (deep)
- Form. For `K` with `K.HasHnd n = false`:

      hnd_n H (K[perform_{n,i} V])  ≡  c_i (V, κ_n(H, K))                    (resuming op_i)
      hnd_n H (K[raise_{n,i} V])    ≡  c_i V          if K.Catches n = false (abortive op_i)

  with `resume κ_n(H, K) w ↦* hnd_n H K[w]` (L-BETA) and
  `cancel κ_n(H, K) ↦* ccatch (hnd_n H K[⊥_N])`, `N = n :: K.hndNames` (L-W). In Plotkin-Pretnar
  form, at `K = (λy.M)[·]`:
  `hnd_n H (op_{n,i}(V; y.M)) ≡ c_i (V, ⟨λy. hnd_n H M, ccatch (hnd_n H (λy.M)[⊥_N])⟩)`,
  whose cancel entry reduces to `()` (Plotkin & Pretnar, LMCS 2013 [via #235]; the cancel entry
  is the linear addition, TR T13.2(3)). The abortive case with finaliser frames in `K` is L-ALG0
  first: `hnd_n H (K[raise_{n,i} V]) ≡ hnd_n H (D_K⟨raise_{n,i} V⟩) ≡ D_K ▷ c_i V` when every
  finaliser answers `()` without raising (`[finalise]` at each frame, then `[unwind]` outside them).
- Binary: as above.
- Unary: forward is `ewp_handle`'s two cases at the handler's name (`Core/EffRules.lean:648-660`
  resuming, `:675-682` abortive), with `κ` in `KapRel` (`Core/EffRules.lean:569`). Backward: T-SI1.
- Route: one `[op]` or `[unwind]` head step (`Paper/S3_Dynamics/Definitions.lean:502, 508`).
  Binary by T-SI2.
- Uses: K-HND, K-KONT, K-OP, K-RAISE, K-STEP, D-KAP.
- Today: the steps; EffModelRel `h_op` (`experiments/EffModelRel/EffModelRel/Laws.lean:164`).
  Changed.
- Slices: `[handle]`, `kTy` 03; `[op]`, `[unwind]` 04; `KapRel`, T-MODEL 05.
- Depends on: L-BETA, L-W, L-ALG0.
- Open: OQ-3 (whether the site opens a lifetime: then `κ`'s relation changes, not the
  equation), OQ-25 (handler state), OQ-47.
- Obligation: **mechanical** given T-SI1, T-SI2.

### L-HFWD: forwarding
- Form. For `m ≠ n`:

      hnd_n H (op_{m,i}(V; y.M))  ≡  op_{m,i}(V; y. hnd_n H M)             (resuming op_{m,i})
      hnd_n H (K[raise_{m,i} V])  ≡  K[raise_{m,i} V]  modulo the hnd_n frame   (abortive)

  The second is L-ALG0: the handler frame catches nothing of `m` (`hndK_catches`,
  `Core/EffRules.lean:556`) and is deleted with the plain frames. The resuming form needs `H`
  duplicable at an `unr` operation of `m`; clauses are `!` (Tang et al.'s T-Handler [via #235]).
- Binary: as above.
- Unary: `ewp_handle`'s forwarding cases (`Core/EffRules.lean:661-672`, `:683-689`): the stop
  passes outward with the handler frame reinstalled in its continuation, `(hndK H).comp K₁`, and
  its cancel passes the frame by `cancel_frame` (`Core/EffRules.lean:168`).
- Route: joinable after capture, as L-ALG with `K = hnd_n H [·]`. That frame is not plain, but it
  catches nothing of `m` or of `0` (`hn0`), so the `D` of L-ALG applies unchanged. The relation
  must hold only at `e = perform_{m,i} V` in the hole. At a general `e` it fails: the left frame
  catches `n` and the right does not. Binary by T-SI2.
- Uses: K-HND, K-CTX, K-ROW.
- Today: the stop configurations in `handle_compatC` (`Core/EffRules.lean:1092`); EffModelRel
  `h_fwd`, `h_fwd_ab` (`experiments/EffModelRel/EffModelRel/Laws.lean:202, 227`). Changed.
- Slices: `[handle]` 03; K-CTX 04; `ewp_handle` 05.
- Depends on: L-ALG, L-ALG0.
- Open: OQ-14 (re-entry of a site resolves dynamically: forwarding to "the next handler of `n`"
  is the one non-lexical case), OQ-47.
- Obligation: unary **as built** at `σ = []`, **unknown** at `W` (the reinstalled frame under
  D-STOP, and OQ-3 for a handler between two lenders). Binary: T-SI2.

### L-HUNIQ: uniqueness of handling (initiality)
- Form. Let `f : U(F_{n:E ⊕ Σ} A) ⊸ F_Σ R` satisfy, at every `V`, `M` and `K` free of `n`,

      (H0) f ≡ λt. 𝒞[force t]  for an evaluation context 𝒞 (K-CTX)          (added hypothesis)
      f (thunk (return V))             ≡  h_ret V
      f (thunk K[perform_{n,i} V])     ≡  c_i (V, ⟨λy. f (thunk K[y]), cancel_f⟩)   (op_{n,i} resuming)
      f (thunk K[raise_{n,i} V])       ≡  D_K ▷ c_i V      K catching nothing of n  (op_{n,i} abortive)
      f (thunk op_{m,i}(V; y.M))       ≡  op_{m,i}(V; y. f (thunk M))           (m ≠ n, resuming)
      f (thunk K[raise_{m,i} V])       ≡  D_K⟨raise_{m,i} V⟩   K catching nothing of m  (m ≠ n, abortive)

  where `cancel_f` is the cancel entry `κ_n(H, K)` has, and `D_K` the destructor of `K` (O-FIN).
  The third line uses the sequential form `D_K ▷ c_i V`: the finalisers of `K` run first, LIFO,
  each under the frames outside it, and then the clause outside all of them, which is what
  `hnd_n H` does (`[finalise]` at each frame, then `[unwind]`). `D_K⟨c_i V⟩ = K°[c_i V]` would
  instead run the clause inside `K`'s finaliser frames and feed its answer to their continuations,
  and `hnd_n H` would not satisfy it at any `K` with a finaliser frame. The fifth line is at a
  raise, where `D_K⟨·⟩` is the right form. The two abortive lines are needed because `raise` is an
  arity-0 operation of `E` (02 K-SIG): Plotkin-Pretnar uniqueness asks `f` to be a homomorphism for
  every operation of the theory, and without them `f` is undetermined on any `M` that raises.

  **The added hypothesis (H0).** The universal property is one of the free model: "the universal
  property of the free model `Tree_Σ(X)` provides a unique Σ-homomorphism `r_X : Tree_Σ(X) → T X`,
  satisfying the equations `r_X(return x) = η_X(x)`, `r_X(op(a, κ)) = op_M(a, r_X ∘ κ)`" (Ahman &
  Bauer, arXiv 1910.11629, §2.2, proof of Prop. 3, read), whose every element is a return or an
  operation node. Here `M` ranges over computations that may first take steps of the BoLo store
  (load, store, alloc, the borrow constants) on cells of `Γ`; `≡` does not identify such an `M`
  with its reduct, and the heap is an ambient effect outside `n:E ⊕ Σ`. The five lines fix `f`
  only at a return, a perform, a raise, or an operation of another name. (H0) supplies what the
  free-model reading assumes: `f` acts on `M` only by running it inside a context, so it is
  transparent to `M`'s silent and store steps. It is non-vacuous: `hnd_n H` satisfies it with
  `𝒞 = hnd_n H [·]` (`hnd_n H M = (λt. hnd_n H [force t]) (thunk M)` by `beta` and `forceE`).
  Its scope is L-HUNIQ and the laws derived from it (L-HBIND, L-HFUSE, L-ETA). Then
  `f (thunk M) ≡ hnd_n H M` at every `M`. The ordering is on the least fixed point: `ewp` is total correctness, so every `M` in
  `𝒞⟦F_{n:E⊕Σ} A⟧_W` performs finitely many operations on every path, and the proof is
  induction on D-EWP's least fixed point. Handling is the unique homomorphism out of the free
  model (Plotkin & Pretnar, LMCS 2013, abstract, §1, §4 [via #235]).
- Binary: as above. Needs `≈`, or the TwoRun form below.
- Unary: **initiality of the least fixed point among models**, which is T-MODEL's M2 (05):
  `ewp_handle` (`Core/EffRules.lean:615`) is its present form. Its hypotheses `hret` and `hop`
  say that the predicate `ewp_W(·){opTable Tout}{Qout}` is closed under the clauses, i.e.
  `IsModel` (D-MODEL). Its conclusion says that handling maps the least fixed point into it.
  This is the unary content of uniqueness: every `IsModel` predicate contains the handled body.
- Route: TwoRun's operational form is "reaches one common value". For a one-operation free
  theory over a pure total algebra, `handle_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/
  Handler.lean:59`, from `fold_unique`, `…/Fold.lean:207`) proves that every homomorphism reaches
  the handler's value on every finite tree. The kernel form, over `hnd` with `κ` and at every
  row, is not built. Its route is induction on D-EWP's least fixed point, the silent and store
  steps of `M` carried through `𝒞` by (H0) and T-SI2, with one case per kind of final
  configuration: a value (the first line), a resuming stop of `n` (the second), an abortive
  stop of `n`, which reaches `D_K` and then the clause (the third, the arity-0 case: `hnd_n H`'s
  `[unwind]` after `[finalise]` at each finaliser frame, 04 §5.2 item 4), a resuming stop of `m`
  (the fourth), and an abortive stop of `m`, which passes `hnd_n H` (the fifth, L-ALG0 with the
  handler frame deleted). Each hypothesis is read as joinability, with T-SI2 at each step. **Unknown**: the case where `f`'s clause cancels, which
  compares `cancel_f` with `κ`'s cancel run.
- Uses: K-HND, K-MODEL, D-MODEL, D-EWP.
- Today: unary as `ewp_handle`, a case analysis rather than a stated initiality (audit §3.2);
  binary only in CoeffectsStrict (one effect, pure algebra) and EffModelRel's denotational
  model; `handle_fold` (`Core/Handlers.lean:211`) is the answering fold, not uniqueness. New.
- Slices: T-MODEL 05; T-ELAB 08 (a surface schema meeting the three laws is `hnd`).
- Depends on: L-HRET, L-HOP, L-HFWD, L-ALG0, L-W; D-MODEL (whose abortive conjunct is the
  unary form of the third line).
- Open: OQ-4, OQ-5, OQ-47.
- Obligation: unary (M2) **mechanical** from `ewp_handle`, restated. Binary: **unknown**.

### L-HBIND: handling a sequence
- Form. For `x ∉ fv(H)`:

      hnd_n H (M to x. N)  ≡  hnd_n (λx. hnd_n H N, hs) M

  the handler of `M` whose return clause handles the rest. It is the standard consequence of deep
  handling used by the lowering (the continuation of a driver is the handled rest) and by L-YIELD's
  loop threading.
- Binary: as above.
- Unary: both sides are in every `IsModel` predicate that contains the other (T-MODEL M2 applied
  to `M`, then to `N` at the return clause).
- Route: a corollary of L-HUNIQ: the left side, as a function of `M`, satisfies L-HUNIQ's five
  hypotheses for the handler `(λx. hnd_n H N, hs)`. Where `M` returns, the law is
  reduction-shaped: `[ret]` and `beta` on both sides, T-SI2.
- Uses: K-HND, K-LET. Today: not stated. New.
- Depends on: L-HUNIQ, L-TO.
- Open: OQ-4, OQ-47.
- Obligation: at a returning `M` **mechanical** given T-SI2; in general as L-HUNIQ's binary half,
  **unknown**.

### L-HFUSE: fusion
- Form. For `H₁` a handler of `n₁` into `F_{n₂:E₂ ⊕ Σ} R₁`, `H₂` a handler of `n₂` into `F_Σ R₂`, and
  `M : F_{n₁:E₁ ⊕ Σ} A` whose row **excludes `n₂`** (otherwise `H₂` handles `M`'s own `n₂`
  operations on the left while a one-name `hnd_{n₁}` forwards them on the right, and the two sides
  are not at the same type):

      hnd_{n₂} H₂ (hnd_{n₁} H₁ M)  ≡  hnd_{n₁} (H₂ ∘ H₁) M

  `H₂ ∘ H₁` is a handler of `n₁` into `F_Σ R₂`, so its clauses have the types `[handle]` gives at
  that carrier:

      return clause   λx. hnd_{n₂} H₂ (h₁_ret x)                                : !U(A ⊸ F_Σ R₂)
      clause i        λ(v, κ). hnd_{n₂} H₂ (c₁_i (v, κ̂))                        : !U(A_i ⊗ K_q(B_i, Σ, R₂) ⊸ F_Σ R₂)
                      where c₁_i needs κ̂ : K_q(B_i, n₂:E₂ ⊕ Σ, R₁)

  The composite's `κ` lands in `F_Σ R₂`; `c₁_i` needs `κ̂` landing in `F_{n₂:E₂⊕Σ} R₁`. No term of
  the kernel is known to turn the one into the other, which is OQ-49. At a clause `c₁_i` that
  resumes in tail position, `κ̂` is not needed: the composite clause is
  `λ(v, κ). hnd_{n₂} H₂ (g₁ v) to r. resume κ r` for `c₁_i = λ(v, κ̂). g₁ v to r. resume κ̂ r`, which is
  well-typed. The law is stated at that case by default (R-FUSETAIL). That it follows from L-HUNIQ
  is not claimed until `H₂ ∘ H₁` is a well-typed model; where it is (the tail case), the left
  side satisfies L-HUNIQ's hypotheses for `H₂ ∘ H₁`. A two-name handler `hnd_{n₁,n₂}`, which the
  kernel does not have, would state the law with no restriction on `M`'s row (OQ-49 (c)).
  Plotkin & Pretnar 2013 state no single-name fusion law of this shape [via #235]; Wu & Schrijvers,
  "Fusion for free" (MPC 2015), fuses folds over a combined carrier, not into a one-name `hnd`, and
  #235 marks that citation unverified.
- Binary: as above. Needs L-HUNIQ's binary half.
- Unary: at the tail case, both sides are in the same `IsModel` predicates.
- Route: through L-HUNIQ, at the tail case.
- Uses: K-HND, K-MODEL, K-KONT.
- Today: not stated (#235 L2 table). New.
- Slices: 03 (whether `H₂ ∘ H₁` types); 08 (the lowering fuses nested drivers when the law holds).
- Depends on: L-HUNIQ.
- Open: OQ-49 (the needed continuation; the `n₂`-forwarding mismatch), OQ-4; R-FUSETAIL.
- Obligation: **unknown** (OQ-49 first).

### L-HCORR: handler correctness
- Form. Let `E` carry equations `Eq(E) = {l_k ≡ r_k}` (OQ-22), each side a term over `E`'s
  operations with continuation variables. `H` is **correct** for `E` iff for every equation and
  every instantiation of its continuation variables by computations of `F_Σ R`,
  `⟦l_k⟧_H ≡ ⟦r_k⟧_H`, `⟦·⟧_H` replacing each operation by its clause (Plotkin & Pretnar, LMCS
  2013, Def. 4.5; undecidable in general, §6 [via #235]). Then
  `hnd_n H (𝒞[l_k]) ≡ hnd_n H (𝒞[r_k])` for every context `𝒞` that does not bind `n`.
- Binary: as above.
- Unary: none. Equations are a binary notion. Their unary shadow is that `IsModel` predicates
  are closed under both sides.
- Route: needs `≈`, or T-SI2 for equations whose two sides join under `H`'s clauses (L-STATE's
  swap laws under a state-passing handler).
- Uses: K-SIG, K-THEORY, K-MODEL.
- Today: vacuous: every effect is a free theory (`OpSig`, `Core/Types.lean:147`, has no
  equations). New, conditional on OQ-22.
- Slices: 02 (`Eq(E)`); 03 (a handler of an equational theory carries the obligation).
- Depends on: L-HUNIQ.
- Open: OQ-22, OQ-4.
- Obligation: **unknown**; vacuous until a kernel theory carries equations (OQ-22's default).

---

## 4. Theory-specific laws

### L-EXC: exceptions
- Form. The theory of `raise : A ↠^{aff} 0` is the free arity-0 theory, with no equations; its
  free model is `A + E` (Ahman & Bauer, ESOP 2020, Ex. 2; Plotkin & Pretnar 2013 [via #235]).
  Its laws are instances:

      (E1) K[raise_{n,i} V] ≡ D_K⟨raise_{n,i} V⟩                         (L-ALG0)
      (E2) hnd_n H (return V) ≡ h_ret V                                  (L-HRET)
      (E3) hnd_n H (K[raise_{n,i} V]) ≡ hnd_n H (D_K⟨raise_{n,i} V⟩)
           ≡ D_K ▷ c_i V    when every finaliser of K answers () cleanly   (L-ALG0, L-HOP)
      (E4) hnd_m H (K[raise_{n,i} V]) ≡ K'[raise_{n,i} V], m ≠ n          (L-HFWD, arity 0)
      (E5) ubind(N, D) K₀[raise_{n,i} V], with D () ↦* K₁[raise_{m,j} W] and K₁ catching
           nothing of m:  the raise of m supersedes, and is finalised outside   (SPEC §19)

  The standard handlers are instances of (E2)/(E3): `to_result` (`h_ret = inj₁`, clause
  `inj₂`), `default d`, `map_err g`. For `to_result` (`toResult`, `Core/EffPrograms.lean:107`):
  `toResult (return V) ≡ return (inj₁ V)` and `toResult (raise_{1,0} V) ≡ return (inj₂ V)`.
- Binary: as above.
- Unary: `opTable`'s abortive branch (`Core/EffDefs.lean:163-167`): the argument holds nothing
  owned, and nothing is owed to the abandoned continuation. `ewp_abortive`
  (`Core/EffWp.lean:811`); `ewp_handle`'s `[unwind]` case (`Core/EffRules.lean:675-682`).
- Route: reduction-shaped; T-SI2.
- Uses: K-RAISE, K-THEN, K-HND, K-CANCEL.
- Today: the steps `[unwind]`, `[finalise]`; `d_toResult` (`Core/EffPrograms.lean:137`) types the
  handler; `abort_passes`, `return_resumes` (`Core/Handlers.lean:153, 167`) for the withdrawn sum
  encoding (decision 52), to be relabelled (audit §3.5). Changed.
- Slices: 03 (`[raise]`), 04, 08 (branch-per-call lowering, SPEC §19 *Lowering*).
- Depends on: L-ALG0, L-HRET, L-HOP, L-HFWD.
- Open: OQ-24 (a payload that owns: `R-NOOWNERR` by default), OQ-21 (E5's policy has no law in
  the literature read: #235 L3a, "the 'a finaliser's raise supersedes' policy has no
  counterpart law in what I read"), OQ-7.
- Obligation: **mechanical** given its constituents.

### L-STATE: state and linearly used state
- Form. A capability is a comodel (O-COMODEL): a state `S` lent at `'l` as `m : Mut 'l S`, with
  a co-operation on the payload `c_op : S ⊗ A ⊸ F_{Σ'}(S ⊗ B)` per operation, run on the cell by
  `withswap`. Write `sw m f ≜ withswap m f` for a state transformer `f : S ⊸ F_∅(S ⊗ B)`.

  *Linear (state-access) laws*, at every `S`, no structure on `S` assumed:

      (S1) sw m (λs. return (s, ()))                ≡  return (m, ())                   (identity)
      (S2) sw m f to (m, b). sw m (g b)             ≡  sw m (λs. f s to (s', b). g b s')  (fusion)

  These are the identity and composition laws of state transformers on linearly used state, the
  structure of the state monad in Møgelberg & Staton's linear-use form `T ≅ S ⊸ !(−) ⊗ S`
  (LMCS 2014, §1.3 [via #235]): the state is used linearly, the arguments and results are not.
  Møgelberg & Staton's (8.9) is an equation of one particular comodel ("reading returns the same
  state", `flip[flip[s]] ≡ s`), not these laws; it is an example of comodel equations under OQ-22.

  *Plotkin-Power laws*, derived from (S1) and (S2) where `S` allows them. `get ≜ sw m (λs. (s, s))`
  needs `S` copyable (persistent, or under `!`), and `put v ≜ sw m (λs. (v, ()))` needs the old
  state to Drop:

      (P1) get to x. put x  ≡  return ()      (P2) put v; get  ≡  put v; return v
      (P3) put v; put w     ≡  put w          (P4) get to x. get to y. M x y  ≡  get to x. M x x

  (P1)-(P3) are the three equations of Ahman & Bauer's Example 1, `getenv(λc. setenv(c, κ)) = κ`,
  `setenv(c, getenv κ) = setenv(c, κ c)`, `setenv(c, setenv(c', κ)) = setenv(c', κ)` (arXiv
  1910.11629 §2.1, read), and Møgelberg & Staton's (8.5)-(8.7) [via #235]. (P4), read-read, is not
  among Ahman & Bauer's three; it is axiom 2 of Plotkin & Power's global state at one location,
  `l_loc(l_loc(t_{vv'})_v)_{v'} = l_loc(t_{vv})_v` (FoSSaCS 2002, §3, the seven axiom schemata,
  read), and here it is derived from (S2) with `S` copyable: both `get`s fuse into one
  `sw m (λs. (s, (s, s)))`, which answers the same state twice [I].

  *Distinct capabilities* commute; that is L-TENSOR.
- Binary: as above.
- Unary: (S1) and (S2) are interchanges at `σ = []` whenever `f` and `g` are in the relation at
  their types: the `withswap` compatibility lemma, applied twice on the left and once on the
  right, gives the same post. Not stated as a lemma today.
- Route: the two sides of (S2) run the same steps except one `store`/`load` pair, so they join
  in a typed context where `g b` does not read `m`'s cell while it is lent. That needs
  `ReadFootprintTyped` (`experiments/TwoRun/TwoRun/Read.lean:81`), not derived, or `≈`. **Unknown.**
- Uses: K-COMODEL, K-CAP, K-SWAP, D-COMODEL.
- Today: `op_tail`, `op_answer` (`Core/Handlers.lean:76, 133`) are the run facts of one
  operation; `handle_fold` (`Core/Handlers.lean:211`) is (S2) iterated, as runs. No equation, no
  commutation. In HandlersAsBorrows an answering handler is `withbor` form (2) with the capability
  `Mut 'x S` (`handle_is_shift`, `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:115`).
  Changed.
- Slices: 02 (the comodel's form; PP08: a theory with an abortive operation has only the empty
  comodel [via 12-sources]); 03 (`withswap`, K-CAP); 05 (T-COMODEL).
- Depends on: OQ-1 (whether a comodel is a derived form of a tail-resumptive `hnd`; under (a)
  L-STATE becomes L-TAIL plus L-HCORR for a state theory).
- Open: OQ-1, OQ-19, OQ-20 (an effectful callee), OQ-22 (State with declared equations: then a
  handler is correct iff its clauses form a comodel of them [via #235 L3b, marked inference
  there]), OQ-4.
- Obligation: unary **mechanical** (a restatement over `withswap`'s compatibility). Binary
  **unknown**.

### L-YIELD: generators
- Form. `Yield[T] = {yield : T ↠^{aff} 1}`, the free theory of output (Møgelberg & Staton
  §8.1.4, "printing" [via #235]). A `for`-site over a generator is a handler of `yield` at a
  static name `n` (SPEC §15 *for over a generator*), whose clause is the loop body `B` threading
  the loop's variables `w`. The H-laws instantiate:

      (Y1) for_n x in (return r) do B          ≡  return (r, w)                     (L-HRET)
      (Y2) for_n x in K[yield_n v] do B        ≡  B[v/x, w] ; resume κ_n(H, K) w'     (L-HOP)
      (Y3) a body leaving by break e or return e:
           for_n x in K[yield_n v] do B        ≡  D_K ▷ (exit e)                      (L-HOP, L-W)

  `take(k)` is a handler that counts in its state and cancels `κ` at `k` (Y3). A stored
  generator, observed step by step, is `ν` codata (K-NU), not a handler (OQ-26).
- Binary, Unary, Route: those of L-HRET, L-HOP and L-W, at the for-site's handler.
- Uses: K-HND, K-NU, K-KONT.
- Today: not stated. The elaboration is SPEC §15; the for-site is one of the six handler schemas
  with no law (audit M15). New.
- Slices: 08 (T-ELAB for the for-site and pull-site schemas; direct-call lowering when `B`
  performs nothing, L-TAIL).
- Depends on: L-HRET, L-HOP, L-W.
- Open: OQ-6, OQ-25, OQ-26.
- Obligation: **mechanical** given its constituents and the for-site's T-ELAB.

### L-ASYNC: asynchrony
- Form. The signature, with a thunk parameter (an algebraic operation, 02 K-SIG):

      Async[Σ] = μe. { suspend : 1 ↠^{aff} 1,   spawn : U(F_{n:e ⊕ Σ} 1) ↠^{lin} 1 }

  `spawn`'s parameter performs the effect that declares it: the signature names its own row in an
  operation type, which 02 K-SIG excludes ("a signature cannot contain its own row in an operation
  type") and a finite `CTy.effOf` chain cannot express. It is written here with K-SELFROW's binder
  (03 §9.12), the construct of OQ-61 (b), not adopted. Under OQ-61's default R-NOSELFROW the
  signature is `Async_Σ = { suspend : 1 ↠^{aff} 1, spawn : U(F_Σ 1) ↠^{lin} 1 }` with the async name
  `n ∉ names(Σ)`: a spawned thread runs at the outer row `Σ` and cannot itself spawn through `n`,
  only through an enclosing scheduler's name. That is a restriction of the asynchronous program,
  named as R-NOSELFROW.

  `suspend` yields control; `spawn` hands a new thread to the scheduler. A **scheduler** is the
  implementation, in one of two forms:

  - *over codata* (the default, OQ-60 (b)): each thread is a `U(Loop_Σ 1 1)` (K-NU), one
    observation running it to its next `suspend` (answer `inj₂` the rest) or its end (`inj₁ ()`);
    the scheduler is a loop over a queue of threads, `bounded_fix` or a `Loop_Σ` itself, with the
    queue an ordinary value or a cell lent to it (K-CAP). The program's own `suspend`/`spawn` are
    handled per observation by a handler that turns them into observation boundaries (03 §9.2).
  - *as a deep handler* (OQ-60 (a)): a model of `Async[Σ]` at carrier `S ⊸ F_Σ R`, the state `S` a
    queue of the continuations it captured. `S` then mentions `K_aff(1, S ⊸ F_Σ R)`, a negative
    recursive type; R-NONEGREC excludes it (03 §9.15), and its settling statement is
    `def DeepSchedulerCarrier : Prop` (OQ-60).

  The laws, at the codata form:

      (A1) hnd_n H_sched (return v)                 ≡  h_ret v                    (L-HRET)
      (A2) hnd_n H_sched (K[suspend_n ()])           ≡  enqueue (κ_n(H_sched, K)) ; next   (L-HOP)
      (A3) hnd_n H_sched (K[spawn_n t])              ≡  enqueue t ; resume κ_n(H_sched, K) ()  (L-HOP)
      (A4) cancelling a parked thread runs its destructor, LIFO   (L-W; L-SIGNAL (1): uninterceptable)
      (A5) suspend and spawn of distinct schedulers interleave freely (L-SUM (2)); operations on
           disjoint capabilities of two threads commute (L-TENSOR)

  where `enqueue` and `next` are the scheduler's queue operations, and at the codata form
  `κ_n(H_sched, K)` is replaced by the rest of the thread's `Loop_Σ`.

  **Finalising the queue.** L-ALG's graded side condition, and 04 §7.6's analysis, require the
  context of any frame around an affine or abortive outer operation to drop. A scheduler's queue of
  parked threads (affine `κ`s, or `U(Loop_Σ 1 1)` values with effectful `close`) does not drop. So a
  scheduler that performs an outer affine or abortive operation (an I/O await, a raise) while
  threads are parked needs the queue finalised by a finaliser frame whose `D` closes every parked
  thread, and closing a thread runs its effectful `close` or cancels its `κ`, which performs at the
  thread's row. That is a finaliser at a resuming table: under R-FINAB (OQ-7) it is not typed, and
  forwarding a cancel to the parked threads is OQ-27's term. So under R-FINAB such a scheduler
  cannot perform an outer affine or abortive operation while threads are parked; that restriction
  of the asynchronous program is named here as R-FINAB's.
- Binary: as above. Unary: those of L-HRET, L-HOP, L-W at the scheduler's carrier.
- Route: (A1)-(A3) reduction-shaped, T-SI2; (A5) as L-SUM, L-TENSOR.
- Typing against the open questions: a parked thread is a stored computation, bounded as OQ-28
  bounds a stored continuation (`[@c]`, K-GEN); its lends across a `suspend` are those of a stored
  `Loop_Σ`, read at the world OQ-46 fixes; a thread suspended inside a borrow needs R-T1 lifted
  (OQ-2) and, for the asynchronous read into a local buffer, an operation whose type mentions the
  lend (OQ-56).
- Uses: K-SIG, K-SELFROW, K-HND, K-NU, K-KONT, K-CAP, K-THEN.
- Today: not stated; no program. New.
- Slices: 08 §9.2 (the async program); 04 (each observation is an ordinary run).
- Depends on: L-HRET, L-HOP, L-W, L-SIGNAL, L-SUM, L-TENSOR, L-DIV.
- Open: OQ-61 (R-NOSELFROW: `spawn`'s self-reference), OQ-7 and R-FINAB (finalising a parked
  queue), OQ-27 (forwarding a cancel to the parked threads), OQ-60, OQ-31, OQ-28, OQ-46, OQ-18
  (threads proper), OQ-2, OQ-56.
- Obligation: **unknown**: the signature is not well-formed until OQ-61 is settled (at R-NOSELFROW
  the restricted form above is well-formed), and a scheduler that performs outer affine or
  abortive operations with threads parked needs R-FINAB lifted. Given both, at the codata form the
  laws follow from their constituents and 03 §9.2's `hndLoop`; the deep-handler form is excluded by
  R-NONEGREC.

### L-SCOPE: scoped operations (only under OQ-12 (b))
- Form. For a scoped operation `sc_j : A_j ↠^{q_j} ⟨S_j⟩ B_j` (03 §9.1, K-SCOPE), with
  `sc_{n,j}(V; M; y. N) ≜ scope_{n,j}(V; M) to y. N`: algebraic in the continuation,
  `K[sc_{n,j}(V; M; y. N)] ≡ sc_{n,j}(V; M; y. K[N])` for a plain `K` under L-ALG's side condition,
  and no law moves computation between the scope and the continuation. L-HRET and L-HFWD hold
  unchanged; L-HOP at a scoped operation is OQ-59's.
- Binary, Unary, Route: those of L-ALG at the continuation.
- Today: not stated; R-FO. New, conditional.
- Depends on: OQ-12, OQ-59. Obligation: **unknown**.

### L-ND: nondeterminism, only if multi-shot is free
- Form. `choose : 1 ↠^{unr} Bool`. The free theory gives the tree monad. The semilattice
  equations (associativity, commutativity, idempotence) give a powerset monad: Plotkin & Power
  (FoSSaCS 2002, §2, Example 3, read) state that "the category of algebras for the convex
  power-domain is the category of semilattices in C (i.e., structures with an associative,
  commutative, idempotent binary operation), equipped with a least element ⊥", over ω-cpos. That
  the same equations over sets without `⊥` give the finite non-empty powerset monad is this
  section's inference [I]. Under OQ-22 these are `Eq(Choose)`, and
  a handler collecting a list is not correct for commutativity (L-HCORR). The clause enters both
  branches, so `κ` is copied, which needs `Γ_K` persistent (L-P).
- Binary, Unary, Route: L-HCORR's; L-ALG at `q = unr`.
- Uses: K-KONT at `unr`, K-THEORY.
- Today: not stated; the persistence condition is built (L-P). New, conditional.
- Slices: 02, 03.
- Depends on: OQ-16 (if `unr` is dropped, L-ND is withdrawn), L-P, L-HCORR. Affect (van Rooij &
  Krebbers, POPL 2025 [via #235]) types one-shot and multi-shot continuations directly; whether
  its typing gives `unr` and L-ND at a lower cost is part of OQ-16's literature check.
- Open: OQ-16, OQ-22, OQ-4.
- Obligation: **unknown**; not stated at all under OQ-16 (b).

### L-DIV: divergence
- Form. Under OQ-15 (a) (as built), divergence is `ν` codata: `Loop_Σ A B ≜ νX. F_Σ(A ⊕ U X) &
  F_Σ B` (SPEC §19 *Divergence*). Its laws are coiteration laws at each observation:

      next (unfold g s)   ≡  next (g s) to x. map_{A ⊕ X} (unfold g) x
      close (unfold g s)  ≡  close (g s) to x. map_B (unfold g) x

  with `F_Σ` leaves, under the `[let]` frame (`node_ok`, SPEC §19 *Divergence*), and handlers
  installed per observation or spanning observations (03 §9.2, K-HDIV: `hndLoop`, `hndLoopS`).
  Under OQ-15 (b) a diverging computation `⊥`
  satisfies `K[⊥] ≡ ⊥`, **without** `D_K`. Staton (POPL 2015 §6.1 [via #235]) gives
  `discard(a, undef) ≡ undef`; the law `K[⊥] ≡ ⊥` at every context is #235's inference [I] from it,
  not Staton's statement.
  That law differs from L-ALG0, and needs the partial-correctness `ewpP_W` (05 D-EWPP; `ewp` is
  total: `∃ k', ARun …`, `Core/EffDefs.lean:36`), a second wp family recorded as a defect in OQ-63.
- Binary: as above, at the chosen reading.
- Unary: (a): `cB` at an effectful leaf is `ewp` at the row's table (SPEC §19 *Divergence*, "as
  built"); each observation is total.
- Route: (a): `unfold_next`, `unfold_close` are joinability facts for pure steps
  (`experiments/CoeffectsStrict/CoeffectsStrict/Unfold.lean:55, 67`); at effectful leaves, T-SI2.
- Uses: K-NU, K-DIV, K-LET.
- Today: pure β laws in CoeffectsStrict; the effectful step `node_ok`; no handler around a div
  computation in the kernel (SPEC §21 *Open*); K-HDIV specifies it, its lift deferred by R-HDIV
  (OQ-67). As built (a).
- Slices: 03, 05 (`Core/NuRel.lean`), 08.
- Depends on: L-ALG (the frame through a leaf).
- Open: OQ-15, OQ-26, OQ-63, OQ-67.
- Obligation: (a) **mechanical** for the β laws; at K-HDIV's spanning form **unknown** (OQ-67).
  (b) **unknown**.

### L-FIX: the fixed point of a generator
- Form. For a generator `s` and a budget `k`:

      bounded_fix (s, (k, a))  ≡  s (fixSelf s k, a)
      fixSelf s 0 = inj₁ ()                fixSelf s (k+1) = inj₂ (λx. bounded_fix (s, (k, x)))

  (`Support/Dynamics/Arrays.lean:89, 97`). A layer `L` composes before the fixed point:
  `with L { f }` is `bounded_fix (L ∘ s_f, …)` (decision 59; SPEC §21). An exhausted budget is
  the abortive operation of `Exhausted` (decision 58), and its laws are L-EXC's.
- Binary: as above.
- Unary: `bounded_fix` is sound at every computation type, rows included, by induction on the
  budget (`boundedFix_compatX`, `Core/BoundedFix.lean:91`).
- Route: one `[boundedFix]` head step (`Paper/S3_Dynamics/Definitions.lean:495`); T-SI1, T-SI2.
- Uses: K-FIX.
- Today: the step and its soundness. As built.
- Slices: 03, 04, 08 (the budget's lowering).
- Depends on: T-SI1, T-SI2.
- Open: OQ-14 (recursion through a site), OQ-47.
- Obligation: **mechanical**.

### L-FOLD: folds and counted loops at a row (under OQ-62 (b))
- Form. For K-FOLDΣ's constants (03 §9.13):

      fold[Σ] alg (roll v)          ≡  map_T (fold[Σ] alg) v to w. alg w
      countFold[Σ](f, (n, (i, s)))  ≡  if i < n then f (i, s) to s'. countFold[Σ](f, (n, (i+1, s'))) else return s

  and fold uniqueness: a map `h` with `h (roll v) ≡ map_T h v to w. alg w` is `fold[Σ] alg`.
- Binary: as above; uniqueness needs `≈` (OQ-4), or L-HUNIQ's route.
- Unary: each level an `ewp_W` at `opTable ⟦Σ⟧`, by `ewp_bind`.
- Route: β by the fold's λ-term steps and `Head.count` (`Core/CountFold.lean:10`), T-SI1, T-SI2;
  uniqueness by induction on the structure, as `fold_unique`
  (`experiments/CoeffectsStrict/CoeffectsStrict/Fold.lean:207`) does for a pure total algebra.
- Uses: K-FOLDΣ, K-LET. Today: `fold_beta`, `fold_unique` (`Fold.lean:76, 207`) for pure algebras
  over Core. New at a row.
- Depends on: L-TO, L-ALG. Open: OQ-62 (R-PUREFOLD), OQ-4, OQ-9 (`foldImm[Σ]` at a resuming row).
- Obligation: β **mechanical** given T-SI2 at abortive rows; **unknown** at resuming rows;
  uniqueness **unknown**.

---

## 5. Composition: sum, tensor, signal, interaction

### L-SUM: rows are sums
- Form.
  1. **Row algebra is meaning-preserving.** `𝒞⟦F_{Σ ⊕ Σ'} A⟧_W δ = 𝒞⟦F_{Σ' ⊕ Σ} A⟧_W δ`,
     `𝒞⟦F_{Σ ⊕ ∅} A⟧_W δ = 𝒞⟦F_Σ A⟧_W δ`, and associativity. Under `Row.Uniq` the interpretation
     `⟦Σ⟧δ` depends only on the set of entries (`Row.find_of_mem`, `Core/EffRules.lean:748`).
     This part is unary.
  2. **No cross-name equation.** Operations of distinct names interleave freely: in general
     `op_n(V; _. op_m(W; _. M)) ≢ op_m(W; _. op_n(V; _. M))`. Two printing logs do not commute
     (`print_print_not_commute`, `experiments/EffModelRel/EffModelRel/Examples.lean:178`, in the
     sibling).
  3. **Forwarding preserves order**: L-HFWD.
  4. **Absorption** `log m; raise_f ≡ raise_f` holds exactly under the handlings that validate
     it. With `Fail` handled outside a `Log` handler whose clause is pure (state passing), the
     `Log` state is lost with the abort (TR T7.9; `absorb_pure`,
     `experiments/EffModelRel/EffModelRel/Tensor.lean:204`). It fails with `Log` outside, with a
     printing `Log`, and with a lent `Log` capability, which survives the abort
     (`not_absorb_print_inside`, `not_absorb_writer_outside`, `not_absorb_print_outside`,
     `lent_state_survives`, `…/Examples.lean:136, 142, 148, 167`). The sum is the program's free
     theory `Log + Fail`; the two nesting orders are two handlings of it: `Log` outside gives
     `W* × (A + E)`, `Fail` outside gives `E + (A × W*)` (#235 L4, from Hyland, Plotkin & Power,
     TCS 2006, as restated by Ahman & Bauer 2020 §3.1 [via #235]).
- Binary: (2) and (4) as stated. Kernel instances, closed: `nFailOutside_answers`
  (`Core/EffPrograms.lean:515`) proves that every run of `to_result (with_log (log; raise))`
  reaches `inj₂ ()` at the empty memory, so the closed instance of absorption holds as equal
  observations; `nLogOutside_answers` (`:505`) and `logOutside_answers` (`:245`) exhibit the
  order that keeps the log. The open law is not stated.
- Unary: (1) as above. For (4), the abortive stop owes nothing (`opTable`,
  `Core/EffDefs.lean:163-167`), so the pure `Log` handler's frame is dropped holding nothing owned.
- Route: (4) under a state-passing `Log` handler joins after the clause resumes, and the abort
  then deletes the handler frame (L-ALG0). T-SI2.
- Uses: K-ROW, K-INT, K-HND.
- Today: as cited; first-match lists, with `Row.Uniq` only at `[then]` (`Core/EffRules.lean:746`,
  `then_compatC`'s `hUq`). Changed (sum with distinct names, 02).
- Slices: 02 (row sum and its algebra), 05 (T-SUMOK).
- Depends on: K-ROW's quotient by `Row.Uniq`; L-HFWD; L-ALG0.
- Open: OQ-18.
- Obligation: (1) **mechanical** (02's quotient). (4) **mechanical** given T-SI2.

**Which pairs of our effects combine which way.** One row per pair; "sum" means no equation
across the pair, and "tensor" means their operations commute (at arity 0, the 0-ary side absorbs
the other).

| pair | combination | law | why |
|---|---|---|---|
| two control sites, distinct names | sum | L-SUM (2), L-HFWD | per-name free theories; forwarding preserves order |
| `Fail` with a pure-model `Log`, `Fail` outside | validates the tensor equation at arity 0 | L-SUM (4) | `log m; raise ≡ raise` is the tensor's commutation at arity 0 (HPP 2006; Ahman & Bauer §3 [via #235]); `E + (A × W*)` is the tensor's model |
| `Fail` with `Log`, `Log` outside, or printing, or lent | sum | L-SUM (4) fails | the log is kept, or the lend survives |
| two capabilities from disjoint borrows | tensor | L-TENSOR | state at distinct cells; disjointness is static |
| a capability borrowed from outside an aborting region | sum for the lender's state | L-BOR | the lend ends and the lender regains the place |
| a resource owned inside an aborting region | finalised | L-ALG0 | its destructor runs on the unwind |
| cancel (`⊥`) with the region's remaining operations | discarded by a free-theory law; whether it is an Ahman-Bauer signal is OQ-66 | L-SIGNAL | no user handler intercepts it; the destructor runs (L-W) |
| a capability with a control operation across a freeze | answering/control commutation | L-INTER | holds at linear operations in a special case; open at affine (OQ-48) |
| `Exhausted` with anything | sum (it is abortive) | L-EXC | decision 58 |
| `Yield` with `Fail` | sum; `break` cancels | L-YIELD (Y3) | the for-site's cancel runs the generator's finalisers |

Threads (required eventually) bear on the tensor rows: a capability shared across threads is
not disjoint state. Each tensor row records that its commutation rests on static disjointness of
borrows. OQ-18.

### L-TENSOR: disjoint capabilities commute
- Form. For capabilities `m₁ : Mut 'l₁ S₁`, `m₂ : Mut 'l₂ S₂` from disjoint borrows, and
  co-operation calls `c₁ = sw m₁ f₁`, `c₂ = sw m₂ f₂` whose transformers perform nothing:

      c₁ to (m₁, b₁). c₂ to (m₂, b₂). M  ≡  c₂ to (m₂, b₂). c₁ to (m₁, b₁). M

  Operations on distinct cells commute: the tensor of theories, "taking the operations of both
  theories and demanding that they commute with each other, while retaining the equations of both"
  (Hyland, Plotkin & Power, TCS 2006, §1, read), and the commutation of operations at distinct
  locations in the theory of state, Plotkin & Power's axioms 5-7 (`l_loc(l_loc'(t)) = l_loc'(l_loc(t))`,
  `u_{loc,v}(u_{loc',v'}(x)) = u_{loc',v'}(u_{loc,v}(x))`, `u_{loc,v}(l_loc'(t)) = l_loc'(u_{loc,v}(t))`,
  each where `loc ≠ loc'`; FoSSaCS 2002, §3, read), whose program form is their 6*:
  `(l ≠ m) ⊃ (l := x; m := y) = (m := y; l := x)`. Distinct cells here are cells from disjoint
  borrows, distinct by BoLo separation rather than by a location inequality [I]. Plotkin & Power,
  MFPS 2008, is the tensor of a model and a comodel, cited at T-COMODEL (05), not here.
- Binary: as above.
- Unary: the disjoint-capability frame fact. Each call's `ewp` frames the other cell
  (`wpG_frame`, `Core/EffWp.lean:1005`; `[TR]` 6.65 at the tagged world), so both orders satisfy
  every separable specification: `ewp_W(c₁;c₂;M){Tb}{Q}` and `ewp_W(c₂;c₁;M){Tb}{Q}` follow from
  the same separated premises. Not stated as a lemma.
- Route: the two orders run disjoint `load`/`store` pairs. They join when neither transformer
  reads the other's cell, which is `ReadFootprintTyped` (`experiments/TwoRun/TwoRun/Read.lean:81`;
  not derived). Otherwise `≈`.
- Uses: K-CAP, K-SWAP, K-BOR, D-COMODEL.
- Today: EffModelRel `tensor` (`experiments/EffModelRel/EffModelRel/Tensor.lean:91`) for `PureCo`
  co-operations, in the sibling. New over the kernel.
- Slices: 05 (T-COMODEL), 07.
- Depends on: L-STATE, T-FRAME.
- Open: OQ-4, OQ-18, OQ-20.
- Obligation: unary **mechanical**. Binary **unknown** (ReadFootprintTyped, or `≈`).

### L-RUN: running a computation against a comodel
- Form. For a comodel `c` of `n:E` on state `S` (O-COMODEL), `run_c` the translation of T-COMODEL
  (each `perform_{n,i}` replaced by a `withswap` call of `c_i` on the lent cell `m : Mut 'l S`),
  `K` free of `n`, and `m ≠ n`:

      (run-return)   run_c (return V)                 ≡  return V
      (run-op)       run_c (K[perform_{n,i} V])       ≡  withswap m (λs. force c_i (s, V)) to b. run_c (K[b])
      (run-forward)  run_c (op_{m,j}(V; y. M))        ≡  op_{m,j}(V; y. run_c M)
      (run-bind)     run_c (M to x. N)                ≡  run_c M to x. run_c N
      (run-unique)   a map satisfying run-return, run-op and run-forward on every computation of
                     F_{n:E ⊕ Σ'} A is run_c

  The state is threaded by the cell, not by the answer: `run_c M` answers what `M` answers, and the
  final state is in the cell the borrow returns (`withbor` form (2)'s `Ref S ⊗ T₂`). Run-return and
  run-bind are KRU's stateful-runner laws (Katsumata-Rivas-Uustalu §4, "a (stateful) runner of T
  [is] an object Y with a family θ of maps θ_X : T X × Y → X × Y natural in X" satisfying the unit
  and multiplication diagrams, arXiv 1912.13477, read in 05 §10); they are not the axioms of a
  monad-comonad interaction law, which also constrain the comonad's counit and comultiplication
  (KRU §3, diagrams (1)). Run-op is Ahman-Bauer's `r_X(op(a, κ)) = op_M(a, r_X ∘ κ)` (§2.2, read in
  05 §10). Run-unique, at `Σ' = ∅`, is the free-model universal property applied to the
  `St_S`-structure `op_M` (A-B §2.1-2.2: "the universal property of the free Σ-model … obtain a
  Σ-homomorphism `r_X`", unique as a homomorphism out of the free model). At `Σ' ≠ ∅` the
  co-operation is effectful over a carrier, neither A-B's Def. 1 nor Def. 2 (05 D-COMODEL), and
  run-unique there is this section's inference [I], by A-B's kernel-monad runner (§3.1) or KRU's
  residual runners. Prop. 3 (monad morphisms `Tree_Σ(−) → T` correspond to carrier-free
  `T`-runners) does not back it directly.
- Binary: as above.
- Unary: run-op is `IsComodel` (D-COMODEL) composed with the `withswap` compatibility and 6.66;
  run-forward is `ewp_handle`'s forwarding case read at `run_c`; T-COMODEL is the unary form of the
  whole.
- Route: run-return and run-op are definitional on `run_c`'s syntax plus T-SI1 at the `withswap`
  steps (`beta`, `load`, `letpair`, `store`, `Paper/S3_Dynamics/Definitions.lean:587-590`);
  run-forward and run-bind are joinable after capture, as L-ALG; run-unique needs `≈` (OQ-4).
- Uses: K-COMODEL, K-CAP, K-SWAP, D-COMODEL.
- Today: `op_tail`, `op_answer`, `handle_fold` (`Core/Handlers.lean:76, 133, 211`) are run facts
  of the answering elaboration for one operation and its fold. New as laws.
- Slices: 05 (T-COMODEL), 08 (T-ELAB.comodel).
- Depends on: T-COMODEL, T-SI1, T-SI2.
- Open: OQ-1 (under (a) L-RUN is L-HRET/L-HOP/L-HFWD/L-HUNIQ at a tail-resumptive handler), OQ-20
  (`Σ'` nonempty), OQ-4.
- Obligation: run-return, run-op **mechanical**; run-forward, run-bind **mechanical** given T-SI2;
  run-unique **unknown**.

### L-SIGNAL: cancel is uninterceptable and runs the destructor
- Form.
  1. **No user handler intercepts a cancel.** Every name is nonzero and a handler frame catches
     `0` only if its name is `0` (`hndK_catches`, `Core/EffRules.lean:556`; `hn0` in
     `handle_compatC`), so `hnd_m H (K[⊥_N]) ≡ D_{hnd_m H [·] ∘ K}⟨⊥_N⟩`: L-ALG0 with the handler
     frame deleted.
  2. **A clause that cancels discards what the body would still perform.** For
     `c_i = λ(v, κ). cancel κ; M'`, `hnd_n H (K[perform_{n,i} V]) ≡ D_K ▷ M'[V/v]` when every
     finaliser of `K` answers `()`. This is L-HOP followed by L-W, a law of every free theory. It
     concerns the operations the continuation would still perform, not the operations already
     performed, which stay performed.

  **Against Ahman & Bauer's signal.** Read in Ahman & Bauer, arXiv 1910.11629. §3.1, eq. (1) and the
  kernel theory `K_{Σ,E,S,C}` below it: a signal absorbs the kernel's state operations,
  `getenv(λc. kill s) = kill s` and `setenv(c, kill s) = kill s` ("a signal discards state"); an
  external operation `op ∈ Σ` is related to state by commutation
  (`getenv(λc. op(a, κ c)) = op(a, λb. getenv(λc. κ c b))`), not absorption. §3.2, the text after
  eq. (3): when a co-operation sends a signal, "the rest of the user code M is skipped and the
  control proceeds directly to the corresponding case of the finalisation part F", the clause
  `kill s ↦ N_s`; Thm 7's finalisation map has the case `φ_γ(ι₂ s) = ⟦N_s⟧`. Only a signal from an
  *enveloping* runner bypasses this run's `F` ("unless some enveloping runner sends a signal,
  finalisation with F is guaranteed to take place", §5.3). So a runner's own signal skips the
  remaining continuation and runs finalisation, which is the shape of our cancel: discard what the
  body would still perform, then run `D_K`. The differences: `kill` discards the kernel state and
  `N_s` does not receive the final state `c`, whereas our `D_K` is the finalisers of the frames the
  continuation holds, each run on its own resources, LIFO, one per frame rather than one per
  `run`. Whether cancel is an instance of the signal is OQ-66 (**[settle by literature]**); no law
  here depends on it. #235's reading of decision C (uninterceptable cancel) as Ahman-Bauer's signal
  (L4, L5-K) is that report's inference [I].
  3. **The error policy** (`[cfin-raise]`: the first error of a name outside the region is
     re-raised at the canceller, the rest suppressed; SPEC §19 *Cancels*) has no counterpart law
     in the literature read (#235 L5-K). It is specified by its steps (04) only.
- Binary: (1), (2) as above; (3) none.
- Unary: `cancelTab` (`Core/EffDefs.lean:131`), `ewp_ccatch` (`Core/EffRules.lean:580`),
  `cancel_frame` (`Core/EffRules.lean:168`), `ewp_cancel_absorb` (`Core/EffRules.lean:325`).
- Route: reduction-shaped; T-SI2.
- Uses: K-CANCEL, K-KONT, O-NAME (`⊥ = 0` reserved).
- Today: the `⊥` name, `cfin`, the cancel steps (`Paper/S3_Dynamics/Definitions.lean:523-545`);
  `Core/EffCancel.lean` checks both outcomes of the policy (`prog_run`, `prog₃_run`, `:103, 113`).
  As built.
- Slices: 04 (K-CANCEL), 05 (D-CANCELTAB).
- Depends on: L-ALG0, L-HOP, L-W.
- Open: OQ-21 (the policy, and whether destructors may perform only answering operations,
  #245), OQ-18 (threads: a cancel across threads), OQ-66 (the classification).
- Obligation: (1), (2) **mechanical** given constituents; (3) none.

### L-INTER: answering/control commutation
- Form. An answering operation on a capability `x` and a control operation on a handler `h` of
  another name, meeting at a freeze, with the lend outside the handler (placement (i)):

      op_x.a(u; z. op_h.o(v; y. M))  ≡  op_h.o(v; y. op_x.a(u; z. M))      (z ∉ fv(v), y ∉ fv(u))

  under the hypotheses of TR T13.13: the co-operations answer in place, `o` is linear, and `h`'s
  clause does not mention `x` and performs no operation before its use of `κ`
  (`docs/effects-tr/13-adjunction.md` §13.5). At an affine operation whose clause cancels, TR
  P13.14 gives two programs answering `1` and `0`, which would make the law need the frozen
  segment resumed exactly once, where ν/op needs at most once. P13.14 was computed by hand in the
  sibling calculus (audit m2); it is not a machine-checked obstruction, and OQ-48 asks for it at
  the kernel.
- Binary: as above, under T13.13's hypotheses.
- Unary: none distinct from L-STATE's and L-HOP's.
- Route: under T13.13's hypotheses, the clause reaches its single use of `κ` with the capability's
  state unchanged, so the two sides join after `κ` is resumed. T-SI2. **Unknown** at the kernel.
- Uses: K-CAP, K-HND, K-KONT.
- Today: TR §13.5, on paper over the sibling's trees. Not stated over the kernel. New. This law
  is a commutation of an answering operation with a control operation, tensor-shaped; it is not
  Katsumata-Rivas-Uustalu's interaction law. A monad-comonad interaction law `ψ_{X,Y} : T X × D Y →
  X × Y` is compatible with the monad's unit and multiplication and with the comonad's counit and
  comultiplication (KRU §3, diagrams (1), four conditions); L-RUN's run-return and run-bind match
  only KRU's stateful-runner laws (§4), which have the unit and multiplication conditions alone.
  The comonad-side conditions, which govern how a cell's state is threaded, are not stated in this
  specification; KRU §4 relates monad-comonad interaction laws to `D`-coalgebraic runner specs,
  the reading under which they would be stated (OQ-19).
- Slices: 05 (T-COMODEL: "one protocol for model and comodel").
- Depends on: L-STATE, L-HOP, L-BETA; OQ-1.
- Open: OQ-1, OQ-4, OQ-48.
- Obligation: **unknown**.

### L-DISCARD, L-COPY, L-COMMUTE: the effect-dependent laws of rows
- Form. Graded by row and qualifier, for `M : F_Σ A`, `M₁ : F_{Σ₁} A₁`, `M₂ : F_{Σ₂} A₂`:

      (L-DISCARD)  M to _. N  ≡  N           Σ has no div entry and no abortive operation, every
                                             operation of Σ is discardable, and Drop A
      (L-COPY)     M to x. M to y. N  ≡  M to x. N[x/y]
                                             every operation of Σ is idempotent, A persistent (!A),
                                             and the context of M persistent (M is copied)
      (L-COMMUTE)  M₁ to x. M₂ to y. N  ≡  M₂ to y. M₁ to x. N
                                             x ∉ fv(M₂), y ∉ fv(M₁), and Σ₁, Σ₂ commute: their
                                             operations are capability calls on disjoint borrows
                                             (L-TENSOR), or are declared to commute by Eq (OQ-22)

  An operation is *discardable* when its entry's continuation may be dropped with nothing
  performed and no observable change: under the free theories of the kernel only the empty row
  qualifies, and a capability call is discardable exactly when its co-operation is a read
  (L-STATE's (P4) shape). `div` excludes discard because `ewp` is total and a diverging `M` cannot
  be discarded without changing the observation (06 §1.2). Linearity adds the conditions on `A` and
  on `M`'s context: a discarded result must drop, a copied computation's captures must be
  persistent (L-P).
- Source. Kammar & Plotkin, *Algebraic foundations for effect-dependent optimisations* (POPL 2012)
  [R]: named in #235's bibliography ("recalled, not re-read") and not retrievable when fetched for
  this section. The side conditions above are this section's [I]; transcribing them from the
  source is OQ-64.
- Binary: as above.
- Unary: an `ewp_W` interchange at the row's table. L-DISCARD: `ewp_W(M to _. N){opTable ⟦Σ⟧}{Q}`
  and `ewp_W(N){…}{Q}` follow from each other when `M`'s every run stops at no operation it cannot
  drop and returns a droppable value with a `NoOwn` leftover. L-COMMUTE: both orders satisfy every
  separable specification, as L-TENSOR's unary half.
- Route: joinability with T-SI2 for L-DISCARD at the empty row (the run of `M` is silent and
  allocation-free, or its allocations are garbage, `wpG_garbage`, `Core/EffWp.lean:730`); `≈` for
  L-COPY and L-COMMUTE in general.
- Uses: K-ROW, K-INT, K-GRADE, K-CAP. Today: not stated. New.
- Slices: 08 §6 (dead-call elimination and reordering in the lowering rest on these laws); T-LOWER.
- Depends on: L-TO, L-TENSOR, L-STATE. Open: OQ-64, OQ-4, OQ-22 (declared commutation), OQ-15
  (the `div` side condition).
- Obligation: L-DISCARD unary at the empty row **mechanical**; at a capability read **unknown**;
  L-COPY, L-COMMUTE **unknown**.

---

## 6. Linear laws

### L-W: weakening of a continuation is its destructor
- Form. For `κ = κ_n(H, K)` at an operation with `q ≠ lin`, `N = n :: K.hndNames`, and `K°` as
  in L-ALG0 (here deleting plain frames and handler frames, which catch nothing of `0`):

      cancel κ  ≡  ccatch (hnd_n H (K°[⊥_N]))

  Its run: `[finalise-cancel]` at each finaliser frame of `K`, innermost first, running `D_j ()`
  under `cfin`, then `[cancel]` answering `()`, or `[cancel-raise]` re-raising the kept error
  (`Paper/S3_Dynamics/Definitions.lean:523-545`). When every `D_j ()` answers `()` without
  raising, `cancel κ ≡ D_K ▷ return ()`. Discarding a continuation runs its destructor (Congard,
  Munch-Maccagnoni & Douence, ESOP 2026: "weakening and exchange rules perform side-effects",
  abstract read for this section; LIFO release from #235's reading of their Prop. 2 [via #235]).
  That `cancel κ` is the destructor of `κ` in their sense is this section's inference [I].
- Binary: as above.
- Unary: `cancel κ` is in `KapRel`'s cancel conjunct (`Core/EffRules.lean:575-576`), discharged
  in `ewp_handle` by `ewp_kappa_cancel` (`Core/EffRules.lean:529`), `ewp_ccatch` (`:580`) and
  `cancelOwed` (`Core/EffDefs.lean:138`), with `cancel_frame` (`Core/EffRules.lean:168`) for a
  frame around the cancel run.
- Route: `cancel κ ↦³ ccatch (hnd_n H K[⊥_N])` by `beta`, `case₂`, `seq`
  (`ewp_kappa_cancel`'s steps), then the deletion relation of L-ALG0. T-SI2.
- Uses: K-KONT, K-CANCEL, K-THEN, O-FIN, D-OWED, D-DTOR.
- Today: the `[cancel]` steps and the lemmas cited. SPEC §19 *Theorems* names `cancel_compatC`
  (SPEC.md:2764), which has no declaration (#235 L5-W, grep). As built (unary), not stated as an
  equation.
- Slices: 03 (`kTy`'s cancel entry at `aff`, `Core/EffRules.lean:976-982`), 04, 05 (D-OWED), 07
  (T-FIN), 08 (the cancel is the state machine's destructor, SPEC §19 *Lowering*).
- Depends on: L-ALG0.
- Open: OQ-7 (finalisers at non-abortive rows: `R-FINAB`), OQ-9 (open frames handed to a
  continuation that is then cancelled: the first probe), OQ-21, OQ-27.
- Obligation: at `σ = []`, unary **as built**, binary **mechanical** given T-SI2. At `W`:
  **unknown**; this is exactly OQ-9's first probe (`[handle]` + cancel with a 6.64 frame open,
  05 §12.1), and OQ-44's probe at a 6.65 frame (05 §12.2).

### L-C: no duplication of a linear or affine continuation
- Form. A typing invariant: in every derivation `Δ; Γ ⊢ e : C`, a variable at `kTy Σ R lin B`
  is used exactly once, and one at `kTy Σ R aff B` at most once, unless it is under `!`, and
  only `unr` gives `!` (`kTy`, `Core/EffRules.lean:976-982`). No linear value is discarded or
  duplicated (Tang et al., POPL 2024, Thm 3.6, *Reduction Safety* [via #235]).
- Binary: none; it is not an equation.
- Unary: `KapRel` holds a nonempty resource only at `lin`/`aff` (`Core/EffRules.lean:571`:
  `unr → ρ = ∅`), so a copied `κ` would duplicate a resource, which `⋆` forbids.
- Route: none.
- Uses: K-KONT, K-GRADE, O-QUAL.
- Today: `kTy`; `[let]`'s side conditions; T-LIN (07) is its corollary of T-FP. As built.
- Slices: 03, 07 (T-LIN).
- Depends on: none.
- Open: OQ-17 (a relevant `κ`).
- Obligation: **as built**.

### L-P: multi-shot persistence
- Form. A continuation may be entered several times only if its captured context is
  persistent: at `q = unr`, `Γ_K` persistent (`[let]`'s `hU : S.Unr → Persistent Γ₂`,
  `Core/EffRules.lean:897`), `contShare`'s `unr → ρ = ∅` (`Core/EffDefs.lean:146`), and a `λ`
  at a `!` type is over persistent slots (`lam_bang_persistent`,
  `experiments/HandlersControl/HandlersControl/Capture.lean:42`). A control-flow-unlimited context
  cannot capture linear resources (Tang et al., POPL 2024 §2.2 [via #235]).
- **The multi-shot condition** (OQ-16). `unr` is kept only if every rule, law and obligation
  that mentions it costs nothing beyond `!`'s existing rules. The laws that mention `unr` are
  L-ALG (the grade), L-P, L-ND and L-NU; L-NU's ν/op fails at `unr`
  (`nu_op_fails_multishot`, `experiments/EffModelRel/EffModelRel/Examples.lean:223`, in the
  sibling). All other laws are stated and proved at `lin` and `aff`.
- Binary: none; a typing invariant.
- Unary: as cited.
- Route: none.
- Uses: K-KONT, K-LET, K-GRADE.
- Today: as cited. As built.
- Slices: 03, 08 (the multi-shot lowering class copies).
- Depends on: none.
- Open: OQ-16.
- Obligation: **as built**.

---

## 7. Freeze, resume, forwarding, hiding

### L-BETA: freeze then resume
- Form. `resume κ_n(H, K) w  ≡  hnd_n H K[w]`. Resuming a captured continuation is the identity,
  up to fresh internal lifetimes. The lifetimes are visible only to the relation.
- Binary: as above.
- Unary: at `σ = []`, `ewp_kappa_resume` (`Core/EffRules.lean:493`), the resume conjunct of
  `KapRel` (`Core/EffRules.lean:573-574`). At `W` with open frames, "up to fresh internal
  lifetimes" is capture rebasing (TR §14.3, L14.4, open as O5) or OQ-9 (a): **unknown**.
- Route: four allocation-free head steps (`beta`, `case₁`, `seq`, `beta`; `ewp_kappa_resume`'s
  proof). T-SI1, T-SI2.
- Uses: K-KONT, D-KAP.
- Today: as cited; TR T13.2 (`docs/effects-tr/13-adjunction.md` §13.2), binary, in the sibling.
  As built (binary form holds by four steps).
- Slices: 04 (`kappa`), 05 (`KapRel`, OQ-8's quantifier).
- Depends on: T-SI1, T-SI2.
- Open: OQ-8, OQ-9, OQ-28 (a stored `κ` bounded by `[@c]`), OQ-2.
- Obligation: binary **mechanical**; unary at `W` **unknown**.

### L-ETA: the forwarding handler, cancel included
- Form. `Fwd_n` has return clause `λz. return z` and, at each operation, the clause
  `λ(p, κ). perform_{n,i} p to r. resume κ r`, which re-performs to the next handler of `n`
  outward: the clause runs outside the handler frame. At an abortive operation its clause is
  `λp. raise_{n,i} p`. Then

      hnd_n Fwd_n M  ≡  M

  At an affine operation the clause must also forward a cancel. The term that does it puts a
  continuation inside a frame of another continuation (#279 external input [via #279]), and
  whether the kernel's terms express it is OQ-27.
- Binary: as above.
- Unary: by L-HUNIQ's unary form, both sides are in the same `IsModel` predicates.
- Route: not reduction-shaped: the left side's re-performed operation carries `hnd_n Fwd_n` in its
  continuation, and the sides agree only after every resumption (TR P13.6). Needs `≈`, or
  L-HUNIQ's binary form with `f = id`.
- Uses: K-HND, K-KONT, K-CANCEL.
- Today: TR T13.8 under conditions; EffModelRel `fwd_id` (`experiments/EffModelRel/EffModelRel/
  Ownership.lean:112`); in that unmoded sibling `eta_fails_linear` (`…/Ownership.lean:181`) and
  `etaAff_leaks` (`:237`) record where its equivalence and its unary model differ from the moded
  calculus (`etaAff_not_moded`, `:242`). Not stated over the kernel. New.
- Slices: 03 (whether `Fwd_n` types at an affine operation: TR L13.5).
- Depends on: L-HUNIQ, OQ-27.
- Open: OQ-27, OQ-4, OQ-14 (re-entry is how the clause reaches the outer handler).
- Obligation: **unknown**; stated at `lin` only by OQ-27's default.

### L-HIDE: hiding
- Form. The body's relation is parametric in the handler's or lender's witness. Unary: a lent
  cell's invariant is never read by the body (BoLo's anti-frame, `[TR]` 6.66). Binary: for two
  handlers into state-passing types whose clauses are related at a relation `R` on states,
  `R(s, s') ⇒ (hnd_n H M) s ≈ (hnd_n H' M) s'` (TR D13.11).
- Binary: as above; needs `≈` with a per-cell relation (§1.6 item 3).
- Unary: `wpTS_M_antiFrameX` (`Core/FrameRules.lean:550`) for pure callbacks;
  `ewpTS_M_antiFrameU` (`Core/EffWp.lean:854`) at abortive tables; `ewpTS_M_antiFrameR`
  (`experiments/GhostEnd/GhostEnd/Frames.lean:89`) at monotone tables, an experiment. At a
  resuming table over `W`: T-FRAME, **unknown**.
- Route: none operational.
- Uses: K-BOR, K-HND, D-TABLEOK.
- Today: as cited; EffModelRel `hnd_sim`, `hiding_counter`
  (`experiments/EffModelRel/EffModelRel/Ownership.lean:253, 402`) in the sibling. Changed.
- Slices: 05 (T-FRAME at 6.66).
- Depends on: T-FRAME.
- Open: OQ-4, OQ-2, OQ-9.
- Obligation: unary at abortive tables **as built**; at `W` **unknown**; binary **unknown**.

---

## 8. Names

### L-NAH: no accidental handling
- Form. For `M : F_Σ A` with `n ∉ Σ`, and `H` a handler of `n`:

      hnd_n H M  ≡  M to x. h_ret x

  In particular, with `h_ret = λx. return x`, `hnd_n H M ≡ M` (TR T7.16). The parametric form,
  "a function parametric in a name it does not handle forwards that name's operations", is the
  same law applied to the copy a renaming produces (L-REN, T-NAH).
- Binary: as above.
- Unary: at a row without `n` the table `⟦Σ⟧δ` has no `n` entry (`Row.tab`,
  `Core/EffRules.lean:47`), so `ewp_handle`'s `hop` hypothesis is vacuous and its forwarding
  cases are the whole proof: `ewp_W(M){opTable ⟦Σ⟧}{Q} ⇒ ewp_W(hnd_n H M){…}{…}` for any `H`.
- Route: the unary fact that `M` never stops at `n`, plus a simulation relating the frame
  `hnd_n H [·]` with the plain frame `(λx. h_ret x)[·]` at every configuration that does not
  stop at `n`: identical steps, then `[ret]` against `beta` in one step each, and forwarding
  joined as in L-HFWD. T-SI2 with the unary premise.
- Uses: K-HND, K-NAME, K-ROW.
- Today: "holds by lexical construction, with no theorem" (#235 L6). EffModelRel
  `no_accidental_handling`, `hnd_transparent` (`experiments/EffModelRel/EffModelRel/Laws.lean:362,
  312`) in the sibling. New over the kernel.
- Slices: 07 (T-NAH).
- Depends on: L-HFWD, L-HRET.
- Open: OQ-14 (re-entry of a site is the dynamic case), OQ-13, OQ-47.
- Obligation: unary **mechanical**; binary **unknown** (T-SI2).

### L-REN: renaming
- Form. For a bijection `π` of `Nm` fixing `0`, acting on names in terms, rows and types:

      Δ; Γ ⊢ e : C   ⇒   Δ; πΓ ⊢ π·e : π·C
      𝒞⟦π·C⟧_W δ (π·e)  ⟺  𝒞⟦C⟧_W δ e
      Δ; Γ ⊢ M ≡ N : C   ⇒   Δ; πΓ ⊢ π·M ≡ π·N : π·C

  For a closed handled computation the handler's name is invisible:
  `hnd_n H M ≡ hnd_m (π·H) (π·M)` with `π = (n m)` and `m` fresh for `H, M`.
- Binary: the third line.
- Unary: the second line, by induction on types; the step relation commutes with `π`, since
  `HasHnd`, `Catches` and `hndNames` compare names only for equality
  (`Paper/S3_Dynamics/Definitions.lean:386-420`).
- Route: the closed-handler line by a simulation along `π`, as TwoRun's `steps_rename`
  (`experiments/TwoRun/TwoRun/Rename.lean`) is for locations.
- Uses: K-REN, K-NAME, K-ROW.
- Today: not built over the kernel. EffModelRel `Rename.lean` renames instances in the sibling.
  The copies per name assignment (decision 57) rest on it. New.
- Slices: 02 (K-REN), 07 (T-REN), 08 (copies justified).
- Depends on: K-REN.
- Open: OQ-13, OQ-14.
- Obligation: unary **mechanical** (the step most likely non-mechanical: `cancelVal`'s name list
  under `π`); binary **mechanical** given T-SI2's simulation technique.

### L-NU: instance laws, only if generative instances are adopted
- Form. Under OQ-14 (b), with `ν a. M` allocating a fresh instance:

      idem-ν   ν a. M ≡ M                                   a ∉ M
      ν/ν      ν a. ν b. M(a, b) ≡ ν a. ν b. M(b, a)
      new-ν    ν b. (if ieq a b then M else N) ≡ ν b. N      a in scope
      ν/op     ν a. op_b(V; y. M) ≡ op_b(V; y. ν a. M)        a ∉ b, V;   at lin and aff only

  (Staton, LICS 2013 §IV-V [via 12-sources, laws via phase A]). ν/op fails at `unr`
  (`nu_op_fails_multishot`, `experiments/EffModelRel/EffModelRel/Examples.lean:223`). In the
  unmoded sibling it also fails at a linear operation (`nu_op_fails_linear`, `…/Ownership.lean:72`).
  That records the sibling's `CtxEq`, which does not read modes; it says nothing about the moded
  calculus, where it is the open `O1` (`…/Ownership.lean:93`).
- Binary: as above.
- Unary: none (generativity is binary).
- Route: ν/ν compares two allocation orders: `freshRun_det` (`experiments/TwoRun/TwoRun/
  Fresh.lean:255`) if instances are allocated as locations; OQ-43. The rest need `≈` with
  instance statuses (§1.6 item 4).
- Uses: K-NAME (generative).
- Today: the sibling's proofs, `idem_nu`, `new_nu`, `nu_nu`
  (`experiments/EffModelRel/EffModelRel/Laws.lean:242, 246, 262`). Not applicable to the kernel
  while names are static (`R-STATIC`).
- Slices: 02, 03 (a scope-confined `κ`, OQ-28).
- Depends on: OQ-14 (b).
- Open: OQ-14, OQ-16, OQ-4, OQ-43.
- Obligation: withdrawn under `R-STATIC`; **unknown** otherwise.

---

## 9. Borrows and lowering

### L-BOR: a borrow across an effect
- Form.
  - **Abortive half.** For a borrow constant `bor_k[Σ]` (O-BOR) whose callback stops at an
    abortive operation, the lend ends at the stop, LIFO, the lender regains the place, and the
    unwinding form's finaliser runs before the raise goes on:

        bor_k[Σ](s, λx. K[raise_{n,i} V])  ≡  D_lend ; raise_{n,i} V

    `D_lend` being the source's finaliser in the unwinding form (`withborUE d`,
    `Core/EffBorrow.lean:200`).
  - **Resuming half.** At a resuming stop the open lend is handed on with the continuation
    (D-STOP). Operationally a borrow frame is plain (the lend is ghost), so the binary form is
    L-ALG at that frame: `bor_k[Σ](s, λx. K[op(V; y.M)]) ≡ op(V; y. bor_k[Σ](s, λx. K[M]))`
    where the side condition admits it. Its unary half is the frame lemmas at a resuming
    `TableOK` table.
- Binary: as above.
- Unary: abortive: `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU`
  (`Core/EffWp.lean:828, 842, 854`), through the unwinding compat lemmas
  (`withbor1U_compatX`, `withbor2U_compatX`, `withbor3U_compatX`, `Core/EffBorrow.lean:446, 275,
  356`). Resuming: `ewpTS_M_frameR`, `ewpTS_I_frameR`
  (`experiments/GhostEnd/GhostEnd/Relend.lean:117`, `…/ImmLend.lean:175`), experiments; T-FRAME
  at every `TableOK` table: **unknown**.
- Route: abortive: reduction-shaped (the callback's raise unwinds the borrow's elaborated
  frames). Resuming: L-ALG's join; T-SI2.
- Uses: K-BOR, O-BOR, D-TABLEOK, D-STOP.
- Today: abortive half as cited; `failOutside_answers` (`Core/EffPrograms.lean:304`) is a closed
  instance in which the lend ends and the source's destructor frees the cell. Changed (one borrow
  per printed constant, at any `TableOK` row).
- Slices: 03 (K-BOR), 05 (T-FRAME, T-SUMOK), 07.
- Depends on: L-ALG, L-ALG0, T-FRAME.
- Open: OQ-2 (`R-T1` by default: only abortive operations cross a borrow's scope), OQ-7, OQ-9,
  OQ-10.
- Obligation: abortive **as built** (unary); resuming **unknown**.

### L-TAIL: a tail-resumptive clause is a direct call
- Form. Let `c_i = λ(p, κ). g p to r. resume κ r` with `g : A ⊸ F_∅ B`, closed, not mentioning
  `κ` (it performs nothing, suspends nothing and raises nothing: SPEC §19 *Lowering*,
  "A tail-resumptive operation is a direct call"). Then for `K` free of `n`:

      hnd_n H (K[perform_{n,i} V])  ≡  hnd_n H (K[g V])

- Binary: as above.
- Unary: by T-SI1 at each step, with `g V`'s run framed (`ewp_bind_pure_frame`,
  `Core/EffWp.lean:941`).
- Route: the left side takes `[op]`, `beta`, then runs `g V` in a `[let]` frame, then the four
  steps of L-BETA, and reaches `hnd_n H K[w]`. The right side runs `g V` inside `K`. `g V` is
  closed and performs nothing, so its run is the same in either context (`Steps.plug`), from the
  same memory and allocation count, since `[op]` and `beta` do not allocate. So the two sides join
  under every allocator, with `D` equality. T-SI2.
- Uses: K-HND, K-OP, K-KONT.
- Today: `op_tail` (`Core/Handlers.lean:76`) for the answering form over `withswap`; the
  lowering (SPEC §19 *Lowering*, `Backend/Clos/Capture.lean`). Not stated over `hnd`. New.
- Slices: 08 (T-LOWER's direct-call class; cost parity).
- Depends on: L-HOP, L-BETA.
- Open: OQ-23 (whether lowering correctness is a theorem), OQ-1.
- Obligation: **mechanical** given T-SI1, T-SI2.

---

## 10. What a binary relation adds (T16)

Each law, with what carries its binary form:

| law | unary half | binary form by joinability + T-SI2 | needs `≈` (or ReadFootprintTyped) |
|---|---|---|---|
| L-TO | `beta`; `ewp_frame_plain` | left unit one step; right unit, assoc after capture | — |
| β of L-UF, L-LAM, L-AMP, L-PAIR, L-CASE, L-BANG, L-ALL | T-SI1 | yes, one step | — |
| η of L-UF, L-LAM, L-AMP, L-PAIR, L-CASE, L-BANG, L-ALL | — | — | yes |
| L-NUB | identity on terms | as built | — |
| L-CC | T-SI1 | yes | — |
| L-ALG | `ewp_frame_plain` | yes, after capture | — |
| L-ALG0 | `ewp_frame_plain`, `ewp_frame_then` | yes, up to deleting plain frames | — |
| L-GEN | L-ALG's | yes | — |
| L-HRET, L-HOP | `ewp_handle` | yes, one step | — |
| L-HFWD | `ewp_handle` | yes, after capture | — |
| L-HUNIQ | `ewp_handle` as initiality (M2) | not known | yes, or a kernel `handle_unique` |
| L-HBIND | T-MODEL M2 twice | at a returning `M` | yes in general |
| L-HFUSE | via L-HUNIQ, tail case | — | yes |
| L-HCORR | — | some equations | yes |
| L-EXC | `opTable`, `ewp_handle` | yes | — |
| L-STATE | `withswap` compat | — | ReadFootprintTyped or `≈` |
| L-YIELD | `ewp_handle` | yes | — |
| L-ASYNC (codata form) | `ewp_handle`, K-NU | (A1)-(A3) yes | (A5) as L-TENSOR |
| L-SCOPE | L-ALG's | at the continuation | OQ-59 |
| L-ND | — | — | yes |
| L-DIV (a) | `cB` at leaves | yes | — |
| L-FIX | `boundedFix_compatX` | yes, one step | — |
| L-FOLD | `ewp_bind` per level | β yes | uniqueness |
| L-SUM (1) | interpretation | — (unary only) | — |
| L-SUM (4) | `opTable` | yes | — |
| L-TENSOR | frame | — | ReadFootprintTyped or `≈` |
| L-RUN | `IsComodel`, T-COMODEL | run-return, run-op, run-forward, run-bind | run-unique |
| L-SIGNAL (1), (2) | cancel lemmas | yes | — |
| L-INTER | — | under T13.13's hypotheses | yes in general |
| L-DISCARD | `ewp` interchange at the row | at the empty row | at a capability read |
| L-COPY, L-COMMUTE | `ewp` interchange; frame | — | yes |
| L-W | `KapRel`, `ewp_ccatch` | yes | — |
| L-C, L-P | typing | (not equations) | — |
| L-BETA | `ewp_kappa_resume` | yes, four steps | — |
| L-ETA | via L-HUNIQ | — | yes |
| L-HIDE | anti-frame | — | yes, per-cell relation |
| L-NAH | `ewp_handle` | yes, with the unary premise | — |
| L-REN | by induction on types | yes, along `π` | — |
| L-NU | — | ν/ν via `freshRun_det` | yes |
| L-BOR | frame lemmas | yes | — |
| L-TAIL | T-SI1 | yes | — |

So a binary relation adds, beyond T-SI2: uniqueness, fusion and correctness of handlers; the
theory equations of state and choice; tensor; η; binary hiding (representation independence);
the interaction law in general; and the instance laws. It adds nothing to the reduction-shaped
laws once T-SI2 holds. TwoRun's README reaches the same split for the Optics laws: locality and
determinism first, a scoped binary relation only for parametricity and representation
independence (`experiments/TwoRun/README.md`, *What would supply the read footprint*, routes (A)
and (B)). Whether `≈` is in scope is OQ-4 (audit Q4), and the default is (b).

---

## 11. The off-kernel proofs each law replaces

EffModelRel (S2-S4) is a model of a sibling calculus (OQ-5): no resources, no machine, unmoded
`CtxEq`. Each of its results is evidence for the law named here, not a kernel result.

| off-kernel result | file:line | kernel law |
|---|---|---|
| `alg_bind`, `alg_app`, `alg_prj1`, `alg_prj2`, `alg_iapp` | `experiments/EffModelRel/EffModelRel/Laws.lean:67, 76, 85, 90, 96` | L-ALG |
| `alg_ab_bind`, `alg_ab_app`, `alg_dtor` | `…/Laws.lean:102, 107, 114` | L-ALG0 |
| `h_ret` | `…/Laws.lean:148` | L-HRET |
| `h_op`, `kVal`, `kVal_den` | `…/Laws.lean:164, 137, 142` | L-HOP, L-BETA |
| `h_fwd`, `h_fwd_ab` | `…/Laws.lean:202, 227` | L-HFWD |
| `idem_nu`, `new_nu`, `nu_nu` | `…/Laws.lean:242, 246, 262` | L-NU |
| `no_accidental_handling`, `hnd_transparent` | `…/Laws.lean:362, 312` | L-NAH |
| `tensor` | `…/Tensor.lean:91` | L-TENSOR |
| `absorb_pure`; `absorb_writer`, `writer_pure` | `…/Tensor.lean:204`; `…/Examples.lean:115, 108` | L-SUM (4) |
| `not_absorb_print_inside`, `not_absorb_writer_outside`, `not_absorb_print_outside`, `not_absorb_runner_inside`, `lent_state_survives`, `print_print_not_commute` | `…/Examples.lean:136, 142, 148, 155, 167, 178` | L-SUM (2), (4) |
| `nu_op_fails_multishot`; `nu_op_fails_linear`, `O1` | `…/Examples.lean:223`; `…/Ownership.lean:72, 93` | L-NU, L-P |
| `fwd_id`; `eta_fails_linear`, `etaAff_leaks`, `etaAff_not_moded` | `…/Ownership.lean:112, 181, 237, 242` | L-ETA |
| `hnd_sim`, `hiding_counter` | `…/Ownership.lean:253, 402` | L-HIDE |
| `handle_return`, `handle_write`, `handle_unique`, `fold_unique` | `experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean:43, 50, 59`; `…/Fold.lean:207` | L-HRET, L-HOP, L-HUNIQ (pure, one effect) |
| `unfold_next`, `unfold_close` | `experiments/CoeffectsStrict/CoeffectsStrict/Unfold.lean:55, 67` | L-DIV |
| `op_tail`, `op_answer` | `Core/Handlers.lean:76, 133` | L-TAIL, L-STATE |
| `handle_fold` | `Core/Handlers.lean:211` | L-STATE (S2 iterated) |
| `abort_passes`, `return_resumes`, `loop_abort` | `Core/Handlers.lean:153, 167, 229` | the withdrawn sum encoding (decision 52); replaced by L-EXC, L-ALG0 |
| TR T7.1-T7.16, T13.2, T13.8, T13.13, P13.14 | `docs/effects-tr/07-laws.md`, `13-adjunction.md` | as cross-referenced in each entry |
| phase A's law suite | `experiments/EffModel/EffModel/Laws.lean:242` (`lawResults`) | the same laws, checked over finite context suites |

---

## 12. Open questions raised here

Boxed in [99](99-open-questions.md):

- **OQ-47**, whether reduction in every context is contained in `≡` (T-SI2), for each relation
  `D` of §1.3; it carries the binary forms of the reduction-shaped laws.
- **OQ-43** (shared with 04 and 07), two-run facts with array steps, which bears on L-NU's ν/ν
  and the allocating forms of L-STATE.
- **OQ-48**, answering/control commutation at an affine operation, on the kernel (L-INTER): P13.14 built in
  `CDerives`, or the law proved at `aff`.
- **OQ-49**, the composite handler `H₂ ∘ H₁` as a kernel term, which L-HFUSE needs, including the
  `n₂`-forwarding mismatch.
- **OQ-59** (with 03), how a handler reaches into a scope (L-SCOPE).
- **OQ-60**, the asynchronous scheduler against the negative-recursion cut-off (L-ASYNC).
- **OQ-61** (with 02, 03), operation types that perform their own effect (L-ASYNC's `spawn`).
- **OQ-62** (with 03), folds and counted loops at a row (L-FOLD).
- **OQ-64**, the effect-dependent laws (L-DISCARD, L-COPY, L-COMMUTE), with Kammar-Plotkin unread.
- **OQ-65**, an operation form with an explicit cancel continuation (R-ALGPLAIN, L-ALG).
- **OQ-66**, whether cancel is an instance of Ahman & Bauer's signal (L-SIGNAL).

Questions of the register this section carries (00 §8): OQ-4 (§1.6, §10), OQ-5 (§11), OQ-11
(§1.7), OQ-15 (§1.2's observation, L-DIV), OQ-16 (L-P, L-ND, L-NU), OQ-18 (§5), OQ-21 (L-ALG0, L-SIGNAL, L-W), OQ-22 (L-HCORR,
L-STATE, L-ND), OQ-27 (L-ETA), OQ-67 (L-DIV at K-HDIV's spanning form). Audit Q4 is OQ-4 and audit Q5 is OQ-5. Audit Q1, Q2, Q3, Q6 and Q7
are OQ-1, OQ-2, OQ-3, OQ-6 and OQ-7, cited where they bear on a law.

## 13. Section contract (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed to `ewp_W`.** `[TR]` 6.150 (the
reborrow) is not lifted to `ewpTS` at any table (00 §5.1, T-FRAME), so L-BOR's resuming half and
L-HIDE at a resuming table rest on a lift that does not exist. `[TR]` 6.64, 6.65 and 6.66 are
lifted at abortive tables in Core (`Core/EffWp.lean:828-854`) and at monotone tables only in
GhostEnd. `[TR]` 6.135 (`wp-bind`) and 6.146 (`wp-ramify`) are at `wpG` (`wpG_bind`,
`wpG_ramify`, `Core/EffWp.lean:878, 978`) and are used here as is.

**Printed hypotheses not spent.** `ewp_handle`'s `hTin` (`Core/EffRules.lean:616`: the inner and
outer tables agree off `n`) is what makes L-HFWD's stop pass outward unchanged. L-NAH spends it at
a row with no `n` entry; no other law here spends it beyond `ewp_handle`'s own use.
`ewp_frame_plain`'s `hFs` and `hFe` (the frame is stable under list permutation and `Ext`) are
spent only in the unary half of L-ALG.

**Uniqueness and functionality results not used.** `AStep1.deterministic`
(`Core/Demonic.lean:117`) is used for §1.2's totality of `Obs_A` and for T-SI1's backward
direction, which is not built. `head_det_eff` (`Core/Steps.lean:596`) is not used directly; T-SI2
needs it for decomposition at the capture-relating `D`. `fold_unique`'s total-algebra hypothesis
(`experiments/CoeffectsStrict/CoeffectsStrict/Fold.lean:177`) has no kernel counterpart yet; L-HUNIQ's
TwoRun form would need it at effectful clauses, where totality is `ewp`'s.

**Literature.** Each claim is marked [via #235], [via #279], [via 12-sources] or [via phase A]
as the report that read it marks it, read from the primary source, or [R] where the source could
not be read (Kammar-Plotkin POPL 2012, boxed as OQ-64). Ahman & Bauer, arXiv 1910.11629, was
fetched (05 §10); §2.1's Example 1, §2.2's proof of Prop. 3, §3.1's eq. (1) and the kernel theory's
equations below it, §3.2's text after eq. (3) and §5.3's Thm 7 are cited from it at L-STATE,
L-HUNIQ, L-RUN and L-SIGNAL. Plotkin & Power, *Notions of computation determine monads* (FoSSaCS
2002, the authors' copy) was fetched: its §2 Example 3 and §3's seven global-state axiom schemata
are cited at L-ND, L-STATE and L-TENSOR. Hyland, Plotkin & Power, *Combining effects: sum and
tensor* (TCS 2006, the authors' copy) was fetched: its §1 definitions of sum and tensor are cited at
L-TENSOR. Katsumata, Rivas & Uustalu (arXiv 1912.13477) was fetched: §3's definition of a
monad-comonad interaction law with diagrams (1) and §4's stateful runner are cited at L-RUN and
L-INTER. The abstract of Congard, Munch-Maccagnoni & Douence
(arXiv 2510.23517) was read for this section, and its statements of the strength of
`T(− ⊕ E)`, of destructors `δ : A → TI`, and of weakening and exchange performing side-effects
are cited from it; the readings drawn from it beyond what it states are marked [I]. The fusion
citation (Wu & Schrijvers) is unverified, as #235 marks it. The [R] marks are motivation only and
back no proof sketch.
