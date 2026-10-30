# §5 The unary relation: resource safety

[← §4 Worlds](04-worlds.md) · [index](README.md) · next: [§6 The binary relation](06-binary.md)

The unary relation is BoLo's `wp` ([TR] p. 6) over this calculus's machine, extended by
protocols as SPEC §19's `ewpTS` extends it, with the three meeting points of §4.2 as its only
heap-specific definitions. Its Fundamental Property (T5.1) gives resource safety (T5.2):

- a typed closed program never gets stuck and terminates;
- it ends with an empty heap;
- every resource is finalised exactly once, including on cancel and on a co-operation's failure;
- no one-shot continuation is resumed twice.

The key lemma is independence (L5.4), used through frame composition (L5.6). There is no step
index: `wpG` is total correctness, `ewp` is a least fixed point written in `Prop`, and the one
recursive type is interpreted by a least fixed point (D5.4).

Status: every lemma here is proved on paper. None is mechanised. The structure is the
structure of borrow-core's `Core/EffWp.lean` and `Core/EffRules.lean` (§19) and of [TR] §6.8;
§11 lists the correspondence lemma by lemma.

---

## 5.1 `wp` with protocols

**Definition D5.1 (relative runs).** For a stack `S` and control `c`, a configuration
`⟨μ, n, tr ; S' ; c'⟩` reached from `⟨μ₀, n₀, tr₀ ; S ; c⟩` is **final relative to `S`** when it
is

- `done v̂`: `c' = rt v̂` and `S' = []`;
- `stop(S₁, j, o, v̂, γ, y.M)`: `c' = ev(op x.o(V; y.M), γ)` with `γ(x) = j`, `⟦V⟧γ = v̂`, `S' = S₁`,
  and `j` not handled in `S₁`;
- `abstop(S₁, j, a, v̂)`: likewise for `ab x.a(V)`.

**Lemma L5.1 (extension).** If `⟨μ, n, tr ; S ; c⟩ →* ⟨μ', n', tr' ; S' ; c'⟩` and no
configuration on the way is final relative to `S`, then for every `S₀`,
`⟨μ, n, tr ; S ++ S₀ ; c⟩ →* ⟨μ', n', tr' ; S' ++ S₀ ; c'⟩`.

*Proof.* By induction on the run. Each row of D3.6 inspects only the control, the top frames,
and `split_j`. A non-final configuration whose step reads `split_j(S')` has `j` handled in `S'`,
and `split_j(S' ++ S₀) = (S₁, f, S₂ ++ S₀)` is the same split. A return reads the top frame,
which exists because `S' ≠ []` (else the configuration is `done`). ∎

**Definition D5.2 (`wpG`).** For a predicate `Φ` over final configurations and resources,

    wpG(S, c){Φ}(r)  ≜  ∀ r_f # r.  ∀ n fresh for ⟦r_f ● r⟧, S, c.  ∀ tr.
                          ∃ r', r⁺, t, n', tr'.  r' # r_f  ∧  r⁺ # (r_f ● r')
                          ∧ ⟨⟦r_f ● r⟧, n, tr ; S ; c⟩ →* ⟨⟦r_f ● r' ● r⁺⟧, n', tr' ; t⟩
                          ∧ t final relative to S
                          ∧ r ↭ r' ● r⁺  ∧  r⁺|own = ∅  ∧  Φ(t)(r')

This is [TR] p. 6's `wp(e){Q̂}` with the run ending at a final configuration instead of a value,
as SPEC §19's `wpG`. "Fresh for" means larger than every location of the heap and every instance
name in `S` and `c`. By L4.1 the conjunct `r ↭ r' ● r⁺` is trivial here; it is kept so the
definition does not change in the lift. [borrow-core `Core/EffDefs.lean` `wpG`, which adds the
tagged-world conjuncts `TW`, `Tagged` of borrow-core's lifetime records and quantifies the
allocator; this calculus has no lifetime records, and its allocator is the counter.]

**Definition D5.3 (`ewp`).** For a table `T` (D4.8) and a postcondition `Q` over values,
`ewp_T(S, c){Q}` is the least predicate `P` on `(S, c, r)` such that `wpG(S, c){Φ_P}(r) ⇒ P(S, c)(r)`,
where

    Φ_P(done v̂)                     ≜  Q(v̂)
    Φ_P(stop(S₁, j, o, v̂, γ, y.M))  ≜  (j, E) ∈ T  ∧  Π_E(o, v̂, λw. P(bind(γ, y.M) :: S₁, rt w),
                                                                Cancel(bind(γ, y.M) :: S₁))
    Φ_P(abstop(S₁, j, a, v̂))        ≜  (j, E) ∈ T  ∧  Π_E(a, v̂, Cancel(S₁))

`Φ_P` is monotone in `P` because each `Π_E` is monotone in `Φ` (D4.6), so the least fixed point
exists (Knaster–Tarski), written in `Prop` as the intersection of all closed predicates.
[SPEC §19 `ewpTS`; borrow-core `Core/EffDefs.lean` `ewpStep`, `ewpTS`.]

**Lemma L5.2 (`ewp` rules).** [borrow-core `Core/EffWp.lean`: `ewp_fold`, `ewp_unfold`,
`ewp_ind`, `ewp_val`, `ewp_mono`, `ewp_step`, `ewp_bot`.]

1. *(fold/unfold)* `ewp_T(S, c){Q} = wpG(S, c){Φ_{ewp_T(·){Q}}}`.
2. *(induction)* If `wpG(S, c){Φ_P} ⊆ P(S, c)` for all `(S, c)`, then `ewp_T(S, c){Q} ⊆ P(S, c)`.
3. *(value)* `Q(v̂)(r) ⇒ ewp_T([], rt v̂){Q}(r)`.
4. *(monotone)* `Q ⊆ Q'` and `T ⊆ T'` give `ewp_T{Q} ⊆ ewp_{T'}{Q'}`.
5. *(step)* If `⟨μ, n, tr ; S ; c⟩ → ⟨μ, n, tr' ; S' ; c'⟩` by a step that does not read or write
   the heap, then `ewp_T(S', c'){Q} ⊆ ewp_T(S, c){Q}`.
6. *(heap steps)* For the steps that allocate, read, write or remove a cell, the rule of [TR]
   §6.7 at the own fragment: allocation 6.141 (`wp-alloc`), removal 6.142 (`wp-free`), read
   6.143 (`wp-load`), write 6.145 (`wp-store`), each with `ewp` in place of `wp`, at the cell
   kinds of D3.2.
7. *(sequencing of `wpG`)* `wpG(S, c){λt. wpG(t){Φ}} ⊆ wpG(S, c){Φ}` when every `t` with a
   non-trivial inner `wpG` is `done` followed by a continuing configuration. This is [TR] 6.135
   (`wp-bind`) at the machine.

*Proof.* (1)–(4) are the Knaster–Tarski facts and the monotonicity of `wpG` and `Π_E`. (5): the
step is deterministic (L3.1) and frame-independent; prefix it to the run `wpG` provides. (6): as
[TR]'s proofs of 6.141–6.145, at own cells, using L4.1.4 for the lowering. (7): concatenate the
runs; the frame `r_f` of the second is `r_f` of the first, and `r⁺` accumulates (`NoOwn` is
closed under `●`, L4.2.2; `↭` composes by [TR] 6.48 and 6.49). ∎

**Lemma L5.3 (dropping).** If `R ∈ NoOwn` and `R # r`, then
`ewp_T(S, c){Q}(r) ⇒ ewp_T(S, c){Q}(r ● R)`.

*Proof.* By L5.2.2 on the left. In the `wpG` of the hypothesis, place `R` into the left-over:
`r⁺_new ≜ r⁺ ● R`. `(r⁺ ● R)|own = ∅` (L4.2.2), the lowering is the same heap
(`⟦r_f ● r ● R⟧ = ⟦(r_f ● R) ● r⟧`: run the hypothesis at frame `r_f ● R`), and
`r ● R ↭ r' ● r⁺ ● R` by [TR] 6.48. At a stop the continuation obligations are the hypothesis's,
unchanged. ∎

This is how a variable used in one branch only is disposed of (L5.5), and it is BoLo's forget
([TR] 6.148, 6.149) at the own fragment.

## 5.2 The relation

**Definition D5.4 (value relation).** `V⟦A⟧_π : v̂ → Res → Prop`, mutually with D5.5, by
recursion on `A`, for a protocol environment `π` (D4.8):

    V⟦G⟧(v̂)(r)            ≜  v̂ ∈ ⟦G⟧  ∧  r = ∅
    V⟦A ⊗ B⟧((v̂₁, v̂₂))(r)  ≜  ∃ r₁ # r₂.  r = r₁ ● r₂ ∧ V⟦A⟧(v̂₁)(r₁) ∧ V⟦B⟧(v̂₂)(r₂)
    V⟦A ⊕ B⟧(inl v̂)(r)     ≜  V⟦A⟧(v̂)(r)        (inr alike)
    V⟦U_m^ρ C⟧(v̂)(r)       ≜  r ∈ ⟦m⟧  ∧  E⟦C⟧^{Tab_π(ρ)}(force-of(v̂))(r)
    V⟦cap_E S⟧(cap(ℓ, co))(r) ≜ ∃ s ∈ ⟦S⟧.  r = Cap(ℓ, s)  ∧  CoOK_E^S(co)
    V⟦tkt⟧(tkt_n)(r)       ≜  r = ∅
    V⟦strm^ρ A⟧            ≜  lfp_P. λ v̂ r. ∃ v̂'. v̂ = fold v̂' ∧ V⟦U_lin^∅ (F (A ⊕ (int ⊗ X)) &^{ρ,∅} F 1)⟧_{π[X↦P]}(v̂')(r)

- `force-of(v̂)` is the control `ev(force y, [y ↦ v̂])`. It is uniform over closures and both kinds
  of continuation: what `force` of a `κ¹` removes from the heap is in `r` (D4.4).
- `CoOK_E^S(co) ≜ ∀ o, p ∈ ⟦A_o⟧, s ∈ ⟦S⟧. ewp_∅([], ev(N_o, [p, s])){V⟦(B_o ⊗ S) ⊕ (E_o ⊗ S)⟧}(∅)`:
  the co-operations run in place, with no resource and no stop.
- In the `strm` clause `X` is interpreted by `P` (`V⟦X⟧ ≜ P`). `X` occurs only positively (to
  the right of `F`, under `⊕` and `⊗`, D1.6), and `ewp` is monotone in its postcondition
  (L5.2.4), so the operator is monotone and the least fixed point exists in the complete lattice
  `v̂ → Res → Prop`. [PB `StrmRel`: the same construction for the binary relation.]

**Definition D5.5 (computation relation).** Computations are related through their
eliminations. For a table `T`, `Elim_T(C)` is the set of tuples `(S_e, A, T_e, r_e)` (an
elimination stack, the type it reaches, the table it reaches, and the resource of its arguments):

    Elim_T(F A)             = {([], A, T, ∅)}
    Elim_T(A' ⇒^ρ C)        = {(arg v̂ :: S_e, A, T_e, r_a ● r_e) |
                                 V⟦A'⟧(v̂)(r_a), r_a ∈ ⟦bnd(T).req⟧, (S_e, A, T_e, r_e) ∈ Elim_{T ∪ Tab(ρ)}(C)}
    Elim_T(C₁ &^{ρ₁,ρ₂} C₂)  = {(prjᵢ :: S_e, …) | (S_e, …) ∈ Elim_{T ∪ Tab(ρᵢ)}(Cᵢ), i ∈ {1,2}}
    Elim_T(Π^ρ(x:E^b). C)   = {(iarg j :: S_e, …) | j a name of effect E, (S_e, …) ∈ Elim_{T ∪ Tab_{π[x↦j]}(ρ)}(C) at π[x↦j]}
    Elim_T(∀^ρ(r ≤ b). C)   = {(S_e, …) | T_r a table with bnd(T_r).req ≤ b.req, (S_e, …) ∈ Elim_{T ∪ Tab_{π[r↦T_r]}(ρ)}(C) at π[r↦T_r]}

and

    E⟦C⟧^T(c)(r)  ≜  ∀ (S_e, A, T_e, r_e) ∈ Elim_T(C).  r # r_e ⇒ ewp_{T_e}(S_e, c){V⟦A⟧}(r ● r_e)

*Why the constraint `r_a ∈ ⟦bnd(T).req⟧`.* An argument waits on the stack while the computation
performs the operations of `T` before taking it, so it is captured by their continuations
(phase A's argument-frame check, D2.6). The constraint is what [app] supplies (L5.11).

**Lemma L5.4 (independence).**

1. *(modes are sound)* `V⟦A⟧_π(v̂)(r) ⇒ r ∈ ⟦mode(A)⟧`.
2. *(independence)* If `capture(Γ, X, m)` and `r ∈ G⟦Γ|_X⟧_u(γ)` (D5.6), then `r ∈ ⟦m⟧`.
3. *(arguments)* If `(S_e, A, T_e, r_e) ∈ Elim_T(C)` then `r_e ∈ ⟦bnd(T).req⟧`, and `S_e` has no
   `fin`, `hnd` or `run` frame.

*Proof.* (1) By induction on `A`. `G`, `tkt`: `r = ∅ ∈ ⟦m⟧` for every `m` (L4.2.2). `A ⊗ B`:
`r = r₁ ● r₂` with `rᵢ ∈ ⟦mode(·)⟧` by induction; `mode(A) ≥ mode(A) ⊓ mode(B)` gives
`r₁ ∈ ⟦mode(A ⊗ B)⟧` (L4.2.1), likewise `r₂`, and `⟦·⟧` is closed under `●` (L4.2.2). `A ⊕ B`
alike, without the composition. `U_m^ρ C`: the first conjunct. `cap`, `strm`:
`⟦lin⟧ = Res`. (2) Each `r_x ∈ ⟦mode(Γ(x))⟧ ⊆ ⟦m⟧` by (1) and L4.2.1, as `mode(Γ(x)) ≥ m`; then
closure under `●`. (3) By induction on the definition of `Elim`. Each argument's `r_a` is in
`⟦bnd(T').req⟧` for the table `T' ⊇ T` at its position; `bnd` is monotone in the table, so
`bnd(T').req ≥ bnd(T).req` and `⟦bnd(T').req⟧ ⊆ ⟦bnd(T).req⟧` (L4.2.1); closure under `●`.
The frames are `arg`, `prj`, `iarg` by construction. ∎

This is the declaration of independence made semantic: a thing at mode `m` holds only resources
`⟦m⟧` admits, so a continuation that captures only things at modes `≥ m` holds a resource in
`⟦m⟧`, and may be dropped (`W ∈ m`) or copied (`C ∈ m`) by L4.2.3–4.

**Definition D5.6 (context relation).** `G⟦Γ⟧_{u,π}(γ)(r) ≜ ∃ (r_x).  r = ●_{x : u(x) ≠ [0,0]} r_x
∧ ∀ x. V⟦Γ(x)⟧(γ(x))(r_x)`.

**Lemma L5.5 (splitting contexts).** Let `u` be admissible for `Γ` (D2.3).

1. If `u = u₁ + u₂`, then `G⟦Γ⟧_u(γ)(r) ⇒ ∃ r₁, r₂. r = r₁ ● r₂ ∧ G⟦Γ⟧_{u₁}(γ)(r₁) ∧ G⟦Γ⟧_{u₂}(γ)(r₂)`.
2. If `u = u₁ ⊔ u₂`, then `G⟦Γ⟧_u(γ)(r) ⇒ ∃ r₀ ∈ NoOwn. r = rᵢ ● r₀ ∧ G⟦Γ⟧_{uᵢ}(γ)(rᵢ)` for each `i`.
3. If `u = ω·u₁`, then `G⟦Γ⟧_u(γ)(r) ⇒ r ∈ Pers ∧ G⟦Γ⟧_{u₁}(γ)(r)`.

*Proof.* Variable by variable. (1) A variable used on both sides has `hi(u(x)) = 2`, so
`C ∈ mode(Γ(x))` (D2.3 and L2.1.2), so `r_x ∈ Pers` (L5.4.1, L4.2.4) and `r_x = r_x ● r_x`;
give a copy to each side. A variable used on one side goes there. (2) A variable used in `u` but
not in `uᵢ` has `lo(u(x)) = 0`, so `mode(Γ(x)) ≠ lin` (D2.3), so `r_x ∈ NoOwn` (L4.2.1 with
`⟦m⟧ ⊆ ⟦cancel⟧` or `⊆ Pers ⊆ NoOwn`); it goes into `r₀`. (3) `ω·u₁` has `hi = 2` wherever it is
non-zero; as in (1) every such `r_x ∈ Pers`, and `Pers` is closed under `●`. ∎

**Definition D5.7 (semantic judgement).**

    Ψ; Θ; Γ ⊧ M : C ! ρ ▷ u  ≜  ∀ π for Ψ, Θ.  ∀ γ, r.  G⟦Γ⟧_{u,π}(γ)(r) ⇒ E⟦C⟧^{Tab_π(ρ)}(ev(M, γ ∪ π))(r)
    Ψ; Θ; Γ ⊧ V : A ▷ u      ≜  ∀ π, γ, r.  G⟦Γ⟧_{u,π}(γ)(r) ⇒ V⟦A⟧(⟦V⟧γ)(r)

for `u` admissible. "`π` for `Ψ, Θ`" assigns each `x : E^b` a name of effect `E` and each
`r ≤ b` a table whose effects have `bnd(E').req ≤ b.req`.

## 5.3 Frame composition: where independence is used

**Definition D5.8 (compatible frames).** A segment `S₀` with resource `R₀` is *compatible* with a
table `T` when `S₀` handles no name of `T` and, for every `(j, E) ∈ T`:

- for every resuming `o` of `E`: `C ∈ q_o ⇒ R₀ ∈ Pers`, and `W ∈ q_o ⇒ Cancel(S₀)(R₀)`;
- if `E` has an abortive operation: `Cancel(S₀)(R₀)`.

**Lemma L5.6 (frame composition).** Let `S₀` with `R₀` be compatible with `T`. If
`ewp_T(S, c){Q}(r)`, and `∀ v̂, r_v. Q(v̂)(r_v) ⇒ ewp_{T'}(S₀, rt v̂){Q'}(r_v ● R₀)`, then
`ewp_{T ∪ T'}(S ++ S₀, c){Q'}(r ● R₀)`.

*Proof.* By L5.2.2 on the first hypothesis, with
`P(S, c)(r) ≜ ewp_{T∪T'}(S ++ S₀, c){Q'}(r ● R₀)`. Assume `wpG(S, c){Φ_P}(r)`; show
`P(S, c)(r)` by L5.2.1, i.e. `wpG(S ++ S₀, c){Φ'}(r ● R₀)` for the composite's `Φ'`.

Take the frame `r_f` of the goal; run the hypothesis at frame `r_f ● R₀`, and lift its run by
L5.1 (the stack `S₀` below). The run ends at `t`, final relative to `S`, with `Φ_P(t)(r')`.

- `t = done v̂`: the composite is at `⟨… ; S₀ ; rt v̂⟩`, not final. `Φ_P(done v̂) = Q(v̂)` gives
  `Q(v̂)(r')`, so by the second hypothesis `ewp_{T'}(S₀, rt v̂){Q'}(r' ● R₀)`; continue the run with
  it (L5.2.7, and L5.2.4 for `T' ⊆ T ∪ T'`).
- `t = stop(S₁, j, o, v̂, γ, y.M)`: `j` is not handled in `S₀` (compatibility), so the composite
  is at `stop(S₁ ++ S₀, j, …)`, final. Its resource is `r' ● R₀`. Show `Π_E(o, v̂, Φ'', Cancel(bind :: S₁ ++ S₀))(r' ● R₀)`
  from `Π_E(o, v̂, λw. P(bind :: S₁, rt w), Cancel(bind :: S₁))(r')`:
  - `C ∈ q_o`: `r' ∈ Pers` and `R₀ ∈ Pers` (compatibility), so `r' ● R₀ ∈ Pers` (L4.2.2);
  - resumption: `P(bind :: S₁, rt w)(r')` is by definition of `P` the composite's obligation
    `ewp((bind :: S₁) ++ S₀, rt w)(r' ● R₀)`;
  - `W ∈ q_o`: `Cancel(bind :: S₁)(r')` and `Cancel(S₀)(R₀)` give
    `Cancel(bind :: S₁ ++ S₀)(r' ● R₀)`, since the `fin` frames of a concatenation are the union
    and `NoOwn` is closed under `●` (D4.5, L4.2.2).
- `t = abstop(S₁, j, a, v̂)`: as the previous case, with `Cancel` only. ∎

This lemma is where the four capture rules of D2.6 pay off. Each compatibility lemma below
pushes one frame and discharges D5.8 from its rule's independence premise through L5.4.

## 5.4 Compatibility lemmas

Each lemma is the semantic counterpart of one rule of Figure 2.1: from `⊧` of the premises,
`⊧` of the conclusion. The pattern of the routine ones is [TR] 6.152–6.160; only the new or
changed steps are written in full. In each, fix `π`, `γ`, `r ∈ G⟦Γ⟧_u(γ)` and an elimination
`(S_e, X, T_e, r_e) ∈ Elim_T(C)` of the conclusion's type, `T = Tab_π(ρ)`.

**Lemma L5.7 (routine rules).** [var], [const], [pair], [inj], [ret], [lam], [force], [rcd],
[prj], [split], [case], [if], [absurd], [prim], [emit], [punch], [ieq], [ilam], [iapp], [rlam],
[rapp], [fold], [unfold], [sub] are compatible.

*Proof.* Each is a pure step (L5.2.5) or a value case, plus L5.5 to split the context, as
[TR] 6.152–6.160:

- **[lam]**: `S_e = arg v̂ :: S_e'` by `Elim`; the step binds `x`; the body's hypothesis at
  `r ● r_a`, where `r_a` is in `V⟦A⟧`.
- **[case], [if]**: L5.5.2, the branch's hypothesis, and L5.3 to drop `r₀`.
- **[rcd]**: `S_e = prjᵢ :: S_e'`; the step selects the method; L5.5.2 and L5.3.
- **[iapp]**: `Elim` of `Π` admits `iarg π(y)`, whose effect is `E` (rule premise).
- **[rapp]**: the table `Tab_π(σ)` has `bnd(Tab_π σ).req ≤ bound(σ).req ≤ b.req` (premise
  `bound(σ) ⊑ b`, and `bnd ≤ bound` because a handler's or runner's bound has the same `req` as
  its effect's or a smaller one).
- **[fold], [unfold]**: the `strm` relation is a fixed point (D5.4), so `V⟦strm A⟧(fold v̂)` and the
  thunk relation of its body are interderivable.
- **[sub]**: L5.8 below.
- **[absurd]**: `V⟦0⟧` is empty.
- **[ieq]**: `rt (π(x) = π(y))`, a ground value at `∅`. ∎

**Lemma L5.8 (subsumption).** If `A ≤ A'` then `V⟦A⟧ ⊆ V⟦A'⟧`; if `C ≤ C'` and `T ⊆ T'` then
`E⟦C⟧^T ⊆ E⟦C'⟧^{T'}`.

*Proof.* By induction on the subtyping derivation. Modes: `m ≥ m'` gives `⟦m⟧ ⊆ ⟦m'⟧` (L4.2.1).
Rows: a larger row is a larger table. `Elim_{T'}(C') ⊆ Elim_T(C)` up to the same eliminations,
because the argument constraint `⟦bnd(T').req⟧ ⊆ ⟦bnd(T).req⟧` is stronger; and `ewp` is
monotone in its table (L5.2.4). Contravariant argument types use the induction hypothesis in the
other direction. ∎

**Lemma L5.9 (thunk, with independence).** [thunk] is compatible.

*Proof.* `⟦thunk_m M⟧γ = clo(γ, M)`. The resource is `r ∈ G⟦Γ⟧_u(γ)`, `u` the usage of `M`, all
of whose variables are in `fv(M)`. By the premise `capture(Γ, fv(M), m)` and L5.4.2,
`r ∈ ⟦m⟧`: the first conjunct of `V⟦U_m^ρ C⟧`. For the second, `force-of(clo(γ, M))` steps to
`ev(M, γ)` (L5.2.5), and the premise gives `E⟦C⟧^{Tab(ρ)}`. ∎

**Lemma L5.10 (`to`, with independence).** [to] is compatible.

*Proof.* `M to x. N` steps to `ev(M, γ)` on `bind(γ, x.N) :: S_e`. Split `r = r_M ● r_N` (L5.5.1).
Apply L5.6 with `S = []`, `c = ev(M, γ)`, `S₀ = bind(γ, x.N) :: S_e`, `R₀ = r_N ● r_e`, and
`T = Tab(ρ₁)`:

- *compatibility*: `S₀` has no handling frame (L5.4.3). `r_N ∈ ⟦bound(ρ₁).req⟧` by the premise
  `capture(Γ, fv(N) ∖ x, bound(ρ₁).req)` and L5.4.2, and `⟦bound(ρ₁).req⟧ ⊆ ⟦bnd(T).req⟧`;
  `r_e ∈ ⟦bnd(T_C).req⟧` for the conclusion's table `T_C ⊇ T` (L5.4.3), so
  `r_e ∈ ⟦bnd(T).req⟧`. So `R₀ ∈ ⟦bnd(T).req⟧`. For `(j, E) ∈ T` and a resuming `o` with
  `C ∈ q_o`: `C ∈ bnd(E).req ≤ bnd(T).req` (L2.2.4), so `⟦bnd(T).req⟧ ⊆ Pers` (L4.2.4). With
  `W ∈ q_o`, or an abortive operation: `⟦bnd(T).req⟧ ⊆ NoOwn` (L4.2.3), and `S₀` has no `fin`
  frame, so `Cancel(S₀)(R₀)`.
- *first hypothesis*: `M`'s at `Elim(F A) = {[]}`;
- *second hypothesis*: from `⟨S₀ ; rt v̂⟩` the step enters `N` with `x ↦ v̂`, and `N`'s hypothesis
  at `r_v ● r_N` with `S_e`. ∎

**Lemma L5.11 (application, with independence).** [app] is compatible.

*Proof.* `M V` steps to `ev(M, γ)` on `arg ⟦V⟧γ :: S_e`. Split `r = r_M ● r_V`. By `V`'s hypothesis
`V⟦A⟧(⟦V⟧γ)(r_V)`, so `r_V ∈ ⟦mode(A)⟧` (L5.4.1) `⊆ ⟦bound(ρ₀).req⟧` (premise
`mode(A) ≥ bound(ρ₀).req`, L4.2.1) `⊆ ⟦bnd(Tab(ρ₀)).req⟧`. So `(arg ⟦V⟧γ :: S_e, …, r_V ● r_e)` is
in `Elim_{Tab(ρ₀)}(A ⇒^ρ C)`, and `M`'s hypothesis applies. ∎

**Lemma L5.12 (operation, with independence).** [op] is compatible.

*Proof.* `ev(op x.o(V; y.M), γ)` on `S_e` is final relative to `S_e`: `stop(S_e, π(x), o, v̂, γ, y.M)`
(`S_e` handles nothing, L5.4.3). Its resource is `r_M ● r_e` (`V` is ground, at `∅`). Show
`Π_E(o, v̂, λw. ewp(bind(γ, y.M) :: S_e, rt w), Cancel(bind(γ, y.M) :: S_e))(r_M ● r_e)`:

- `r_M ∈ ⟦b_x.req⟧` by the premise `capture(Γ, fv(M) ∖ y, b_x.req)` and L5.4.2, and
  `q_o ≤ b_x.req` because `Ψ` is well formed (D1.5: `bnd(E).req ≤ b_x.req`). `r_e ∈ ⟦bnd(T).req⟧`
  (L5.4.3) with `(π(x), E) ∈ T`, so `r_e ∈ ⟦bnd(E).req⟧`, and `q_o ≤ bnd(E).req` (L2.2.4).
- `C ∈ q_o` ⇒ both parts in `Pers` (L4.2.4); `W ∈ q_o` ⇒ both in `NoOwn` (L4.2.3), and the segment
  has no `fin` frame: `Cancel`.
- resumption: from `⟨bind(γ, y.M) :: S_e ; rt w⟩` the step enters `M` with `y ↦ w`; `M`'s
  hypothesis. ∎

**Lemma L5.13 (abortive operation).** [ab] is compatible.

*Proof.* `abstop(S_e, π(x), a, v̂)` with resource `r_e`. `Π_E(a, v̂, Cancel(S_e))(r_e)` needs
`Cancel(S_e)(r_e)`: `r_e ∈ ⟦bnd(T).req⟧ ⊆ ⟦cancel⟧ = NoOwn` because `E` has an abortive operation,
so `cancel ≤ bnd(E).req ≤ bnd(T).req`. ∎

**Lemma L5.14 (handler).** [handle] and [handleAt] are compatible.

*Proof.* Write `j` for the handled name (fresh for [handle], `π(x)` for [handleAt]) and
`f_H = hnd(j, γ, H)`. Split `r = r_M ● R_H` (L5.5.1), `R_H` the clauses' part, of usage
`u_once' + u_many`; further `R_H = R_once ● R_many` with `R_many ∈ Pers` (L5.5.3). The step pushes
`f_H` on `S_e` and enters `M`. By `M`'s hypothesis at the table `T_M = Tab(ρ) ∪ {(j, E)}`,
`ewp_{T_M}([], ev(M, γ[x↦j])){V⟦A⟧}(r_M)`. By L5.2.2, show for every `(S, c, r')` in the least
fixed point:

    (★)  ewp_{T_e}(S ++ f_H :: S_e, c){V⟦X⟧}(r' ● R_H ● r_e)

Assume `wpG(S, c){Φ_★}(r')`. Run it at frame `r_f ● R_H ● r_e`, lifted by L5.1 (`f_H :: S_e`
below). It ends at `t`:

1. **`done v̂`.** The step enters `N_ret` with `z ↦ v̂` on `S_e`. Split `R_H = R_ret ● R_rest` with
   `R_rest ∈ NoOwn` (L5.5.2 at `u_once ⊔ …`, and `R_many ∈ Pers ⊆ NoOwn`). `N_ret`'s hypothesis
   at `V⟦A⟧(v̂)(r'') ● R_ret`, then L5.3 for `R_rest`.
2. **A stop on `j` at a resuming `o`**, segment `S₁`, resource `r''`, with
   `Π_E(o, v̂, λw. ★(bind :: S₁, rt w), Cancel(bind :: S₁))(r'')` (writing `bind` for the op's
   frame). The machine builds `κ` over `S_κ = bind :: S₁ ++ [f_H]` (and a cell `ℓ_κ` if
   `C ∉ q_o`), and enters `N_o` on `S_e` with `k ↦ κ`. Its resource is `r'' ● R_H` (●
   `ℓ_κ ↦ own(seg S_κ)` for `κ¹`). Show `V⟦K(q_o, B_o, ρ ∪ ρ_h, C)⟧(κ)(r'' ● R_H [● ℓ_κ…])`:
   - **mode** (D1.8): if `C ∈ q_o`, the mode is `unr` or `rel` and the resource must be `Pers`:
     `r'' ∈ Pers` by the protocol, `R_H ∈ ⟦⨆_o q_o⟧ ⊆ Pers` by the premise
     `capture(Γ, fv(H), … ⊔ ⨆_o q_o)` and L5.4.2, L4.2.4; there is no `ℓ_κ`. Otherwise
     `q_o ∈ {lin, cancel}` and the type is a `lin` thunk (D1.8), which asks nothing of the resource.
   - **resume** (eliminations `[prj₁,] arg w :: S_e'`): forcing removes `ℓ_κ` (it is in the
     resource) and reaches `⟨S_κ ++ S_e' ; rt w⟩ = ⟨bind :: S₁ ++ f_H :: S_e' ; rt w⟩`, which is
     (★) at `(bind :: S₁, rt w)` with `S_e'` for `S_e`: the induction hypothesis, given by the
     protocol's resumption conjunct.
   - **cancel** (eliminations `prj₂ :: S_e'`, only if `W ∈ q_o`): the machine runs
     `dtors(S_κ)`, which are those of `bind :: S₁` (`f_H` has none). `Cancel(bind :: S₁)(r'')` by
     the protocol: each `fin` frame's resource is in `r''`, so each free succeeds (L5.2.6, 6.142),
     leaving `r₀ ∈ NoOwn`; `R_H ∈ NoOwn` because `W ∈ q_o ≤ ⨆ q_o` (L4.2.3). Then `rt ()` at
     `V⟦1⟧`, and L5.3 drops the rest.
   Then `N_o`'s hypothesis, at `R_many` (shared, `Pers`) and the `κ` resource, gives (★).
3. **An abortive stop on `j`**, segment `S₁`, with `Cancel(S₁)(r'')`: the machine runs
   `dtors(S₁)` and enters `N_a`. As the cancel case of 2, then `N_a`'s hypothesis at `R_a ⊆ R_H`
   with the rest dropped (L5.5.2, L5.3).
4. **A stop on `j' ≠ j`**, `(j', E') ∈ Tab(ρ)`. The composite is at a stop with segment
   `S₁ ++ f_H :: S_e` and resource `r'' ● R_H ● r_e`. This is L5.6's stop case with
   `S₀ = f_H :: S_e`, `R₀ = R_H ● r_e`; compatibility: `R_H ∈ ⟦bound(ρ).req⟧` by the premise's
   first part and L5.4.2, `r_e` by L5.4.3, and neither `f_H` nor `S_e` has a `fin` frame. The
   resumption obligation is (★) by induction. (This case is forwarding.) ∎

[SPEC §19 *Theorems* 1, `handle_compatC`'s four cases; borrow-core `Core/EffRules.lean`
`ewp_handle`.]

**Lemma L5.15 (lend: capabilities are resources).** [lend] is compatible.

*Proof.* `⟦V⟧γ = cap(ℓ, co)` with `V⟦cap_E S⟧`: `r_V = Cap(ℓ, s₀)` and `CoOK(co)`. The step checks
`μ(ℓ) = cell(s₀)` (owned: in the heap), takes a fresh `j`, pushes `f_L = run(j, ℓ, co)` and
enters `M`. By `M`'s hypothesis at `T_M = Tab(ρ) ∪ {(j, E)}`. Show by L5.2.2, for every `(S, c, r')`
in the fixed point and every state `s`:

    (★)  ewp_{T_e}(S ++ f_L :: S_e, c){V⟦cap ⊗ (A ⊕ int)⟧}(r' ● Cap(ℓ, s) ● r_e)

1. **`done v̂`**: `rt (cap(ℓ, co), inl v̂)`; the value relation at `Cap(ℓ, s) ● r''`.
2. **A stop on `j`** (an operation of the capability), resource `r''`, protocol
   `Π_E(o, v̂, λw. ★(bind :: S₁, rt w), Cancel(bind :: S₁))(r'')`. The machine reads `ℓ`
   (owned: L5.2.6, 6.143) and runs `N_o` with `p ↦ v̂, s ↦ s` above `coret(j, ℓ)`. By `CoOK`, it
   ends at a ground value, at `∅`, with no stop. Then:
   - `inl (w, s')`: the cell is written (6.145) and the machine continues at
     `⟨bind :: S₁ ++ f_L :: S_e ; rt w⟩`: (★) at `s'`, from the protocol's resumption conjunct.
   - `inr (e, s')`: only if `o` is fallible (`E_o = int`), so `W ∈ q_o` and the protocol gives
     `Cancel(bind :: S₁)(r'')`. The cell is written, `dtors(bind :: S₁)` run (as in L5.14.2's
     cancel), and the lend answers `(cap(ℓ, co), inr e)` at `Cap(ℓ, s')`.
3. **A stop on `j' ≠ j`**: L5.6's stop case with `S₀ = f_L :: S_e`, `R₀ = Cap(ℓ, s) ● r_e`.
   Compatibility is vacuous: the premise `bound(ρ).req = lin` gives `bnd(Tab(ρ)).req = lin`, so
   every effect of the table has only `lin` operations and no abortive one, and D5.8 asks
   nothing. ∎

The lent capability travels with its frame. If a continuation of an outer handler captures
`f_L`, it captures `Cap(ℓ, s)` with it, and the continuation is linear (`lin` qualifiers only),
so it is resumed exactly once and the frame is reinstated. Nothing outside the frame can reach
`ℓ` meanwhile: the owner gave the capability to the lend.

**Lemma L5.16 (using: cancellation is finalisation).** [using] is compatible.

*Proof.* The step allocates `ℓ_r ↦ own(rsrc ℓ)` (6.141), emits `acq ℓ`, pushes
`f_U = fin(j, ℓ_r, ℓ)` and enters `M`. Show (★) as for L5.15 with `R₀ = {ℓ_r ↦ own(rsrc ℓ)} ● r_e`:

1. **`done v̂`**: the frame frees `ℓ_r` (owned, 6.142), emits `free ℓ`; the value.
2. **A stop on `j`** (`use`): the frame answers in place (`ℓ_r` is owned by `R₀`, so present),
   emits `use ℓ`, and continues by the protocol's resumption (`Res`'s protocol is `Φ(())`).
3. **A stop on `j' ≠ j`**: L5.6's stop case. Compatibility: `cancel ≥ bound(ρ).req ≥ bnd(Tab ρ).req`
   (premise), so no effect of the table has a `C` operation; for `W` or an abortive operation,
   `Cancel(S₀')(R₀)` holds exactly, because `ℓ_r ↦ own(rsrc ℓ)` is the resource of the `fin`
   frame `f_U` and `r_e ∈ NoOwn`. So a cancel or an unwind through the frame frees `ℓ_r`. ∎

**Lemma L5.17 (ν, capabilities, recursion).** [nu], [newcap], [getcap], [bfix] are compatible.

*Proof.*
- **[nu]**: a fresh `j` with effect `E`; `M`'s hypothesis at `π[x ↦ j]`. Its table is
  `Tab(ρ)`, which does not contain `j` (premise `x ∉ atoms(ρ)`), so `M` never stops on `j`.
- **[newcap]**: allocation of `ℓ ↦ own(cell s)` (6.141), emit `mk`, and `cap(ℓ, co)` at
  `Cap(ℓ, s)`. `CoOK(co)`: each `N_o` is closed and typed at row `∅`, so its own hypothesis
  (induction on the derivation of [newcap]'s premises) at the empty context gives
  `ewp_∅([], ev(N_o, [p, s])){…}(∅)`.
- **[getcap]**: `Cap(ℓ, s)` owns `ℓ`; removal (6.142), emit `fin`, `rt s` at `∅`.
- **[bfix]**: by induction on `n`. `n = 0`: L5.13. `n + 1`: the step binds
  `f ↦ clo(γ, bfix_n …)`. Its relation `V⟦U_unr^ρ C⟧` needs the closure's resource in `Pers`: it
  is the resource of `fv(M) ∖ f` and of `V`, which the premise `capture(Γ, fv(M) ∖ f, unr)` puts in
  `Pers` (L5.4.2); `V` is ground. Being `Pers`, it is shared between the closure and `M`
  (L4.2.4). Then the induction hypothesis at `n` for the closure, and `M`'s hypothesis.
  [SPEC §20: "the induction on the budget"; borrow-core `fixSelf_valid`, `boundedFix_compatX`.] ∎

## 5.5 The theorems

**Theorem T5.1 (Fundamental Property, unary).** If `Ψ; Θ; Γ ⊢ M : C ! ρ ▷ u` with `u` admissible
for `Γ`, then `Ψ; Θ; Γ ⊧ M : C ! ρ ▷ u`; likewise for values.

*Proof.* By induction on the derivation, applying the compatibility lemma of its last rule:
L5.7–L5.17. Sub-derivations have admissible usages by L2.1. ∎

**Lemma L5.18 (heap accounting).** Along any run of the machine:

1. every location or instance name is created at most once (the counter only grows);
2. a cell is removed only if present, so at most once;
3. `cell(_)` cells are created only by `newcap` and removed only by `getcap`; `rsrc(ℓ)` cells
   are created only by `using` (with event `acq ℓ`) and removed only by a `fin` frame's return
   or by `dtors` (each with event `free ℓ`); `seg(_)` cells are created only at a one-shot
   capture and removed only by forcing the continuation.

*Proof.* By inspection of D3.6: each row that changes the heap is listed. ∎

**Theorem T5.2 (resource safety).** Let `·; ·; · ⊢ P : F G ! ∅`. The machine run from
`⟨∅, 0, [] ; [] ; ev(P, ∅)⟩` reaches `done ĝ` with `ĝ ∈ ⟦G⟧` and an **empty heap**. Hence:

1. **no stuck states**: the run never reaches a stuck or unhandled configuration, and it ends;
2. **every capability is consumed exactly once**, and no operation of a lend reaches a consumed
   capability (the harm phase A's T1 prevents: "a lent capability used after its owner consumed
   it");
3. **every acquired resource is finalised exactly once**: each `acq ℓ` event is matched by
   exactly one `free ℓ` event of the same resource, whether the frame returns, is unwound by an
   abortive operation, is cancelled with a continuation, or is unwound by a co-operation's
   failure;
4. **every one-shot continuation is used exactly once**: resumed or cancelled, never both, never
   twice.

*Proof.* T5.1 at the empty contexts gives `E⟦F G⟧^∅(ev(P, ∅))(∅)`. `Elim_∅(F G) = {([], G, ∅, ∅)}`,
so `ewp_∅([], ev(P, ∅)){V⟦G⟧}(∅)`. Unfold it (L5.2.1) and instantiate `wpG` at `r_f = ∅`,
`n = 0`, `tr = []`: the run reaches a configuration `t` final relative to `[]` with `Φ(t)(r')`.
`t` is not a stop, because `Φ` of a stop requires the name in the empty table. So `t = done ĝ`
with `V⟦G⟧(ĝ)(r')`, which gives `ĝ ∈ ⟦G⟧` and `r' = ∅`; the heap is `⟦∅ ● ∅ ● r⁺⟧` with
`r⁺|own = ∅`, so `r⁺ = ∅` (L4.1) and the heap is empty. By determinism (L3.1) this is the run.

(1) The run reaches `done`. (2)–(4) By L5.18: every cell created is removed (the final heap is
empty), at most once, and only by the listed steps. A `cell` is removed only by `getcap`; a runner
operation reads its cell, so a consumed cell would make the run stuck, which (1) excludes. An
`rsrc` cell's removal emits exactly one `free ℓ`, and its creation exactly one `acq ℓ`. A `seg`
cell's removal is the one force of the continuation, which takes exactly one of the two entries
(D3.6). ∎

**Corollary C5.3 (independence is the key lemma).** In T5.2, the four obligations that a
continuation's capture creates are discharged by L5.4 alone, through L5.6:

| what a continuation captured at mode `m` may hold | discharged by |
|---|---|
| copyable (`C ∈ m`): only `Pers` | L5.4.2 at [to], [app], [op], [handle], [bfix]; L4.2.4 |
| droppable (`W ∈ m`): only `NoOwn`, beyond what its `fin` frames own | L5.4.2; L4.2.3; D4.5 |
| a capability (no destructor): only under `lin` | [lend] premise, L5.15.3 |
| a resource (a destructor): not under `C` | [using] premise, L5.16.3 |

*Proof.* Inspection of L5.10–L5.17: these are every use of L5.6's compatibility. ∎
