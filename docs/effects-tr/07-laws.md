# §7 The laws

[← §6 The binary relation](06-binary.md) · [index](README.md) · next: [§8 Two decisions](08-decisions.md)

Phase A's laws L1–L6 (`docs/effect-model.md` §3.1, `experiments/EffModel/EffModel/Laws.lean`),
written as schemas. Each is a theorem `LR(lhs, rhs)` about intrinsically typed terms, so
`CtxEq_den` by C6.6, and `CtxEq_op` whenever both sides are moded (T6.7). Phase A checked each
in a finite suite of contexts; here each holds in every context.

**Status of each law.**

| law | theorem | proof |
|---|---|---|
| L1a at `to`, `⇒`, `&`, `Π` | T7.1 | phase B (Lean) |
| L1a at arity 0 | T7.2 | phase B (Lean) |
| L1a, destructor form, any context | T7.3 | here; phase B proved one frame |
| H-ret, H-op, H-fwd, H-fwd at arity 0 | T7.4–T7.7 | phase B (Lean) |
| tensor: disjoint capabilities commute | T7.8 | phase B (Lean) |
| absorption by a pure model | T7.9 | phase B (Lean) |
| the sum: where absorption and commutation fail | T7.10 | phase B (Lean, by `decide`) |
| writers commute | T7.11 | here |
| idem-ν, ν/ν, new-ν | T7.12–T7.14 | phase B (Lean) |
| ν/op | T7.15 | **refuted at contractible qualifiers** (phase B, Lean); **open** otherwise (O1) |
| no accidental handling | T7.16 | phase B (Lean), identity return clause; here, any return clause |

Throughout, `y` is fresh for the frame it is moved past, and `M.wk` is weakening (phase B's
`Cmp.wk`, `Cmp.wkI`); the mechanisation states each law with explicit renamings, as phase B does.

---

## 7.1 L1: algebraicity

**Theorem T7.1 (algebraicity, L1a).** For an operation `op x.o(V; y.M)`:

    (op x.o(V; y.M)) to z. N   ≡  op x.o(V; y. M to z. N)
    (op x.o(V; y.M)) W         ≡  op x.o(V; y. M W)
    prjᵢ (op x.o(V; y.M))      ≡  op x.o(V; y. prjᵢ M)
    (op x.o(V; y.M)) z         ≡  op x.o(V; y. M z)              (an instance argument)
    (op x.o(V; y.M)) [σ]       ≡  op x.o(V; y. M [σ])

*Proof.* The two sides have equal denotations, hence are related (PB `LR.of_den`, `CtxEq.of_den`).
`⟦op x.o(V; y.M)⟧ = opA_C(…)` (D3.13), and at `F` the fold `bindC` of an `op` node is an `op` node
whose continuation is folded (`Tree.bindC`); at `⇒`, `&`, `Π` the model operation is pointwise
(D3.11), so applying, projecting or instantiating commutes with it. Rows are erased. [PB
`alg_bind`, `alg_app`, `alg_prj1`, `alg_prj2`, `alg_iapp`.] ∎

Phase A confirmed it holds "by construction" from the stack semantics (`docs/effect-model.md`
§4); here it is a theorem of every computation type being a model (Plotkin & Pretnar 2013, §2).

**Theorem T7.2 (algebraicity at arity 0).**

    ab x.a(V) to z. N  ≡  ab x.a(V)          (ab x.a(V)) W  ≡  ab x.a(V)

and likewise at projection and instance application.

*Proof.* Equal denotations: `bindC` and the pointwise model operations carry an `ab` node
unchanged (`Tree.bindC`'s `ab` case, `CTy.abA`). [PB `alg_ab_bind`, `alg_ab_app`.] ∎

In a linear setting `K[raise] ≡ raise` discards `K`'s context, which is unsound when `K` owns
something; T7.2 holds because `to`, an argument and a projection own nothing a cancel must run.
T7.3 is the general form.

**Definition D7.1 (evaluation contexts and their destructors).** An evaluation context is

    K ::= [] | K to z. N | K W | prjᵢ K | K z | K [σ]
        | using x' = acquire ℓ in K | handleAt y with H in K | handle y : E with H in K

with the hole not under a binder of the instance it is applied to (below, `x ≠ y`).
`K^fin` keeps exactly `K`'s `using` frames, in order, with hole `ret ()`:

    []^fin = ret ()      (using x' = acquire ℓ in K)^fin = using x' = acquire ℓ in K^fin
    and K^fin = (K')^fin for every other frame around K'

**Theorem T7.3 (algebraicity at arity 0, destructor form).** For `K` with no `lend` frame and
`x` not bound by `K`:

    K[ab x.a(V)]  ≡  K^fin ; ab x.a(V)

*Proof.* First, by induction on `K`, `⟦K[ab x.a(V)]⟧ η ρ` is a tree of `nu` and `act (acq ℓ r)`
nodes (one per `using` frame, outermost first) ending in `ab (η x) E a v δ`, with
`δ = [free ℓ_k r_k, …, free ℓ_1 r_1]` (innermost first):

- `to`, an argument, a projection, an instance or row application: `bindC` and the model
  operations carry the `ab` node and its list unchanged (as T7.2);
- `using`: `addFin(ℓ, r)` appends `free ℓ r` to the node's list (`Tree.addFin`'s `ab` case), under
  `nu (λr. act (acq ℓ r) …)` (D3.13);
- `handleAt y` and `handle y` with `y ≠ x`: `Tree.hnd`'s non-matching `ab` branch is `abA`, the node
  unchanged (`catchAb_ne` or `if_neg`; for `handle`, the fresh name differs from `η x`: PB
  `fresh_of_free`, so the `nu` is matched by `nu` on both sides as below).

Second, `⟦K^fin ; ab x.a(V)⟧` is the same `nu`/`acq` prefix, then `Tree.dtors δ (ab (η x) E a v [])`:
each `addFin` on `ret ()` is `act (free …) (ret ())` (`Tree.addFin`'s `ret` case), and `bindC` into
the abort. Relate the two trees at any `w` with nothing pending and `IR(w, η, η')`, `ER(w, ρ, ρ')`:
`TreeRel.nu` at each allocation (both sides allocate, matched); `TreeRel.act` at each `acq` with
the matched name; then `TreeRel.abE` with `d = δ`, `f = []`, its premises being
`w.r(η x, η' x)` (`IR`) and `δ ~ δ'` (the matched names). So `LR(lhs, rhs)` (the handlers of `K`
contribute `nu` nodes only for `handle`, matched by `nu`). [PB `alg_dtor` is the case
`K = using x' = acquire ℓ in ([] to z. N)`; `TreeRel.abE` is the relation's built-in form of this
law.] ∎

*Why no `lend` frame.* A lend frame contributes `wb c s` to `δ`, whose right-hand side would be a
write-back of the current state, which is no term. In the moded calculus the case does not arise:
an abortive operation inside a lend's body violates [lend]'s `bound(ρ).req = lin`.

*Source.* Congard, Munch-Maccagnoni & Douence, *Linear effects, exceptions, and resource safety:
a Curry–Howard correspondence for destructors* (ESOP 2026, arXiv 2510.23517): in a linear
setting the strength of `T(− ⊕ E)` needs destructors, which makes the law
`K[raise e] ≡ D_K; raise e` (abstract and §1, as read for phase A; the section numbers of the
published version are **not re-verified here**).

## 7.2 L2: the handler laws

**Theorem T7.4 (H-ret).** `handle x : E with H in ret V  ≡  N_ret[V/z]`.

*Proof.* [PB `h_ret`.] The left allocates a name nothing uses: `nuA_gL` (garbage on the left),
then `Tree.hnd` of `ret` is the return clause. ∎

**Theorem T7.5 (H-op).** For a handler of an instance in scope,

    handleAt x with H in op x.o(V; y.M)  ≡  N_o[V/p, κ_M/k]

where `κ_M ≜ thunk_{m} (⟨λy. handleAt x with H in M, ret ()⟩)` if `W ∈ q_o`, and
`thunk_{q_o} (λy. handleAt x with H in M)` otherwise (`m` the mode of D1.8).

*Proof.* [PB `h_op`, `kVal`, `kVal_den`.] Equal denotations: `Tree.hnd` of an `op` node on its own
instance is the clause at the folded continuation (`catchOp_self`), and the continuation value's
denotation is `mkK` of it, with cancel `Tree.dtors [] (ret ()) = ret ()` (no frames lie between
the operation and the handler). ∎

Phase A states H-op with `ν h` around both sides; T7.5 holds at any instance in scope, so in
particular there.

**Theorem T7.6 (H-fwd).** For `x' ≠ x` (`x` bound by `ν`, `x'` in scope outside it):

    ν x. handleAt x with H in op x'.o(V; y.M)  ≡  ν x. op x'.o(V; y. handleAt x with H in M)

*Proof.* [PB `h_fwd`.] `LR.nu_of_fresh`: on every fresh name the bodies' denotations agree, since
`Tree.hnd` passes an operation of another name (`if_neg` with `fresh_of_free`). ∎

**Theorem T7.7 (H-fwd at arity 0).** `ν x. handleAt x with H in ab x'.a(V)  ≡  ab x'.a(V)`.

*Proof.* [PB `h_fwd_ab`.] `LR.nuG_of`: the left's name is garbage, and `Tree.hnd` passes the abort. ∎

## 7.3 L4: sum and tensor

**Theorem T7.8 (tensor: operations on disjoint capabilities commute).** Let `co₁`, `co₂` be
co-operations that answer in place (`PureCo`: every co-operation's denotation is
`ret (inl (r, s'))`, no effect, no failure). Then for every `K`:

    newcap c₁ := a₁ ; newcap c₂ := a₂ ; lend c₁ as x₁ in lend c₂ as x₂ in op x₁.o₁(v₁; _. op x₂.o₂(v₂; _. K))
    ≡ newcap c₁ := a₁ ; newcap c₂ := a₂ ; lend c₁ as x₁ in lend c₂ as x₂ in op x₂.o₂(v₂; _. op x₁.o₁(v₁; _. K'))

with `K'` = `K` with its two answer variables exchanged.

*Proof.* [PB `tensor`, `runL_pair`, `runL_pair'`, `cap_rel`, `coSem_rel`.] Both sides allocate
two cells and two instances, matched (`TreeRel.nu`, `act new`, `act rd`). Under the two lends, each
operation is answered by its own runner (`coStep_self` on its own instance, the other's `runL`
passing it, `if_neg` with `x₁ ≠ x₂`), so both trees reduce to `K`'s at the two next states
(`runL_pair`, `runL_pair'`), and `runL_rel` twice relates the rest. ∎

*Source.* Plotkin & Power, *Tensors of comodels and models for operational semantics* (MFPS
2008, ENTCS 218, DOI 10.1016/j.entcs.2008.10.018 [verified via Crossref]): running a model against
a comodel is their tensor; two runners over separate cells are the tensor of their comodels, and
their operations commute (Hyland, Plotkin & Power, *Combining effects: sum and tensor*, TCS 357,
2006 [recalled, via phase A]).

**Theorem T7.9 (absorption by a pure model).** Let `H` be a handler of `E` into a state-passing
type `A₀ ⇒ D` whose clause for `o` is *pure* (`PureClause`: its denotation at any continuation `k`
is `λs. k (ans v) (next v s)`), and `f ≠ E`. Then

    (handle x : E with H in op x.o(v; _. ab x'.a(u))) s  ≡  (handle x : E with H in ab x'.a(u)) s

*Proof.* [PB `absorb_pure`, `absorb_writer`, `writer_pure`.] Equal denotations: the handler
catches `o` (`hnd_op_self`) and the pure clause resumes at once with the next state; the abort of
another effect passes the handler (`hnd_ab_other`), carrying no destructor of the model, so the
state is lost with it. ∎

**Theorem T7.10 (the sum: where absorption and commutation fail).** Each of the following pairs is
**not** contextually equivalent; each is witnessed by one closed context whose two observations
differ, computed by `decide` in Lean [PB `Examples.lean`]:

| placement | law that fails | Lean |
|---|---|---|
| `Fail` outside a printing `Log` | `log m; raise ≡ raise` | `not_absorb_print_inside` |
| a writer `Log` outside `Fail` | the same | `not_absorb_writer_outside` |
| a printing `Log` outside `Fail` | the same | `not_absorb_print_outside` |
| a runner `Log`, lent outside `Fail` | the same: the lend survives the abort | `lent_state_survives` |
| a runner `Log`, lent inside `Fail` | the same (not moded here: see below) | `not_absorb_runner_inside` |
| two printing `Log`s | `log₁ 1; log₂ 2 ≡ log₂ 2; log₁ 1` | `print_print_not_commute` |

With T7.9 this is phase A's finding exactly: absorption holds where `Fail` is outside a pure-model
`Log` and in none of the other placements of phase A's family (`docs/effect-model.md` §3.1, "holds
exactly with `Fail` outside a writer `Log`"). The runner-inside placement is a closed un-moded
program: under §2's [lend], a lend whose body may abort is refused (its capability has no
destructor). So in the moded calculus that placement is not a context at all, and the other four
negative rows are. [Hyland, Plotkin & Power 2006, as restated by Ahman & Bauer, *Runners in
action*, ESOP 2020, §3 [via phase A]: exceptions combine by sum, signals by tensor.]

**Theorem T7.11 (writers commute).** Let `H₁`, `H₂` be handlers of distinct instances `x₁`, `x₂`
into state-passing types, each with pure clauses (T7.9), installed by `writerᵢ(N) ≜
(handle xᵢ with Hᵢ in N) sᵢ`. Then

    writer₁(writer₂(op x₁.o₁(v₁; _. op x₂.o₂(v₂; _. M))))  ≡  writer₁(writer₂(op x₂.o₂(v₂; _. op x₁.o₁(v₁; _. M))))

*Proof (here; not mechanised).* Equal denotations. Write `h₂(t)` for `Tree.hnd` of `x₂`'s
handler on `t`, a function of the state `s₂`. Two facts: the pure clause gives
`h₂(op x₂ v₂ (λ_. t)) s = h₂(t) (next₂ v₂ s)` (`hnd_op_self`, `PureClause`), and `h₂` passes an
operation of `x₁` pointwise at the state-passing type: `h₂(op x₁ v₁ (λ_. t)) s =
op x₁ v₁ (λ_. h₂(t) s)` (`Tree.hnd`'s non-matching branch, `CTy.opA` at `⇒`). Then

    left:   h₂(op x₁ v₁ (λ_. op x₂ v₂ (λ_. ⟦M⟧))) s₂ = op x₁ v₁ (λ_. h₂(⟦M⟧)(next₂ v₂ s₂))
    right:  h₂(op x₂ v₂ (λ_. op x₁ v₁ (λ_. ⟦M⟧))) s₂ = h₂(op x₁ v₁ (λ_. ⟦M⟧))(next₂ v₂ s₂)
                                                     = op x₁ v₁ (λ_. h₂(⟦M⟧)(next₂ v₂ s₂))

The outer handler `h₁` receives the same tree on both sides. ∎

Phase A's matrix also has "two `Log` instances commute unless both print" over all nine pairs of
implementations; T7.11 is the writer–writer pair, and T7.10 the print–print failure. The other
pairs (print with a runner, a writer with a runner) are phase A's evidence `[run]` only.

## 7.4 L6: instances

**Theorem T7.12 (idem-ν).** `ν x. M  ≡  M` for `x ∉ M`.

*Proof.* [PB `idem_nu`, `LR.nuG_of`.] The left's name is garbage (`gL`). ∎

**Theorem T7.13 (ν/ν).** `ν x₁. ν x₂. M(x₁, x₂)  ≡  ν x₁. ν x₂. M(x₂, x₁)`.

*Proof.* [PB `nu_nu`.] Each side allocates two names in an order the other side does not: the
left's first name is pending (`nuL`), the right's first pending (`nuR`), then each side's second
name is matched with the other's pending one (`mL`, `mR`). The final world matches the left's
`(i₁, i₂)` with the right's `(j₂, j₁)`, which is the exchange. ∎

**Theorem T7.14 (new-ν).** `ν x. (if ieq a x then M else N)  ≡  ν x. N` for `a` in scope.

*Proof.* [PB `new_nu`, `fresh_of_free`.] A fresh name differs from every name an environment
related at the world holds. ∎

**Theorem T7.15 (ν/op).**

    ν x. op a.o(V; y. M)  ≡  op a.o(V; y. ν x. M)            (x ∉ a, V)

1. **It fails when `C ∈ q_o`.** [PB `nu_op_fails_multishot`, `nuOp_obs`.] With `M` returning a
   predicate that tests an instance against `x` and a function that applies a predicate to `x`,
   and a handler of `a` that resumes twice and combines the first run's predicate with the second
   run's function, the left answers `true` (both runs share `x`) and the right `false`.
2. **When `C ∉ q_o` it is open** (O1 below).

*On Staton's law.* Staton (*Instances of computational effects: an algebraic perspective*, LICS
2013, §IV–V) states ν/op in a parameterized algebraic theory; there the operations are the
theory's, and no user handler duplicates a continuation. With deep handlers that may resume
twice, the law needs the continuation to be resumed at most once. That is a difference in setting.
Phase A's suite checked ν/op only at a linear operation (`docs/effect-model.md` §3.1), where it
holds in every tested context.

**Open problem O1 (ν/op at a non-contractible qualifier).** *Statement:* for moded `M` and
`C ∉ q_o`, `CtxEq_op(ν x. op a.o(V; y. M), op a.o(V; y. ν x. M))`.

*The step that does not go through.* The left allocates before the operation, the right inside
its continuation. In D6.2 the left's name can be pending (`nuL`), but then the left's `op` node
cannot be related: `TreeRel.op` requires `w.noPend`. It can be garbage (`gL`), but a garbage name
is never matched with the name the right allocates later. No constructor relates an operation
under a pending name, and none should in general, because of 1: a handler that resumes twice
observes the difference.

*What a proof needs.* The relation must know that the continuation is forced at most once. The
binary relation does not read modes, so it cannot. A proof needs a binary relation in which a
pending name is **owned**, as a resource, by the continuation value that will allocate its
partner, and is consumed when that value is forced: a resource-indexed binary relation whose
value relation at a `lin` thunk type carries the pending names it owns. I have not defined it,
and I have not verified that any obstruction to defining it is real. §9.1 records this as the
one place where the factoring strains: the third meeting point, continuations as values in the
resource world, reaches into the instance supply.

**Theorem T7.16 (no accidental handling: parametricity in instances).** For `M` not mentioning
`x`:

    ν x. handleAt x with H in M  ≡  M to z. N_ret

and in particular, for the identity return clause, `ν x. handleAt x with H in M ≡ M`.

*Proof.* The identity case is [PB `no_accidental_handling`, `hnd_transparent`]: the left's name is
garbage (`gL`), and a handler of a name the world never matches is, on related trees, the identity
(`hnd_transparent`, by induction on `TreeRel`: every `op` and `ab` node carries a matched name,
hence not the garbage one, so the handler passes it). The general case (here; not mechanised):
the same induction with the conclusion `TreeRel` between `t.hnd(i, ⟦N_ret⟧, …)` and
`t'.bindC(⟦N_ret⟧)`; every case is `hnd_transparent`'s except `ret`, which is `hnd`'s and `bindC`'s
`ret` case on both sides, related by the return clause's own Fundamental Property at the leaf's
related values (T6.5). ∎

This is abstraction safety as a parametricity theorem (Zhang & Myers, *Abstraction-safe effect
handlers via tunneling*, POPL 2019 [via phase A]; Biernacki, Piróg, Polesiuk & Sieczkowski,
*Abstracting algebraic effects*, PACMPL 3 (POPL 2019), DOI 10.1145/3290319 [verified via
Crossref; content recalled]): a term treats every instance it is not given alike, so it treats
`x` as it treats a name the world never matches. Here it needs no type abstraction over effects:
`ν` and the garbage status suffice.
