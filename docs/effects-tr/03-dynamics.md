# §3 Dynamics

[← §2 Statics](02-statics.md) · [index](README.md) · next: [§4 Worlds](04-worlds.md)

Two semantics, related by Theorem T6.6 (agreement):

- **§3.1 the machine**: a CK machine with a heap, phase A's `Eval.lean` adapted to §1's changes.
  It is the operational semantics. Resource safety (§5) is a statement about it, and contextual
  equivalence (D3.16) is defined by it.
- **§3.2 trees**: phase B's denotation into finite trees (`EffModelRel/Tree.lean`,
  `Denot.lean`). The binary relation (§6) is defined over it.

Neither semantics is step-indexed or fuelled. The machine is a partial function; that every
typed run ends is part of what §5 proves (the unary relation is total correctness, as BoLo's
`wp` is). Every tree is finite, because the denotation is by structural recursion on terms and
`bfix` unrolls a known number of times (§9.4).

---

## 3.1 The machine

**Definition D3.1 (machine values).** Environments `γ` map value variables to machine values and
instance variables to **instance names** `j ∈ ℕ`.

    v̂ ::= () | n | tt | ff | (v̂, v̂) | inl v̂ | inr v̂ | tkt_n
        | clo(γ, M)          a thunk: M in γ (the mode is erased)
        | fold v̂             a stream
        | cap(ℓ, co)         a capability: its cell ℓ and its co-operations
        | κ¹(ℓ_κ, w)         a one-shot continuation, stored at ℓ_κ; w = (W ∈ q)
        | κ*(S, w)           a copyable continuation (C ∈ q): the frames themselves

**Definition D3.2 (heap).** `μ : Loc ⇀ H` with `Loc = ℕ` and

    H ::= cell(s)       a capability's state, s ground
        | rsrc(ℓ)       an acquired resource with label ℓ
        | seg(S)        the frames of a one-shot continuation

Locations and instance names are drawn from one supply, the counter `n` (the least unused name).
[PA `St.cells`, `St.konts`, `St.next`. Phase A keeps continuations in a separate store with a
status flag; here a one-shot continuation is a heap cell that its use frees, so "resumed twice"
is a use after free: §4.2, meeting point 2.]

**Definition D3.3 (frames and stacks).** A stack `S` is a list of frames, top first.

    f ::= arg v̂ | bind(γ, x. N) | prj₁ | prj₂ | iarg j
        | hnd(j, γ, H)              the handler of instance j
        | run(j, ℓ, co)             a lend: instance j answered by the capability in ℓ
        | coret(j, ℓ)               a co-operation of the runner j is running
        | fin(j, ℓ_r, ℓ)            a using frame: instance j, resource at ℓ_r, label ℓ

`j` is *handled in* `S` when `S` has a frame `hnd(j, …)`, `run(j, …)` or `fin(j, …)`. For a stack
`S = S₁ ++ [f] ++ S₂` with `f` the topmost frame handling `j`, `split_j(S) = (S₁, f, S₂)`.

**Definition D3.4 (destructors of a segment).** For a segment `S₁`, `dtors(S₁)` is the list of
its `fin(j, ℓ_r, ℓ)` frames, top (innermost) first. *Running* `dtors(S₁)` in `(μ, tr)` frees
each `ℓ_r` in turn: it requires `μ(ℓ_r) = rsrc(ℓ)`, removes `ℓ_r`, and appends `free ℓ` to `tr`.
Other frames are discarded: a `bind`, `arg`, `prj`, `iarg` holds nothing a cancel must dispose of
(§5 proves it holds nothing owned), a `hnd` frame's clauses are persistent, and a `run` frame
cannot be in a cancelled segment of a typed program (the [lend] premise `bound(ρ).req = lin`).
[PA `St.cancel` (runs `fin` frames only); PB `Tree.dtors`.]

**Definition D3.5 (configurations).** `⟨μ, n, tr ; S ; c⟩` with control
`c ::= ev(M, γ) | rt(v̂)`, `tr` the trace (a list of events, D3.14).

**Definition D3.6 (the step).** `→` is the partial function below. `fresh` takes `n` and
increments it. Values in computation position are evaluated by `⟦V⟧γ` in the obvious way
(`thunk_m M ↦ clo(γ, M)`).

*Returns.*

| control and stack | step |
|---|---|
| `rt v̂`, `[]` | final: **done** `v̂` |
| `rt v̂`, `bind(γ, x.N) :: S` | `ev(N, γ[x↦v̂])`, `S` |
| `rt v̂`, `hnd(j, γ, H) :: S` | `ev(N_ret, γ[z↦v̂])`, `S` |
| `rt v̂`, `run(j, ℓ, co) :: S` | `rt (cap(ℓ, co), inl v̂)`, `S` |
| `rt (inl (w, s'))`, `coret(j, ℓ) :: S` | `μ[ℓ ↦ cell(s')]`; `rt w`, `S` |
| `rt (inr (e, s'))`, `coret(j, ℓ) :: S` | `μ[ℓ ↦ cell(s')]`; with `(S₁, run(j,ℓ,co), S₂) = split_j(S)`: run `dtors(S₁)`; `rt (cap(ℓ, co), inr e)`, `S₂` |
| `rt v̂`, `fin(j, ℓ_r, ℓ) :: S` | requires `μ(ℓ_r) = rsrc(ℓ)`: remove `ℓ_r`, emit `free ℓ`; `rt v̂`, `S` |

*Computations.* (`S` the current stack.)

| control | step |
|---|---|
| `ret V` | `rt ⟦V⟧γ` |
| `M to x. N` | `ev(M, γ)`, `bind(γ, x.N) :: S` |
| `λx. M` | requires `S = arg v̂ :: S'`: `ev(M, γ[x↦v̂])`, `S'` |
| `M V` | `ev(M, γ)`, `arg ⟦V⟧γ :: S` |
| `⟨M, N⟩` | requires `S = prjᵢ :: S'`: `ev(M or N, γ)`, `S'` |
| `prjᵢ M` | `ev(M, γ)`, `prjᵢ :: S` |
| `M x` (instance) | `ev(M, γ)`, `iarg γ(x) :: S` |
| `Λx:E^b. M` | requires `S = iarg j :: S'`: `ev(M, γ[x↦j])`, `S'` |
| `Λr ≤ b. M`, `M [ρ]` | `ev(M, γ)` (rows are erased) |
| `split`, `case`, `if`, `prim` | as usual |
| `absurd V` | none (unreachable: `⟦V⟧γ ∈ ⟦0⟧ = ∅`) |
| `emit V` | emit `out ⟦V⟧γ`; `rt ()` |
| `punch V` | with `⟦V⟧γ = tkt_n`: emit `punch n`; `rt ()` |
| `force V`, `⟦V⟧γ = clo(γ', M)` | `ev(M, γ')` |
| `force V`, `⟦V⟧γ = fold v̂` | (not a computation: `unfold` reads streams) |
| `force V`, `⟦V⟧γ = κ¹(ℓ_κ, w)` | requires `μ(ℓ_κ) = seg(S_κ)`; remove `ℓ_κ`; see *continuations* |
| `force V`, `⟦V⟧γ = κ*(S_κ, w)` | see *continuations* (nothing is removed) |
| `unfold V`, `⟦V⟧γ = fold v̂` | `force` of the thunk `v̂` |
| `op x.o(V; y.M)` | see *operations* |
| `ab x.a(V)` | see *operations* |
| `handle x : E with H in M` | `j = fresh`; `ev(M, γ[x↦j])`, `hnd(j, γ, H) :: S` |
| `handleAt x with H in M` | `ev(M, γ)`, `hnd(γ(x), γ, H) :: S` |
| `ν x : E^b. M` | `j = fresh`; `ev(M, γ[x↦j])` |
| `ieq x y` | `rt (γ(x) = γ(y))` |
| `newcap_E S co V` | `ℓ = fresh`; `μ[ℓ ↦ cell(⟦V⟧γ)]`; emit `mk`; `rt cap(ℓ, co)` |
| `getcap V`, `⟦V⟧γ = cap(ℓ, co)` | requires `μ(ℓ) = cell(s)`: remove `ℓ`; emit `fin`; `rt s` |
| `lend V as x in M`, `⟦V⟧γ = cap(ℓ, co)` | requires `μ(ℓ) = cell(_)`; `j = fresh`; `ev(M, γ[x↦j])`, `run(j, ℓ, co) :: S` |
| `using x = acquire ℓ in M` | `j = fresh`, `ℓ_r = fresh`; `μ[ℓ_r ↦ rsrc(ℓ)]`; emit `acq ℓ`; `ev(M, γ[x↦j])`, `fin(j, ℓ_r, ℓ) :: S` |
| `bfix_0 x.a(V)(f.M)` | `ev(ab x.a(V), γ)` |
| `bfix_{n+1} x.a(V)(f.M)` | `ev(M, γ[f ↦ clo(γ, bfix_n x.a(V)(f.M))])` |

*Continuations.* Forcing a continuation (`κ¹` after its cell is removed, or `κ*`) with frames
`S_κ` and weakening flag `w`:

- if `w`: requires `S = prjᵢ :: S'`.
  - `i = 1`: requires `S' = arg v̂ :: S''`: `rt v̂`, stack `S_κ ++ S''` (**resume**);
  - `i = 2`: run `dtors(S_κ)`; `rt ()`, stack `S'` (**cancel**).
- if not `w`: requires `S = arg v̂ :: S'`: `rt v̂`, stack `S_κ ++ S'` (**resume**).

*Operations.* `op x.o(V; y.M)` with `j = γ(x)`, `v̂ = ⟦V⟧γ`. If `j` is not handled in `S`, the
configuration is final: **unhandled**. Otherwise let `(S₁, f, S₂) = split_j(S)`:

- `f = fin(j, ℓ_r, ℓ)` (`o = use`): requires `μ(ℓ_r) = rsrc(ℓ)`; emit `use ℓ`;
  `ev(M, γ[y↦()])`, `S`.
- `f = run(j, ℓ, co)`: requires `μ(ℓ) = cell(s)`; `ev(N_o, [p↦v̂, s↦s])`,
  `coret(j, ℓ) :: bind(γ, y.M) :: S` (the co-operation runs in place; nothing is captured).
- `f = hnd(j, γ_h, H)`, `o` resuming: let `S_κ = bind(γ, y.M) :: S₁ ++ [f]`. If `C ∈ q_o`,
  `κ = κ*(S_κ, W ∈ q_o)`. Otherwise `ℓ_κ = fresh`, `μ[ℓ_κ ↦ seg(S_κ)]`,
  `κ = κ¹(ℓ_κ, W ∈ q_o)`. Then `ev(N_o, γ_h[p↦v̂, k↦κ])`, `S₂`.

`ab x.a(V)` with `j = γ(x)`: unhandled if `j` is not handled in `S`; otherwise
`(S₁, hnd(j, γ_h, H), S₂) = split_j(S)`, run `dtors(S₁)`, then `ev(N_a, γ_h[p↦v̂])`, `S₂`.
(A `run` or `fin` frame never handles an abortive operation: `Res` has none, and a capability's
effect has none, [newcap].)

Any configuration that is neither final nor has a step is **stuck**.

[PA `evalStep`, `retTo`, `findFrame`, `St.cancel`; differences: no `clauseEnd` frame (§8.1), the
one-shot continuation as a heap cell, the co-operation's failure branch, `fin` frames tagged with
an instance, `lend` answering the capability.]

**Lemma L3.1 (determinism).** `→` is a partial function.

*Proof.* Each control form and top frame selects at most one row of D3.6; `split_j` is the
topmost frame for `j`, a function of `S`. ∎

**Definition D3.7 (observation of a program).** For a closed `P`, run `→` from
`⟨∅, 0, [] ; [] ; ev(P, ∅)⟩`. `Obs_op(P)` is `(o, tr)` if the run reaches a final or stuck
configuration with outcome `o ∈ {ret ĝ, unhandled, stuck}` and trace `tr`, where `ĝ` is the
rendering of a ground value; it is `↑` if the run does not end.

## 3.2 Trees

This section transcribes phase B's semantic domain. Each definition names its Lean counterpart;
"as phase B" means the definition is that declaration, read on paper. The only changes are the
three of §1 that reach the denotation: `lend` pairs its answer with the capability, `use` is a
world action addressed through the `Res` instance, and `punch` is a world action.

**Definition D3.8 (actions and destructors).** [PB `Act`, `Dtor`, `Dtor.act`.]

    act ::= out n | acq ℓ r | use ℓ r | free ℓ r | new c s | rd c G | wr c s | kill c G | punch n
    δ   ::= free ℓ r | wb c s                (a destructor: free a resource; write a state back)

`punch n` is added to phase B's `Act`.

**Definition D3.9 (trees and streams).** `Tree X` is the inductive type [PB `Tree`, `Strm`]

    t ::= ret x | op i E o v k d | ab i E a v d | nu k | act α k

with `k` a function from the answer (`⟦B_o⟧`, `ℕ`, or the action's answer) to trees, and `d` a
list of destructors: those of the frames between the operation and its eventual handler,
innermost first. `Strm X` is the inductive type of pairs `(pull : Tree (X + ℤ × Strm X),
drop : Tree 1)`.

**Definition D3.10 (semantic types).** [PB `VTy.den`, `CTy.den`.]

    ⟦G⟧ = ⟦G⟧         ⟦A ⊗ B⟧ = ⟦A⟧ × ⟦B⟧      ⟦A ⊕ B⟧ = ⟦A⟧ + ⟦B⟧     ⟦U_m^ρ C⟧ = ⟦C⟧
    ⟦cap_E S⟧ = ℕ × CoSem(E, S)                 ⟦tkt⟧ = ℕ              ⟦strm^ρ A⟧ = Strm ⟦A⟧
    ⟦F A⟧ = Tree ⟦A⟧  ⟦A ⇒^ρ C⟧ = ⟦A⟧ → ⟦C⟧    ⟦C₁ & C₂⟧ = ⟦C₁⟧ × ⟦C₂⟧
    ⟦Π(x:E^b). C⟧ = ℕ → ⟦C⟧                    ⟦∀(r ≤ b). C⟧ = ⟦C⟧

where `CoSem(E, S) = Π o. ⟦A_o⟧ → ⟦S⟧ → Tree((⟦B_o⟧ × ⟦S⟧) + (ℤ × ⟦S⟧))`. Rows and modes are
erased.

**Definition D3.11 (every computation type is a model).** For each `C`, operations
`opA_C`, `abA_C`, `nuA_C`, `actA_C` and `dtorsA_C`, defined by recursion on `C`: at `F A` they
are the tree constructors (`dtorsA_{F A} d t = Tree.dtors d t`, which prefixes `act (δ.act)` for
each `δ ∈ d`, innermost first), and at `⇒`, `&`, `Π`, `∀` they act pointwise. [PB `CTy.opA`,
`CTy.abA`, `CTy.nuA`, `CTy.actA`, `CTy.dtorsA`, `Tree.dtors`.] *Source:* Plotkin & Pretnar,
*Handling algebraic effects*, LMCS 9(4:23), 2013, §2: every computation type is a model.

**Definition D3.12 (folds).** As phase B:

- `Tree.bind` and `bindC_C` (sequencing into the model `C`) [PB `Tree.bind`, `Tree.bindC`];
- `hnd_C(i, E, hr, hop, hab)` (a deep handler of instance `i`): at `op j E' o v k d` with `j = i`
  and `E' = E`, `hop o v (λy. hnd(k y)) d`; at `ab j E' a v d` with `j = i`, `E' = E`,
  `dtorsA_C d (hab a v)`; otherwise the model's operation, recursively [PB `Tree.hnd`,
  `catchOp`, `catchAb`];
- `runL(i, E, c, S, co)`, the lend of cell `c` as instance `i` at state `s` (state-passing): at
  `ret x`, write `s` back and answer `inl x`; at an operation on `i`, run the co-operation, then
  either resume the client with the next state or, on failure `inr (e, s')`, run the client's
  destructors `d`, write `s'` back and answer `inr e`; at any other operation or abort, append
  the write-back `wb c s` to its destructors [PB `Tree.runL`, `coStep`, `coK`];
- `addFin(ℓ, r)`: free `r` on return, and append `free ℓ r` to the destructors of every operation
  and abort inside [PB `Tree.addFin`].

**Definition D3.13 (denotation).** `⟦V⟧ η ρ ∈ ⟦A⟧` and `⟦M⟧ η ρ ∈ ⟦C⟧`, for `η` an instance
environment (instance variables to names; a `Res` instance to a pair `(ℓ, r)`) and `ρ` a value
environment, by structural recursion on the term, clause for clause phase B's `Val.den`,
`Cmp.den`, with:

    ⟦lend V as x in M⟧ η ρ  = let (c, co) = ⟦V⟧ η ρ in
                               act (rd c S) (λs. nu (λi. Tree.bind (runL(i, E, c, S, co, s)
                                 (⟦M⟧ (η[x↦i]) ρ)) (λz. ret ((c, co), z))))
    ⟦using x = acquire ℓ in M⟧ η ρ = nu (λr. act (acq ℓ r) (λ_. addFin(ℓ, r)(⟦M⟧ (η[x↦(ℓ,r)]) ρ)))
    ⟦op x.use((); y. M)⟧ η ρ = let (ℓ, r) = η(x) in actA (use ℓ r) (λ_. ⟦M⟧ η ρ[y↦()])
    ⟦punch V⟧ η ρ = act (punch (⟦V⟧ η ρ)) (λ_. ret ())
    ⟦Λr ≤ b. M⟧ = ⟦M[ρ]⟧ = ⟦M⟧ (rows erased)

and for a resuming clause, the continuation argument is `mkK(k, Tree.dtors d (ret ()))`: the
pair `(resume, cancel)` when `W ∈ q`, the resume function otherwise [PB `mkK`, `dtorsT`]. The
`lend` clause differs from phase B's `Cmp.den` only by the final `Tree.bind` that pairs the
answer with the capability.

**Lemma L3.2 (the denotation is total and finite).** Every `⟦M⟧ η ρ` is defined, and every tree
it produces is a finite tree (an element of the inductive type `Tree`).

*Proof.* Structural recursion on `M` (phase B's `Cmp.den` is accepted by Lean's structural
recursion checker); `bfix_n` is `n`-fold iteration [PB `iter`]. An inductive type has only
finite (well-founded) elements. ∎

## 3.3 Observations and contextual equivalence

**Definition D3.14 (events and tree observation).** Events are

    ev ::= out n | acq ℓ | use ℓ | free ℓ | mk | fin | punch n

(names erased; labels kept, so the order in which destructors run is observable).
`obs(t) = t.obs(render, Wd.init)` runs a tree against a world of a name counter, a store and a
trace: `nu` takes the next name, `act` executes against the store (`rd`, `wr`, `kill` of a dead
cell is **stuck**), an `op` or `ab` reaching the top unwinds its destructors and is
**unhandled**. [PB `Ev`, `Outcome`, `Obs`, `Wd`, `Act.exec`, `Wd.unwind`, `Tree.obs`,
`Prog.obs`.]

**Definition D3.15 (denotational contextual equivalence).** [PB `Context`, `holeTy`, `close`,
`CtxEq`.] For `M, N : C` over `Ψ; Γ` (intrinsically typed; modes and rows ignored):

    CtxEq_den(M, N)  ≜  ∀ G. ∀ P : Context(Ψ, Γ, C, G).  obs(⟦P⟧ (close ⟦M⟧)) = obs(⟦P⟧ (close ⟦N⟧))

where a context is a closed program of type `F G` with one free variable `h : U_unr(holeTy(Ψ, Γ,
C))`, `holeTy` abstracting the instances then the values, and `close` currying the denotation.

**Definition D3.16 (operational contextual equivalence).** For moded `M, N` with
`Ψ; Θ; Γ ⊢ M, N : C ! ρ`, write `hole(M) = thunk_m (Λx⃗. λy⃗. M)` (closed). A *moded context* is a
derivation `·; ·; h : U_m^{ρ_h}(holeTy) ⊢ P : F G ! ∅` for some `m` (`ρ_h` places `ρ` at the
innermost abstraction). Then

    CtxEq_op(M, N)  ≜  ∀ moded P.  Obs_op(P[hole(M)/h]) = Obs_op(P[hole(N)/h])

**Remark.** Every moded context is an intrinsically typed one (erase modes and rows), so
`CtxEq_den(M, N)` quantifies over more contexts than `CtxEq_op`, but observes trees, not runs.
Theorem T6.7 joins them: for moded `M, N`, `CtxEq_den(M, N) ⇒ CtxEq_op(M, N)`, through the
agreement of the two semantics on moded programs (T6.6).
