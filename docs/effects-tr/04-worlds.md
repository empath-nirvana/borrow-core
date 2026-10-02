# §4 Worlds

[← §3 Dynamics](03-dynamics.md) · [index](README.md) · next: [§5 The unary relation](05-unary.md)

A world has two components, and each relation reads one of them:

| component | what it is | read by |
|---|---|---|
| a **resource** `r ∈ Res` | BoLo's resource world ([TR] §5) over the machine's heap contents | the unary relation (§5): resource safety, finalisation, the three meeting points |
| an **instance supply** | names and how the two sides match them (phase B's `W`) | the binary relation (§6): the laws |

Instances are local: a name is bound by a frame and confined by rows. Resources are global: the
heap and its ownership. The design brief asks for the calculus to be BoLo's resource world plus
a local control discipline; this section states exactly where the two meet (§4.2), and §9 says
whether the factoring held.

---

## 4.1 The resource world

**Definition D4.1 (resources).** `Res` is [TR] §5's carrier

    Res ≜ Loc ⇀_fin Cell        Cell ≜ own(Val) + imm(Imm) + mut(Mut)

with its composition `●`, compatibility `#`, validity `✓`, flattening `⦇ρ⦈`, lowering `⟦ρ⟧`, the
frame-preserving relation `↭`, the restriction `ρ|own`, and the predicate operators of [TR] p. 6
(`⋆`, `─⋆`, `emp`, `!`, `∧`, `∨`, `∀`, `∃`, `⌜−⌝`), instantiated at `Val ≜ H`, the machine's
heap contents (D3.2). (The mechanisation's carrier is `BoCa.Fig16.ResU`; borrow-core's
`Core/World.lean` uses it as `WRes`.)

**Lemma L4.1 (the own fragment).** Every resource that the unary relation (§5) assigns to a value,
a frame or a configuration of this calculus is in `Res_own ≜ {r | r = r|own}`. On `Res_own`:

1. `r₁ ● r₂` is defined iff `dom r₁ ∩ dom r₂ = ∅`, and is then the disjoint union;
2. `r₁ # r₂` iff `r₁ ● r₂` is defined ([TR] 6.9, and every own-only resource is valid, `⦇r⦈ = r`);
3. `r ↭ r'` holds for all valid `r, r'` ([TR] p. 5: `↭` constrains only cells that flatten to
   `mut` or `imm`);
4. `⟦r⟧ = r` read as a heap (the lowering of an own cell is its content).

*Proof.* The first sentence is by inspection of D5.2–D5.6: the only cells they create are
`ℓ ↦ own(cell s)`, `ℓ_r ↦ own(rsrc ℓ)` and `ℓ_κ ↦ own(seg S)`. (1) [TR] p. 5: `ψ₁ ● ψ₂` is
defined only when `ψ₁ ▸◂ ψ₂`, which needs two `imm` cells; so two own-only resources compose
exactly when their domains are disjoint. (2) `ex(r)● = r|own = r` and `ag(r) = ∅`, so
`⦇r⦈ = r` is defined. (3) Both conjuncts of `↭` quantify over cells of `⦇r⦈` that are `mut` or
`imm`, and there are none. (4) `⟦ψ⟧ = v` for `ψ = own(v)` ([TR] p. 5). ∎

So, for this calculus, BoLo's resource world reduces to a separation logic of owned heap cells,
and BoLo's `wp` ([TR] p. 6) to a total-correctness `wp` quantified over frames. The full carrier
is kept because the kernel lift adds borrows (`imm`, `mut`), and the definitions below are
written so that they do not change when it does. Where a lemma uses L4.1 to shorten a step, it
says so; that step is one the lift must redo.

**Definition D4.2 (mode interpretation).** Each mode denotes a set of resources:

    ⟦lin⟧ ≜ Res
    ⟦aff⟧ ≜ NoOwn ≜ {r | r|own = ∅}
    ⟦rel⟧ = ⟦unr⟧ ≜ Pers ≜ {r | r|own = ∅ ∧ r|mut = ∅ ∧ r ● r = r}

In `Res_own`, `NoOwn = Pers = {∅}`.

**Lemma L4.2 (the mode algebra).**

1. `m ≥ k ⇒ ⟦m⟧ ⊆ ⟦k⟧`.
2. `∅ ∈ ⟦m⟧`, and `⟦m⟧` is closed under `●` where it is defined.
3. `W ∈ m ⇒ ⟦m⟧ ⊆ NoOwn` (what a mode with weakening holds may be dropped).
4. `C ∈ m ⇒ ⟦m⟧ ⊆ Pers`, and `r ∈ Pers ⇒ r = r ● r` (what a mode with contraction holds may be
   duplicated).

*Proof.* (1) The pairs with `m ≥ k`, `m ≠ k` are `aff ≥ lin`, `rel ≥ lin`, `unr ≥ lin`,
`unr ≥ aff`, `unr ≥ rel`; every set is in `⟦lin⟧ = Res`, `Pers ⊆ NoOwn` by definition, and
`⟦unr⟧ = ⟦rel⟧`. (2) `∅` satisfies each condition. `(r₁ ● r₂)|own = r₁|own ⊎ r₂|own` because
`●` combines only `imm` with `imm` ([TR] p. 5); likewise for `mut`. For `Pers`:
`(r₁ ● r₂) ● (r₁ ● r₂) = (r₁ ● r₁) ● (r₂ ● r₂)` by commutativity and associativity
([TR] 6.2, 6.3), `= r₁ ● r₂`. (3), (4) by the definitions; `W ∈ m` gives `m ∈ {aff, unr}` and
`C ∈ m` gives `m ∈ {rel, unr}`. ∎

`NoOwn` is what BoLo's `wp` lets a run leave behind (`ρ⁺|own = ∅`, [TR] p. 6) and what the
forget rules drop ([TR] 6.148, 6.149). `Pers` is BoLo's persistence: `!P ≜ emp ∧ P` holds of
`∅`, and an `imm` cell is idempotent ([TR] 6.43 at `α = β`, 6.116). In the lift, `⟦aff⟧`
contains `mut` and `imm` borrows and `⟦unr⟧` contains `imm` borrows.

*Source.* The reading of a mode as a set of resources closed under composition is ours. It is
how adjoint logic's structural rules (Pruiksma et al. §2, `σ(m)`) become semantic: `W` is
`⊆ NoOwn` (dropping is a forget) and `C` is `⊆ Pers` (copying is idempotence).

## 4.2 The three meeting points

Each meeting point is a definition about resources. Nothing else in the unary relation mentions
the heap.

**Definition D4.3 (meeting point 1: capabilities are resources).** A capability with state `s`
in cell `ℓ` is the resource

    Cap(ℓ, s) ≜ {ℓ ↦ own(cell(s))}

- **Owned**: a value `cap(ℓ, co)` carries `Cap(ℓ, s)` (D5.2).
- **Lent**: a `run(j, ℓ, co)` frame carries `Cap(ℓ, s)` while its body runs (L5.10). The body
  holds no part of it; its operations on `j` are answered by the frame, in place.

In the kernel lift a lend of a borrowed capability gives the body `ℓ ↦ Mut α P̂` with
`P̂(v) = ⌜v = cell(s), s ∈ ⟦S⟧⌝`, as [TR] 6.65 (Mut Frame) does for `withbor`. This calculus has
no borrow types, so it does not need that form; §9.3 says where it would.

**Definition D4.4 (meeting point 2: continuations are values in the resource world).** A
continuation is a thunk value (D1.8), so its resource is whatever `V⟦U_m^ρ C⟧` assigns to it
(D5.2): the resource of the frames it holds. Two forms:

- **one-shot** (`C ∉ q`): `κ¹(ℓ_κ, w)` holds `{ℓ_κ ↦ own(seg(S_κ))} ● r_κ`, where `r_κ` is the
  resource of the frames `S_κ`. Forcing it removes `ℓ_κ`. A second force is a use after free.
  An affine continuation that is neither resumed nor cancelled is an `own` cell left at the end
  of the run, which BoLo's `wp` forbids (`ρ⁺|own = ∅`).
- **copyable** (`C ∈ q`): `κ*(S_κ, w)` holds `r_κ`, which must be in `Pers` (D4.6).

What a suspended continuation may hold is therefore decided by one condition on `r_κ`, in each
protocol (D4.6), and it is discharged by independence (L5.4).

**Definition D4.5 (meeting point 3: cancellation is finalisation).** For a segment `S₁`,

    Cancel(S₁)(r)  ≜  ∃ r₀ ∈ NoOwn.  r = (●_{fin(j, ℓ_r, ℓ) ∈ S₁} ℓ_r ↦ own(rsrc ℓ)) ● r₀

`Cancel(S₁)` holds exactly of the resources that running `dtors(S₁)` (D3.4) disposes of: it frees
each owned resource of a `fin` frame of `S₁`, and what remains may be dropped. Cancelling a
continuation, unwinding to an abortive operation's handler, and failing a co-operation all run
`dtors` of a segment, so all three owe `Cancel` of it.

**Definition D4.6 (protocols).** The protocol of an instance of effect `E` describes what a
computation owes at a stop on that instance. For a resuming operation `o`, an argument
`v ∈ ⟦A_o⟧`, a resumption predicate `Φ : ⟦B_o⟧ → Res → Prop` and a cancel predicate
`Ψc : Res → Prop`:

    Π_E(o, v, Φ, Ψc)(r)  ≜  (C ∈ q_o ⇒ r ∈ Pers)  ∧  (∀ w ∈ ⟦B_o⟧. Φ(w)(r))  ∧  (W ∈ q_o ⇒ Ψc(r))

and for an abortive operation `a`, `Π_E(a, v, Ψc)(r) ≜ Ψc(r)`. `Π_Res(use, (), Φ, Ψc) = Φ(())`
(`use` is linear).

- The argument is ground, so it carries no resource; the whole of `r` is the continuation's
  share.
- **The resumption and the cancel are additive**: both hold of the same `r`, and the clause takes
  one. This is the `&` of `K(q, B, ρ', C)` (D1.8).
- **One protocol per effect, for every implementation.** A handler (model) and a runner
  (comodel) of `E` meet the same protocol. A function abstracted over `x : E^b` cannot tell them
  apart, which is phase A's `inst E b` covering both (`docs/effect-model.md` §1.2).
- **The bound's `susp` component does not appear.** In this calculus no suspended continuation
  can hold anything whose validity ends before the continuation is used: a lent capability
  travels with its `run` frame, and a resource with its `fin` frame. `susp` becomes load-bearing
  only in the kernel lift, where a continuation may hold a borrow (Theorem T9.2).

[SPEC §19 *Protocols* (`Π_Σ`): the same shape, with BoLo's argument and answer relations where
this calculus has ground types; borrow-core's `Core/EffDefs.lean` `Table`, `OpEnt`.]

## 4.3 The instance supply

**Definition D4.7 (binary worlds).** As phase B [PB `St`, `W`, `World.lean`]: a world `w` gives
each name on the left and on the right a status

    free | m(b) (matched with b on the other side) | p (pending) | g (garbage)

with `w.coh : sl(a) = m(b) ⇔ sr(b) = m(a)`. `w.r(a, b) ≜ sl(a) = m(b)`, a partial bijection
[PB `W.fn`, `W.inj`, `W.r_iff`]. `w.noPend` says nothing is pending.

- **Kripke order** `w ≤ w'` [PB `W.le`]: more matched, fewer free, the same pending.
- **Value order** `w ⊑ w'` ≜ `gcP(w) ≤ gcP(w')` [PB `W.sub`], where `gcP` reads pending names as
  garbage [PB `W.gcP`].
- **Updates** [PB `W.both`, `W.pendL`, `W.pendR`, `W.garbL`, `W.garbR`, `W.matchL`,
  `W.matchR`]: both sides allocate and match; one side allocates a name to match later; one side
  allocates a name never to be matched; one side allocates and matches the other's pending name.

**Lemma L4.3 (world facts).** [PB, `World.lean` and `Rel.lean`.] `≤` and `⊑` are preorders
(`le.refl`, `le.trans`, `sub.refl`, `sub.trans`); `w ≤ w' ⇒ w ⊑ w'` (`le.sub`); on worlds with
nothing pending the two agree (`noPend_le_of_sub`); every update moves up `⊑` (`sub_both`,
`sub_pendL`, `sub_pendR`, `sub_garbL`, `sub_garbR`, `sub_matchL`, `sub_matchR`) and is monotone in
`≤` (`le_both`, …, `le_matchR`); `noPend` is preserved by `≤` (`W.noPend_le`), by `both` and by
`garb*` (`noPend_both`, `noPend_garbL`, `noPend_garbR`).

*Proof.* Phase B's Lean proofs, one per named lemma. ∎

*Source.* Partial bijections of names as Kripke worlds are the standard treatment of generated
names in logical relations (Pitts & Stark, *Observable properties of higher order functions that dynamically
create local names, or: What's new?*, MFCS 1993, LNCS 711, DOI 10.1007/3-540-57182-5_8 [verified
via Crossref; content recalled]); matched names are Staton's instances in `[Inj, Set]` (LICS 2013, §IV)
[PA `docs/effect-model.md` §2]. The pending and garbage statuses, which let the two sides
allocate in different orders or allocate a name only one side uses, are phase B's (new to us).

**Definition D4.8 (the unary instance supply).** The unary relation needs only which protocol
each name has: a *protocol environment* `π` maps each instance variable of `Ψ` to a name and its
effect, and each row variable `r ≤ b` of `Θ` to a finite table of names and effects. The table of
a row is `Tab_π(ρ) ≜ {(π(x), E_x) | x ∈ ρ} ∪ ⋃_{r ∈ ρ} π(r)`. Since protocols depend only on the
effect (D4.6), a table is a set of names with effects. `bnd(T)` is the join of the declared
bounds of `T`'s effects, with `bnd(Res) = none`.

## 4.4 The factoring, stated

The design brief: the calculus is BoLo's resource world plus a local control discipline, meeting
at exactly three points. Formally:

1. The **binary relation** (§6) is defined over the instance supply alone (D4.7). It mentions no
   resource. Every law of §7 is proved through it.
2. The **unary relation** (§5) is BoLo's `wp` (§5.1) with protocols (D4.6). Its only
   heap-specific definitions are D4.3–D4.5.
3. The two meet only through **agreement** (T6.6), which uses the unary relation's safety to show
   that the binary relation's semantics (trees) is the machine's on moded programs.

§9.1 records where this held and where it was strained.
