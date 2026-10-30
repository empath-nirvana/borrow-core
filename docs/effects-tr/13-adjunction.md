# §13 The adjunction framing: β, η, hiding, and the interaction law

[← §12 Sources and novelty](12-sources.md) · [index](README.md) · next: [§14 Stored continuations, borrows, and proof cost](14-stored-continuations.md)

**A candidate extension, not adopted** (issue #250; the design discussion is on #245). §§1–12 are
unchanged by it. This section and §14 test one proposed structure against the TR as it stands.
They answer one question: does the structure reduce the proof obligations of the kernel lift?
§14.5 gives the verdict and the count.

The structure under test:

- **Reify and reflect are the two sides of linear CBPV's `F ⊣ U` adjunction**, read as in
  Curien, Fiore & Munch-Maccagnoni's adjunction models, and extended from closed computations to
  stack segments: *freeze* is thunk-of-a-stack, *resume* is force.
- **Three facts:**
  - **β**: freeze then resume is the identity, up to fresh internal lifetimes;
  - **η**: the forwarding handler is the identity, cancellation included;
  - **hiding**: the body's relation is parametric in the handler's witness.
- **The claim to check:** tensor, instance parametricity, cancellation and contraction follow from
  β, η and hiding plus the frame rule.

Numbering continues the TR's: `D13.n`, `L13.n`, `T13.n`, `P13.n` (a property that fails,
computed here), and open problems `O5` onward. Proof status uses the TR's four labels (README,
*Conventions*). A fifth label is used for the two failures computed here: *computed here by
hand* means a run of D3.6 or an evaluation of D3.13 written out, and not machine-checked.

---

## 13.0 Results

| fact | binary (laws) | unary, own fragment (§5) | unary, kernel lift |
|---|---|---|---|
| β | T13.2: each step mechanised (phase B); composite here | L5.14, the *resume* bullet | needs the re-stratification lemma L14.4, **open (O5)** |
| η | T13.8: proved here at the level of its cases, under conditions; with a new frame (D13.7) at cancellable operations; in general **open (O6)** | L13.9 for the new frame, proved here | typing at a suspending outer operation reduces to O5 (§14.3) |
| hiding | not expressible in the binary relation; **open (O7)**; no law of §7 or §13 needs it | L5.15's (★), quantified over every state | `wpTS_M_antiFrameX` (pure), `ewpTS_M_antiFrameU` (abortive), mechanised; at a suspending table **open (part of O8)** |
| interaction law | T13.13: proved here in a special case; **fails at cancellable operations** (P13.14); general linear case **open (O6)** | — | — |

The claim (§13.6): it is **partly** true. Two of the four follow from β and η: the cancellation
laws and the tensor of pure handlers. The other two come from facts the TR already uses and
that are not β, η or hiding: instance parametricity from generativity, contraction from
independence. The tensor of a model with a comodel needs a fourth fact, the interaction law,
and that law holds only at linear operations.

---

## 13.1 The framing

**Definition D13.1 (freeze and resume).** Let `x` be an instance with a handler frame
`f_H = hnd(j, γ_h, H)`, and let a resuming operation `op x.o(V; y.M)` stop with segment
`S_κ = bind(γ, y.M) :: S₁ ++ [f_H]` (D3.6). Read as an evaluation context, `S_κ` is a stack
`K : F B_o → C` from the operation's answer to the handler's result.

    freeze(K)  ≜  thunk_m (λy. K[ret y])                       if W ∉ q_o
               ≜  thunk_m ⟨λy. K[ret y],  K^dtor⟩             if W ∈ q_o
    resume(κ)  ≜  [·] to y. resume κ y                         (a stack again)

Here `m` is D1.8's mode, and `K^dtor` is the segment's destructor: run `dtors(S_κ)` (D3.4) and
answer `()`. The machine's capture in D3.6 is `freeze` of the segment. Its `force` of a
continuation is `resume`.

**The adjunction.** In CBPV the stacks `F B → C` correspond bijectively to the values
`U(B ⇒ C)`:

    φ : Stk(F B, C) ≅ Val(U(B ⇒ C))        φ(K) = thunk(λy. K[ret y])      φ⁻¹(κ) = [·] to y. (force κ) y

`freeze` is `φ` and `resume` is `φ⁻¹`; at `W ∈ q` the cancel entry is added. `φ⁻¹ ∘ φ = id` is
the existence half of `F`'s universal property: a stack is determined by what it does to `ret`.
`φ ∘ φ⁻¹ = id` is `U`'s η together with `⇒`'s. In the TR's tree semantics `F A` is `Tree A`. That
is the **free** model on `A` over every instance's operations: D3.9 is an inductive type, and
D3.11 makes every computation type a model. So `F ⊣ U` there is the free ⊣ forgetful adjunction
for models, and its universal property has two halves:

- **existence**: a deep handler is the fold out of `Tree A` (D3.12), and a stack is `bindC`;
- **uniqueness**: a fold that sends each operation to the same operation, and each leaf to
  `ret`, is the identity.

Below, β is the existence half applied to a stack segment (T13.2), and η is the uniqueness half
(T13.8).

*Source and novelty.* The adjunction is Levy's: stacks correspond to the computations of the
other side (Levy, *Adjunction models for call-by-push-value with stacks*, TAC, DOI
10.70930/tac/e17sf9pc [verified via Crossref; content recalled]). Curien, Fiore &
Munch-Maccagnoni (*A theory of effects and resources: adjunction models and polarised
calculi*, POPL 2016, pp. 44–56, DOI 10.1145/2837614.2837652 [verified via Crossref]) give the
resource reading of such adjunctions. I recall only this general reading of their paper: thunk
and force, and return and bind, are the two transposes of one adjunction between values and
computations. I use nothing more specific from it and have not re-read it for this section.
Handlers as the unique homomorphisms out of the free model are Plotkin & Pretnar's (LMCS 2013,
[via phase A]). The reading of D3.6's capture as `φ` is standard; none of §13.1 is new.

**What "resource-carrying delimited thunk" means here.** At the own fragment it is the TR's
D1.8 type and D4.4's resource. A frozen segment is a thunk value whose resource is the
segment's. When `W ∈ q` it is an additive pair whose `cancel` entry is the segment's destructor.
At the kernel lift the resource also contains borrows. Turning a segment that holds borrows into
a value is §14's re-stratification lemma, and it is the only part of the framing with new
content.

---

## 13.2 β: freeze then resume

**Theorem T13.2 (β).** Let `K` be an evaluation context built from `to`, argument, projection,
instance-application and row-application frames (D7.1 without `using` and handlers). Let `H` be
a handler of `x` with resuming clause `N_o`, and `κ ≜ freeze(handleAt x with H in K[M])` (y
free). Then:

1. `handleAt x with H in K[op x.o(V; y.M)]  ≡  N_o[V/p, κ/k]`;
2. `resume κ w  ≡  handleAt x with H in K[M[w/y]]`;
3. if `W ∈ q_o`: `cancel κ ≡ ret ()`. If `K` is given `using` frames as well, then on the machine
   `cancel κ` runs `K^fin` (D7.1) and answers `()`.

*Proof.*

1. T7.1 moves the operation out of `K` (PB `alg_bind`, `alg_app`, `alg_prj1`, `alg_prj2`,
   `alg_iapp`). Then T7.5 applies (PB `h_op`, `kVal`).
2. The two sides have equal denotations. `⟦resume κ w⟧` is the first component of `mkK` at the
   folded continuation, applied to `⟦w⟧` (PB `kVal_den`, D3.13). That is `hnd(⟦K[M]⟧[y ↦ ⟦w⟧])`.
3. The cancel component of `mkK` is `Tree.dtors d (ret ())`, where `d` is the operation's
   destructor list. With no `using` frame in `K`, `d = []`. With `using` frames, `addFin`
   appends one `free` per frame, innermost first (D3.12). That is `K^fin`'s denotation, as in the
   first half of T7.3's proof. On the machine, D3.6's cancel row runs `dtors(S_κ)`, which are the
   same frames. ∎

*Status.* Each step cites a mechanised lemma, and the composite takes one line. β adds **no
obligation** to the TR. "Up to fresh internal lifetimes" is not visible here, because the
binary relation erases lifetimes (D3.10). The lifetimes matter only to the unary relation at the
kernel lift, which is §14.

---

## 13.3 η: the forwarding handler

**Definition D13.4 (forwarding handler).** For an instance `x : E^b`,

    Fwd_x ≜ ( ret z. ret z ;  { o(p, k). op x.o(p; y. resume k y) }_o ;  { a(p). ab x.a(p) }_a )

In `handleAt x with Fwd_x in M`, a clause runs on `S₂`, outside the handler frame (D3.6). Its
`op x.o` therefore reaches the next handler of `x` *outward*. The law to test is
`handleAt x with Fwd_x in M ≡ M`.

**Lemma L13.5 (where `Fwd_x` types).** Under §2, [op]'s capture premise in `Fwd_x`'s clauses
holds if and only if, for every resuming `o` of `E`, the mode of `k : K(q_o, …)` is `≥ b.req`. In particular:

- it types when every resuming operation of `E` is linear and `E` has no abortive operation
  (`b.req = lin`);
- it never types when some resuming `o` has `W ∈ q_o` and `C ∉ q_o`.

*Proof.* In `N_o`, `k` is free in the continuation `y. resume k y` of `op x.o`. So [op]'s premise
`capture(Γ, {k}, b.req)` asks `mode(K(q_o, …)) ≥ b.req`. By D1.8 that mode is `lin` when
`C ∉ q_o`, and `unr` or `rel` otherwise. If `b.req = lin` the premise holds. If `W ∈ q_o`, then
`W ∈ b.req` (D1.5, well-formed `Ψ`), and a `lin` thunk has no `W`. ∎

*Remark.* [op]'s premise is at `b.req`, the join over every operation of `E` (D2.6). L5.12's proof
uses only `q_o ≤ b.req` and then the protocol at `q_o`. Its two bullets would go through with
`r_M ∈ ⟦q_o⟧` in place of `r_M ∈ ⟦b.req⟧`. A premise at `q_o` would type `Fwd_x` at the linear
operations of an effect that also has abortive ones. §2 is not changed here.

**Property P13.6 (why the cancellable case fails, in the trees).** Leave typing aside. On an
operation `op i o v k d` of the handled name, the left side's fold is the clause, which builds
`op i o v (λy. hnd(k y)) []`. The right side is `op i o v k d`. The re-performed operation carries
the destructor list `[]`, where the original carried `d`, the destructors of the segment. An
outer handler that cancels therefore runs `d` on the right and nothing on the left. On the
machine, the left side's segment cell `ℓ_κ` is never freed. *Computed here by hand from D3.12.*

Forwarding a cancel needs a frame that owns the inner continuation and cancels it when unwound.
§2 has no such frame: `fin` frames free a `Res` resource and nothing else, and D3.4 discards a
`bind` frame. That is the next definition.

**Definition D13.7 (a frame that holds a continuation).** A new computation former

    M to^k y. N          (k a one-shot continuation variable with W ∈ q_k; k ∉ fv(M))

- runs `M`;
- on return of `v`, runs `N[v/y]`, which uses `k`;
- when unwound (cancel, abort, or a co-operation's failure), runs `cancel k`.

Typing, rule **[to-hold]**: the premises of [to], except that `k` is exempt from the `W` part of
`capture(Γ, fv(N) ∖ y, bound(ρ₁).req)`, because the frame disposes of it. The rule also requires
`C ∉ bound(ρ₁).req`, because a linear `k` cannot be copied. The usage of `k` is `[1,1]`.

The pieces it needs:

| piece | definition |
|---|---|
| machine | a frame `bindk(γ, y.N, κ)`. It returns as `bind`. D3.4 is extended: running the destructors of a segment that contains `bindk(…, κ¹(ℓ_κ, w))` requires `μ(ℓ_κ) = seg(S')`, removes `ℓ_κ`, and runs `dtors(S')`. The recursion is well founded because `S'` was captured before the frame holding it was pushed, so its cells are older (L5.18.1). |
| trees | `Dtor` gains a constructor `run t` for `t : Tree 1`, the held continuation's cancel, and the frame appends `run (cancel component of ⟦k⟧)` to the destructors of every operation inside it. `obs` unwinds `run t` by executing `t`. |
| relation | `DtorR`: `run t ~ run t'` at `TreeRel_⊤`. `DR` gains a flattening rule: `[run (Tree.dtors e (ret ()))] ~ e'` when `e ~ e'`. |
| unary | D4.5's `Cancel` is extended: a `bindk` frame's resource is `ℓ_κ ↦ own(seg S')` together with its resource, and running it is `Cancel(S')`, recursively. |

**Theorem T13.8 (η).** `handleAt x with Fwd_x in M ≡ M` holds, as `LR`, in each of these cases:

- **(a) linear operations:** `Fwd_x` types (L13.5), and every operation of `M` on `x` carries an
  empty destructor list, i.e. it crosses no `using` or `lend` frame of `M`;
- **(b) cancellable operations:** the clause at each `o` with `W ∈ q_o` is written with D13.7,
  `o(p, k). (op x.o(p; y. ret y)) to^k y. resume k y`. This holds for every `M`;
- **(c) abortive operations:** every `M`.

*Proof (proved here at the level of its cases; not mechanised).* Fix `w` with `w.r(i, i')`,
where `i` and `i'` are the two sides' names for `x`. By induction on `TreeRel_R(w, t, t')`, show
`TreeRel_R(w, hnd_i(Fwd)(t), t')`. This follows phase B's `hnd_transparent`, with `i` matched
where that lemma has it garbage.

- **`ret`.** The return clause is `ret z`, so the leaf is related as before.
- **`act`, `nu`.** The fold commutes with both (`Tree.hnd`'s cases). Use the induction hypothesis,
  and at `nu` also the world update.
- **`op j …` with `j ≠ i`.** The fold passes it as `opA` with continuation `hnd ∘ k` and the same
  `d` (`Tree.hnd`'s non-matching branch). Use `TreeRel.op` with the induction hypothesis.
- **`op i o v k d`, own name, case (a).** The left side is the clause's tree,
  `op i o v (λy. hnd(k y)) []`, and the right side is `op i' o v k' d'`. A `using` or `lend` frame of
  `M` between the operation and the handler would put a `free` or a `wb` in `d'`. The hypothesis
  of (a) gives `d' = []`, and `d = []` by `TreeRel.op`'s premise `DR(w, d, d')`.
  So `DR(w, [], [])` holds, and `TreeRel.op` applies with the induction hypothesis on `k y`.
- **`op i o v k d`, own name, case (b).** The `bindk` frame appends `run (Tree.dtors d (ret ()))`.
  The flattening rule of D13.7 relates that list to `d'`. Then `TreeRel.op`. The order is right:
  an outer cancel of the forwarded operation runs `cancel k`, which runs `dtors(S₁)` innermost
  first, then `dtors(S₂)`. The right side's segment is `S₁ ++ [f_H] ++ S₂`, and its destructors
  run in the same order (`f_H` has none).
- **`ab i a v d`, case (c).** The fold runs `dtorsA d` and then the clause, `ab i a v []`. The
  right side is `ab i' a v d'`. This is `TreeRel.abE` with the split `d ++ []`. ∎

**Property P13.9 (the linear case in general).** Drop (a)'s hypothesis. Take the context
`ν x. [·]` (no handler of `x`) and
`M = using r = acquire 1 in op x.o((); y. ret ())` with `o` linear.

- `⟦M⟧`'s operation node carries `d' = [free 1 r]`.
- The left side's re-performed node carries `[]`.
- Both operations reach the top unhandled, and D3.14 unwinds their destructors. The traces are
  `[acq 1, free 1]` on the right and `[acq 1]` on the left.

So `CtxEq_den` fails, and with it `LR`: D6.2's `op` rule needs `DR(w, [], [free 1 r'])`, which
relates lists pointwise. *Computed here by hand from D3.12–D3.14.*

The context is not moded: a moded closed program has no unhandled operation (T5.2). In a moded
program a linear operation is never cancelled, so its destructor list is never run. Whether
`CtxEq_op` holds in the linear case is **open (O6)**. The step that does not go through is that
D6.2 relates the destructor lists of every operation, while a moded program runs only those of
weakenable operations.

**Lemma L13.9 ([to-hold] is compatible).** Under the unary relation of §5, extended by D13.7's
`Cancel`, [to-hold] is compatible.

*Proof.* As L5.10, with `S₀ = bindk(γ, y.N, κ) :: S_e` and `R₀ = r_N ● r_κ ● r_e`, where `r_κ`
is `k`'s resource (D4.4, with its `seg` cell). Compatibility (D5.8):

- `C ∈ q` for an operation of `ρ₁`: the rule refuses it (`C ∉ bound(ρ₁).req`).
- `W ∈ q`, or an abortive operation: `Cancel(S₀)(R₀)` holds because `r_N ● r_e ∈ NoOwn` (L5.4.2,
  L5.4.3), and because `r_κ` is the `bindk` frame's own resource, whose running is
  `Cancel(S_κ)(r_κ)` by `k`'s value relation (D5.4 at `K`, its `prj₂` elimination).

The return case is L5.10's. ∎

**Generativity: why η is stated at `handleAt`.** The form with a fresh instance would read
`handle x : E with Fwd_{x→x'} in M ≡ M[x'/x]`, where the clauses re-perform on an outer `x'`.

**Property P13.10.** That form fails at `M = ieq x x'`. The left side's `x` is fresh, so
`ieq` answers `ff`. The right side is `ieq x' x'`, which answers `tt`. *Computed here by hand
from D3.6.* Both sides are moded.

So η holds only at the same instance. It needs generativity in exactly the sense of T7.14
(new-ν): a fresh name differs from every name in scope.

**What η needs.** The binary relation (T13.8 is a `TreeRel` induction), and generativity through
P13.10. At cancellable operations it also needs a frame that holds a continuation (D13.7). It does not
need rebasing: the binary relation erases lifetimes. At the lift, the forwarding clause holds
`k` across an outer operation. If that operation suspends, `k` is a continuation held inside
another continuation. When `k` holds a borrow, that is §14's case. Its typing then rests on L14.4
(§14.3).

---

## 13.4 Hiding

**Unary hiding is in the TR.** L5.15 proves (★) "for every `(S, c, r')` in the fixed point *and
every state `s`*". The lend's body is uniform in the capability's state, which is framed in
`R₀` and never read by the body. At the kernel lift the same fact is BoLo's Anti Frame.
`wpTS_M_antiFrameX` (`Core/FrameRules.lean`, `[TR]` 6.66 at the tagged world) proves it for pure
callbacks, and `ewpTS_M_antiFrameU` (`Core/EffWp.lean`) for abortive tables. At a suspending
table it is **open** (part of O8); §14.4 states where it is needed.

**Definition D13.11 (binary hiding).** For handlers `H` and `H'` of `x` into state-passing types
`A₀ ⇒ D`, and a relation `R ⊆ ⟦A₀⟧ × ⟦A₀⟧` such that the clauses are related at `R`-related
states:

    R(s, s')  ⇒  LR( (handleAt x with H in M) s,  (handleAt x with H' in M) s' )

**Binary hiding is not in the binary relation.** D6.4 relates a state of type `A₀` by `VR(A₀)`,
which is equality at ground types. No relation can be substituted for it. A capability's cell is
matched with equal contents (L6.5's `Inv`). D13.11 is representation independence, and it needs
one of two new constructs:

1. a relational interpretation of an abstract state type in `VR` and `CRU`, in Reynolds' style,
   with the Fundamental Property re-proved over it. The calculus has no abstract types, so the
   abstraction would have to be added;
2. worlds that carry a relation per matched cell (Ahmed, Dreyer & Rossberg, *State-dependent
   representation independence*, POPL 2009, DOI 10.1145/1480881.1480925 [verified via Crossref;
   content recalled]). At ground states the relation does not mention worlds, so this adds no
   stratification. At higher-type states it is O4.

This is **open (O7)**. No law of §7 or §13 uses D13.11: T7.8, T7.9 and T7.11 relate identical
states, and T13.8 relates a handler to no handler. Binary hiding would be a new capability, not a
step any existing proof is waiting for.

**"The only bridge."** In the tree semantics the body never sees its handler: by D3.13,
`⟦handleAt x with H in M⟧ = hnd_H(⟦M⟧)`, and `⟦M⟧` does not depend on `H`. So "the body interacts
with the handler only by freezing at an operation" holds by definition there, and costs nothing.

---

## 13.5 Answering operations and freeze/resume: the interaction law

Take an instance `x` bound by a `lend` with co-operations `co`, and a handler of another instance
`h`. An answering operation on `x` and a control operation on `h` meet at a freeze in two
placements:

- **(i)** the lend outside the handler, so the clause may see `x`;
- **(ii)** the lend inside the handler, so the frozen segment holds the `run` frame. [lend]
  then forces `q_o = lin` (§2).

**Theorem T13.13 (interaction law, special case).** Assume placement (i), and:

- the co-operations are `PureCo` (T7.8: they answer in place and emit nothing);
- `o` is linear;
- `h`'s clause `N` for `o` does not mention `x`, and performs no operation before its use of `k`.

Then, under `lend c as x in handle h : E with H in [·]`,

    op x.a(u; z. op h.o(v; y. M))  ≡  op h.o(v; y. op x.a(u; z. M))        (z ∉ fv(v), y ∉ fv(u))

*Proof (proved here; equal denotations).* Let the lend's state be `s`, and let `s₁` be the state
after `a`.

- **Left side.** The handler passes `op x a` (`Tree.hnd`'s non-matching branch). `runL` answers
  it by `coStep` and continues at `s₁`. At `op h o`, the handler gives `N[k₁]` with
  `k₁ y = hnd(⟦M⟧ y)`.
- **Right side.** The handler gives `N[k₂]` at `s`, with `k₂ y = hnd(op x a u (λz. ⟦M⟧ y))`.

`N` performs no operation before it uses `k`, so `runL` reaches the use with no write-back
recorded and the state unchanged. Since `o` is linear, `N` uses `k` exactly once. There `k₂`
performs `a`, moving `s` to `s₁`. Both sides then continue with `hnd(⟦M⟧ y)` at `s₁`, and anything
`N` does after `k` returns is at the same state on both sides. ∎

**Property P13.14 (it fails at a cancellable operation).** Take

- `Ctr` with `inc : 1 ↠^{lin} 1`, run by `co_inc(p, s) = ret (inl ((), s + 1))`;
- `Stop` with `stop : 1 ↠^{cancel} 1`, handled by `H_drop = (ret z. ret z ; stop(p, k). cancel k ; ret 0)`;
- `P(body) ≜ newcap_Ctr int co_inc 0 to c. lend c as x in (handle h : Stop with H_drop in body) to z. split z as (c', r). getcap c'`.

Then:

- `P(op x.inc((); _. op h.stop((); _. ret 1)))` answers `1`: `inc` runs, then `stop` is
  cancelled;
- `P(op h.stop((); _. op x.inc((); _. ret 1)))` answers `0`: `stop` is cancelled first, and `inc`
  never runs.

Both are moded:

- [lend]'s row after removing `x` is `∅`;
- the continuations capture nothing;
- the clause uses `k` once, by `cancel`.

*Computed here by hand from D3.6.*

So the commutation needs the frozen segment to be resumed **exactly once**. Compare ν/op (T7.15),
which needs **at most once**. An unused name is unobservable (garbage), but a dropped answering
operation is observable through the state.

**The general linear case.** Suppose the clause performs an operation crossing the `run` frame
before its use of `k`. Under [lend] that operation is linear. `runL` appends `wb c s₁` to that
operation's destructors on the left and `wb c s` on the right (D3.12). D6.1 relates `wb c s` only
with `wb c' s`, at the same state. So D6.2's `op` rule does not relate the two trees, and `LR`
fails. The moded program never runs those destructors, because a linear operation is not
cancelled. Whether `CtxEq_op` holds is **open (O6)**, with the same missing step as P13.9. In
placement (ii) the same happens whenever an operation crosses the lend inside the segment.

*Source.* Commuting an operation of a model with an operation of a comodel is the tensor of a
model with a comodel (Plotkin & Power, MFPS 2008, DOI 10.1016/j.entcs.2008.10.018 [verified via
Crossref; Thm 4.4 via phase A]). Katsumata, Rivas & Uustalu (*Interaction laws of monads and
comonads*, LICS 2020, DOI 10.1145/3373718.3394808 [verified via Crossref; content recalled])
give the general setting, with runners as an instance. I read T13.13 as their compatibility
condition at one operation of each. I have not checked that reading against their statement.
The finding that the law needs exactly-once resumption, and that its `LR` proof stops at the
destructor lists, is new to us.

**#184 at the boundary.** An answering operation is a call (SPEC §19, *Kinds of operation*):
under #184 it is `withswap` on the handler's `Mut` state. A freeze cannot happen *inside* one,
because an answering clause does not capture a continuation (§8.2, option (d) excluded). So
answering operations are atomic with respect to freeze. What remains is T13.13 and its limits.

---

## 13.6 The claim: what follows from β, η, hiding and the frame rule

| consequence | follows from β, η, hiding + frame? | what it actually uses |
|---|---|---|
| **tensor of pure models** (two handlers with pure clauses; T7.11) | **yes** | T13.2(1)–(2) at each handler, then the two state updates commute on disjoint components (frame). This is T7.11's proof as written. `PureClause` is a hypothesis on the handlers, not a law. |
| **tensor of runners** (T7.8) | **only up to destructors** | It would need the identification of a `lend` with a tail-resumptive state-passing handler. The two have equal denotations except for the `wb` destructors `runL` records (D3.12), so they are not `LR`-related (as in §13.5). T7.8's direct proof (`runL_pair`) stays. |
| **model ⊗ comodel** (a handler's operation against a runner's) | **no** | It needs the interaction law, a fourth fact. That law holds at linear operations in the case of T13.13, fails at cancellable ones (P13.14), and is open in general (O6). |
| **instance parametricity** (T7.16) | **no** | It uses generativity: a fresh name is garbage (`gL`), so the fold never fires on it. A route through η exists: handlers that agree on `M`'s operations are equal, then T13.8. But "agree on `M`'s operations" is itself generativity, and the TR's proof does not use η. |
| **cancellation: the destructor form** (T7.3) | **yes, with one rule** | β's cancel half, T13.2(3), gives `cancel κ = K^fin`. An abort is a cancellable operation at answer `0` whose handler cancels first (SPEC §19 encodes `raise` this way). The binary relation still needs the cancel to be eager at answer `0`, which is the rule `TreeRel.abE`. |
| **cancellation: forwarding a cancel** | **it is η's cancel half** | T13.8(b), which needs the new frame of D13.7. |
| **cancellation: exactly once** (T5.2.3–4) | **no** | It is unary: a one-shot continuation is a heap cell its one use frees (D4.4). |
| **contraction** (a continuation copied) | **no** | Independence (L5.4) and the mode algebra (L4.2.4): a copyable continuation holds only `Pers`. In the adjunction reading, a copyable value is under `!`, and `!` is not one of the three facts. Out of scope (#245: multi-shot only if free). |

**Verdict on the claim.** It holds for the cancellation laws and for the tensor of pure models.
It does not hold for instance parametricity or contraction, which rest on generativity and
independence; the TR already has both, and β, η and hiding are not used. It does not hold for
the tensor of a model with a comodel, which needs the interaction law, true only at linear
operations. No proof in §7 becomes shorter when re-derived this way.
