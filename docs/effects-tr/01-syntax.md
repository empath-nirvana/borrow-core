# §1 Syntax

[← index](README.md) · next: [§2 Statics](02-statics.md)

The calculus is phase A's (`experiments/EffModel/EffModel/Syntax.lean`, `docs/effect-model.md`
§1.1) with five changes, each argued where it is made:

| change | where | why |
|---|---|---|
| `lend` consumes the capability and returns it (BoLo's `withbor` shape) | D1.9, [lend] in §2 | phase A's place-based `lend` is unsound once the place has been moved (§10.1, machine-checked) |
| a frame-owned resource is an **instance** of a built-in effect `Res`, not a value of type `resD` | D1.3, D1.9 | phase A lets a continuation carry the handle past its frame (§10.2, machine-checked) |
| a continuation is the static pair `⟨resume, cancel⟩` (phase B's `kty`) | D1.8 | destructor placement is static (§8.1) |
| a co-operation may fail, at an operation whose qualifier admits weakening | D1.3, D1.9 | phase A open problem 3 (§8.2) |
| recursion is `bfix`, bounded (phase B's form of SPEC §20's `bounded_fix`) | D1.9 | no step-indexing (§9) |

Names are used in this document; the mechanisation uses de Bruijn indices for value variables
and for instance variables separately, as phase B does (`EffModelRel/Syntax.lean`, `Var`). That
is an encoding, not a change.

---

**Definition D1.1 (modes).** A *mode* is a subset of the structural rules `{W, C}` (weakening,
contraction):

    lin = ∅      cancel = {W}      rel = {C}      unr = {W, C}

`m ≥ k` iff `m ⊇ k`. `m ⊓ k = m ∩ k` (the rules a pair or a sum admits); `m ⊔ k = m ∪ k`.

*Source.* Pruiksma, Chargin, Pfenning & Reed, *Adjoint Logic* (manuscript, 2018), §1–2: a mode
`m` has structural rules `σ(m)`, and `m ≥ k ⇒ σ(m) ⊇ σ(k)`. [PA `Mode`, `Mode.ge`, `meet`,
`join`; PB `Mode`, `Mode.ge`.]

**Definition D1.2 (ground types).** `G ::= 1 | int | bool | 0`, with `⟦1⟧ = {()}`,
`⟦int⟧ = ℤ`, `⟦bool⟧ = {tt, ff}`, `⟦0⟧ = ∅`. [PB `G`, `G.den`.]

Operation arguments and answers, and capability states, are ground. This is phase A's practice
(every signature in `Prelude.lean` is ground) and phase B's restriction (`Sig.arg`, `Sig.res` are
`G`). §9.5 says what lifting it costs.

**Definition D1.3 (signatures).** A signature `Σ` is a finite set of effect names `E`, each with

- resuming operations `o : A_o ↠^{q_o} B_o`, with `A_o, B_o` ground and `q_o` a mode, the
  *continuation qualifier*;
- abortive operations `a : A_a ↠ 0`, with `A_a` ground.

By convention an abortive operation has qualifier `q_a = cancel` (phase A, `docs/effect-model.md`
§1.2: "an abortive operation counts as cancellable"). An operation `o` is *fallible* when `W ∈ q_o`; a
co-operation may fail only at a fallible operation (D1.9, §8.2).

The signature contains one built-in effect, `Res`, with one resuming operation
`use : 1 ↠^{lin} 1` and nothing else. Its instances are the handles of `using` frames (D1.9).

[PA `OpSig`, `Sigs`; PB `Sig` (with `O`, `A`, `arg`, `res`, `q`, `aarg`). `Res` is new here.]

**Definition D1.4 (bounds).** A *bound* is a pair `b = (b.req, b.susp)` of a mode and a boolean.

- `b.req`: the structural rules a handler may apply to a continuation captured at an operation of
  the instance;
- `b.susp`: whether a handler may keep the continuation past the operation.

    none = (lin, false)        top = (unr, true)
    b ⊔ b' = (b.req ⊔ b'.req, b.susp ∨ b'.susp)
    b ⊑ b'  iff  b'.req ≥ b.req  ∧  (b.susp ⇒ b'.susp)

The *declared bound* of an effect is `bnd(E) = ⨆_o (q_o, true) ⊔ ⨆_a (cancel, false)`, starting from
`none`. The *runner bound* of an effect is `rbnd(E) = (⨆_o q_o, false)`. [PA `Bound`,
`Bound.le`, `boundOf`; `rbnd` is phase A's `Bound.none` refined by §8.2.]

**Definition D1.5 (instance and row contexts).**

    Ψ ::= · | Ψ, x : E^b          (instance variables, each with its effect and bound)
    Θ ::= · | Θ, r ≤ b            (row variables, each with its bound)
    ρ ::= finite set of atoms     atoms: instance variables x, row variables r

`Ψ` is *well formed* when every `x : E^b` has `bnd(E).req ≤ b.req`: an instance's bound admits
every qualifier of its effect. (Every bound the rules create satisfies it: `bnd(E)`, a handler's
`hb` (D2.8) and a runner's `rbnd(E)` all contain each `q_o`; `Res^{none}` has only `lin`.) The
same is asked of a row variable's instantiations (D4.8).

An instance is second class: it is never a value. It is bound by `handle`, `ν`, `lend`, `using`
and instance abstraction, and passed only as an instance argument. [PB: instances in `Ψ`, never
data; PA: rows of `Atom`.]

**Definition D1.6 (value types).**

    A ::= G | A ⊗ A | A ⊕ A | U_m^ρ C | cap_E S | tkt | strm^ρ A

- `U_m^ρ C`: a suspended computation at mode `m` that performs `ρ` when forced, then behaves as
  `C`. It fuses the polarity shift and the mode shift (phase A §2, *inferred*).
- `cap_E S`: an owned capability, a comodel of `E` with state of ground type `S`.
- `tkt`: a relevant token (phase A's `ticket`).
- `strm^ρ A`: a stored generator, `μX. U_lin^∅ ((F^ρ (A ⊕ (int ⊗ X))) &^{ρ,∅} F 1)` (D1.7's `&`).
  It is the one recursive type; `X` occurs only positively, to the right of `F` (§9.2).

**Definition D1.7 (computation types).**

    C ::= F A | A ⇒^ρ C | C &^{ρ₁,ρ₂} C | Π^ρ(x : E^b). C | ∀^ρ(r ≤ b). C

A row sits where effects happen: after an argument is received (`⇒^ρ`), after a method is
projected (`&^{ρ₁,ρ₂}`), after an instance is received (`Π^ρ`), after a row is received (`∀^ρ`).
The row of a computation before its first such point is on the judgement (§2). [PA `CTy`
(`arr`, `rcd`, `allR`); PA's dependent arrow at an instance type is `Π` here, as in PB `CTy.pi`.]

**Definition D1.8 (continuation types).** The type of the continuation a resuming clause of
operation `o` receives, in a handler into `C` whose outer row is `ρ'`:

    K(q, B, ρ', C) = U_{q.c ? unr : lin}^∅ ( (B ⇒^{ρ'} C) &^{∅,∅} F 1 )     if W ∈ q
    K(q, B, ρ', C) = U_q^∅ ( B ⇒^{ρ'} C )                                if W ∉ q

writing `q.c` for `C ∈ q`. The first component resumes; the second, `cancel`, runs the
continuation's destructors and answers `()`. A cancellable continuation is a **linear** thunk of the
pair, so the clause consumes it exactly once, by one of the two entries: the `A & 1` encoding
(SPEC §19's `κ`), which Munch-Maccagnoni reads as an affine type in his system (*Resource
Polymorphism*, 2018 [recalled]). A
continuation that may be both dropped and copied (`unr`) is an unrestricted thunk of the pair:
its captures are persistent (Lemma L5.6), so dropping it runs nothing. [PB `ktyB`, `kty`; PA
`kty` in `clauses` (without the cancel entry).]

**Definition D1.9 (terms).** Values and computations:

    V ::= x | () | n | tt | ff | (V, V) | inl V | inr V | thunk_m M | fold V | tkt_n

    M ::= ret V | M to x. N | λx:A. M | M V | force V
        | ⟨M, N⟩ | prj₁ M | prj₂ M
        | split V as (x, y). M | case V of inl x. M | inr y. N | if V then M else N | absurd V
        | prim p V V | emit V | punch V
        | op x.o(V; y. M)            (resuming operation o on instance x, at any C)
        | ab x.a(V)                  (abortive operation a on instance x, at any C)
        | handle x : E with H in M   (ν x, then a deep handler of x)
        | handleAt x with H in M     (a deep handler of an instance in scope)
        | ν x : E^b. M | ieq x y
        | Λx : E^b. M | M x          (instance abstraction and application)
        | Λr ≤ b. M | M [ρ]          (row abstraction and application)
        | newcap_E S co V | getcap V
        | lend V as x in M           (run M against the capability V, as instance x)
        | using x = acquire ℓ in M   (a frame owning resource ℓ, as instance x of Res)
        | unfold V
        | bfix_n x.a(V) (f. M)       (n unrollings of M, then ab x.a(V))

    H  ::= (ret z. N_ret ; {o(p, k). N_o}_{o ∈ E} ; {a(p). N_a}_{a ∈ E})
    co ::= {o(p, s). N_o}_{o ∈ E}

- `prim p` for `p ∈ {add, sub, lt, eq}`; `emit V` writes an integer to the world; `punch V` uses
  a ticket. These are the observable actions (D3.9).
- **Handlers.** `N_o` binds the argument `p : A_o` and the continuation `k : K(q_o, B_o, ρ', C)`.
  `N_a` binds only the argument: the machine cancels the continuation before the clause runs
  (§3).
- **Co-operations.** `N_o` is closed: `p : A_o, s : S ⊢ N_o : F ((B_o ⊗ S) ⊕ (E_o ⊗ S))` with
  empty row, where `E_o = int` if `o` is fallible and `E_o = 0` otherwise. `inl (w, s')` answers
  `w` and leaves state `s'`; `inr (e, s')` fails with code `e`, leaving `s'` (§8.2). A capability
  exists only for an effect with no abortive operation and with every `q_o ∈ {lin, cancel}` (a
  runner answers in place; it neither duplicates a continuation nor answers a constant, §2 rule
  [newcap]). [PB `coRes`, with `int` for every operation; here `0` at a non-fallible one.]
- **`lend V as x in M`** consumes the capability `V` and answers
  `F (cap_E S ⊗ (A ⊕ int))`: the capability back, beside `inl` of `M`'s answer or `inr` of a
  co-operation's failure code. Phase A's `lend c as x in M`, which leaves `c` in scope, is the
  derived form `lend c as x in M to z. split z as (c, r). …` that rebinds `c`. [PB `Cmp.lend`
  answers `F (A ⊕ int)` and does not return the capability; the two agree on denotations up to
  the pairing (§6.1).]
- **`using x = acquire ℓ in M`** acquires a resource with label `ℓ`, binds `x : Res^{none}`, and
  runs `M` under a frame that frees the resource when `M` returns or is unwound. `use` is
  `op x.use((); _. ret ())`, answered in place by the frame. [PA `using`/`use` with `resD`; PB
  `using`, `use` with value type `res`.]
- **`bfix_n x.a(V) (f. M)`** is `M[thunk_unr (bfix_{n-1} …)/f]` for `n > 0` and `ab x.a(V)` for
  `n = 0`: the kernel's `bounded_fix` with its budget known (SPEC §20), exhaustion being the
  abortive operation `a`. [PB `Cmp.bfix`.]

**Definition D1.10 (derived forms).**

    perform x.o V      ≜ op x.o(V; y. ret y)
    M ; N              ≜ M to _. N                      (M : F 1)
    drop V             ≜ prj₂ (unfold V)
    resume k w         ≜ (prj₁ (force k)) w             if W ∈ q;   (force k) w   otherwise
    cancel k           ≜ prj₂ (force k)                 (only if W ∈ q)
    call V w           ≜ (force V) w

[PA `perform`, `seq`, `call`; PB `kVal` builds the continuation value of the handler laws.]
