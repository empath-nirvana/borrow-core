# §2 Statics

[← §1 Syntax](01-syntax.md) · [index](README.md) · next: [§3 Dynamics](03-dynamics.md)

The judgement synthesises a row, a type and a **usage** for every variable, as phase A's `check`
does (`experiments/EffModel/EffModel/Typing.lean`). Every property this document proves rests on
four side conditions, all phase A's:

- **grades**: a variable's uses are allowed by its type's mode (D2.2);
- **independence**: at every place something is captured, every captured variable has a mode
  `≥` the capturer's (D2.6);
- **scope**: an instance never appears in a type outside its binder;
- **frame captures**: a frame that owns something without a destructor is captured only by
  continuations that must be resumed (rules [lend], [using]).

Phase A's fifth check, T1, is not a premise here. §9.3 shows the owning `lend` does not need it
for this calculus (Theorem T9.1) and says where T1 is still needed (Theorem T9.2).

---

## 2.1 Grades

**Definition D2.1 (grades).** A *grade* is an interval `g = [lo, hi]` with
`0 ≤ lo ≤ hi ≤ 2`, `2` read "many".

    g + g' = [min(2, lo + lo'), min(2, hi + hi')]      (sequencing)
    g ⊔ g' = [min(lo, lo'), max(hi, hi')]              (alternatives: branches, record methods,
                                                        the return and abortive clauses)
    ω·g    = [0, 2]   if g ≠ [0,0];   [0,0] otherwise   (a clause run once per operation)

A *usage* `u` maps the variables of `Γ` to grades, `[0,0]` where unmentioned; `+`, `⊔` and `ω·`
act pointwise. [PA `G`, `G.add`, `G.hull`, `Uses.scale`.]

**Definition D2.2 (grade admitted by a mode).**

    gradeOK(m, [lo, hi])  ≜  (lo ≥ 1 ∨ W ∈ m) ∧ (hi ≤ 1 ∨ C ∈ m)

[PA `gradeOK`.] It is checked at every binder (rules below, "check `x`").

**Definition D2.3 (semantic admissibility).**

    Adm(m, g)  ≜  (m = lin ⇒ g ∈ {[0,0], [1,1]})  ∧  (C ∉ m ⇒ hi ≤ 1)

A usage `u` is *admissible* for `Γ` when `Adm(mode(Γ(x)), u(x))` for every `x`.

**Lemma L2.1 (admissibility is inherited).**

1. `gradeOK(m, g) ⇒ Adm(m, g)`, and `Adm(m, [0,0])` for every `m`.
2. `Adm(m, g₁ + g₂) ⇒ Adm(m, g₁) ∧ Adm(m, g₂)`.
3. `Adm(m, g₁ ⊔ g₂) ⇒ Adm(m, g₁) ∧ Adm(m, g₂)`.
4. `Adm(m, ω·g) ⇒ Adm(m, g)`.

*Proof.*
1. If `m = lin`, `gradeOK(lin, g)` forces `lo ≥ 1` and `hi ≤ 1`, so `g = [1,1]`. If `C ∉ m`,
   `gradeOK` forces `hi ≤ 1`. `[0,0]` satisfies both conjuncts of D2.3.
2. `hi(g₁ + g₂) ≥ hi(gᵢ)`, so the second conjunct passes down. For `m = lin`: if
   `g₁ + g₂ = [0,0]` both are `[0,0]`. If `g₁ + g₂ = [1,1]`, then `lo₁ + lo₂ = 1` and
   `hi₁ + hi₂ = 1` with `loᵢ ≤ hiᵢ`. So one summand is `[1,1]` and the other `[0,0]`.
3. `hi(g₁ ⊔ g₂) = max(hi₁, hi₂)`, so the second conjunct passes down. For `m = lin`, if the hull
   is `[0,0]` both are; if it is `[1,1]`, then `min(lo₁, lo₂) = 1` and `max(hi₁, hi₂) = 1`, so
   both are `[1,1]`.
4. `ω·g = [0,2]` for `g ≠ [0,0]`. That is not admissible at `lin` (first conjunct) nor at any
   `m` without `C` (second). So the hypothesis forces `C ∈ m ≠ lin` or `g = [0,0]`, and either
   way `Adm(m, g)`. ∎

Item 1 is stated for the binder checks; the Fundamental Property (T5.1) is stated for admissible
usages, and L2.1.2–4 are what make the induction go through sub-derivations.

## 2.2 Modes of types, bounds of rows

**Definition D2.4 (mode of a value type).** [PA `VTy.mode`.]

    mode(G) = unr       mode(A ⊗ B) = mode(A ⊓ B) = mode(A) ⊓ mode(B)   (also for ⊕)
    mode(U_m^ρ C) = m   mode(cap_E S) = lin      mode(tkt) = rel     mode(strm^ρ A) = lin

**Definition D2.5 (bound of a row).** For `Ψ; Θ`, `bound(ρ) = ⨆_{x ∈ ρ} b_x ⊔ ⨆_{r ∈ ρ} b_r`,
from `none`, where `x : E^{b_x} ∈ Ψ` and `r ≤ b_r ∈ Θ`. [PA `Ctx.bound`.]

**Definition D2.6 (independence).** `capture(Γ, X, m)  ≜  ∀ x ∈ X. mode(Γ(x)) ≥ m`.
[PA `Ctx.capture`.] Adjoint logic's declaration of independence (Pruiksma et al. §2): a thing at
mode `m` depends only on hypotheses at modes `≥ m`.

The capturers and their modes:

| capturer | mode | rule |
|---|---|---|
| a thunk at mode `m` | `m` | [thunk] |
| a recursive thunk (`bfix`) | `unr` | [bfix] |
| the rest of a `to` while `M : F A ! ρ₁` runs | `bound(ρ₁).req` | [to] |
| an argument waiting on the stack while `M : A ⇒ C ! ρ₀` runs | `bound(ρ₀).req` | [app] |
| an operation's own continuation | `b_x.req` | [op] |
| a handler's clauses, forwarded through by `ρ` | `bound(ρ).req` | [handle] |
| a resuming clause (run once per operation) | `unr` | [handle] |
| a `using` frame (affine: it has a destructor) | `aff ≥ bound(ρ).req` | [using] |
| a `lend` frame (linear: the capability has no destructor) | `lin = bound(ρ).req` | [lend] |

**Lemma L2.2 (order facts).** For modes `m, k, m'` and bounds `b, b'`:

1. `≥` is a partial order; `m ⊓ k` is the greatest lower bound, `m ⊔ k` the least upper bound.
2. `capture(Γ, X, m) ∧ m ≥ m' ⇒ capture(Γ, X, m')`.
3. `ρ ⊆ ρ' ⇒ bound(ρ) ⊑ bound(ρ')`; in particular `bound(ρ).req ≤ bound(ρ').req`.
4. `W ∈ q_o ⇒ W ∈ b.req` and `C ∈ q_o ⇒ C ∈ b.req` for `b = bnd(E)` or `b = hb(H, ρ_h)` (D2.8),
   and the same for an abortive operation with `q_a = aff`.

*Proof.* (1) is the subset order on subsets of `{W, C}`. (2) by transitivity of `⊇`. (3) `⊔` is
monotone. (4) `bnd(E).req` and `hb(H, ρ_h).req` are `⨆_o q_o ⊔ ⨆_a aff` (D1.4, D2.8), which
contains each `q_o` and `aff`. ∎

## 2.3 Tail resumption

**Definition D2.7 (tail resumption).** `tail_k(N)` holds when `k` occurs in `N` only as the head
of a call in tail position [PA `Tm.tailOnly`, extended to the static continuation of D1.8]:

    tail_k(M to x. N)          ⇔  k ∉ fv(M) ∧ (x = k ∨ tail_k(N))
    tail_k(if V then M else N) ⇔  k ∉ fv(V) ∧ tail_k(M) ∧ tail_k(N)
    tail_k(case V of inl x. M | inr y. N)
                               ⇔  k ∉ fv(V) ∧ (x = k ∨ tail_k(M)) ∧ (y = k ∨ tail_k(N))
    tail_k(split V as (x,y). M) ⇔ k ∉ fv(V) ∧ (x = k ∨ y = k ∨ tail_k(M))
    tail_k(λx:A. M)            ⇔  x = k ∨ tail_k(M)
    tail_k(T)                  ⇔  tcall_k(T) ∨ k ∉ fv(T)        for T an application
    tail_k(T)                  ⇔  k ∉ fv(T)                     otherwise

    tcall_k(force k)  tcall_k(prj₁ (force k))  tcall_k(prj₂ (force k))
    tcall_k(T W)  if tcall_k(T) ∧ k ∉ fv(W)

`tail_k` refuses `k` under every frame-pushing form other than `to` and a binder: under
`handle`, `handleAt`, `lend`, `using`, `prj`, an instance or row application, and in any value
position. That is what Lemma L5.12 uses: at a tail call the clause's own frames are all gone.

**Definition D2.8 (handler bound).** For a handler `H` of `E` whose clauses may perform `ρ_h`:

    keeps(H) ≜ ∃ resuming o ∈ E. ¬ tail_k(N_o)
    hb(H, ρ_h) ≜ (⨆_o q_o ⊔ ⨆_a aff,  keeps(H) ∨ bound(ρ_h).susp)

[PA `handlerBound`.] An instance with `b.susp = false` is **in place**; otherwise
**suspending**.

## 2.4 The judgement

**Definition D2.9 (judgements).** `Ψ; Θ; Γ ⊢ V : A ▷ u` and `Ψ; Θ; Γ ⊢ M : C ! ρ ▷ u`, by the
rules of Figure 2.1. `Ψ; Θ; Γ` is fixed and omitted where it does not change. "check `x`" is the
premise `gradeOK(mode(A), u(x))` for the binder `x : A`, after which `x` is removed from the
usage. Subtyping `≤` is phase A's `vsub`/`csub` (rows covariant, modes forgotten downward along
`≥`, bounds widened along `⊑`, `cap` invariant in its state) [PA `vsubN`, `csubN`]. Every
`handle`/`handleAt` carries the annotations `ρ_h, C` of phase A's syntax.

**Figure 2.1 — typing rules.** Values:

    [var]    Γ(x) = A                                  ⊢ x : A ▷ {x ↦ [1,1]}
    [const]  ⊢ () : 1,  n : int,  tt, ff : bool,  tkt_n : tkt        ▷ ∅
    [pair]   V : A ▷ u₁    W : B ▷ u₂                   ⊢ (V, W) : A ⊗ B ▷ u₁ + u₂
    [inj]    V : A ▷ u                                  ⊢ inl V : A ⊕ B ▷ u   (inr alike)
    [thunk]  M : C ! ρ ▷ u    capture(Γ, fv(M), m)       ⊢ thunk_m M : U_m^ρ C ▷ u
    [fold]   V : U_lin^∅ (F (A ⊕ (int ⊗ strm^ρ A)) &^{ρ,∅} F 1) ▷ u
                                                        ⊢ fold V : strm^ρ A ▷ u

Computations:

    [ret]     V : A ▷ u                                 ⊢ ret V : F A ! ∅ ▷ u
    [to]      M : F A ! ρ₁ ▷ u₁    Γ, x:A ⊢ N : C ! ρ₂ ▷ u₂    check x
              capture(Γ, fv(N) ∖ x, bound(ρ₁).req)
                                                        ⊢ M to x. N : C ! ρ₁ ∪ ρ₂ ▷ u₁ + u₂
    [lam]     Γ, x:A ⊢ M : C ! ρ ▷ u    check x          ⊢ λx:A. M : A ⇒^ρ C ! ∅ ▷ u
    [app]     M : A ⇒^ρ C ! ρ₀ ▷ u₁    V : A ▷ u₂    mode(A) ≥ bound(ρ₀).req
                                                        ⊢ M V : C ! ρ₀ ∪ ρ ▷ u₁ + u₂
    [force]   V : U_m^ρ C ▷ u                           ⊢ force V : C ! ρ ▷ u
    [rcd]     M : C₁ ! ρ₁ ▷ u₁    N : C₂ ! ρ₂ ▷ u₂       ⊢ ⟨M, N⟩ : C₁ &^{ρ₁,ρ₂} C₂ ! ∅ ▷ u₁ ⊔ u₂
    [prj]     M : C₁ &^{ρ₁,ρ₂} C₂ ! ρ₀ ▷ u               ⊢ prjᵢ M : Cᵢ ! ρ₀ ∪ ρᵢ ▷ u
    [split]   V : A ⊗ B ▷ u₁    Γ, x:A, y:B ⊢ M : C ! ρ ▷ u₂    check x, y
                                                        ⊢ split V as (x,y). M : C ! ρ ▷ u₁ + u₂
    [case]    V : A ⊕ B ▷ u₀    Γ, x:A ⊢ M : C ! ρ₁ ▷ u₁    Γ, y:B ⊢ N : C ! ρ₂ ▷ u₂    check x, y
                                                        ⊢ case … : C ! ρ₁ ∪ ρ₂ ▷ u₀ + (u₁ ⊔ u₂)
    [if]      V : bool ▷ u₀    M : C ! ρ₁ ▷ u₁    N : C ! ρ₂ ▷ u₂
                                                        ⊢ if V then M else N : C ! ρ₁ ∪ ρ₂ ▷ u₀ + (u₁ ⊔ u₂)
    [absurd]  V : 0 ▷ u                                 ⊢ absurd V : C ! ∅ ▷ u
    [prim]    V, W : int ▷ u₁, u₂                       ⊢ prim p V W : F G_p ! ∅ ▷ u₁ + u₂
    [emit]    V : int ▷ u                               ⊢ emit V : F 1 ! ∅ ▷ u
    [punch]   V : tkt ▷ u                               ⊢ punch V : F 1 ! ∅ ▷ u
    [op]      x : E^b ∈ Ψ    o : A_o ↠^{q_o} B_o ∈ E    V : A_o ▷ u₁
              Γ, y:B_o ⊢ M : C ! ρ ▷ u₂    check y    capture(Γ, fv(M) ∖ y, b.req)
                                                        ⊢ op x.o(V; y. M) : C ! {x} ∪ ρ ▷ u₁ + u₂
    [ab]      x : E^b ∈ Ψ    a : A_a ↠ 0 ∈ E    V : A_a ▷ u
                                                        ⊢ ab x.a(V) : C ! {x} ▷ u
    [handle]  Ψ, x:E^{b_H}; Γ ⊢ M : F A ! ρ_M ▷ u_M    ρ = ρ_M ∖ {x}    b_H = hb(H, ρ_h)
              Clauses(H; A; ρ ∪ ρ_h; C) = (u_once, u_many, ends)
              x ∉ atoms(ρ) ∪ atoms(ρ_h) ∪ atoms(C) ∪ atoms(A)
              capture(Γ, fv(H), bound(ρ).req ⊔ ⨆_{o resuming} q_o)
                                                        ⊢ handle x : E with H in M : C ! ρ ∪ ρ_h
                                                          ▷ u_M + u_once' + u_many
    [handleAt] x : E^{b_x} ∈ Ψ,  E ≠ Res    hb(H, ρ_h) ⊑ b_x    M : F A ! ρ_M ▷ u_M    ρ = ρ_M ∖ {x}
              the other premises of [handle], without binding x
                                                        ⊢ handleAt x with H in M : C ! ρ ∪ ρ_h ▷ (as [handle])
    [nu]      Ψ, x:E^b ⊢ M : C ! ρ ▷ u    x ∉ atoms(ρ) ∪ atoms(C)
                                                        ⊢ ν x : E^b. M : C ! ρ ▷ u
    [ieq]     x : E^b, y : E'^{b'} ∈ Ψ                  ⊢ ieq x y : F bool ! ∅ ▷ ∅
    [ilam]    Ψ, x:E^b ⊢ M : C ! ρ ▷ u                  ⊢ Λx:E^b. M : Π^ρ(x:E^b). C ! ∅ ▷ u
    [iapp]    M : Π^ρ(x:E^b). C ! ρ₀ ▷ u    y : E^{b'} ∈ Ψ    b' ⊑ b
                                                        ⊢ M y : C[y/x] ! ρ₀ ∪ ρ[y/x] ▷ u
    [rlam]    Θ, r ≤ b ⊢ M : C ! ρ ▷ u                  ⊢ Λr ≤ b. M : ∀^ρ(r ≤ b). C ! ∅ ▷ u
    [rapp]    M : ∀^ρ(r ≤ b). C ! ρ₀ ▷ u    bound(σ) ⊑ b
                                                        ⊢ M [σ] : C[σ/r] ! ρ₀ ∪ ρ[σ/r] ▷ u
    [newcap]  E has no abortive operation, every q_o ∈ {lin, aff}
              ·; ·; p:A_o, s:S ⊢ N_o : F ((B_o ⊗ S) ⊕ (E_o ⊗ S)) ! ∅  for every o   (D1.9)
              V : S ▷ u                                 ⊢ newcap_E S co V : F (cap_E S) ! ∅ ▷ u
    [getcap]  V : cap_E S ▷ u                           ⊢ getcap V : F S ! ∅ ▷ u
    [lend]    V : cap_E S ▷ u₁    Ψ, x:E^{rbnd(E)}; Γ ⊢ M : F A ! ρ_M ▷ u₂    ρ = ρ_M ∖ {x}
              x ∉ atoms(A)    bound(ρ).req = lin
                                                        ⊢ lend V as x in M : F (cap_E S ⊗ (A ⊕ int)) ! ρ ▷ u₁ + u₂
    [using]   Ψ, x:Res^{none}; Γ ⊢ M : F A ! ρ_M ▷ u    ρ = ρ_M ∖ {x}
              x ∉ atoms(A)    aff ≥ bound(ρ).req
                                                        ⊢ using x = acquire ℓ in M : F A ! ρ ▷ u
    [unfold]  V : strm^ρ A ▷ u                          ⊢ unfold V : F (A ⊕ (int ⊗ strm^ρ A)) &^{ρ,∅} F 1 ! ∅ ▷ u
    [bfix]    x : E^b ∈ Ψ    a : A_a ↠ 0 ∈ E    V : A_a ▷ u₁    x ∈ ρ
              Γ, f : U_unr^ρ C ⊢ M : C ! ρ' ▷ u₂    ρ' ⊆ ρ    check f    capture(Γ, fv(M) ∖ f, unr)
                                                        ⊢ bfix_n x.a(V)(f. M) : C ! ρ ▷ u₁ + u₂
    [sub]     M : C ! ρ ▷ u    C ≤ C'    ρ ⊆ ρ'         ⊢ M : C' ! ρ' ▷ u

**Clauses.** `Clauses(H; A; ρ'; C) = (u_once, u_many, ends)` is defined, and its premises hold,
when ([PA `clauses`]):

- `Γ, z:A ⊢ N_ret : C ! ρ_r ▷ u_r`, `ρ_r ⊆ ρ'`, check `z`;
- for each abortive `a`: `Γ, p:A_a ⊢ N_a : C ! ρ_a ▷ u_a`, `ρ_a ⊆ ρ'`, check `p`;
- for each resuming `o`: `Γ, p:A_o, k:K(q_o, B_o, ρ', C) ⊢ N_o : C ! ρ_o ▷ u_o`, `ρ_o ⊆ ρ'`,
  check `p`, `k`, and `capture(Γ, fv(N_o) ∖ {p, k}, unr)`;
- `u_once = u_r ⊔ ⨆_a u_a` (alternatives: one of them ends each run of the handler frame);
  `u_many = Σ_o ω·u_o` (each resuming clause runs once per operation);
  `u_once' = ω·u_once` if some `C ∈ q_o` (a resumed-twice continuation reinstalls the handler
  frame twice, so the return clause may run twice), else `u_once ⊔ [0,0]` if some `W ∈ q_o` (a
  dropped continuation means the return clause may never run), else `u_once`.

The capture premise of [handle] has two parts. `bound(ρ).req` is phase A's: the handler frame
sits in every continuation *forwarded* through it. `⨆_o q_o`, over the handler's own resuming
operations, is new: the frame also sits in every continuation of those operations (the handler is
deep), so its clauses' captures must admit what those continuations undergo. The handler's own
abortive operations do not contribute: they capture no continuation, and the frame is replaced
by the clause. Phase A checks only the first, and the `ends` hull
for weakening; it accepts a return clause that owns a capability under an operation whose
continuation is resumed twice, and that program consumes the capability twice (§10.3,
machine-checked).

## 2.5 Changes from phase A, rule by rule

| rule | phase A | here | reason |
|---|---|---|---|
| [lend] | `lend c x M`, `c` not consumed, `c ∉ fv(M)`, T1 | consumes `V`, answers the capability back, `bound(ρ).req = lin`, no T1 | §10.1, Theorem T9.1 |
| [using] | binds `x : resD` (a value) | binds `x : Res^{none}` (an instance) | §10.2 |
| [thunk] | no lent place, no `resD` captured | independence only | both side conditions are now carried by rows: a lent instance or a resource handle is an instance, and `x ∉ atoms(A)` at its binder confines it |
| [handle] | clause captures checked at the forwarded row only | also at the handler's own bound | §10.3 |
| [op], [handle] | `κ` the resume entry only | `κ : K(q, B, ρ', C)`, with `cancel` when `W ∈ q` | §8.1 |
| [newcap] | co-operations `A × S → F (B × S)` | `F ((B ⊗ S) ⊕ (E_o ⊗ S))`, `aff` operations admitted | §8.2 |
| [bfix] | `fix` (general recursion) | bounded | §9.4 |
| [ab] | `raise` as `op` at answer `void` | a separate former | phase B's `Cmp.ab`; the clause receives no continuation |

**Lemma L2.3 (weakening, renaming, instance substitution).** If `Ψ; Θ; Γ ⊢ M : C ! ρ ▷ u`, then

1. `Ψ'; Θ'; Γ' ⊢ M : C ! ρ ▷ u` for `Ψ ⊆ Ψ'`, `Θ ⊆ Θ'`, `Γ ⊆ Γ'` (`u` extended by `[0,0]`);
2. for `y : E^{b'} ∈ Ψ` with `b' ⊑ b` and `x : E^b ∈ Ψ`, `Ψ ∖ x; Θ; Γ ⊢ M[y/x] : C[y/x] ! ρ[y/x] ▷ u`;
3. for `bound(σ) ⊑ b`, `Ψ; Θ ∖ r; Γ ⊢ M : C[σ/r] ! ρ[σ/r] ▷ u`.

*Proof.* By induction on the derivation. (1) No premise reads an unused variable. (2) and (3):
every bound check is preserved because `bound` is monotone in each atom's bound (L2.2.3), and
`hb(H, ρ_h)[σ/r] ⊑ b_x` follows from `bound(σ) ⊑ b` by the same monotonicity. Independence
premises do not mention instances or rows. ∎

*Note for the mechanisation.* With de Bruijn instance variables, (2) is phase B's `Cmp.ren` at
the instance renaming plus its semantics `Cmp.den_ren` [PB `Rename.lean`]; the moded premises
are a separate predicate over phase B's terms (phase B's `Syntax.lean` header names it `Moded`;
it is not written yet).
