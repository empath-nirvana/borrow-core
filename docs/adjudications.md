# Adjudications

Where the mechanisation reads [CONF] (Wagner, Gierczak, Marshall, Li & Ahmed, *From
Linearity to Borrowing*, PACMPL 9:OOPSLA2:415, 2025) and [TR] (its supplement, which prints
the complete definitions and proofs) in a way that needs an argument: the two documents
differ, a printed item admits more than one reading, or the literal reading of a printed
item does not support a step a printed proof takes.  Each entry gives the printed form (with
page), the sentences that ground the reading, the reading and the Lean declarations that
carry it, and what the literal reading admits, with the declaration that measures it where
there is one.

Comments in the Lean files cite entries by number (`docs/adjudications.md` §12.42, or §12.42
alone).  The numbers are stable and not consecutive.

* §12.N — readings of the printed text.  §12.67–§12.73 are the repairs behind the
  headline results (`Fig16.LogRel.Typed.fundamentalProperty`, `Fig16.LogRel.Typed.adequacy`).
* §C.25, §C.26 — the judgment forms' boxes on [TR] p. 2.
* G1–G8, F1, L3–L5, W2 — conventions: representation choices, not claims about the
  paper.
* C14, D3, D6, D8, D10 — recorded differences between a Lean statement and the printed
  one.
* §A.1, §A.2a — [CONF] Theorem 3.2 and Corollary 3.3, which neither document proves.

Row numbers ("definition row 5.30") are those of `Paper/INDEX.md`, *Definitions*; lemma
numbers are [TR]'s.  Page references are to the physical pages of [TR] ("p. 5") and to
[CONF]'s journal pages ("p. 415:22").

## Part I — Readings of the printed text

### §12.1 Evaluation order

[CONF] Fig. 1 writes application as `e₂ e₁` and gives no evaluation contexts (p. 415:3: "a
standard call-by-value variant of the untyped lambda calculus").  [TR] §3, p. 3 fixes the
order:

```
Kont ∋ K ::= [] | (K, e) | (v, K) | let (x, y) = K in e
             | case K {inj₁ x.e₁ | inj₂ y.e₂} | e K | K v
```

`e K` has the hole in the argument position under an arbitrary function expression; `K v`
has it in the function position with a value argument.  So application evaluates the
argument first, and with the β-rule `(λx.e) v ↦ e[v/x]` the function stands on the left.
Pairs evaluate left to right; `let` and `case` reduce the scrutinee first.  The statics
agree: `⊸E` numbers the argument's context `Γ₁` and the function's `Γ₂`, and `⊗I` numbers
the left component's `Γ₁`, so subscript order is evaluation order.

### §12.2 `⊸E`'s conclusion and the grammar

[TR] p. 2 prints `⊸E`'s conclusion as `Δ; Γ₁, Γ₂ ⊢ e₁ e₂ : T₂`, with `e₁ : T₁` the argument
and `e₂ : T₁ ⊸ T₂` the function.  Under the grammar's `e₂ e₁` and the β-rule (§12.1) the
function stands on the left, so the term is read as `e₂ e₁`.  `BoCa.Derives.lolliE`
concludes `Derives Δ Γ (.app f a) T₂` from `Derives Δ Γ₁ a T₁` and
`Derives Δ Γ₂ f (.lolli T₁ T₂)`.

### §12.3 The carrier tuple's relation: [TR] labels it `⊑`, [CONF] labels it `⊏`

Both glyphs occur in the rules: `⊑` in `⊑Imm`, `⊑Mut` and [CONF] Fig. 7's `[b]T ⊐ a`; `⊏` in
`∀'a ⊏ @b`, `∀E` and `Δ ⊢ T ⊐ @a`.  The carrier defines one of them:

- [TR] p. 4: `Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)`, the relation glyph under-barred.
- [CONF] Fig. 11 (p. 415:12): `Life ≜ (ℕ, ⊔̇ ≜ min, ⊓̇ ≜ max, ⊤ ≜ 0, ⊏̇ ≜ >)`, no under-bar.
- [TR] p. 3 defines only `Δ ⊨ @a ⊏ @b ≜ ∀δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ`; [CONF] Fig. 11 adds "(and
  similarly for `⊑̇`)".

The reading follows [CONF]: `⊏ ≜ >`, and `⊑` is its reflexive closure `≥`.  [CONF] p. 415:12
calls the structure "a semi-bounded lattice of natural numbers"; with [TR]'s labelling `⊤ = 0`
is not `⊑`-greatest and `⊔ = min` is not a join, with [CONF]'s every lattice law holds.  Both
documents print the two glyphs distinctly within one block ([TR] p. 2, p. 6).  The carrier
is `ℕᵒᵈ` (`BoCa.Fig16.Life`), so `⊤`, `⊔`, `⊓` are Mathlib's and are `0`, `min`, `max` on
`ℕ`, as printed.  The reflexive instance of `⊑Imm`/`⊑Mut` is the identity coercion, which no
printed program needs.

### §12.4 `⊑Imm` / `⊑Mut` conclusions: the two documents differ

[TR] p. 2 prints both conclusions at `@b`, which makes the rules identities.  [CONF] Figs.
7/9 print `@a`, as do [TR]'s own Lemmas 6.167/6.168.  `BoCa.Derives.immSub` and
`BoCa.Derives.mutSub` conclude at `.imm a T` / `.mut a T` from a premise at `b` with
`Δ ⊨ @a ⊑ @b`.

### §12.5 `□` in `[l]I` / `[l]E`: the two documents differ

`□e` appears in [TR]'s `[l]I` and `[l]E`; it is not in the `Expr` grammar, has no reduction
rule, and is absent from Lemmas 6.163/6.164.  [CONF] Figs. 6/7 print the rules without it.
`□` is read as a typesetting marker and the rules are not syntax-directed
(`BoCa.Derives.boxIctx`, `BoCa.Derives.boxE`).

### §12.6 `Δ ⊨ Γ ⊐ @a`: the context lift, and `⊢` beside `⊨`

[TR] does not define the lift `Γ ⊐ @a`.  It is read as `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a`, as
[CONF] Figs. 6/7 spell it.  Lemma 6.163's statement writes the premise with `⊨` and its proof
with `⊢`; both are read as this premise.

### §12.7 The `@aδ` clause guards: the two documents differ

[TR] p. 3 prints two clauses with the same guard `@a = @b₁ ⊔ @b₂`, mapping to `⊓` and `⊔`.
[CONF] Fig. 11's homomorphic version (`⊔ ↦ ⊔̇`, `⊓ ↦ ⊓̇`) is used.

### §12.8 `Life`'s first alternative: the two documents differ

[TR] p. 1 prints the first alternative of `Life` as a bare `'`, under
`LifeVar ∋ 'a, 'b, …`; [CONF] Fig. 7 (p. 415:8) prints `'a`.  [CONF] is followed; [TR]'s own
`@aδ` has a case for `@a = 'a`, and the bare `'` reads as the sort's sigil.

### §12.9 The `withbor` (Ref → Mut) side condition and its lifetime `@b`

Printed as `Δ ⊢ T₁ ⊐ 'b` ([CONF] Fig. 9) and `Δ ⊢ T₁ ⊐ @b` ([TR] p. 3); the lifetime does not
occur in the conclusion.  Lemma 6.173's proof uses it to obtain `𝒱⟦T₁⟧δ ⊨ [@bδ] 𝒱⟦T₁⟧δ`.
[CONF] p. 415:10: "the payload type for a mutable borrow is required to have an unambiguous
lifetime bound".  The condition is read existentially: `BoCa.Derives.withbor2Ax` carries
`hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b`.

The `Δ.Defines b` conjunct is [TR] p. 2's `Δ ⊢ T ⊐ @a   Presumes ⊨ Δ and Δ ⊨ @a`, which
`BoCa.Outlives` does not carry (§C.25); since `@b` is bound by the side condition itself, the
existential must carry it.  It restricts nothing: a derivation of `Outlives Δ T₁ b` through an
`imm`, `mut` or `box` rule has `Δ.EntailsLt b c`, which contains `Δ.Defines b`; one through
only the `1`, `⊗`, `⊕` and `Ref` rules also gives `Outlives Δ T₁ ⊤`, and `Δ.Defines ⊤` holds.
The side condition rejects `T₁ ⊸ T₂`, `∀'a ⊏ @b. T` and `Unk`, which have no `⊐` rule.

### §12.10 The `Mut` clause of the `Imm` metafunction

[TR] p. 3 lists eight clauses; [CONF] Fig. 9 prints a ninth, `Imm 'b (Mut a T) ≜ Imm 'b T`,
and p. 415:11 discusses it.  Without it `withload` cannot be used on a payload containing a
mutable borrow.  It is a clause of `BoCa.Ty.immReborrow`, the right-hand side the type
constructor (§12.28).  The image remains the fixpoint set and the metafunction remains
idempotent.

### §12.11 The `Imm` metafunction and `Unk`

`Imm 'b (Ref Unk) = Imm 'b Unk` needs a clause for `Unk`, and neither document gives one.
`BoCa.Ty.immReborrow` adds `Imm 'b Unk ≜ Unk`.  `𝒱⟦Unk⟧δ(v) ≜ emp` ([TR] p. 4), so an
inhabitant owns no resource; `forget` is the only operation on `Unk`; the alternative `1`
would hold only of `()`.  `Unk` is a fixpoint, keeping the metafunction idempotent.

### §12.14 Lifetime application: `e[]` and `e ()`

[TR]'s `∀E` concludes `Δ; Γ ⊢ e[] : T[@a/'a]`; `e[]` is not in the grammar and has no
reduction rule.  [CONF] Fig. 7 concludes `Δ; Γ ⊢ e () : T[a/'a]` and states `Λ. e ≜ λ_. e`,
and [TR] p. 4's `𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())` and the compatibility proofs
(`v_f () ℓ`) agree.  `BoCa.Derives.allE` concludes at `.app e (.val .unit)`.

### §12.15 `⊓Δ`

`⊓Δ` bounds every `withbor`/`withload` type and neither document defines it.  [CONF]
p. 415:8: "a fresh lifetime `'a`, which is shorter than all existing lifetimes in `Δ`".  It
occurs only in the axiom table and the statements of 6.172–6.175; the proofs convert it to
the freshness quantifier ([TR] l. 2523):

    𝒱⟦∀'a ⊏ ⊓Δ. Imm a T ⊸ [a]T⟧(v) ⊧ ⋔α. ℓ ↦I 𝒱⟦T⟧(v) ─⋆ wp (v () ℓ) {v. [α] 𝒱⟦T⟧(v)}

with existence by [TR] l. 1285: "Such an α always exists because for any lifetime, the set of
lifetimes shorter than it is infinite."

`⊓Δ` ranges over `dom(Δ)`: `⟦Δ⟧` requires `δ('a) ⊏ Δ('a)δ`, so being below every variable
puts a lifetime below every bound, and not conversely.  It is the right fold of binary meets
over `dom(Δ)` with `⊓∅ = ⊤` (`BoCa.Lifetime.meetOfDomL`, `BoCa.Lifetime.LifeCtx.meetOfDom`);
`⊤ = 0` is the empty `max`.

### §12.16 `⊕I`'s conclusion `i e`

[TR] p. 2 prints `Δ; Γ ⊢ i e : T₁ ⊕ T₂`; the grammar has `inj₁ e | inj₂ e`.  Read as
`inj_i e`.

### §12.17 The `[b]T ⊐ a` rule: [CONF] and [TR] differ

- [CONF] Fig. 7: premise `(Δ ⊨ b ⊒ a) ∨ (Δ ⊢ T ⊐ a)`, the first disjunct non-strict.
- [TR] p. 2: premise `Δ ⊨ @b ⊐ @a`, strict, no disjunction.

[TR]'s rule is the one Lemma 6.60 is proved for; the `box` constructor of `BoCa.Outlives`
has premise `Δ.EntailsLt a b`.  It loses derivations [CONF] admits, such as `[b](1) ⊐ a` for
a short `b`.  ([CONF] Fig. 6 has `[]T ⊐ Imm` as an axiom; the indexed judgment has none.)

### §12.19 The axiom table and `Γ`

[TR] p. 3 writes `Δ ⊢ op : T` with no term context; p. 2's `alloc`/`free` rules write
`Δ; • ⊢ ...`; the compatibility lemmas use both (6.165: `Δ; ∅ ⊨ alloc : ...`; 6.172:
`Δ ⊨ withbor : ...`).  The table is read at the empty context: each axiom constructor (e.g.
`BoCa.Derives.withbor2Ax`) takes a context whose slots are all dead (`BoCa.Ctx.Dead`).

### §12.20 The sugar bodies of [TR] p. 4 and of [CONF]: `swap`, `withload`, `withbor`

Both documents print the same types ([TR] p. 3; [CONF] Figs. 3b, 7, 9, 14, 15).  For `swap`,
`withload` and `withbor` the bodies differ, and [CONF]'s has the ascribed type in each case;
`BoCa.swap`, `BoCa.withload`, `BoCa.withbor` follow [CONF].

- `swap`: [TR] p. 4 prints `λx.λy. let z = load x; store x y; (x, y)`, returning the new
  payload where the type `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` returns the old.  [CONF] Fig. 3b
  (p. 415:4): `swap ≜ λx λy₂. let y₁ = load x; store x y₂; (x, y₁)`.  [TR]'s proof of 6.169
  (p. 44) evaluates `let z = load v₁; store v₁ v₂; (v₁, z)`, [CONF]'s body; at it 6.169 is
  `Fig16.LogRel.swap_compat`, as printed.
- `withload`: [TR] p. 4 prints `λx.λf. (x, f (load x))`, a pair, where the type returns
  `T₂`.  [CONF] Fig. 14 (p. 415:16): `withload ≜ λx λf. f () (load x)`; [TR]'s proof of 6.175
  (p. 47) unfolds to `λf. f () (load v)`.
- `withbor`: [TR] p. 4 and [CONF] p. 415:6 print `λx.λf. (x, f x)`.  The §2.3 type makes `f`
  a `∀`-thunk, forced with `()` before it receives the borrow; read literally,
  `withbor x (Λ.λb. e)` reduces to `(x, λb. e)`.  [CONF] Fig. 15 (p. 415:17):
  `withbor ≜ λxλf. (x, f () x)`; [TR]'s proof of 6.172 writes `wp (v () ℓ)` (p. 46).
  (p. 415:6's body has its own §2.2 type, which has no lifetimes.)
- `withswap`: the two documents agree, and the term has its type.
- Single-binder `let z = e; e′`, which p. 1's grammar does not produce, is `(λz. e′) e`
  (`BoCa.elet`), as [TR]'s proof of 6.169 unfolds it.

### §12.21 Two names for the same operation

[CONF] `dupl`, [TR] `copy`, same type; `BoCa.copy`.

### §12.24 Fig. 5's borrower and Fig. 6's `[]I`

The borrower `λf'. avg f'` of [CONF] Fig. 5 has type `Imm File ⊸ []ℕ`, so `avg f'` must be
typed `[]ℕ` with `f' : Imm File` in context.  Only `[]I` concludes a `[]`, and its premise
scans the context and finds `Imm File`, for which Fig. 6 has no rule.  Read literally, `[]I`
does not type `avg f'` in the form Fig. 5 writes; a let-normal βη-variant, with the
borrow-consuming work in a scrutinee and the tail boxed, is typed by the printed rules.

In the lifetime-indexed system ([CONF] Fig. 7, [TR] p. 2), `Δ ⊢ Imm @b T ⊐ @a` holds when
`Δ ⊨ @b ⊐ @a`, so `BoCa.Derives.boxIctx` boxes at any lifetime strictly shorter than the
borrows in scope (`login`, [CONF] §2.3).  It does not box at the borrower's own lifetime:
that needs `Δ ⊨ 'a ⊐ 'a`, false since `⊐` is strict (§12.3).  Making `⊐` reflexive would
admit [CONF] p. 415:6's identity-borrower use-after-free.  §12.26 records the rule that would
type the printed form.

### §12.26 A result-directed `[]I`: sound in the model, and not among the printed rules

```
 Δ ⊢ T ⊐ @a
────────────────────────────────────
 Δ; Γ ⊢ e : T  ⟹  Δ; Γ ⊢ e : [@a] T
```

never inspects `Γ`:

| program | borrower's result | premise | verdict |
| --- | --- | --- | --- |
| [CONF] Fig. 5 `avg` | `ℕ = 1 ⊕ 1` | the `1` and `⊕` rules | accept |
| [CONF] p. 415:6, identity borrower | `Imm 'a T₁` | `Δ ⊨ 'a ⊐ 'a` | reject |
| [CONF] p. 415:6, closure capturing the borrow | `T₁ ⊸ T₂` | no rule for `⊸` | reject |
| [CONF] §2.3 `login` | `Imm ('a ⊓ 'b) File` at `'c` | `'c ⊏ 'a` and `'c ⊏ 'b` | accept |

It is not among the statics: [CONF] Figs. 6, 7 and [TR] p. 2 print `[]I` with the context
premise only, and `Derives` has that rule alone (`BoCa.Derives.boxIctx`).  It is sound:
Lemma 6.60 with `[α]P(ρ) ≜ P(ρ) ∧ @ρ ⊐ α` gives `𝒱⟦T⟧δ ⊨ [@aδ] 𝒱⟦T⟧δ`, a step [TR] takes in
6.173 and 6.174.  The two rules are incomparable: at `Δ; • ⊢ λx.x : T ⊸ T` the
context-directed rule boxes and `Δ ⊢ T ⊸ T ⊐ @a` has no rule.

### §12.27 `Λ.e ≜ λ_.e` makes `λx. ()` well typed

With `Λ.e` read as `λ_.e` (§12.14), `∀I`'s premise has no binder in `Γ` to leave unconsumed,
so `λx. ()` — the body of `forget` ([TR] p. 4; `BoCa.forget`) — is typed at `∀'a ⊏ @b. 1`.
Linearity is a property of `⊸`: `λx. ()` has no `⊸` type, in particular not the
`Imm @a T ⊸ 1` the axioms give `forget`.

### §12.28 The `Imm` metafunction and the `Imm` constructor: told apart by an underline

Both documents underline the metafunction and not the constructor, side by side within
clauses:

```
Imm 'b (Ref T)     ≜  Imm 'b T        ← LHS underlined, RHS not              (5)
Imm 'b ([@a] T)    ≜  Imm 'b T        ← both underlined                      (7)
Imm 'b (Imm @a T)  ≜  Imm @a T        ← LHS underlined, RHS not              (6)
Imm 'b (Mut @a T)  ≜  Imm 'b T        ← LHS underlined, RHS not ([CONF] Fig. 9) (9)
```

([TR] p. 3; [CONF] Figs. 8, 9, p. 415:10, on the rendered pages; the text layer drops the
underline.)  Under a recursive reading `Imm 'b (Ref 1) = 1` and clause (5) forgets the
borrow; under the printed reading it is `Imm 'b 1`, which keeps [CONF] §2.4's double-free
program ill-typed while leaving its nested borrow usable.  [CONF] p. 415:11 on (9): "the
lifetime on this reborrow is the fresh lifetime `'b` introduced for the load, and not the
original lifetime `a`" — the right-hand side is a borrow type.  The metafunction is
`BoCa.Ty.immReborrow`, distinct from the constructor.  In [TR] p. 3's axiom list the
underline appears once, on `withload`'s `Imm 'b T₁`.

### §12.32 `Δ ⊢ Mut @a T`: the printed rule and the premise Lemma 6.174 reads off it

[TR] p. 2 prints

```
 Δ ⊢ T    Δ ⊨ @a
 ───────────────
  Δ ⊢ Mut @a T
```

and [TR] l. 2624, in 6.174's proof (p. 47):

> "Have `Δ ⊢ T₁ ⊐ @a` by well-formedness of the type `Mut @a T₁`, hence
> `𝒱⟦T₁⟧δ ⊧ [α] 𝒱⟦T₁⟧δ` by theorem 6.60"

The two printed premises do not give `Δ ⊢ T₁ ⊐ @a`; [CONF] p. 415:10's "the payload type for
a mutable borrow is required to have an unambiguous lifetime bound" supports the proof.
`BoCa.WfTy.mut` has the two printed premises.  6.174 (`Fig16.LogRel.withbor3_compat`) reads
`𝒱⟦T₁⟧δ ⊨ [β] 𝒱⟦T₁⟧δ` off the `mut` cell in hand, whose invariant is supported at the cell's
lifetime (`Fig16.BoLo.ptoMut`, `Fig16.LogRel.vDen_mut_supported`); the rest follows p. 47.

### §12.33 `fin` on `Res`: the two documents differ

[TR] p. 4, row 7: `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell`; row 2, `Res_α ≜ Loc ⇀ Cell_α`, is bare.  [CONF]
Fig. 16 (p. 415:20) prints both bare, and "finite" does not occur in [CONF].

`Res` is finite, as [TR] prints it:

1. [CONF] prints no `wp-alloc` and no equation for `@ρ` (it glosses `@ρ` in prose, p. 415:23),
   so the question does not arise on its pages.
2. `@ρ ≜ ⨅_{ψ ∈ cod(ρ)} @ψ` ([TR] p. 5) with `⊓ ≜ max` has no value on an unbounded codomain,
   and `[α]P(ρ) ≜ P(ρ) ∧ @ρ ⊐ α` is defined through it.
3. [TR] 6.141 (`wp-alloc`, p. 37) has no hypotheses and its proof reads "Choose an `ℓ` such
   that `ℓ ∉ ρ_f • ρ`", available when `ρ_f • ρ` misses a location.

Row 2 inherits row 7's mark: every operation from `▶◀` on is defined on `Res`, and `Mut_α`'s
witness is a `Res_β` composed by the walks, so a `Res_β` must be a `Res` (D10, G1;
`[variant: …]` at `Fig16.Res`).  That `Loc` is infinite enters as a hypothesis, through
`Fig16.PMap.exists_fresh`.

### §12.34 [TR] Definition 6.3, last sub-bullet: `ρ′` read as `ρ″`

[TR] p. 17:

```
Definition 6.3.  ρ ⊟ ρ′ ≜ ρ|own,mut ● ρ″  where
  • ρ′|own,mut = ∅
  • ρ″ ≤ ρ|imm
  • if ℓ ∈ dom(ρ|imm) ∖ dom(ρ′) then ℓ ∈ dom(ρ″)
  • if ℓ ∈ dom(ρ|imm) ∩ dom(ρ′) and ρ(ℓ) = imm(ᾱ, ρᵢ, v) and ρ′(ℓ) = imm(β̄, ρᵢ, v) then
      – if ᾱ ∖ β̄ = ∅, then ℓ ∉ ρ″,
      – if ᾱ ∖ β̄ ≠ ∅, then ρ′(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)
```

The last line carries a single prime.  It is read as `ρ″(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)`.

Literally, the bullet's hypothesis fixes `ρ′(ℓ) = imm(β̄, ρᵢ, v)`, and `β̄` and `ᾱ ∖ β̄` are
disjoint and nonempty, so the second sub-case cannot be met and `ρ ⊟ ρ′` is defined only
where `ᾱ ⊆ β̄` at every shared `imm` location.  [TR] supports `ρ″` twice: Lemma 6.52's proof
(pp. 17–18) writes `ρ⁺ = (ρ⁺ ⊟ ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)) ● ℓ ↦ imm({α}, ρ_ℓ, v_ℓ)` where
`⦇ρ⁺⦈(ℓ) = imm(β̄⁺, ρ_ℓ, v_ℓ)` with `β̄⁺` not required to be `{α}`; and the prose below the
definition: "'without' means removing the lifetimes of borrows from `ρ′`, but keeping the
lifetimes only in `ρ`".

`BoCa.Fig16.ResU.SubClause`/`BoCa.Fig16.ResU.Sub` carry the `ρ″` reading (`[variant: …]`);
`ResU.SubClauseL`/`ResU.SubL` are the bullet as printed.  Downstream uses
`BoCa.Fig16.ResU.SubKeep` (§12.58).  [TR] §6 writes `imm` cells as `(lifetimes, witness,
value)` where p. 5 writes `(lifetimes, value, witness)`; the metavariables name the
positions, and p. 5's order is used.  `≤` is [CONF]'s `●`-extension order (§12.37).

### §12.35 `⋈` is the domain of `○`

[TR] p. 5 ([CONF] prints no `⋈`):

```
ψ₁ ⋈ ψ₂ ≜ ψ₁ ▶◀ ψ₂ ∨ ∃ i, ᾱ, β, v, ρ, P̂. {ψ₁, ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}
```

Literally the second disjunct makes a two-element set an element of a three-element set, and
binds an unused `i`.  The reading is `ψ₁ ⋈ ψ₂ ⟺ ψ₁ ○ ψ₂ is defined`, as `▶◀` is the domain of
`●` (Lemma 6.9).  Reading `∈` as `⊆` with the binders shared by both cells would make two
`mut` cells at different lifetimes or invariants never `⋈`, so `○`'s clause (3),
`mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`, would only ever return `mut(α ⊓ α, v, ρ, P̂ ∧ P̂)`; letting `β` and
`P̂` vary per cell gives exactly the pairs `○` composes, which is `dom(○)`.

[TR] Lemma 6.3's `○` case (p. 7): "if it is mut then we use associativity of `⊓` and `∧`" —
clause (3) at three lifetimes and three invariants.  Lemma 6.1's `⋈` case, "immediate since
sets are unordered", reads `{ψ₁,ψ₂}` as a set; Lemma 6.37 uses `ρ₁ ⋈ ρ₂` as "`ρ₁ ○ ρ₂` is
defined".  `BoCa.Fig16.CellU.CompatR` is `dom(○)` (`[variant: …]`), and
`BoCa.Fig16.ResU.CompatR`/`BoCa.Fig16.ResU.CompR` instantiate p. 5's schemas at it.

### §12.36 The walks' iterated comprehension is a family indexed by locations

[TR] p. 5:

```
ex(ρ)_◐ ≜ ρ|own ◐ ρ|mut ◐ ⨀_◐ {ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}
ag(ρ)_◐ ≜ ρ|imm ○ ◯{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}
                 ○ ◯{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}
```

[CONF] p. 415:22, Fig. 18a:

```
E⦇ρ⦈_◐ ≜ … ◐ ⨀_{ρ′ ∈ cod(ρ|mut)} E⦇ρ′⦈_•
A⦇ρ⦈   ≜ … ○ ◯_{ρ′ ∈ cod(ρ|mut)} A⦇ρ′⦈ ○ ◯_{ρ′ ∈ cod(ρ|imm)} E⦇ρ′⦈_○ ○ A⦇ρ′⦈
```

[TR]'s existential over locations reads as a family indexed by locations; [CONF]'s `cod`
as a set of values, in which two locations with equal cells contribute once.  [TR] is
followed: one component per `ℓ ∈ dom(ρ|mut)` (resp. `dom(ρ|imm)`).

Lemma 6.18 (p. 8) — `ρ₁ ▸◂ ρ₂` implies `ex(ρ₁ ● ρ₂)_●` and `ex(ρ₁)_● ● ex(ρ₂)_●` are
Kleene-equal — cannot be reconciled with the set reading at pairwise-distinct `ℓ₁, ℓ₂, ℓ₃`:

```
σ  ≜ ℓ₃ ↦ own(w)          ρ₁ ≜ ℓ₁ ↦ mut(α, v, σ, P̂)          ρ₂ ≜ ℓ₂ ↦ mut(α, v, σ, P̂)
```

On the set reading the left side's family is `{ex(σ)_●}` and is defined, while the right needs
`σ ● σ`, undefined.  On the family reading both are undefined.  6.18's proof (p. 9) splits
`⨀_{∈ρ₁₂}` into `⨀_{∈ρ₁} ● ⨀_{∈ρ₂}` from "disjoint own-or-mut cells", valid for a
location-indexed family.  `BoCa.Fig16.ExW.mk`/`BoCa.Fig16.AgW.mk` bind a list of
`(location, resource)` pairs enumerating `dom(ρ|ι)` once each (`BoCa.Fig16.ResU.Sites`),
tagged `[variant: the printed comprehension is a set and this is the family it indexes]`;
Lemma 6.3 makes the order immaterial.

### §12.37 `≤` on resources: printed by [CONF] p. 415:24 footnote 1

[CONF] p. 415:24, footnote 1:

```
¹Where ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃.
```

[TR] uses `≤` in Definition 6.3 (`ρ″ ≤ ρ|imm`, p. 17) and in the proofs of 6.54 and 6.57, and
gives no row; `reb_α` ([TR] p. 5, [CONF] Fig. 19) writes the converse
`ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)`.  `BoCa.Fig16.ResU.Le` is the footnote, `[as printed]`, with `▶◀`'s
operands transposed by Lemma 6.1.  A sub-map reading of `≤` would conflict with Definition
6.3's fourth bullet.

### §12.38 [TR] Definition 6.3's bullets and the term `ρ ⊟ ρ′`

[TR] writes `ρ ⊟ ρ′` as a term (pp. 17–20, 40); Lemma 6.52 states
`ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`.  The four bullets alone (§12.34) do not fix `ρ″`: off
`dom(ρ′)` the third fixes only `ℓ ∈ dom(ρ″)`, and `ρ″ ≤ ρ|imm` admits a smaller lifetime set
by Lemma 6.43.  At `Loc = Val = ℕ`:

```
ρ  ≜ ℓ₀ ↦ imm({1,2}, 0, ∅)        ρ′ ≜ ∅
χ₁ ≜ ρ                            χ₂ ≜ ℓ₀ ↦ imm({1}, 0, ∅)
```

both satisfy every bullet (bullet 2 for `χ₂` via `τ = ℓ₀ ↦ imm({2},0,∅)`), on either reading
of the last sub-bullet.  The paragraph below the bullets fixes it: "removing the lifetimes of
borrows from `ρ′`, but keeping the lifetimes only in `ρ`" gives `ρ″(ℓ) = ρ(ℓ)` off `dom(ρ′)`
(§12.58).  `BoCa.Fig16.ResU.Sub` and `ResU.SubL` admit two values here;
`BoCa.Fig16.ResU.SubKeep` is functional (`ResU.SubKeep.functional`), implies `ResU.Sub`
(`ResU.SubKeep.toSub`), and satisfies 6.52's equation at every admissible value
(`ResU.SubKeep.compS`).

### §12.39 [TR] p. 5, the second clause of `↭`: `mut` read as `imm`

[TR] p. 5:

```
ρ₁ ↭ ρ₂ ≜  ∀ ℓ, α, β, v, ρ, P̂.
             (⦇ρ₁⦈(ℓ) = mut(α, _, _, P̂)  ⇔  ⦇ρ₂⦈(ℓ) = mut(α, _, _, P̂))
           ∧ (⦇ρ₁⦈(ℓ) = imm(β, v, ρ)     ⇔  ⦇ρ₂⦈(ℓ) = mut(β, v, ρ)),        ✓ρ₁ ∧ ✓ρ₂
```

The second clause writes a three-argument `mut`, where `Mut_α` has four components and the
row above writes four.  [CONF] Fig. 18b (p. 415:22):

```
ρ₁ ↭ ρ₂ ≜ ∀ℓ, ᾱ, β, v, ρ, P̂.
    ⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ)    ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)      (1)
  ∧ ⦇ρ₁⦈(ℓ) = mut(β, −, −, P̂) ⇔ ⦇ρ₂⦈(ℓ) = mut(β, −, −, P̂)   (2)
```

and below it: "The update relation `↭`, defined in Fig. 18b, requires that all reachable
immutable borrows are preserved with their value `v` witness `ρ` exactly as is (Clause 1),
and that all mutable borrows are preserved up to a change in the witness (Clause 2)."  The
clause is read `imm ⇔ imm`.  `BoCa.Fig16.ResU.Upd` is Fig. 18b at the flattenings
(`BoCa.Fig16.ResU.Flat`); `BoCa.Fig16.ResU.UpdV` adds [TR]'s guard `✓ρ₁ ∧ ✓ρ₂`.  D3: inside
`wp` they are the same proposition.

### §12.41 `reb_α`: the escrow witness and the surviving `imm` cells

[CONF] §3.2.3, p. 415:15:

> Recall that in well-typed programs, immutable borrows are accessed using the `withload`
> operation, whose type is parameterized by the metafunction `Imm`.  This metafunction maps
> a type to its reborrowed type, which immutably borrows any linear references or mutable
> borrows in the payload […]  To access immutable borrows in the logic, we will use a rule
> of a similar shape, but the metafunction `Imm` does not have a clear counterpart for
> separation logic propositions. […]  We instead adopt the more extensional approach of
> characterizing the full space of safe reborrows, which is captured by the reborrow
> modality, `⟲α P`.

`reb_α(ρ)` is the metafunction's action on cells: a reference becomes an immutable borrow
whose witness is the payload's resource `π(ℓ)/ℓ`; a mutable borrow becomes an immutable one;
an immutable one is kept.  [CONF] p. 415:24: "For a borrow cell (Cases 2–3), the partition
`π(ℓ)` is additionally constrained to contain only that cell, since it already has a witness
resource."  `Fig16.ResU.RebAt` and `Fig16.ResU.Reb` follow the formula ([TR] p. 5; [CONF]
Fig. 19) and prose (pp. 415:23–24) clause by clause: `ℓ ∈ dom(π(ℓ))` for every
`ℓ ∈ dom(π)`; `own(v) ⇒ imm({α}, v, π(ℓ)/ℓ)`; `mut(_,v,ρ″,_) ⇒ imm({α},v,ρ″)` and the `imm`
clause, each with `dom(π(ℓ)) = {ℓ}`; the `imm` clause at a subset of the source's lifetime
set (definition row 5.28, §12.67(b)).

The proofs of [TR] 6.53, 6.55 and 6.61 each use a fact the formula, read over all resources,
does not state.  [CONF] p. 415:24: *"The conditions placed on each partition `ℓ` in `π`
depends on the type of cell at `ℓ` in the original resource `ρ`"* (§12.57, §12.59).

*For 6.61: every immutable cell of `ρ` survives in `ρ′`.*  [TR] p. 22: *"any overlapping
locations of `ρ′₁` and `ρ′₂` are in `(ρ₁ ● ρ₂)|imm`, which means `(ρ′₁ ● ρ′₂)(ℓ) =
(ρ₁ ● ρ₂)(ℓ)`."*  [CONF] p. 415:24: *"its imm locations are preserved at their original
lifetimes"*.  At the literal `imm` clause `ρ′(ℓ) = ρ(ℓ)`, an `own` location's escrow may
absorb an `imm` cell of `ρ₁`, and 6.61 needs survival as an added hypothesis.  At the subset
reading 6.61 is `Fig16.ResU.six61`, as printed, with the overlap sentence derived
(`Fig16.ResU.reb_overlap`, `Fig16.ResU.six61_imm_at`).

*For 6.53 and 6.55: the escrow at an `own` location is determined by `(ρ, ℓ)`.*  [TR] p. 18,
in 6.55's proof: *"`ρ` and `ρ′` differ only by potentially changing from own or mut to imm,
but witnesses and values always stay the same."*  At the `own` clause the witness is
`π(ℓ)/ℓ`, left to the choice of `π`.  6.53's proof uses the fact as *"the only way for
`ρ_f(ℓ)` to not be composable with `ρ(ℓ)` is for `ρ_f(ℓ)` to be own or mut"*; 6.55's first
bullet uses it at `ag(ρ_f)` against `ag(ρ)`, where `ag(ρ_f)` can be defined, and `mut`, where
`ρ_f` is not.  `Fig16.EscrowAgree` states it at `ag(ρ_f)` against the reborrow, over
non-`own` cells, and 6.53's use is recovered through `Fig16.AgW.get_imm`.  6.53 and 6.55
(`Fig16.ResU.six53`, `Fig16.ResU.six55`) carry it as a named hypothesis with printed
conclusions; it holds off the `own` clause (`Fig16.escrowAgree_of_no_own`) and is discharged
at every reborrow 6.150 takes at the typed world (`Fig16.LogRel.Typed.rebChooseO_top`,
`Fig16.LogRel.Typed.rebChooseO_deep_tw`, §12.71).  6.55 also carries `Fig16.AgW ρ A`, which
the printed `ag(ρ_f) ▷◁ ag(ρ)` presupposes (F1).

Neither fact follows from validity or from the call sites.  [CONF] p. 415:22: *"If `⦇ρ⦈` is
defined, the resource is considered to be valid"*; the configurations where the facts fail
are `✓`-valid, and a strengthening that excludes them also excludes Fig. 17a.  At [TR] p. 39
the frame comes from `wp`'s unrestricted `∀ρ_f # ρ`; at p. 33 the additions are arbitrary
`SProp`.

### §12.42 [TR] §3's machine: elided congruences, and their completion

[TR] §3 prints seven `Kont` productions and eight reduction rules (`TR3.Head` and the `Kont`
of `Paper/S3_Dynamics/Definitions.lean`).  Read as exact, the machine takes no step from
terms §2 types:

- `⊕I` types `injᵢ e` at any `e`, and there is no `injᵢ K` frame: `TR3.no_step_inj₁`,
  `TR3.derives_wInj`, `TR3.stuck_wInj`.
- `1E` types `e₁; e₂` at any `e₁ : 1`, there is no `K; e` frame, and `1↦` fires only at
  `()`: `TR3.no_step_seq`.  [TR] p. 4's `swap` has that shape.

`free (alloc ()); ()` is typed at `1` (`TR3.derives_wSeq`) and takes no step
(`TR3.stuck_wSeq`), so [CONF] Corollary 3.3's conclusion is unreachable for it over the
literal machine (`TR3.corThree_unreachable`).  `store v` is not a further instance: it is a
`Prim` value, and `(store) v` is the same string (§12.43).

§3 is read as elided, the congruences for `injᵢ` and `;` left to the reader.  `BoLo.Kont`
adds `injᵢ K` and `K; e`; `BoLo.Head` is the p. 4 box (`BoLo.Head.seq` at `()`, definition
row 3.14; `Fig16.BoLo.wp_1` states 6.137 at `()`).  `TR3.Head`/`TR3.Steps` remain the printed machine (D6).

### §12.43 `Val` is a subset of `Expr`: the subset encoding

[TR] p. 1:

    Val  ∋ v ::= () ∣ (v₁,v₂) ∣ inj₁ v ∣ inj₂ v ∣ λx.e ∣ Λ.e ∣ ℓ ∣ p
    Expr ∋ e ::= x ∣ v ∣ (e₁,e₂) ∣ inj₁ e ∣ inj₂ e ∣ e₁;e₂ ∣ let (x,y) = e₁ in e₂
                   ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂} ∣ e₂ e₁

`e ::= v` makes `Val` a subset of `Expr`, and `(v₁,v₂)`, `injᵢ v` are derivable two ways,
identified as in any paper grammar.  One `Expr` inductive carries the value formers,
`IsVal : Expr → Prop` is inductive over it, and `Val ≜ {e // IsVal e}` with `Expr.val` the
inclusion (definition row 1.17).  `Val.storeV v` and `.app (.prim .store) v` are one term, so
`store ℓ v` takes one step as in the p. 4 box.  So `Derives` is p. 2's rules alone, `BoLo.Head`
has no coercion steps, `Fig16.LogRel.wp_pair`/`wp_inj₁`/`wp_inj₂` are reflexivity, and a
value takes no step (`BoLo.no_step_val`).  `Val` is a subtype because the paper quantifies
over it as a type (`Mem ∋ μ : Loc ⇀ Val`, p. 1; `P̂ : Val → SProp`, p. 6); `Val.shift` and
`Val.subst` are the `Expr` operations with their `IsVal` preservation.

### §12.44 ∀I's `Δ, ('a ⊏ @b)` extends a partial map: `Derives.allI`'s freshness premise

[TR] p. 2, ∀I:

        Δ, ('a ⊏ @b); Γ ⊢ e : T
      ───────────────────────────
      Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T

([CONF] Fig. 7 the same.)  No freshness condition is printed.  [TR] p. 1 and [CONF] p. 415:8:

    LifeCtx ∋ Δ : LifeVar ⇀ Life

a partial map, used as one in [TR] p. 3's
`⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀ 'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}`.  `Δ, ('a ⊏ @b)` is extension
at a point outside the domain, which the Barendregt convention of a named presentation
guarantees.  `LifeCtx` is an association list whose `find?` returns the first match, so
`LifeCtx.extend` shadows; `Derives.allI`'s premise `hx : Δ.find? x = none` is the condition
under which extension and shadowing coincide, and is the first conjunct of `LifeCtx.Ok`.

Cost: `Ty` equality is syntactic, so a conclusion with `'a ∈ dom(Δ)` has no derivation here
where on the page it names its fresh α-variant.  The premise is not the freshness
`Fig16.LogRel.allI_compat` (6.161) needs — `@b`, `Δ`'s bounds and `Γ`'s live types not
mentioning `'a` — which `Fig16.LogRel.AllISide` carries (C14): at `Δ = ∅`,
`Γ = x : Imm 'a 1`, `hx` holds and the third fails.  The other constructors with a premise
beyond the printed rule are `withbor1Ax`/`withbor2Ax`/`withbor3Ax`/`withloadAx`'s `hx`
(§12.45) and `withbor2Ax`'s `hside` (§12.9).

### §12.45 The axiom table's `∀` binder is schematic

[TR] p. 3:

    Δ ⊢ withbor  : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂
                   Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂    Δ ⊢ T₁ ⊐ @b
                   Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂
    Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂

`'a`, `'b` are bound; types are identified up to α.  The bound `⊓Δ` depends on `Δ`
(`LifeCtx.meetOfDom`, §12.15); the binder does not.  `Derives.withbor1Ax` takes the binder
as a parameter with §12.44's premise, `(x : LifeVar) (hx : Δ.find? x = none)`, concluding at
`axWithbor1Ty x Δ.meetOfDom T₁ T₂`; likewise `withbor2Ax`, `withbor3Ax`, `withloadAx`.  A fixed
binder would make one α-variant derivable, while `Derives.var` returns a stored type verbatim
and `Derives.allE`'s `Ty.instLife` renames binders to avoid capture.
`Fig16.LogRel.fundamental_of_open`'s `open_withbor1` … `open_withload` are stated at the
schematic `x`, with its freshness for `T₁`, `T₂` read off `Fig16.LogRel.DerivesIn`;
`Fig16.LogRel.withbor1_compat` is 6.172 in that form.

### §12.47 Four facts at [TR] 6.59's open location

A location of 6.59 where a reborrow put `imm({β}, w, v)` and something else carries
`mut(b, v, w, P)`:

- (a) `β ⊑ b`, so `Res_b ⊆ Res_β` (`Fig16.ResU.InStratum.mono`); the two typings of the
  payload are compatible.
- (b) `#` does not exclude a second `mut` over the same payload: `○`'s clause (3) asks only
  for the same value and witness.  Validity makes the walks' domains disjoint
  (`Fig16.LogRel.Typed.ex_ag_disjoint`).
- (c) `Res_β` is hereditary (`Fig16.CellU.wit_inStratum_at`, `Fig16.BoLo.cell_wit_inStratum`),
  with `β ⊏ ⊓ᾱ ⊑ ⊔ᾱ ⊏ b` at an `imm` cell (`Fig16.LSet.meet_le_join`).
- (d) At the composites `A ○ S ∼ B ○ S`, the `mut`/`mut` case asks `a ⊓ γ = b ⊓ γ`; `a` and
  `γ` both outlive `β` and nothing orders them.

What constrains the location: the aliasable walk introduces a `mut` only through `ex(−)_○`
in its `imm` family, so every `mut` of `ag(ρ)` sits beneath an `imm`; `↭`'s first clause pins
that `imm` with its witness, the second pins only lifetime and invariant (§12.53).

### §12.49 Definition 6.2 (`∼`) and the unfolding of `↭` in [TR] §6

[TR] p. 13's Definition 6.2 is `∼`; the proofs of 6.39, 6.40, 6.44 and 6.59 unfold `↭` as
*"dom(⦇ρ₁⦈∣imm,mut) = dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in that domain, ⦇ρ₁⦈(ℓ) ∼
⦇ρ₂⦈(ℓ)"*.  `Fig16.CellU.Sim` is definition row 5.65, and `Fig16.ResU.upd_iff_sim` proves the
unfolding equivalent to `Fig16.ResU.Upd`.  Definitions 6.1, 6.2, 6.3 share numbers with
Lemmas 6.1–6.3; they are definition rows 5.61, 5.65 (`Fig16.CellU.Sim`) and 5.66
(`Fig16.ResU.Sub`).

### §12.50 Deep immutability is the two-operator design

[CONF] p. 415:24: *"our model enforces deep immutability of the data an immutable borrow
points to"*.  In Fig. 17a, `ℓ₃` carries `ρ₂`'s `mut(α₃, v₃, ρ₃, P̂₃)`, raised through `ag`'s
`imm` family by `ex(ρ₂)_○`, and `ρ₁`'s `imm(ᾱ₃′, v₃, ρ₃)`; `○`'s clause (5) returns the
`imm`.  Without the second view — an `imm` cell whose witness holds `mut(α₁, v₁, ρ_own, P̂₁)`
— the resource is valid and `ℓ₁` stays `mut` in the flattening.  [CONF] §4.3: *"even though
`ℓ₃` is incident from a mut cell, which would normally be exclusive, it has an imm ancestor,
which makes its whole subtree shared and `ℓ₃` aliasable"*.  The two documents' `ag` rows
agree here ([TR] p. 5; [CONF] Fig. 18a); the one difference, in the exclusive walk's
recursive subscript, is recorded on `Fig16.ExW`.

Deep immutability is the two-operator design: the exclusive walk composes at `●`, where
`▶◀` permits only two `imm` cells; everything under an `imm` is reached through `○`, whose
clause (3) composes two `mut` cells over one value and witness.

### §12.52 [CONF] §4.3's aliasing invariant is composition, and multiple paths are the licensed case

[CONF] p. 415:21 (definition row 5.67):

> "Conceptually, in a valid resource, every pair of aliases map to the same object and each
> has an immutable ancestor."

> "It also portrays aliasing of exclusive locations, like `ℓ₁`, that do map to the same cell
> but, unlike the previous example, are not guarded by immutable cells, which violates the
> mutability-xor-aliasing restriction."

> "The advantage of reusing composition is that it already rules out all of the
> inconsistent aliasing cases mentioned above."

> "flattening the resource in Fig. 17b is not defined — the conflict at `ℓ₁` causes `•` and
> therefore `E•` to be undefined, while the conflict at `ℓ₂` causes `◦` and therefore `A` to
> be undefined."

Each clause is a theorem: *same object* — `Fig16.CellU.compatR_iff`
(`▷◁ ψ₁ ψ₂ ↔ (ψ₁.erase = ψ₂.erase ∧ (neither own → ψ₁.wit = ψ₂.wit))`) and
`Fig16.CellU.CompatS.imm_imm`; *immutable ancestor* — `Fig16.AgW.nonimm_beneath_imm`, with
`Fig16.ExW.immFree` (6.36); *not both exclusive and aliasable* —
`Fig16.ResU.CompatS.disjoint_of_immFree`, `Fig16.ResU.flat_eq_ag_at`.  The invariant does
not make paths unique: Fig. 17a reaches `ℓ₃` by two (§12.50).  It constrains value and
witness, not a `mut` cell's lifetime or invariant, which come from §12.53's ancestor step.

### §12.53 [TR] 6.48's ancestor step

`Fig16.BoLo.updV_frame` is [TR] Lemma 6.48, `[as printed]`, proved as on p. 16.  The
`mut ○ mut` case, p. 16:

> "By the update hypothesis, we have `ag(ρ₃)(ℓ) = mut(β, _, _, Q̂)`.  And furthermore, by the
> definition of `ag`, there must exist `ℓ′, ρ′` such that `ag(ρ₂)(ℓ′) = imm(_, _, ρ′)` and
> `ag(ρ₂)(ℓ) = ⦇ρ′⦈_○(ℓ)`.  By the update hypothesis, we also have
> `ag(ρ₃)(ℓ′) = ag(ρ₂)(ℓ′)`, which implies `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)`."

A `mut` in the aliasable walk is accounted for by the `imm` cell it sits beneath: clause (1)
of `↭` pins that cell with its witness, supplying the value and witness clause (2)
wildcards; the conclusion is cell equality.  `Fig16.ResU.upd_ag_imm_wit_factor`,
`Fig16.ResU.upd_ag_nonimm_transfer` and `Fig16.ResU.upd_ag_mut_eq` are the step;
`Fig16.ResU.upd_ag_eq_of_ne_own` packages it (with `Fig16.ResU.upd_ag_own_or_none` at an
`own` cell).  [TR] 6.59's closing sentence uses it (§12.55, §12.58).

### §12.55 Stating a residual through the proved unfolding of `↭`

[TR] p. 20 unfolds `↭` to a domain equality and `∼` on `dom(⦇−⦈∣imm,mut)`.
`Fig16.ResU.SimForm` transcribes it (`Fig16.ResU.upd_iff_sim`), and residuals of 6.59's last
step are stated through it (`Fig16.ResU.SimFormAt`, `Fig16.ResU.simForm_iff_at`).
`Fig16.CellU.Sim` does not hold at an `own` cell, hence the guard.  Where `⦇LHS⦈(ℓ)` is
`own`, the domain clause asks that `⦇RHS⦈(ℓ)` be `own` or absent; only `○`'s clause (1)
returns an `own`, so both operands are `own`.  Both residuals are discharged at
`Fig16.ResU.SixFiftyNineResidualKeep` and `Fig16.ResU.SixFiftyNineOffRebKeep` (§12.58).

### §12.57 `reb_α`'s escrowed witness and the resources the calculus produces

`DeepReborrow.rebA β v u` is `0 ↦ imm({β}, v, 1↦own(u))`, a reborrow of
`0↦own(v) ⊎ 1↦own(u)` by `reb_β`'s `own` clause with witness `π(0)/0 = 1↦own(u)`
(`DeepReborrow.reb_rho2_rebA`).  At `v = ()` the escrow corresponds to no program:

```rust
// Location 0 holds a POINTER to location 1: the escrow is legitimate.
let x = Box::new(String::from("hi"));   // 0 -> 1
let r = &x;
let _z = *x;        // error[E0505]: cannot move out of `*x` because it is borrowed
```
```rust
// Location 0 holds (), which points at nothing.
let x = ();                      // location 0
let y = String::from("hi");      // location 1, unrelated
let r = &x;
let z = y;          // compiles and runs: y is NOT in &x's footprint
```

Against `reb_α` as printed, `rebA` is a legal reborrow.  What excludes it is the semantic
type (§12.59): `ptoImm ℓ α P̂` carries `P̂(v)(ρ′)`, and `𝒱⟦T⟧δ(())` refuses the witness
`1↦own(u)`.

Two conditions the proofs use:

*`imm` locations survive a reborrow.*  [CONF] p. 415:24: *"`ρ′` must be just like a
subresource of the original resource `ρ` … its imm locations are preserved at their original
lifetimes"*:

```rust
let mut y = 5;
let r = &y;              // location 1: imm borrow of y
let b = Box::new(r);     // location 0: owns that borrow
let s = &b;              // reborrow of location 0
y = 6;   // error[E0506]: cannot assign to `y` because it is borrowed
```

With [TR] 6.57's `≤`, this grounds the subset reading of `reb_α`'s `imm` clause (§12.67(b),
definition row 5.28), at which 6.61, 6.125 and 6.127 need no added hypothesis.

*Two reborrows agree on the escrowed witness.*  `Fig16.EscrowAgree` carries [TR] p. 18's
sentence in 6.55's proof (§12.41, §12.60), a named hypothesis on `Fig16.ResU.six53` and
`Fig16.ResU.six55` (`proved*`).  `Fig16.BoLo.deepReborrow_not_rebEscrow` shows it excludes
`rebA`.

### §12.58 Definition 6.3's third bullet and the paragraph below it

[TR] p. 17, under Definition 6.3's bullets:

> Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But since immutable
> borrows can alias at the same location, "without" means removing the lifetimes of borrows
> from `ρ′`, but keeping the lifetimes only in `ρ`.

The third bullet's glyphs ask only `ℓ ∈ dom(ρ″)` off `dom(ρ′)` and admit more than one `ρ″`
(§12.38); by the paragraph every lifetime of `ρ(ℓ)` there is "only in `ρ`", so
`ρ″(ℓ) = ρ(ℓ)`.  `Fig16.ResU.SubKeep` is Definition 6.3 with the third bullet read through
that sentence; `Fig16.ResU.Sub` is the bullets alone (`Fig16.ResU.SubKeep.toSub`).  On
`SubKeep`, `⊟` is single-valued where the operands carry `imm` cells over one value and
witness at each shared location — the hypothesis of `Fig16.ResU.sub_of_le`, established by
6.52's H1 (`Fig16.ResU.six52_H1`) — so `ρ ⊟ ρ′` is a term (`Fig16.ResU.SubKeep.functional`);
6.52's equation holds at every admissible `χ` (`Fig16.ResU.SubKeep.compS`); and
`Fig16.ResU.sub_of_le` produces `SubKeep`.  6.59 (`Fig16.ResU.six59`) composes
`Fig16.ResU.SixFiftyNineResidualKeep` and `Fig16.ResU.SixFiftyNineOffRebKeep`, both at
`SubKeep` (§12.64).

### §12.59 "The type of cell" in [CONF] p. 415:24 is `own` / `imm` / `mut`

[CONF] p. 415:24: *"The conditions placed on each partition `ℓ` in `π` depends on the type of
cell at `ℓ` in the original resource `ρ`."*  Three sentences later: *"If the cell was owned in
`ρ` (Case 1) … If the cell was immutable in `ρ` (Case 2) … if the cell was mutable in `ρ`
(Case 3)."*  "Type of cell" is the cell kind, and Fig. 19's three implications case on it;
the partition is not directed by the payload's semantic type.  The implications are not
vacuous: `Fig16.ResU.RebAt`'s `ℓ ∈ dom(π(ℓ))` with the printed `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)` gives
`dom(ρ′) ⊆ dom(ρ)` (`Fig16.ResU.reb_dom_subset`).  So what separates §12.57's
`DeepReborrow.rebA` from the calculus's resources is the semantic-type criterion.

### §12.60 Two kinds of unstated condition: supplied by prose, and used by a proof

(a) A sentence beside a definition states a property its formula does not carry: the
sentence is transcribed as part of the definition, quoted (§12.64; `Fig16.ResU.SubKeep`,
§12.58).  (b) No sentence states it and a proof step proceeds as though it held: a named
hypothesis with the step quoted, conclusion unchanged, row `proved*`.

| instance | finding |
|---|---|
| `Fig16.EscrowAgree` | (b).  Its sentence is [TR] p. 18, inside 6.55's proof — "`ρ` and `ρ′` differ only by potentially changing from own or mut to imm, but witnesses and values always stay the same".  [TR] p. 8's 6.14 sentence is about `○` on two cells and is carried by `Fig16.CellU.compatR_iff`. |
| survival of `imm` locations under `reb_α` | [CONF] Fig. 19 prints `reb_α`'s body quantifier as `∀ℓ, v, ρ_ℓ` where [TR] p. 5 prints `∀ℓ ∈ dom(π)`.  The unguarded form is not a statement of survival: [CONF] p. 415:24 says "The conditions placed on each partition `ℓ` in `π`", [TR] 6.52 unfolds `reb` with "if `ℓ ∈ dom(ρ)`", 6.54's bullet 2 restricts the `imm` equation on both sides, 6.123/6.124/6.127 reduce the `∀` by its guard, and a total clause (2) would break `Fig16.BoLo.reb_emp_iff`, hence 6.124 and 6.130.  The condition is carried by the subset reading of the `imm` clause (§12.67(b)). |
| a licence on the recorded borrows in 6.60's `Imm` case | Printed as an assertion: [CONF] Fig. 13b's `⟲I` (p. 415:15), `ℓ ↦I_β P̂ ⊨ ⟲_α ℓ ↦I_β P̂` under `β ⊐ α` alone, at `α := ↓β` with 6.63 is `@ρ ⊒ β`.  6.123 (`Fig16.BoLo.reborrow_ptoImm`) spends its `box α` once, so transcribing `⟲I` reproduces the obligation.  At `⊓β̄` (§12.67(a)) the case needs no licence. |

### §12.61 [TR] 6.150 is printed twice, and the two printings agree

[TR] Theorem 6.150 (p. 39):

> `ℓ ↦ Imm α (Иβ. ↺_β P̂) ⋆ (Иβ. ∀v. P̂(v) ─⋆ wp(e){[β]Q̂}) ⊧ wp(e){Q̂}`

[CONF] Fig. 13b (p. 415:15), `I Reborrow`:

> `ℓ ↦ I_α (Иβ. ⟲_β P̂) ⋆ (Иβ. ∀v. P̂(v) ─⋆ wp(e){[β]Q̂}) ⊨ wp(e){Q̂}`

The same rule in the two documents' spellings; `Fig16.BoLo.wp_reborrow` transcribes it.
[CONF] Fig. 14 (p. 415:16) derives `withload` with a middle step labelled `(I Reborrow)` whose
goal reads

> `ℓ ↦ I_α ( _. Иβ. ⟲_β P̂(v) ) ⋆ Иβ. ∀v. P̂(v) ─⋆ wp(v_f () v){Q̂} ⊨ wp(v_f () v){Q̂}`

The `_.` comes from the preceding `wp Load I` step (*"we can specialize its borrowed predicate
to `v` by turning it into a constant function"*, p. 415:16), so the rule is applied at a `P`
constant in its value.  The `{Q̂}` without `[β]` is not highlighted (caption: *"Changes between
proof states are highlighted"*), and Fig. 14's conclusion and Fig. 13b carry `{[β]Q̂}`; it is
read as typesetting.  Fig. 14 is [CONF]'s sketch of 6.175, a separate row.

`P̂` stands under the `Иβ`.  [TR] 6.175's proof (p. 48) applies 6.150 at

> `P̂ ≔ (v′. ⌜v′ = v_ℓ⌝ ⋆ 𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}(v′))`

and writes that `β` under the `Иβ`:

> `𝒱⟦∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸['b]T₂⟧δ(v_f) ⊨ Иβ. ∀v′. v′ = v_ℓ ⋆ 𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}(v′) ─⋆ wp(v_f () v′){[β]𝒱⟦T₂⟧δ}`

`𝒱⟦Imm̲ 'b T₁⟧_{δ['b↦β]}` reads `β` at every borrow leaf of `T₁`.  `Fig16.BoLo.wp_reborrow`
takes `P : Life → Val → SProp`, with `Fig16.BoLo.RebEscrow` indexed to match; H11 picks one
`β` and every later step reads `P̂` there.  The `β`-independent statement is the instance at a
constant `P̂` (`Fig16.BoLo.wp_reborrow_emp_applies`).
`DeepReborrow.wp_reborrow_unreconciled_at_split_view` has the same indexed shape, and
`Fig16.BoLo.deepReborrow_not_rebEscrow` separates them.

### §12.62 [TR] 6.130's `P` is one of the printed `SProp_α`, and `↺_α emp` is `Res_α`

[TR] p. 34:

> **Lemma 6.130.**  `P ⊧ ↺_α emp`
>
> *Proof.*  Suppose `ρ ∈ P`.  Then `∅` vacuously satisfies the conditions needed to be a
> reborrowed version of `ρ`, so `ρ ∈ ↺_α emp`.

`emp` holds of `∅` alone ([TR] p. 6), so `↺_α emp` holds of `ρ` exactly when
`∅ ∈ reb_α(ρ)`, where ([TR] p. 5)

```
reb_α(ρ) ≜ {ρ′ | @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ∧ ∀ℓ ∈ dom(π), v, ρ″. …}
```

At `π = ∅` three conjuncts are vacuous (`Fig16.BoLo.reb_emp_iff`); the fourth, `@ρ ⊐ α`, is
`ρ ∈ Res_α` (§C.25).  So `↺_α emp` is `Res_α` (`Fig16.BoLo.reborrow_emp_iff`) and 6.130 is
`P ⊆ Res_α`.  That set is printed: [TR] p. 4's `SProp_α ≜ Res_α → ℙ`, placed inside
`SProp` by `Fig16.SPropS.toU_range`.  Both of [TR]'s uses, in 6.131's induction (p. 34),
supply it: at `T₁ ⊸ T₂` the antecedent `[α] 𝒱⟦T₁ ⊸ T₂⟧δ(v)` carries it
(`Fig16.BoLo.reborrow_emp_box`); at `Ref T′` the owned cell lies in every stratum
(`Fig16.BoLo.reborrow_emp_ptoOwn`).  `Fig16.BoLo.reborrow_emp` states the entailment with the
inclusion as a named hypothesis (`proved*`); `Fig16.BoLo.reborrow_emp_outside_stratum`
exhibits a resource outside `Res_α` (the `mut` witness of `Fig16.RebExample.mutRes`).

### §12.63 Where 6.125 would carry 6.61's input: at the resource, not at `P` and `Q`

[TR] 6.125's proof (p. 33) is *"By theorem 6.61"*.  At the subset reading (§12.67(b)) 6.61
carries nothing and `Fig16.BoLo.reborrow_star` is 6.125 as printed.  At the literal clause
`ρ′(ℓ) = ρ(ℓ)`, 6.61 needs survival of `imm` locations at its two sources, which are the
factors `ρ = ρ₁ ● ρ₂` of 6.125's `⋆`, so the input is a condition on `ρ`.  Lifted onto `P` and
`Q` it would empty the row: every `ρ₁ ∈ Res_α` has `∅` among its reborrows (§12.62), so at
`P = Q = emp` it would say no member of `Res_α` carries an `imm` cell.

### §12.64 Where the prose disambiguates the formula, the prose is the definition

When a displayed formula is accompanied by a paragraph that fixes what the formula leaves
open, the two together are the definition.  Instance: Definition 6.3's third bullet with the
paragraph below it (§12.58); `Fig16.ResU.SubKeep` is Definition 6.3, `Fig16.ResU.Sub` the
bullets alone.  A row proved at the completed reading is `proved` ([TR] 6.59,
`Fig16.ResU.six59`).  This applies only where a sentence states the property (§12.60 (a));
a condition only a proof uses, such as `Fig16.EscrowAgree`, stays a named hypothesis and its
rows stay `proved*`.

### §12.65 [TR] 6.144 and [CONF]'s `wp Load I` are two rules, and both are proved

[TR] p. 37:

> **Lemma 6.144 (`wp-load-I`).**
> `ℓ ↦I_α P̂ ⋆ (∀ v. ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v)) ─⋆ Q̂(v)) ⊧ wp (load ℓ) {Q̂}`

[CONF] Fig. 13b (p. 415:15), `wp Load I`:

> `ℓ ↦ I_α P̂ ⋆ (∀ v. ℓ ↦ I_α (_. P̂(v)) ─⋆ wp (v) {Q̂}) ⊨ wp (load ℓ) {Q̂}`

They differ twice.  The family: [TR]'s `(v′. ⌜v = v′⌝ ⋆ P̂(v))` against [CONF]'s constant
`(_. P̂(v))` (*"we can specialize its borrowed predicate to `v` by turning it into a constant
function, since all future reads from the immutable borrow must produce the same value"*,
p. 415:16); inside `↦I_α` [TR]'s is [CONF]'s plus the equation pinning the value.  The wand's
conclusion: `Q̂(v)` against `wp (v) {Q̂}`, related by 6.136 (`Fig16.BoLo.wp_val`), whose printed
`⫤⊨` is read as `⊨` since every citation of `wp-val` in [TR] is forward.  The differences
push the premises opposite ways, so neither rule is derived from the other.
`Fig16.BoLo.wp_load_I` is 6.144 (`[as printed]`), `Fig16.BoLo.wp_load_I_conf` is Fig. 13b's
row (`[variant: …]`), and `TR3.wp_load_I` is 6.144 over [TR] §3's machine (D6).  [CONF]'s form
is transcribed because Fig. 14 cites it to produce the constant family
`Fig16.BoLo.wp_reborrow` then consumes.

### §12.66 `β̄` is the borrows outstanding at a location, not the borrows ever taken

[CONF] 415:19 (§4.1):

> "an immutable cell will record the set of lifetimes `β̃` that it has been borrowed at
> (written `imm(β̃, v, ρ′)`), and the borrow connective will bound its lifetime index `α` by
> the longest among them."

[TR] Definition 6.3 subtracts lifetime sets, `ᾱ ∖ β̄`, and its paragraph says

> "since immutable borrows can alias at the same location, 'without' means removing the
> lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`."

A set of outstanding claims is subtracted from; a history is not.  `β̄` is read as the
borrows outstanding (§12.64).  Then every member is held by a live slot, `Δ ⊢ Γ ⊐ @a` bounds
every live slot, and `⊓β̄ ∈ β̄` (`Fig16.LSet.meet_mem`), so 6.60's premise `@bδ ⊐ @aδ` is spent
where the page spends it.  `Fig16.LogRel.LifeMembers` is the reading as a predicate, closed
under `∅`, `reb_α` and `●` (`Fig16.LogRel.lifeMembers_empty`, `Fig16.LogRel.lifeMembers_reb`,
`Fig16.LogRel.lifeMembers_compS`, `Fig16.LogRel.lifeMembers_compS_left`);
`Fig16.LogRel.Arises` is the family of resources it holds at, with
`Fig16.LogRel.lifeMembers_of_arises`.

At the literal `⊔β̄` (definition row 5.30), 6.60's `Imm` step asks that every recorded
lifetime be outstanding, a condition like `✓` absent from `Res`'s grammar;
`Fig16.LogRel.MutImmCell.cell` and `Fig16.LogRel.MutImmCell.lset` build the cell this
concerns, at `𝒱⟦Mut @a (Imm @b 1)⟧`.  That under `α ⊑ ⊔β̄` this type has no member is
argued here and not derived in Lean; an argument for it passes through row 4.16's
`Supported`.  At `⊓β̄` (§12.67(a)) no licence is needed.

### §12.67 `ℓ ↦ Imm α P̂` bounded by `⊓β̄`, and a subset in `reb_α`'s `imm` clause

Two definition rows changed so that printed proofs go through as printed (§12.64).  Each
entry quotes the prose that supports the change and, under *Literal reading*, the prose
that describes the printed form.

(a) `Fig16.BoLo.ptoImm`: `α ⊑ ⊓β̄`, where [TR] p. 6 prints `α ⊑ ⊔β̄`.  Definition row
5.30, changed so that 6.60's `Imm` step goes through as printed.

* [TR] Definition 6.3 and the sentence after it (p. 17): *"since immutable
  borrows can alias at the same location, 'without' means removing the lifetimes
  of borrows from `ρ′`, but keeping the lifetimes only in `ρ`"* — each lifetime in a cell's
  set is one borrow held (§12.66).
* [CONF] 415:8: *"`Δ ⊢ T ⊐ a`, which now only forbids the context from holding
  borrows at lifetime `a` or shorter"*.
* [CONF] 415:9: *"the lifetime `a` is really only a lower bound on the 'true'
  lifetime that the borrow was originally assigned"*.
* [CONF] 415:10: *"the payload type for a mutable borrow is required to have an
  unambiguous lifetime bound"*.
* [CONF] 415:14: *"the borrowed predicate must have an unambiguous lifetime
  bound … expressed at the logical level using `[β]`"*.
* [CONF] 415:20: `Mut_α`'s *"predicate `P̂` … sits in the stratification at its
  lifetime `β`"*.
* [TR] 6.60's `Imm` step (p. 21): *"`@bδ ⊑ ⊔β̄`.  And by the hypothesis,
  `@bδ ⊐ @aδ`.  Therefore `@ρ ⊐ @aδ`"*, where `@ρ = ⊓β̄` (p. 5).

An index is a lower bound on the borrow it names and each member of `β̄` is a borrow, so the
index bounds every member: `α ⊑ ⊓β̄` (`Fig16.LSet.meet_mem`, `Fig16.LSet.meet_least`).  Then
`Fig16.LogRel.vDen_outlives` is 6.60 as printed, and 6.60, 6.62, 6.163 and 6.173 carry no
added hypothesis for the `Imm` case.

Literal reading: [CONF] 415:19 says *"the borrow connective will bound its lifetime index `α`
by the longest among them"*, and [TR] p. 6 prints `⊔`.  [CONF] 415:20 gives the two bounds of
an `imm` cell separately: *"For an imm cell, the shortest among its lifetimes `β̃` must still
be longer than the stratification index `α`, and the witness `ρ` sits in the stratification at
the longest among its lifetimes `β̃`."*  At `⊔β̄` we cannot reconcile 6.60's `Imm` step with
`@ρ = ⊓β̄`, since the two bound different members (`Fig16.LogRel.MutImmCell.cell`,
`Fig16.LogRel.MutImmCell.lset_meet`; `Fig16.LogRel.MutImmCell.inRel_same` is the case
`β = α₀` under `⊓β̄`).  §12.66 argues that `𝒱⟦Mut @a T⟧δ` then has no member whenever `T`
has a top-level `Imm`; that is not derived in Lean.

Cost of `⊓β̄`: [TR] 6.115 (`I-ag`) concludes at `α ⊔ β`, and its printed proof goes through
at the printed `⊔β̄`; cells at `{1}` and `{2}` compose to
`{1, 2}`, whose meet is not `⊒ 1 ⊔ 2` (`Fig16.BoLo.not_iAgreeAtJoin`).
`Fig16.BoLo.ptoImm_agree` is 6.115 at `α ⊓ β` and `Fig16.BoLo.ptoImm_agree_eq` at equal
indices; [CONF] 415:13 describes `I Agree` as aliases that "all agree on the lifetime".  6.115
is a variant.

(b) `Fig16.ResU.RebAt`'s `imm` clause: `ρ′(ℓ) = imm(t̄, v, χ)` for a nonempty
`t̄ ⊆ s̄`, where [TR] p. 5 prints `ρ′(ℓ) = ρ(ℓ)` at `ρ(ℓ) = imm(s̄, v, χ)`.  Definition row
5.28, changed so that 6.61, 6.125 and 6.127 follow their printed proofs.

* [CONF] 415:24: *"`ρ′` must be just like a subresource of the original
  resource `ρ` … its imm locations are preserved at their original
  lifetimes"*.  A subresource of an `imm` cell is that cell over fewer outstanding borrows
  (Definition 6.3).
* [TR] 6.57's proof (p. 19) prints *"`ρ|dom(ρ′ᵢ|imm) ≤ ρ′ᵢ|imm`"*, with `≤` and not `=`.
* [TR] 6.61's proof (p. 22) opens with *"the only interesting cases are locations
  `ℓ` that are in both `ρ′₁` and `ρ′₂`"*, which holds under the subset reading
  (`Fig16.ResU.six61_imm_at`).

`t̄` is nonempty because `Fig16.LSet` is (G2).  Literal reading: the printed equation is
described three times.

* [CONF] 415:24, in the paragraph quoted above: *"If the cell was immutable in `ρ` (Case 2),
  then it will be preserved as is in the reborrowed resource `ρ′`."*
* [TR] p. 18, in 6.55's proof: *"`ρ` and `ρ′` differ only by potentially changing from own or
  mut to imm, but witnesses and values always stay the same"*.
* [TR] 6.61's proof (p. 22) ends *"`(ρ′₁ ● ρ′₂)(ℓ) = (ρ₁ ● ρ₂)(ℓ)`"*, which
  `Fig16.ResU.six61_imm_at` states as a subset.

At the printed equation a `●`-factor of an image is not an image, and 6.61, 6.125 and 6.127 each need an added hypothesis (§12.41, §12.57,
§12.63).  At the subset reading they are `Fig16.ResU.six61`, `Fig16.BoLo.reborrow_star` and
`Fig16.BoLo.reborrow_weak` (through `Fig16.ResU.RebAt.factor`), as printed; 6.131–6.133 and
6.175 carry no such hypothesis.  Consumers of the printed equation (6.52–6.59, 6.150) read it
through `Fig16.ResU.reb_imm_cell_kw`: the image cell is `imm`, at the source's value and
witness, in every stratum the source cell is in.

### §12.68 A `withload` configuration of our carrier

`Fig16.LogRel.ViewWitness` has an argument `ℓ₂ ↦ imm({1}, ℓ₀, ρ″)`, whose witness owns `ℓ₀`,
and a callback resource holding the view `ℓ₀ ↦ imm({1}, (ℓ₁,()), ∅)`.  `ρ₁ ● ρ₂` is `✓`
(`DeepReborrow.Valid_composite`), the callback is in its type
(`Fig16.LogRel.ViewWitness.f_den`), and it gets stuck when `withload` hands it `ℓ₀`
(`Fig16.LogRel.ViewWitness.run_stuck`).  On our carrier, the literal `Sem` at that
`withload` node does not hold there (`Fig16.LogRel.ViewWitness.withloadSem_refused`), nor
does `FundamentalProperty` at `Sem` (`Fig16.LogRel.ViewWitness.fundamentalProperty_refused`).

We cannot reconcile this configuration with [TR] 6.150's H19 (p. 39): *"by lemma 6.55 with
H16, `ρ_P̂(v′) # ρ_b`"*.  The step runs through p. 5's `▶◀` between `imm` and `own`, which
compares only the value, and p. 6's `wp`, which constrains only the endpoint memories.  The
configuration measures the literal p. 6 `wp` and p. 4 `𝒱⟦−⟧`; §12.69–§12.72 read those two
definitions, leaving `▶◀` untouched, and §12.73 shows the resulting judgment excludes it
(`Fig16.LogRel.ViewWitness.excluded`).

### §12.69 `𝒱⟦Imm @a T⟧`'s payload read at its observable view

Definition row 4.8.  [TR] p. 4 prints `ℓ ↦ Imm @aδ 𝒱⟦T⟧δ`.  The `Imm @a T` clause of
`Fig16.LogRel.Typed.vX` holds its payload at `vX wpX false T`: `𝒱⟦T⟧` with every `⊸`/`∀`
position not under a `Mut` relaxed to `True`, a weakening (`Fig16.LogRel.Typed.vO_obs`);
every other clause is the full relation's, and `Mut` stores the full relation.

* [CONF] 415:9: *"In some cases, like for computations with capture environments that may
  hold linear references, there is no view at which it would be safe to access the payload,
  so we map these types to a new, distinguished unknown type, Unk, for which the only
  operation that is defined is forget."*
* [CONF] Fig. 8 (415:10), clauses (4) and (8): `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` and
  `Imm̲ 'b (∀'a ⊏ @a. T) ≜ Unk`.
* [CONF] 415:15: the metafunction *"immutably borrows any linear references or mutable borrows
  in the payload and obfuscates any closures that may hold onto such resources"*.
* [TR] 6.131 (p. 34), the `T₁ ⊸ T₂` bullet: *"Unfold: [α] 𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊧ ↺α emp.  Apply
  theorem 6.130."*  The `∀` bullet: *"analogous to case T = T₁ ⊸ T₂"*.

The only operation a printed proof performs on a `⊸`/`∀` payload is to discard it, and the
prose says no view may access it (§12.64, §12.60 (a)).  Every printed consumer of an `Imm`
payload (6.60, 6.64–6.172, 6.131–6.133, 6.167, 6.170, 6.171, 6.175) reads it through 6.131 or
not at all; every producer (6.64–6.172, 6.131's `↺↦`, `↺m`, `↺i`) makes the full payload,
which `vO_obs` weakens.  All of §6.8 runs at this reading
(`Fig16.LogRel.Typed.fundamentalProperty`); it has not been checked against rules outside §6.

Literal reading: `Fig16.LogRel.vDen`'s `Imm` clause keeps the full payload.  Then 6.150's
reborrow is not determined by types: at a `⊸` position the full `𝒱⟦⊸⟧` is
resource-sensitive, and the image a later `withload` needs cannot be typed from what the
world records.  The chooser at the literal reading is not derived, and no obstruction is
verified.  At the observable view it is proved: `Fig16.LogRel.Typed.obs_transfer` moves the
view between two pieces of one escrow (both `True` at `⊸`/`∀`), and
`Fig16.LogRel.Typed.rebChooseO_top_tw`/`Fig16.LogRel.Typed.rebChooseO_deep_tw` choose from
the tagged world.

### §12.70 The `Mut` and `Imm` payloads stratified by the record list

Definition rows 4.8, 4.9.  With `𝒱` read relative to a record list (§12.72), a borrow cell's
payload is held at the records strictly longer-lived than the cell:
`Fig16.LogRel.Typed.ptoMutS` stores `P(ls₀)`, `ls₀` the members longer-lived than `b`, with `P`
in `Res_b` at every list; `Fig16.LogRel.Typed.ptoImmS` holds the payload at the members
longer-lived than `⊓β̄`.

* [TR] p. 4: `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}`.
* [TR] 6.65 (p. 24): *"If P̂ ⊧ [β] P̂, then …"*, the cell made at *"α ⊏ γ ⊓ β"*.
* [CONF] 415:20: *"we break the circularity using stratification, but using a very different
  measure: the outlives lifetime ordering"*; *"For a mut cell, its lifetime β must be longer
  than the stratification index α, its witness ρ sits in the stratification at its lifetime β,
  and so does its predicate P̂"*.
* [CONF] 415:25: *"the lifetime stratification inherent to the type system is enough to avoid
  the use of step-indexing altogether"*.

`Ext` never changes the records longer-lived than a cell, so a stored predicate is stable
along it (`Fig16.LogRel.Typed.vX_local`).  Reading gives the content at the current list
(`Fig16.LogRel.Typed.ptoMutX_read`); a write needs content relevant only above the cell
(`Fig16.LogRel.Typed.ptoMutX_write`, `Fig16.LogRel.Typed.lifeBound_of_tagged`); a cell made
below every record stores the whole list (`Fig16.LogRel.Typed.ptoMutX_create`), 6.65's
*"α ⊏ γ ⊓ β"* taken below every tag.

The last conjunct of `ptoMutS`, `P̂ : Val → SProp_b`, asks that every resource the payload
predicate holds of lie in stratum `b`.  At a `Mut @a T` whose `T` has a `⊸` or `∀`
position, [TR] p. 47 supplies this *"by well-formedness of the type `Mut @a T₁`"*
(`Δ ⊢ T₁ ⊐ @a`), which definition row 2.28 does not carry.  Where the conjunct fails,
`𝒱X⟦Mut @a T⟧` has no member and `SemX` holds at any context with such a live slot; this is
not derived in Lean here.  `adequacy`'s statement does not mention `SemX`, so it is unaffected.

Literal reading: `Fig16.LogRel.vDen` has one list-independent predicate per cell.  One that
mentions the list is not stable as it grows; one that does not cannot carry `CohE` at its
`Imm` positions or `wpTS` at its `⊸` positions.  Neither half is machine-checked here.

### §12.71 The `Imm` clause carries the type the world recorded at the cell

Definition row 4.8.  The `Imm @a T` clause of `Fig16.LogRel.Typed.vX` adds
`Fig16.LogRel.Typed.CohE (rsOf ls) ℓ T δ`: the record list names at `ℓ` a record of type `T`,
or a chain position of a record with pointee type `T`, up to `Fig16.LogRel.Typed.TyEq`
(equality once each lifetime is read at its substitution).

[TR] 6.150's proof (p. 39) spends 6.55 on H16's reborrow at H19: *"by lemma 6.55 with H16,
`ρ_P̂(v′) # ρ_b`"*.  What makes that step go through is printed twice:

* [TR] p. 18, inside 6.55's proof: *"ρ and ρ′ differ only by potentially changing from own or
  mut to imm, but witnesses and values always stay the same"*;
* [CONF] 415:19: *"immutable cells ψ₁, ψ₂ at the same location must all have the same
  witness"*.

`↺` *"is a ⋄-style modality; it existentially quantifies over resources ρ′ that satisfy the
given proposition"* ([CONF] 415:23), over *"the full space of safe reborrows"* (415:15), so
H16's reborrow must be the one the context's other views already agree with, and `CohE`
lets it be chosen from types.  `Fig16.LogRel.Typed.wpTS_reborrow` is
`Fig16.BoLo.wp_reborrow`'s H1–H33 with `Fig16.BoLo.RebEscrow` replaced by the chooser
`Fig16.LogRel.Typed.RebChooseTW`, discharged by `Fig16.LogRel.Typed.rebChooseTW_top` and
`Fig16.LogRel.Typed.rebChooseTW_deep`.  `TyEq` is needed because 6.162's `Δ-subst` moves a
value between syntactically different types (`Fig16.LogRel.Typed.vX_tyEq`).

Literal reading: without `CohE`, 6.175 at `Fig16.LogRel.Sem` takes
`Fig16.LogRel.WithloadEscrow` as a hypothesis (§12.68).

### §12.72 `⊸`/`∀` Kripke over the record list, and `wp` over tagged typed worlds

Definition rows 4.4, 4.5, 4.11, 4.13, 4.14, 5.33.

* `Fig16.LogRel.Typed.TW W ps rs`: `W` (every frame with the resource a `wp` runs at) is
  reached from `∅` by the operations the printed proofs perform — 6.141, 6.142, 6.145, 6.64's
  entry and exit, 6.65/6.66's fold and unfold, 6.150's entry and exit at H11's `β`.  `ps`
  holds the open 6.64 frames as records `(ℓ, v, ρ′, T, δ)`, `rs` their lineages;
  `Fig16.LogRel.Typed.TW.inv` is the invariant.
* `Fig16.LogRel.Typed.wpTS ls e Q̂` is [TR] p. 6's `wp` with `∀ρ_f # ρ` over the frames that
  complete `ρ` to a tagged (`Fig16.LogRel.Typed.Tagged`) `TW` world at `ls`; the
  post-configuration is such a world with the same records and members; every other
  conjunct is `Fig16.BoLo.wp`'s, and `Q̂` receives the list.
* `vX`'s `⊸` and `∀` clauses quantify over lists `Fig16.LogRel.Typed.Ext`-above the current
  one at the closure's resource; `Fig16.LogRel.Typed.SemX` holds at every list.

§6's lemmas quantify over resources that arise.  [CONF] 415:21: *"Conceptually, in a valid
resource, every pair of aliases map to the same object and each has an immutable
ancestor."*  The carrier's `✓` does not carry this (§12.68's `ρ₁ ● ρ₂`).  [CONF] 415:19: *"At
the moment the borrow is created, there is a particular witness—the value v and a resource
ρ′—for the payload predicate P̂(v)(ρ′) … ownership of this witness ρ′ is temporarily moved
into the borrow."*  A record is that witness with the `(T, δ)` of its payload predicate.  The
list is carried because a world does not determine it; `⊸`/`∀` are Kripke over `Ext`, so a
closure is not credited with records it holds no borrow of; the members are kept because
6.64 ends its record before the run returns.  At `wpTS`, 6.135–6.149 are the proofs of
`Fig16.BoLo.wp_bind` … `Fig16.BoLo.wp_I_forget` with the post-world's `TW` constructor added.

Literal reading: `Fig16.BoLo.wp` quantifies over every `ρ_f # ρ`, including §12.68's
configuration.  `Fig16.LogRel.fundamentalProperty` runs 6.151's printed induction at the
literal definitions with `WithloadEscrow` as a hypothesis at the `withload` case; it is not
among the results.

### §12.73 Why the judgment tracks history

§12.68's configuration is `✓` and no pointwise condition excludes it: the view at `ℓ₀` agrees
with the owning payload in value, and the callback is in its type
(`Fig16.LogRel.ViewWitness.f_den`).  It is refused only by the view's agreement with the
owning payload's type, a fact about how the borrow was made.
`Fig16.LogRel.ViewWitness.excluded`: no `TW` world holding `ρ₁ ● ρ₂` has `ρ₁` in
`𝒱X⟦Imm 'b T₁⟧` at its list, because

1. `CohE` names a record of type `T₁` at `ℓ₂`, or a chain position of one
   (`Fig16.LogRel.ViewWitness.tyEq_T₁`);
2. either way `ℓ₀` is a chain position at pointee `Ref 1 ⊗ 1`;
3. `Fig16.LogRel.Typed.DeepInv` requires the view at `ℓ₀` to have that shape, and its witness
   `∅` does not (`Fig16.LogRel.ViewWitness.not_vShape_pair_empty`,
   `Fig16.LogRel.ViewWitness.chain_refuses`).

So `Fig16.LogRel.Typed.fundamentalProperty` holds with no hypothesis.  6.150's chooser needs
a witness's typing only at the observable view, which the world's first-order data determine
(`Fig16.LogRel.Typed.obs_transfer`), so `TW` records no relation fact and mentions only
`Fig16.LogRel.Typed.vShape`.

## Part II — The judgment boxes of [TR] p. 2

### §C.25 `@ρ ⊐ α` is universal over the borrow cells, and `[⊤]P` is the borrow-free restriction

[TR] p. 5 writes the relation as a comparison of `@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ`, with `@own ≜ ⊤`
and `⊓` = `max`, `⊤ ≜ 0` ([TR] p. 4).  As a single strict comparison of that meet it fails at
`α = ⊤` on every borrow-free resource, `∅` included.  [TR]'s proofs discharge it there at an
unrestricted `α`:

- Lemma 6.121 (`↺↦`, p. 32): "it suffices if `@(ℓ ↦ own(v)) ⊐ α`, which holds by
  definition."
- Lemma 6.124 (p. 33): "`@∅ ⊐ α` … hold by definition."
- Lemma 6.107 (`[]↦`, p. 30) is closed "by inspection", with no side condition on `α`.

So `@ρ ⊐ α` constrains the borrow cells only: it is Fig. 16's stratum membership
(`own ↦ True`, `imm ↦ ⊓β̄ ⊐ α`, `mut ↦ β ⊐ α`) over the codomain, `ρ ∈ Res_α`.
`BoCa.Fig16.BoLo.Outlives ρ α` is `ρ.InStratum α` (`BoCa.Fig16.ResU.InStratum`).  `[⊤]P` is
`P` restricted to resources holding no borrow.  The two readings differ only at `⊤` on
borrow-free resources; `BoCa.Fig16.ResU.inStratum_of_atLife` (and
`BoCa.Fig16.BoLo.outlives_of_atLife`) is the direction from the meet comparison.

| Lemma | Status | Lean |
| --- | --- | --- |
| 6.107 (`[]↦`) | `[as printed]` | `BoCa.Fig16.BoLo.box_ptoOwn` |
| 6.121 (`↺↦`) | `[as printed]` | `BoCa.Fig16.BoLo.reborrow_ptoOwn` |
| 6.124 (`↺⌜⌝`) | `[as printed]` | `BoCa.Fig16.BoLo.reborrow_pure`, over `BoCa.Fig16.BoLo.reb_empty` |
| 6.102 (`[]∀`) | restricted to a nonempty index type, per [TR]'s "Suppose X ≠ ∅" | `BoCa.Fig16.BoLo.box_all`; the literal reading is measured at any `ρ` outside `Res_⊤` by `BoCa.Fig16.BoLo.box_all_needs_nonempty` |

`reb_α`'s leading `@ρ ⊐ α` ([TR] p. 5) is read the same way (`BoCa.Fig16.ResU.Reb`).  `⊐` is
strict in both documents ([TR] p. 6, no under-bar beside a `⊒` that has one; [CONF] Fig. 19;
[CONF] §4.4: the modality restricts `P` "to the resources that strictly outlive `α`"); the
reading concerns what it is applied to.  `⊤` is not used as a modality index in either
document, but `[⊤]T` is well formed (`Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined`, [TR] p. 3; 6.163 has no
index bound), and on this reading its denotation is the borrow-free resources.

### §C.26 The typing judgment's box, and the hypotheses `⊧ Δ` and `Δ ⊢ Γ`

On [TR] p. 2 the box for the typing judgment reads `Δ; Γ ⊢ e : T` and nothing more.  The two
boxes beneath it read `Δ ⊢ T   Presumes ⊧ Δ` and `Δ ⊢ T ⊐ @a   Presumes ⊧ Δ and Δ ⊧ @a`.

`BoCa.Derives` is the typing rules as the figures print them; none of its constructors has
a well-formedness premise, and `BoCa.WfTy` is consumed by none of them (definition row 2.19).
`BoCa.DerivesWf` is p. 2's typing rules with p. 2's `Δ ⊢ T` consulted at binders and
eliminated types (`Ty.scopedB`).  The headline results are stated over `DerivesWf`.
`Fig16.LogRel.Typed.FundamentalProperty` is

    ∀ Δ Γ e T, DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T

It takes `⊧ Δ` (as `Δ.Ok`, sufficient, `Lifetime.LifeCtx.sat_of_ok`) and `Δ ⊢ Γ`
(`Ctx.ScopedB`) as hypotheses, which p. 2's typing box does not print; p. 2 prints
`Presumes ⊧ Δ` only on the boxes of `Δ ⊢ T` and `Δ ⊢ T ⊐ @a`.  The proof threads them through
the induction (`Lifetime.LifeCtx.Ok.extend`, `Ctx.ScopedB.allI`, …).  At `adequacy`'s empty
contexts both hold (`Fig16.LogRel.Typed.ok_empty`, and vacuously for `[]`), so `adequacy`
has the typing derivation as its only hypothesis.  C14 records what `DerivesWf`'s `Δ ⊢ T`
supplies at `∀I`.

## Part III — Conventions of the mechanisation

Choices of representation, where the paper leaves a detail open or Lean needs one.  None is
a reading of the paper; where one depends on such a reading, the reading has its own entry.

### G1 `Res` is finite at every depth

`Res_α` and `Res` are both `Loc ⇀ᶠⁱⁿ Cell`, by `BoCa.Fig16.PMap`: a function
`Loc → Option _` with a field saying some list covers its domain (`PMap.finite`).  §12.33 and
D10 argue finiteness at row 2.

### G2 `℘⁺(Life)` as a bounded set

`℘⁺(Life)` is `BoCa.Fig16.LSet`: a set of lifetimes with its least and greatest member, so
`⊓ᾱ` and `⊔ᾱ` are total (`LSet.meet`, `LSet.join`).  An `ᾱ` with no greatest element has no
`⊓ᾱ` (`⊓` is `max`) and satisfies no `⊓ᾱ ⊐ α`; every `ᾱ` meeting the printed side condition is
an `LSet` with the same members and meet.  So `Imm_α` (strata row 4) is the printed set.

### G3 Strata as subtypes of the unstratified carrier

The strata `Cell_α`, `Res_α` are subsets of one set in the paper and distinct types in Lean.
`BoCa.Fig16.Cell.stratumEquiv` and `BoCa.Fig16.Res.stratumEquiv` identify each stratum with
the members of the unstratified type satisfying `CellU.InStratum`/`ResU.InStratum`
(`Cell.toU`, `Res.toU`, `Cell.toU_inStratum`, `Res.toU_inStratum`), and `own`, `imm`, `mut`
take an unstratified resource with its membership proof.  Every definition from the
operations on is stated through this identification, so a clause sharing one `ρ` across two
strata (rows 5.13, 5.15; clauses (2), (3), (5) of 5.16) has one Lean term for it.  Definition
row 5.48 is the membership this presupposes.

### G4 Partial operations as graphs

A partial operation is a graph (a relation single-valued where defined) or a function taking
a proof of its domain, never a total function with a default.  The walks and flattening are
graphs — `BoCa.Fig16.ExW`, `BoCa.Fig16.AgW`, `BoCa.Fig16.ResU.Flat` (`⦇ρ⦈`),
`BoCa.Fig16.ResU.Lower` (`⟦ρ⟧`) — each proved functional (`ExW.functional`,
`AgW.functional`, `ResU.Flat.functional`, `ResU.Lower.functional`).  A statement mentioning a
partial term binds it by its graph, and presupposed definedness is inhabitation.  The
`[about ours: … is its graph (G4)]` tags mark lemmas about the representation itself.

### G5 The reflexive order `⊑`

`⊑` (`BoCa.Fig16.Life.Sqsubseteq`) is the reflexive closure of the strict `⊏` (§12.3); neither
document defines a reflexive order on lifetimes.  The printed definitions stated with it are
`ResU.AtLife`, `BoLo.ptoImm` and `BoLo.ptoMut`; `[as printed]` lemmas stated with it include
`BoLo.box_antitone`, `BoLo.ptoImm_antitone` ([TR] 6.114) and `BoLo.ptoMut_antitone`.

### G6 The walks' comprehension as a family indexed by locations

The walks' iterated `⨀`/`◯` range over a family indexed by locations (§12.36).  The index set
is `BoCa.Fig16.ResU.Sites`, the locations of `ρ` carrying a cell of a given tag, each once;
`ExW` and `AgW` compose one summand per location.

### G7 `ρ ≤ ρ′` (not a convention)

Printed: [CONF] p. 415:24, footnote 1, `BoCa.Fig16.ResU.Le` (§12.37).

### G8 Equality of locations is decided classically

`Loc` is abstract and its equality is decided classically, so `ℓ ↦ ψ`
(`BoCa.Fig16.ResU.single`), domain subtraction, and everything stated at them depend on
`Classical.choice`; `[DecidableEq Loc]` would add a hypothesis to printed statements.  Rows
5.29–5.31 and [TR] 6.41–6.44 inherit it.

### F1 Partial terms and their definedness

[TR] writes `✓ρ ≜ ⦇ρ⦈ defined`; `ex(ρ)` and `ag(ρ)` are partial likewise.  All three are graphs
(G4), and `✓ρ` is `BoCa.Fig16.ResU.Valid`, inhabitation of `ResU.Flat` (definition row 5.23:
*"definedness of a graph is inhabitation of it"*).  `ResU.Lower` carries `⟦ρ⟧`'s `✓ρ` guard in
its existential.  Where a printed step applies a partial term (`ag(ρ)` in
`ag(ρ_f) ▷◁ ag(ρ)`, `ag(ρ|dom(ρ′ᵢ|imm))`) whose definedness no printed hypothesis delivers,
the statement carries the graph's inhabitation (e.g. `AgW ρ A`), tagged `[restricted: …]`,
conclusion unchanged: [TR] 6.55 and 6.57 (`ResU.six55`, `ResU.six57`).

### L3 `@aδ` is eliminated, not computed

`BoCa.Lifetime.Life.interp` is `Option`-valued: `@aδ` is undefined when a variable of `@a` is
outside `dom(δ)` ([CONF] Fig. 11: `aδ ≜ δ('a)`).  Neither document says what a clause means
there; the position fixes it:

- As a connective's argument (`[@aδ] P`, `ℓ ↦ Imm @aδ P̂`, `ℓ ↦ Mut @aδ Ŝ`), the clause holds
  of nothing (`BoCa.Fig16.LogRel.atLife`).
- As a quantifier's bound (`∀α ⊏ @bδ.`; [CONF] p. 415:12's `∀α. ⌜α ⊏ @bδ⌝ ─⋆`), the
  quantifier is vacuous and the clause holds of everything (`BoCa.Fig16.LogRel.LtLife`).

[TR]'s proof of 6.161 (p. 42) introduces `α ⊏ @bδ` without establishing that `@bδ` is
defined, which only the `LtLife` reading allows.  Under `Δ ⊢ T` and `δ ∈ ⟦Δ⟧` every lifetime
in `T` is defined (`Lifetime.Life.interp_defined_of_wf`), and `atLife_eq` reduces `atLife` to
the printed clause.

### L4 `dom(Γ)` is the live slots

`Γ` is positional (de Bruijn); `Derives`'s `Ctx` keeps every position and marks a consumed
slot with a liveness bit.  `dom(Γ)` is the live slots: a consumed slot contributes no
conjunct to `⊛_{x∈dom(Γ)}` (`gSep`), and `dom(Γ) ⊆ dom(γ)` is `Ctx.LiveWithin`.  Row 4.13's
printed `⌜dom(Γ) ⊆ dom(δ)⌝` is read as `dom(γ)`, since `δ` maps lifetime variables.

### L5 `γ(e)` is a parallel substitution

`γ(e)` is `BoCa.Expr.psub`, named by `Fig16.LogRel.substAll`.  A fold of `Expr.subst 0`
agrees with it only for closed `γ`, since `Expr.subst` descends into `Expr.val`.  [TR]'s `γ`
ranges over closed runtime values, but `𝒱⟦T⟧δ` does not force closedness (at `1 ⊸ Unk` an
open `λ` satisfies it).  `Expr.psub_cons` peels one value off the front for the §6.8
compatibility proofs.

### W2 Three machines, and what each is for

[TR] §3's reduction is a relation on memories `μ : Loc ⇀ Val` whose `alloc` rule
`(μ, alloc v) ↦ (μ ⊎ ℓ ↦ v, ℓ)` is nondeterministic in `ℓ`.  It is kept on
`BoCa.BoLo.Heap` (`Loc → Option Val`):

- The printed machine: `BoCa.TR3.Kont` (p. 3's seven productions), `BoCa.TR3.Head` (the p. 4
  box, `⊕↦` as two instances), `BoCa.TR3.Step1`, `TR3.Steps`.
- The completed machine: `BoCa.BoLo.Kont` adds `K; e` (`Kont.seq`) and `injᵢ K`
  (`Kont.inj₁`, `Kont.inj₂`); `BoCa.BoLo.Head` has the same nine rules; `BoLo.Steps`
  (§12.42, D6).  `Fig16.BoLo.wp` runs it; `TR3.wp` is the same row over the printed machine.
- The executable interpreter: `BoCa.Mem`, `BoCa.step`, `BoCa.run`, `BoCa.eval`, a
  deterministic total function on association-list memories, allocating at `μ.next`, with the
  same two congruences.

The `wp` development and the adequacy results are stated over the two relations on `Heap`
only.  `Fig16.BoLo.wp_alloc` may choose any fresh location (`PMap.exists_fresh`,
`BoLo.loc_infinite`).  `Adequacy.Theorem32` and `Adequacy.Theorem32Printed` run `BoLo.Steps`
and `TR3.Steps` from `Adequacy.emptyMem`.  No result is stated over the interpreter (D8).

## Part IV — Recorded differences

### C14 The three freshness conditions of `∀I-compat`

`BoCa.Fig16.LogRel.allI_compat` ([TR] 6.161, `[variant: …]`) adds three hypotheses on the
binder `'a`: `@b` does not mention `'a`; no bound of `Δ` mentions `'a`; `'a` is free in no
live type of `Γ`.  They come from p. 42: *"By Δ-extend, `δ['a↦α] ∈ ⟦Δ, ('a ⊏ @b)⟧`"* needs the
first two, *"Extend `𝒢⟦Γ⟧δ` with `δ['a↦α]`"* the third; [TR]'s named presentation gives them by
the Barendregt convention.  `BoCa.Fig16.LogRel.AllISide` bundles them; `BoCa.Derives.allI`
carries only `Δ.find? x = none` (§12.44).

All three follow from [TR] p. 2's `Δ ⊢ T`: `BoCa.Fig16.LogRel.allISide_of_scopedB` (through
`Lifetime.Life.mentions_false_of_wf`, `Lifetime.LifeCtx.Ok.bound_mentions_false`,
`Fig16.LogRel.not_lfree_of_scopedB`, over `BoCa.Ty.scopedB` and `BoCa.Ctx.ScopedB`), and
likewise the `¬ LFree` conjuncts of `Withbor1Side` … `WithloadSide`
(`withbor1Side_of_scopedB` … `withloadSide_of_scopedB`).  `BoCa.DerivesWf.allI` carries p. 2's
`Δ ⊧ @b` beside `'a ∉ dom(Δ)`, so `Fig16.LogRel.Typed.fundamental`'s `∀I` node passes
`AllISide` to `Fig16.LogRel.Typed.allI_compatX` and 6.151 needs no freshness hypothesis.  Over
`Derives` alone the conditions are not supplied: `Fig16.LogRel.witness` is
`∅; • ⊢ λ().() : ∀('a ⊏ 'a). 1`, and `Fig16.LogRel.not_everyDerivationInRegime` is refuted at
it.  `Δ ⊨ @b` is not a fourth condition: by L3 an undefined `@bδ` empties the quantifier.

### D3 The two printed readings of `↭` inside `wp`

[TR] p. 5 prints `↭` guarded by `✓ρ₁ ∧ ✓ρ₂` (`BoCa.Fig16.ResU.UpdV`); [CONF] Fig. 18b
(p. 415:22) unguarded (`BoCa.Fig16.ResU.Upd`).  `BoCa.Fig16.BoLo.wp` is [TR] p. 6's row at the
guarded relation and `BoCa.Fig16.BoLo.wpU` at the unguarded one; they are the same
proposition (`BoCa.Fig16.BoLo.wp_eq_wpU`), since `✓ρ` follows from `ρ_f # ρ`
(`Fig16.BoLo.hash_valid`) and `✓(ρ′ • ρ⁺)` from `ρ⁺ # (ρ_f ● ρ′)` by 6.11
(`Fig16.ResU.Hash.split`).  Away from `wp` they differ: `ResU.Upd.refl` (6.47) needs no
hypothesis, `ResU.UpdV.refl` needs `✓ρ`.  `BoCa.Adequacy.Reclaim` is stated at `UpdV`, and
`Adequacy.reclaim` spends the guard to obtain `⦇ρ⦈`.

### D6 The printed machine and the completed machine

[TR] p. 3's seven `Kont` productions and p. 4's eight rules (`1↦` at the literal `()`) are
`BoCa.TR3.Kont`, `BoCa.TR3.Head`, `BoCa.TR3.Step1`, `TR3.Steps`, and `BoCa.TR3.wp` is p. 6's
`wp` over them.  `BoCa.BoLo.Steps` has the same nine head constructors and two further frames,
`K; e` and `injᵢ K` (§12.42), and nothing else differs; `(v₁,v₂)`, `injᵢ v`, `store v` are one
term each (§12.43).

Without `injᵢ K`, `inj₁ e` takes no step (`TR3.no_step_inj₁`); without `K; e`, `e₁; e₂` steps
only at `e₁ = ()` (`TR3.step_seq_inv`, `TR3.no_step_seq`, `TR3.steps_seq_ne_val`).  Closed
witnesses typed by p. 2:

- `TR3.stuck_wInj` at `inj₁ (free (alloc ()))`, typed at `1 ⊕ T` by `TR3.derives_wInj`.
- `TR3.stuck_wSeq` at `(free (alloc ())); ()`, typed at `1` by `TR3.derives_wSeq`.

Over the printed machine [CONF] Corollary 3.3's conclusion is not reached for the second
(`TR3.corThree_unreachable`); at `wp`, `TR3.wp_inj₁_false` and `TR3.wp_seq_false`, at an
admissible frame (`TR3.wp_stuck_false_nonvacuous`).  [CONF] Fig. 1 prints `e₁; e₂` as its own
production and [TR] p. 4 prints `1↦` as its own rule.  The primitives need no frame: `alloc v`
and `store ℓ v` are applications (`TR3.steps_alloc`, `TR3.steps_store`).

`TR3.Steps.toWp` puts the printed relation inside `BoLo.Steps`; `TR3.wp_le_fig16` carries it
to the `wp`s, strictly (`TR3.wp_lt_fig16`).  Every §6.7 rule, 6.135–6.149, is proved over both
machines (`TR3.wp_bind` … `TR3.wp_I_forget`).  6.136–6.145 have no `wp` in the antecedent and
so imply their `Fig16.BoLo` counterparts; 6.135 and 6.146–6.149 have `wp` in the antecedent,
and the two versions are incomparable.  [CONF] Theorem 3.2 likewise (`Adequacy.Theorem32`,
`Adequacy.Theorem32Printed`).

### D8 No bridge between the executable interpreter and the heap relations

No lemma relates `BoCa.Mem`/`BoCa.step` to `BoCa.BoLo.Heap` or either `Steps`.  Nothing in the
`wp` development or the adequacy results depends on the interpreter, so this limits only what
its runs witness (W2).

### D10 `fin` on `Res_α`: the two strata rows

`BoCa.Fig16.Res` (Fig. 16, strata row 2) carries a finiteness mark that neither document
prints at that row; it comes from row 7, `Loc ⇀ᶠⁱⁿ Cell` in [TR].  The declarations are tagged
`[variant: …]` in `Paper/S5_Model/Definitions.lean`; the reading is §12.33, the representation
G1.

## Part V — Adequacy

### §A.1 Neither document prints a proof of Theorem 3.2 or Corollary 3.3

[CONF] states Theorem 3.2 (Adequacy) and Corollary 3.3 in §3.

- [TR]'s §6 has eight subsections, 6.1–6.8, and no appendix; its last result is 6.176, ending
  on p. 49, the last page.  Its four Theorems are 6.64, 6.65, 6.66 and 6.150; nothing is
  numbered 3.2 or 3.3.  It contains no occurrence of "adequacy", "termination", "reclaim",
  "leak", "liveness", "progress" or "safety".
- [CONF] numbers three results, Lemma 3.1, Theorem 3.2 and Corollary 3.3, all in §3, followed
  by *4 A Semantic Model of Borrowing*, which states none.  Its Data-Availability Statement
  reads *"Complete definitions and proofs may be found in our supplementary material [37]"*,
  and [37] is [TR].

[CONF] p. 415:18: *"Additionally, we must show adequacy of the weakest precondition — that it
really does characterize executions that are safe, terminating, and reclaim memory. The next
section develops proofs for these properties"*.  p. 415:23:

> Inspired by Charguéraud and Pottier [5], in order to support `forget` on borrows, the post-condition is only required to hold of a fragment `ρ′` of the post-resource, but the discarded fragment `ρ⁺` must not contain any owned cells. This is essential for the memory reclamation component of adequacy (Theorem 3.2), which insists that owned cells are freed rather than forgotten.

The statements are transcribed and the proofs are ours.  The printed `wp` is a
total-correctness row; at `ρ = ρ_f = ∅` what remains is `BoCa.Adequacy.Reclaim`, where the
p. 415:23 conjunct is spent (`Adequacy.reclaim`).  Each result is stated per machine (W2,
D6): `Adequacy.Theorem32`/`Adequacy.theorem32` over `BoLo.Steps`,
`Adequacy.Theorem32Printed`/`Adequacy.theorem32Printed` over `TR3.Steps`, and
`Adequacy.Corollary33`, `Adequacy.Corollary33Printed`; and at the typed world
(`Fig16.LogRel.Typed.theorem32`, `Fig16.LogRel.Typed.corollary33`).
`Fig16.LogRel.Typed.adequacy` composes Corollary 3.3 with 6.151.

### §A.2a The bare turnstile

Neither document defines `⊨ H` with nothing to its left.  Three printed things fix it:

- [CONF] p. 415:23's *"an unrestricted modality `! P` for propositions that hold with the empty resource"*.
- Fig. 19's `{P} e {Q̂} ≜ !(P ─⋆ wp(e){Q̂})`.
- p. 415:13's `P ⊨ wp(e){Q̂} ⇔ ⊨ {P} e {Q̂}`.

With [TR] p. 6's `emp ≜ ⌜⊤⌝` and `⌜P_Meta⌝(ρ) ≜ ρ = ∅ ∧ P_Meta`, the equivalence holds when
the bare `⊨` means *holds of `∅`*.  `BoCa.Fig16.LogRel.Sem` reads `Δ; Γ ⊨ e : T` the same way
(`BoCa.Fig16.LogRel.sem_iff`), and Theorem 3.2's antecedent `⊨ wp(e){⌜P̂⌝}` is
`wp(e){⌜P̂⌝}(∅)` (`Adequacy.Theorem32`).
