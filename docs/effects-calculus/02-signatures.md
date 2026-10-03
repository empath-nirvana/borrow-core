# 02 · Signatures, rows, names, models and comodels

This section fixes the algebraic syntax of the effect calculus: what an effect signature is, how
signatures combine into rows, what a name is and how it is scoped, how a row is interpreted as
the one operation table every semantic definition reads, what an equation of a signature is, how
names are renamed, and the syntactic form of the two implementations of a signature, a model (a
handler) and a comodel (a capability). It uses the objects of `00-structure.md` §1 verbatim and
owns K-SIG, K-ROW, K-NAME, K-INT, K-THEORY, K-REN, K-MODEL and K-COMODEL.

Everything here is syntax plus one interpretation function. The relation that reads the
interpretation (`opTable`, `ewp_W`, `𝒱`, `𝒞`) is 05's; the typing rules that mention rows are
03's; the laws are 06's. Where a definition here must be read at the world `W`, it is stated with
the value relation as a parameter, so it is one definition at every `W` and reduces to today's
kernel at `σ = []` by T-NIL (OQ-11).

Marks are those of 00 §0.1. Literature claims are **[via #235]** (the literature study posted on
#235, "Linear effect algebras: the laws, the literature, and borrow-core", which marks its own
claims [P] for a passage read), **[via 12-sources]** (`docs/effects-tr/12-sources.md`, with that
document's marks), or **[I]** (an inference made here, not a literature claim).

---

## 1. Judgement forms owned here

```
Δ ⊢ E sig                 E is a well-formed signature in lifetime context Δ
Δ ⊢ Σ row                 Σ is a well-formed row
Σ ⊑ Σ'                    row inclusion
Σ₁ # Σ₂                   disjoint names; Σ₁ ⊕ Σ₂ is defined exactly when Σ₁ # Σ₂
⟦Σ⟧δ : OpTab              the interpretation of Σ at the lifetime substitution δ
g(Σ) : Grade              the grade of a row (§3)
π · X                     the renaming of names in X (a row, type, term, context, heap, derivation)
Δ; Γ ⊢ H : Model(n:E ⇒ A; Σ; C)        H is a model of n:E for a body answering A, its
                                          clauses performing Σ, at carrier C
Δ; Γ ⊢ c : Comodel(n:E; S @ 'l; Σ')    c is a comodel of n:E on state S lent at 'l, its
                                          co-operations performing Σ'
```

The last two are derived judgements over `CDerives` (`Core/Fundamental.lean:60`), not new
judgements of the kernel: each unfolds to typing premises on values. 00 §1 lists each under
O-SIG, O-ROW, O-QUAL, O-MODEL and O-COMODEL.

---

## 2. Signatures

### K-SIG: effect signature

- **Form.**

  ```
  E  =  { op_i : A_i ↠^{q_i} B_i }_{i ∈ I}        I finite, |I| ≤ 2^32
        optionally with equations Eq(E)           (K-THEORY; OQ-22)

  A_i  the parameter of op_i   (what perform_{n,i} sends; a value type)
  B_i  the arity of op_i       (what the continuation receives; a value type)
  q_i  the continuation qualifier, a grade (O-QUAL, §3)

  op_i is abortive   ⟺   B_i = 0  ∧  q_i ≠ lin
  ```

  Well-formedness:

  ```
  for every i ∈ I:
    Δ ⊢ A_i val      Δ ⊢ B_i val      q_i ∈ {lin, aff, unr}
    A_i, B_i closed in type variables  (Cl 0)
    op_i abortive  ⟹  Drop(A_i)                       (R-NOOWNERR, OQ-24)
    [Closed E only under OQ-35 (a); none by default]
  ─────────────────────────────────────────────────────────── [sig]
  Δ ⊢ { op_i : A_i ↠^{q_i} B_i }_{i ∈ I} sig
  ```

  **Reading.** `op : A ↠^q B` is the generic-effect presentation of an algebraic operation with
  parameter `A` and arity `B`: `perform_{n,i} V : F_Σ B` is the generic effect, and the algebraic
  form `op(v; y.M)` is `perform_{n,i} v to y. M`. The two are inter-definable (Plotkin & Power,
  ACS 2003; Møgelberg & Staton, LMCS 2014, §8.1.1 [via #235, L1b, marked P there]); in the
  linear setting Møgelberg & Staton's Thm 8.1 adds a third equivalent form, the state access
  operation `B·S → A₁·S ⊕ … ⊕ Aₙ·S` [via #235, L1b], which is the comodel form of §10. An
  operation with several continuation branches is an operation whose arity is a sum
  (binary choice is `choose : 1 ↠^{unr} 1 ⊕ 1`).

  **What parameter and arity types may be.** Any value type of O-TY, subject to the premises
  above. In particular:

  - *Higher-order operations.* `A` or `B` may be `U C` for any computation type `C`, including
    `U(F_{Σ'} A')` and `U(A' ⊸ F_{Σ'} B')`: an operation may send an effectful thunk to its
    handler, and a handler may answer one. As built, `VTy.Cl` holds at every thunk
    (`Core/Types.lean:380`), so `EffLeaf`'s closedness premise (`Core/Types.lean:1141-1144`) does not
    restrict thunks; and `⟦Σ⟧` is defined by structural recursion on the type, because `A` and
    `B` are direct subterms of the layer `CTy.eff n i q A B C` (`Core/Types.lean:92`) that the
    relation's clause reads (`Core/Relation.lean:165-169`). A row cannot mention itself: there are
    no recursive computation types at a row, so a signature cannot contain its own row in an
    operation type. That excludes every operation whose parameter or answer performs its own
    effect (`spawn : U(F_{n:Async ⊕ Σ} 1) ↠ 1`, `fork`, an `ask` answering a computation of the
    same effect). It is the named restriction **R-NOSELFROW**, the default of OQ-61, not a
    property of the calculus: the full construct, a signature binder `μe. E` with `e` occurring
    positively in parameters and `⟦μe. E⟧` the least fixed point of the table functional, is
    K-SELFROW (03 §9.12); occurrences in answers are negative and are OQ-61 (c). A handler that
    returns its own continuations is the negative recursion of OQ-31.
  - *Operations that take computations as arguments in the scoped sense* (`catch(M₁; M₂)`, an
    operation whose argument computations are delimited by the operation, for which algebraicity
    does not hold) are a different thing from an operation with a thunk parameter. Decision 57
    puts them out of scope (`docs/decisions.md`, decision 57, last bullet but one); they are
    OQ-12, default R-FO. Their full form, with its signature, typing, step reading, model entry
    and law, is K-SCOPE (03 §9.1, not adopted); the part that cannot be specified yet is OQ-59.
    An operation with a thunk *parameter* is algebraic and is in the calculus as built.
  - *Borrowed types.* `A` or `B` may be `Imm @a T`, `Mut @a T` or contain them, at lifetimes of
    the handler site's `Δ`: the row's operation types are fixed where the row is introduced
    (`effHandle` types the body at the same `Δ`, `Core/Fundamental.lean:367-372`), and the
    interpretation reads them at the handler's `δ` (`OpSig.ent`, `Core/EffRules.lean:43-44`). A
    borrow of an outer lender passed to a handler is therefore in the calculus as built. An
    answer that is a borrow at the handler's **own** extent is OQ-29 (default R-NOBORANS), which
    needs a handler extent (OQ-3); its full form is K-BORANS (03 §9.4). At a borrow **callback**
    the row is the borrow's result row, outside the lend's scope, so an operation type there may
    not mention the lend's variable; whether it may be lifetime-polymorphic instead is OQ-56
    (default R-CLOSEDOP, 03 K-BOR).
  - *Abortive parameters* hold nothing owned: `effRaise` requires `Drop A`
    (`Core/Fundamental.lean:348-351`) and `opTable`'s abortive branch requires `NoOwn` of the
    argument (`Core/EffDefs.lean:168-172`). This is R-NOOWNERR (OQ-24).
  - *A linear operation at answer `0`* (`B = 0`, `q = lin`) is not abortive (`OpSig.abort`,
    `Core/EffRules.lean:40`): its clause receives a `κ` whose resume branch can never be taken
    and which has no cancel branch. It is well-formed and useless; no rule excludes it.

- **Uses.** O-SIG, O-TY, O-QUAL.
- **Today.** `OpSig` is one operation keyed by `(n, i)` (`Core/Types.lean:147-152`); there is no
  object for a whole signature. `[handle]` carries an effect's operations as
  `E : List (Qual × VTy × VTy)` and builds its keys with `Row.ofEff n E 0`
  (`Core/EffRules.lean:969-972`), so the `j`-th operation has index `j` and
  `hlen : E.length ≤ 2^32` (`Core/Fundamental.lean:371`) keeps indices in `UInt32`. The frontend
  has a separate, string-named `EffSig` (`Frontend/Elab/Effects.lean:57-61`) whose kind is fixed
  per effect (`EffSig.answering`, `:63`). No equations anywhere. Status **changed**: a signature
  becomes one object, grouped per effect, with optional equations; the per-operation record is
  kept as the row's entry.
- **Slices.** typing of `perform`/`raise` (03, K-OP, K-RAISE); clause types (§9 here, K-MODEL);
  co-operation types (§10, K-COMODEL); interpretation (§6, K-INT); laws (06, L-GEN, L-HCORR).
- **Depends on.** O-TY.
- **Open.** OQ-35 (closedness in lifetimes), OQ-12 (R-FO), OQ-22 (equations), OQ-24
  (R-NOOWNERR), OQ-29 (R-NOBORANS), OQ-31 (closed operation types as a cut-off), OQ-61
  (R-NOSELFROW).
- **Obligation.** *Mechanical:* the grouped signature is a re-presentation of `List (Qual × VTy ×
  VTy)`; `[sig]`'s premises are the conjunction of what `EffLeaf`, `effRaise` and `effHandle`
  already demand. The step most likely to be non-mechanical is OQ-35: adding a lifetime
  closedness premise changes which derivations exist.

---

## 3. Qualifiers as grades (O-QUAL)

The qualifier of a continuation is a grade of the semiring of `experiments/Grades`: an interval
`[lo, hi]` of use counts over `{0, 1, ∞}` (`experiments/Grades/Grades/Algebra.lean:58-60`,
`lo`/`hi` at `:68-76`), with `+` and `·` on the endpoints and containment as the order
(`:98`). Every semiring law and monotonicity is proved by `decide` (`:120-137`).

| `q` | grade | interval | `κ` may be dropped (`droppable`, `:107`) | copied (`copyable`, `:110`) | `κ`'s type (`kTy`, `Core/EffRules.lean:976-980`) |
|---|---|---|---|---|---|
| `lin` | `linear` | `[1,1]` | no | no | `U((B ⊸ F_Σ R) & ⊤)` |
| `aff` | `affine` | `[0,1]` | yes, by its destructor (L-W) | no | `U((B ⊸ F_Σ R) & F_Σ 1)` |
| `unr` | `unrestricted` | `[0,∞]` | yes | yes | `!U((B ⊸ F_Σ R) & F_Σ 1)` |
| `rel` | `relevant` | `[1,∞]` | no | yes | OQ-17 (default: not provided) |

`[0,0]` (`erased`) is never a continuation qualifier: an operation whose continuation is never
used is abortive, and that is expressed by `B = 0`, not by a grade.

**The grade of a row.** For a row `Σ`,

```
g(Σ)  =  ⊔ { q_op | op ∈ Σ }          (join in the containment order; g(∅) = [1,1])
```

Over `{lin, aff, unr}` the order is a chain (`order_facts`, `Algebra.lean:141-144`), so the join
is a maximum. With `rel` present, `aff ⊔ rel = unr`. `Algebra.lean` defines no join; it is a
finite function over five grades, decided like every other fact there (mechanical).

**`[let]`'s side condition is a grade condition.** `effLet` (`Core/Fundamental.lean:353-358`)
asks of the context `Γ₂` that the continuation captures:

```
hW : Row.Weak Σ → Γ₂.Drops          Row.Weak Σ  ⟺  g(Σ).droppable    (Core/EffRules.lean:705)
hU : Row.Unr Σ  → Persistent Γ₂     Row.Unr Σ   ⟺  g(Σ).copyable     (Core/EffRules.lean:708)
```

with `Ctx.Drops` (`Core/EffRules.lean:858`) and `Persistent` (`Core/Relation.lean:235`). The
pair is, slot by slot, `Grade.ok (g Σ) (Drop T) (isBang T)` (`Grade.ok`, `Algebra.lean:115-116`),
which is `experiments/Grades`' endpoint type condition at the profile whose droppable types are
`Drop` and whose persistent types are `!`-types (`Profile`, `experiments/Grades/Grades/Context.lean:51-63`).
This is the row-level (coarse) form of graded algebraicity: the context of the rest of the
computation is checked at the worst qualifier of the row, whether or not that operation is
performed. The per-operation form is L-ALG (06); the rule that carries the grade is K-GRADE (03).

**What `experiments/Grades` covers.** The semiring, graded contexts, and the equivalence of a
graded judgement with `CDerives` (`cderives_iff_graded`,
`experiments/Grades/Grades/Judgment.lean:349`; `fundamentalG`,
`experiments/Grades/Grades/Soundness.lean:327`), for the fragment that predates effects: the
constructors of `GDerives` (`Judgment.lean:40` ff.) include no `effSub`, `effPerform`,
`effRaise`, `effLet`, `effThen` or `effHandle`. The graded reading of `[let]` above is therefore
a reading, not a built equivalence. It is part of K-GRADE's obligation (03).

**Literature.** That the `κ` qualifiers are the grade intervals and that `[let]` is graded
algebraicity is the #235 report's inference [via #235, §6, marked I there]. Graded algebraic
theories in the literature grade a theory by effect sorts, without linearity (Kura, FoSSaCS 2020
[via #235, §6, abstract]); a graded monad and a graded comonad are related by graded
distributive laws in Gaboardi, Katsumata, Orchard, Breuvart & Uustalu, ICFP 2016 [via #235, §6,
abstract]. Neither is the structure used here, which grades the use of the continuation.

---

## 4. Names and instances

### K-NAME: names and instances

- **Form.**

  ```
  n, m ∈ Nm  =  UInt32 ∖ {⊥}          ⊥ = 0, reserved for cancel
  π : Nm ⊎ {⊥} → Nm ⊎ {⊥}  a bijection with π ⊥ = ⊥                    (K-REN)

  names(Σ)       the names of the row
  names(A), names(C), names(Γ)   the names in every row occurring in a type or context
  ```

  **Scoping.** `hnd_n H e` binds `n` in the row of `e`: `e : F_{n:E ⊕ Σ} A` and
  `hnd_n H e : F_Σ R` (`effHandle`, `Core/Fundamental.lean:367-372`, with
  `hnS : ∀ o ∈ S, o.n ≠ n`, i.e. `n:E # Σ`). A name is **static**: each site has its own name,
  given by elaboration (SPEC §19 *Names*, `SPEC.md:2404-2419`). `perform_{n,i}` is resolved at
  run time by the nearest enclosing `hnd (n, H)` frame whose context is free of `n`
  (`Head.hop`, `Paper/S3_Dynamics/Definitions.lean:502-506`; `Kont.HasHnd`, `:386-395`).

  **The binder is static, the resolution dynamic.** Since `hnS` makes `n` fresh for the outer
  row, `hnd_n` is a binder of `n` over its body's row, and α-renaming it is K-REN. Resolution
  at run time is by nearest enclosing frame, so the binder is respected exactly when no value
  carrying `n` from outside the site reaches the inside of another site of `n`. Two such cases
  exist:

  1. **Re-entry of one site** (a function containing `hnd_n` called under its own handler):
     an operation inside the inner activation reaches the inner frame, which is the lexically
     correct one. SPEC §19 justifies its soundness by "operation types are closed in lifetimes"
     (`SPEC.md:2418-2419`), a sentence no rule enforces (audit M13, `docs/effects-audit.md:454-463`;
     OQ-35).
  2. **A value carrying `n` passed into another site of `n`.** `effHandle` constrains the outer
     row only; nothing constrains `names(Γ₂)`. A thunk `t : U(F_{n:E} A)` in `Γ₂` forced inside a
     second `hnd_n` with the same `E` is typed (by `[sub]`, since `n:E ⊑ n:E ⊕ Σ''`), sound
     (the operation types agree, because `RowLe` requires the same `OpSig`,
     `Core/EffRules.lean:699`), and its operations are caught by the inner handler: accidental
     handling. The elaborator prevents this by site freshness (R3), which decision 57 states is
     "checked by the elaborator only" and "may move into `[handle]` later as a pure
     restriction" (`docs/decisions.md`, decision 57). This configuration is read off the rules; it
     is not built in Lean. Whether site freshness becomes a kernel premise is OQ-38.

  **Generative instances** (under OQ-14 option (b); default R-STATIC). The calculus with
  generative instances adds one machine step and no new type former:

  ```
  (μ, hnd_ν (n, H) e)  ↦  (μ, hnd (m, H) (m/n)·e)        m ∉ names(μ, e, K), m ≠ ⊥     [new]
  ```

  where `(m/n)·e` is K-REN at the transposition. This is Staton's restriction `νa. x(a)`
  composed with a handler ("with is ν plus a handler", the #235 report's §4 [via #235, I]);
  Staton's four instance laws (idem-ν, ν/ν, ν/op, new-ν; LICS 2013 §IV-V [via #235, L6, marked P
  there]) are L-NU (06). Freshness relative to the configuration makes names a nominal resource
  like locations. Because the heap is leak-free, a name is reusable after its handler ends, and a
  continuation that escapes its handler can meet a reused name (SPEC §19 *Why not generative
  names*, `SPEC.md:2421-2437`). What confines a continuation to its handler's scope is the
  question OQ-14 holds; a lifetime-bounded `κ` (OQ-3 option (a) with OQ-28) is the candidate the
  #235 report names as a hypothesis [via #235, Answers §4, marked "a hypothesis to check"]. SPEC
  §19 records that `[@c] U C` alone is not that confinement, because `[]E` removes the box
  (`SPEC.md:2431-2434`).

  **Entries with extents.** Under OQ-3 option (a), a handler site opens a lifetime `α_n`, and
  each row entry carries it: `n:E @α_n`. A row then has a lifetime `life(Σ) = ⊓_n α_n` (the
  meet; `⊤` for `∅`), as EffModelRel's rows pair each instance with its lifetime and take the
  meet (`Rw`, `Rw.life`, `experiments/EffModelRel/EffModelRel/Syntax.lean:94-109`). That would
  give `U(F_Σ A)` an outlives rule from `life(Σ)` [I], which is OQ-28 option (b). Under the
  default R-MID there is no extent and the annotation is absent (O-ROW).

- **Uses.** O-NAME, O-ROW, O-KONT.
- **Today.** Names are `UInt32` literals at fixed term positions: the payload `(n, (i, v))`
  (`opPayload`, `Paper/S3_Dynamics/Definitions.lean:349`), the handler value `(n, (h_ret, hs))`
  (`hndVal`, `:352`), and the cancel payload's name list (`cancelVal`, `namesVal`,
  `:362-375`). `⊥ = 0` is excluded from rows by `Row.NZ` (`Core/EffRules.lean:702`), from
  handlers by `hn0` (`Core/Fundamental.lean:370`), and from tables by `Row.tab_zero`
  (`Core/EffRules.lean:738`). Status **as built** for static names; generative instances are
  **new** under OQ-14 (b).
- **Slices.** resolution steps (04, K-STEP `[op]`, `[unwind]`; K-CTX `HasHnd`, `Catches`,
  `hndNames`); instance laws (06, L-NU, L-NAH); abstraction (07, T-NAH, T-ABS); elaboration's
  site numbering (08).
- **Depends on.** O-NAME, K-ROW.
- **Open.** OQ-14 (R-STATIC), OQ-3 (R-MID), OQ-28, OQ-35, OQ-38.
- **Obligation.** *Unknown:* whether re-entry is sound with lifetime-open operation types
  (OQ-35); the configuration of case 2 above, to be built in Lean as a typed derivation and a run
  (`def AccidentalHandlingTyped : Prop`, settle by proof). *Mechanical:* the scoping facts are
  read from `effHandle` and `Head.hop`.

---

## 5. Rows

### K-ROW: rows as sums

- **Form.**

  ```
  Σ  ::=  ∅  |  Σ ⊕ n:E                   n ∉ names(Σ), n ≠ ⊥

  as a finite partial function   Σ : Nm × UInt32 ⇀ (Qual × VTy × VTy),
      Σ(n, i) = (q_i, A_i, B_i)  for  n:E ∈ Σ,  op_i : A_i ↠^{q_i} B_i ∈ E

  ──────────── [row-∅]        Δ ⊢ Σ row    Δ ⊢ E sig    n ≠ ⊥    n ∉ names(Σ)
  Δ ⊢ ∅ row                   ─────────────────────────────────────────────── [row-⊕]
                              Δ ⊢ Σ ⊕ n:E row

  Σ₁ # Σ₂  ⟺  names(Σ₁) ∩ names(Σ₂) = ∅
  Σ₁ ⊕ Σ₂  defined iff Σ₁ # Σ₂;  (Σ₁ ⊕ Σ₂)(k) = Σ₁(k) if defined, else Σ₂(k)
  Σ ⊑ Σ'   ⟺  ∀ k, Σ(k) = some o → Σ'(k) = some o
  Σ^abort  =  the restriction of Σ to its abortive operations
  F A      =  F_∅ A
  ```

  **The row algebra.** On well-formed rows:

  ```
  (Σ₁ ⊕ Σ₂) ⊕ Σ₃ = Σ₁ ⊕ (Σ₂ ⊕ Σ₃)        Σ₁ ⊕ Σ₂ = Σ₂ ⊕ Σ₁        Σ ⊕ ∅ = Σ
  ⊑ is a partial order;   Σ ⊑ Σ ⊕ Σ';   Σ₁ ⊑ Σ₁' ∧ Σ₁' # Σ₂ ⟹ Σ₁ ⊕ Σ₂ ⊑ Σ₁' ⊕ Σ₂
  Σ^abort ⊑ Σ;   (Σ₁ ⊕ Σ₂)^abort = Σ₁^abort ⊕ Σ₂^abort;   g(Σ₁ ⊕ Σ₂) = g(Σ₁) ⊔ g(Σ₂)
  names(Σ^abort) ⊆ names(Σ)
  ```

  **The quotient of today's lists.** Today a row is `List OpSig` read by first match
  (`Row`, `Row.find`, `Core/EffRules.lean:33-37`), and only `[then]` requires distinct keys
  (`Row.Uniq`, `:746`; `effThen`'s `hUq`, `Core/Fundamental.lean:361`). The row of this section
  is the quotient of `{S : List OpSig | Row.Uniq S ∧ Row.NZ S}` by "same `Row.find`":

  ```
  ROW-1   Uniq S ∧ Uniq S'  ⟹  ((∀ n i, find S n i = find S' n i) ⟺ S ~ S')     (~ is List.Perm)
  ROW-2   Row.tab S δ depends on S only through Row.find S         (by definition, :47)
  ROW-3   names(S) ∩ names(S') = ∅  ⟹  find (S ++ S') = find (S' ++ S)  ∧  Uniq (S ++ S')
         (from Row.find_append, Core/EffRules.lean:1028)
  ROW-4   every S has a first-match deduplication S↓ with Uniq S↓ and find S↓ = find S
  ```

  ROW-4 is what makes the change conservative: a derivation over non-`Uniq` rows becomes one over
  their deduplications with the same tables (ROW-2). `Row.Uniq` is needed at `[then]` today because
  `Σ^abort ⊑ Σ` fails for a first-match list with a shadowed abortive duplicate:
  `Row.abortOnly_le` takes `Uniq` (`Core/EffRules.lean:760`). With rows as sums the premise is
  part of `⊢ Σ row` everywhere.

  **`[handle]` already forms a sum.** Its body's row is `Row.ofEff n E 0 ++ S` with
  `hnS : ∀ o ∈ S, o.n ≠ n` (`Core/Fundamental.lean:369-372`), which is `n:E ⊕ Σ`; and
  `ewp_handle`'s premise `hTin : ∀ m i, m ≠ n → Tin m i = Tout m i`
  (`Core/EffRules.lean:616`) is the table form of the same sum.

  **`[sub]` is inclusion.** `effSub` takes `RowLe S S'` (`Core/Fundamental.lean:340-342`;
  `RowLe`, `Core/EffRules.lean:699`), which is `⊑` on the quotient. Its compatibility is
  `sub_compatC` (`Core/EffRules.lean:774-778`) through `Row.tab_le` (`:728`) and `ewp_sub`
  (`:159`).

  **A row inside a type.** `F_Σ A` is `CTy.effOf S A`, a chain of one `CTy.eff` layer per
  operation (`Core/Types.lean:155-157`). Two lists with the same `find` give different `CTy`
  terms, so the sum's commutativity is not an equality of types, and `[sub]` applies only at the
  top of a computation judgement, not under `U`, `⊸` or `&`. The relation sees only the table
  (`cC_effOf`, `Core/EffRules.lean:73-76`), so the two types have the same meaning; the question
  is how the typing judgement identifies them. That is OQ-36. Rows are also part of every
  function over types (`instT`, `EffLeaf`, `VFree`, `applyLSub` treat a layer structurally,
  `Core/Types.lean:1135, 1143, 194, 1587`), and each of these is invariant under a permutation of
  the layers of a `Uniq` row (mechanical, one induction each).

  **Qualifier subsumption** (`F_{n:{op : A ↠^{aff} B}} C ≤ F_{n:{op : A ↠^{lin} B}} C`, a
  computation that tolerates a dropped continuation also tolerates one resumed exactly once) is
  not provided: `RowLe` requires the same `OpSig`. Whether it belongs in `[sub]` is OQ-39.

- **Uses.** O-ROW, O-SIG, O-NAME, O-QUAL.
- **Today.** `Row = List OpSig` (`Core/EffRules.lean:33`), first match (`:36-37`), `RowLe`
  (`:699`), `Row.NZ`, `Row.Weak`, `Row.Unr`, `Row.abortOnly` (`:702-711`), `Row.Uniq` (`:746`),
  `Row.find_append` (`:1028`). Status **changed**: a sum with distinct names, replacing
  first-match lists.
- **Slices.** `[sub]` and every rule at a row (03); the interpretation (§6); `TableOK` closed
  under sum (05, T-SUMOK); L-SUM (06); the frontend's row computations (08, §12 here).
- **Depends on.** K-SIG, K-NAME.
- **Open.** OQ-36, OQ-39, OQ-13 (R-NOROWVAR), OQ-18, OQ-3 (extents).
- **Obligation.** *Mechanical:* ROW-1 to ROW-4 and the row algebra, each a list lemma over
  `Row.find`. The step most likely to be non-mechanical is OQ-36's choice: under its option (b) the type conversion must be a congruence through every former, including `∀` and `ν`.

---

## 6. The interpretation of a row

### K-INT: `⟦Σ⟧δ`, and `opTable` as the one interpretation

- **Form.** With the value relation `𝒱` as a parameter (so the definition is one definition at
  every world `W`, OQ-11):

  ```
  ⟦Σ⟧[𝒱]δ (n, i)  =  ⟨q_i, abort_i, 𝒱⟦A_i⟧δ, 𝒱⟦B_i⟧δ⟩    if Σ(n, i) = (q_i, A_i, B_i)
                   =  none                                   otherwise
  abort_i = (B_i = 0 ∧ q_i ≠ lin)

  ⟦Σ⟧δ  =  ⟦Σ⟧[𝒱_W]δ        at the world of 05;   ⟦Σ⟧[vC]δ = Row.tab Σ δ  at σ = []
  ```

  **One interpretation.** Every semantic reading of a row goes through `opTable ⟦Σ⟧δ` (D-OPTAB,
  05). As built, the relation's clause at `F_Σ R` is `ewpTS` at `opTable (effTab (F_Σ R) δ)`
  (`Core/Relation.lean:165-169`), and `effTab (CTy.effOf S R) δ = Row.tab S δ`
  (`effTab_effOf`, `Core/EffRules.lean:49-58`), so `cC (F_Σ R) = ewpTS (opTable ⟦Σ⟧δ)`
  (`cC_effOf`, `:73-76`). A capability's operations are to be checked against the same table
  (K-COMODEL, T-COMODEL); today no table checks them (audit C2, `docs/effects-audit.md:303-312`).

  **Properties stated here.**

  ```
  I-1  Σ ⊑ Σ'          ⟹  ⟦Σ⟧δ ≤ ⟦Σ'⟧δ                  (Row.tab_le, Core/EffRules.lean:728)
  I-2  Σ₁ # Σ₂          ⟹  ⟦Σ₁ ⊕ Σ₂⟧δ = ⟦Σ₁⟧δ ⊎ ⟦Σ₂⟧δ    (disjoint union of partial functions; ROW-3)
  I-3  entries are Kripke along the world order        (Row.tab_local, :733, along Ext; at W: T-MONO)
  I-4  ⟦Σ⟧δ ⊥ i = none                                 (Row.tab_zero, :738)
  I-5  ⟦Σ^abort⟧δ is abort-only                         (Row.abortOnly_abort, :765)
  I-6  ⟦Σ⟧ does not see a lifetime variable x free in no operation type
                                                        (as Row.Unwind.tab_extend, Core/EffBorrow.lean:150, generalised)
  ```

  **The protocol of a sum is not the disjunction of the summands' protocols.** `opTable T` is a
  disjunction over the entries of `T` (`Core/EffDefs.lean:157-172`), but each resuming entry's
  continuation share mentions the whole table: `contShare T en n ls K Φ` owes `cancelOwed T n`
  (`:144-150`), a cancel run at `cancelTab T N` (`:131-135`), whose admissible errors `errOk T N`
  (`:121-127`) are the abortive operations of all of `T`. So an operation of `Σ₁` stopped under
  `opTable ⟦Σ₁ ⊕ Σ₂⟧` owes a cancel run whose finalisers may raise operations of `Σ₂`. I-2 holds
  for the interpretation; `opTable ⟦Σ₁ ⊕ Σ₂⟧` is not assembled from `opTable ⟦Σ₁⟧` and
  `opTable ⟦Σ₂⟧`. This is why `TableOK` closed under sum (T-SUMOK, 05) is a lemma to prove at the
  union, not a consequence of the summands' `TableOK`.

- **Uses.** O-INT, O-ROW, O-TAB, O-REL, O-W.
- **Today.** `OpSig.ent`, `Row.tab` (`Core/EffRules.lean:43-47`); `OpEnt` (`Core/EffDefs.lean:104-109`);
  `OpTab.ext` (`:117-118`), which is first match and is the sum when names are disjoint. Status
  **as built** at `σ = []`. At `W` the entry type `OpEnt`'s `PA`, `PB : List SRec → Val → WProp`
  must take the world's other components; that is D-W's change (05), and K-INT is parametric in
  it.
- **Slices.** `opTable` (05, D-OPTAB); `TableOK` and T-SUMOK (05); the relation (05, D-REL);
  L-SUM (06).
- **Depends on.** K-ROW, K-SIG.
- **Open.** OQ-11, OQ-1 (one table for both implementations).
- **Obligation.** *Mechanical:* I-1 to I-5 exist at `σ = []`; I-2 is a corollary of ROW-3; I-6 is
  `Row.Unwind.tab_extend` without the abortive premise. At `W` each is restated through the
  parameter `𝒱`; the step most likely to be non-mechanical is I-3 at `W`, which is T-MONO (05)
  under OQ-8.

---

## 7. Equations of a signature

### K-THEORY: equations and handler correctness

- **Form.** An equation of `E` is a pair of `E`-terms over a context of parameters and
  continuation variables:

  ```
  Θ ; k₁ : B₁ ⊸^{g₁} X, …, k_m : B_m ⊸^{g_m} X  ⊢  t₁ ≡ t₂

  t ::= k_j(V)  |  op_i(V; y. t)  |  case V of (inl x. t | inr x. t)  |  let (x, y) = V in t
  ```

  `Θ` holds value variables (parameters); each `k_j` is a continuation variable used at the
  grade `g_j`, so a linear theory's equations respect use counts (Staton's two-zoned contexts,
  linear parameters with continuations sharing them additively, POPL 2015 §2 [via #235, L1a and
  L6, marked P there]). `X` is a schematic carrier.

  An `E`-term is interpreted in two ways:

  ```
  in the free model:   op_i(V; y.t)  ↦  perform_{n,i} V to y. t      at F_{n:E ⊕ Σ} A
  in a model H:        op_i(V; y.t)  ↦  h_i (V, ⟨λy. t, cancel⟩)       at the carrier C
  in a comodel c:      the state-access form, op_i(V; y.t) ↦ c_i(s, V) to (s', y). t
  ```

  **Handler correctness.** A model `H` of `(E, Eq(E))` is correct iff for every equation and
  every instantiation of `Θ` and the `k_j` at its carrier, the two interpretations are equivalent
  (L-HCORR, 06; Plotkin & Pretnar, LMCS 2013, Def. 4.5, "in general undecidable" §6 [via #235, L2,
  marked P there]). A comodel is correct iff its co-operations satisfy the equations in
  state-access form (Møgelberg & Staton, LMCS 2014, (8.9) [via #235, L3b]). Both need `≡`
  (OQ-4).

  Every effect of the kernel today is a free theory, so correctness is vacuous (the #235 report,
  L2 [via #235]). The theories 06 must express are state and linearly used state (get/put,
  with commutation at distinct locations), nondeterminism (semilattice laws, only if multi-shot
  is free, OQ-16) and user theories; exceptions and `Yield` are free (L-EXC, L-YIELD).

- **Uses.** O-SIG, O-MODEL, O-COMODEL, O-EQ, O-QUAL.
- **Today.** Not built. Status **new** (OQ-22).
- **Slices.** L-HCORR, L-STATE, L-ND (06); the binary relation (05, D-BIN; OQ-4).
- **Depends on.** K-SIG, K-MODEL, K-COMODEL.
- **Open.** OQ-22 (default (a): the form exists, no kernel theory carries equations until one is
  needed), OQ-4, OQ-16.
- **Obligation.** *Unknown:* the interpretation in a model at an affine or unrestricted
  continuation variable must pass the cancel entry; whether a theory equation can mention
  `cancel` is not settled (it bears on L-ETA, OQ-27). *Mechanical:* the syntax.

---

## 8. Renaming

### K-REN: renaming of names on rows, types, terms, configurations and derivations

- **Form.** For a bijection `π` of `Nm ⊎ {⊥}` with `π ⊥ = ⊥` (finite support is enough):

  ```
  π · ∅ = ∅           π · (Σ ⊕ n:E) = π·Σ ⊕ (π n):(π·E)          π·E renames the operation types
  π · (F_Σ A) = F_{π·Σ} (π·A);  π acts homomorphically on every other type former
  π · Γ        pointwise on slot types
  π · e        at the name positions only:
                 perform (π n, (i, π·V))   raise (π n, (i, π·V))   hnd (π n, π·H) (π·e)
                 the cancel payload (0, (0, (π·N, π·err)))  with π·N the image list
               and homomorphically elsewhere; integer data is not renamed
  π · K        on the frames of an evaluation context, hnd frames included
  π · μ        on every value stored in the heap
  π · 𝒟        on a derivation, rule by rule
  π · W        on the world: (ρ, ls, π·σ), each entry's row R : Nm → Bool renamed to R ∘ π⁻¹
               (D-W); ρ and ls hold no names. The relation half of T-REN is stated at π·W.
  ```

  **Syntactic lemmas owned here.**

  ```
  N-1  π·(Σ₁ ⊕ Σ₂) = π·Σ₁ ⊕ π·Σ₂;  Σ ⊑ Σ' ⟹ π·Σ ⊑ π·Σ';  (π·Σ)^abort = π·(Σ^abort);  g(π·Σ) = g(Σ)
  N-2  (π·Σ)(π n, i) = π·(Σ(n, i))
  N-3  HasHnd (π n) (π·K) = HasHnd n K;   Catches (π n) (π·K) = Catches n K;
       hndNames (π·K) = map π (hndNames K);   (π·K).plug (π·e) = π·(K.plug e)
  N-4  π·(kappa n H K) = kappa (π n) (π·H) (π·K);   π·(cancelVal N err) = cancelVal (π·N) (π·err)
  N-5  π commutes with substitution and shifting on terms whose name positions hold literals
  N-6  Head μ e μ' e'  ⟹  Head (π·μ) (π·e) (π·μ') (π·e')     and likewise Step1 and ARun
  ```

  The consumers are T-REN (07: `CDerives Δ Γ e C ⟹ CDerives Δ (π·Γ) (π·e) (π·C)`, and the
  relation at `W` is equivariant, `𝒱⟦π·A⟧_{π·W} δ (π·v) = 𝒱⟦A⟧_W δ v`), L-REN (06), and through
  them `⟦π·Σ⟧δ (π n) i = ⟦Σ⟧δ n i`. Their corollaries: the elaborator's copies per assignment of
  names (decision 57, "a renaming lemma would let the checker derive once") are α-variants with
  the same meaning, and no accidental handling under site freshness (T-NAH).

  **Names occupy positions, not a sort.** Names are `UInt32` literals at the positions listed
  (`opPayload`, `hndVal`, `cancelVal`, `Paper/S3_Dynamics/Definitions.lean:349-375`), and the
  machine matches the literal `.prim (.lit (.i32 m))` in a handler frame (`Kont.HasHnd`, `:386-395`).
  A typed term always has a literal at a name position (`effPerform`, `effRaise` and `effHandle`
  build `opArgE n i V` and `hndTerm n ir ic e` with literal `n`, `Core/EffRules.lean:696, 997`),
  and the steps that create name positions (`kappa`, `cancelVal`, `errNext`, `Paper/S3_Dynamics/Definitions.lean:373-384, 438-442`)
  create literals. So `π·e` is well defined on reachable configurations, but it is not a
  homomorphism of raw `Expr`: an untyped `perform x` with `x` later bound to a payload would not
  be renamed. N-5 and N-6 need the invariant "every name position holds a literal", preserved by
  every step.

  **Pattern.** `experiments/TwoRun` proves the same shape of lemma for permutations of
  locations: `Expr.rename`, `Kont.rename`, `Heap.rename`
  (`experiments/TwoRun/TwoRun/Rename.lean:29, 269, 288`), `head_rename`, `step1_rename`,
  `steps_rename` (`:359, 410, 419`), excluding array steps because they compute locations. Names
  are never computed (`count_try`'s integers are loop counters, `Support/Dynamics/Arrays.lean:65`),
  so no step class needs excluding. EffModelRel renames its instance context
  (`Val.ren`, `Cmp.ren`, `experiments/EffModelRel/EffModelRel/Rename.lean:32, 43`) on an
  intrinsically typed sibling calculus; it does not transport (OQ-5).

- **Uses.** O-NAME, O-ROW, O-TY, O-KONT, O-JDG.
- **Today.** Not built in Core (audit M13, `docs/effects-audit.md:454-463`). Status **new**.
- **Slices.** T-REN, T-NAH, T-ABS (07); L-REN, L-NAH (06); copies (08).
- **Depends on.** K-NAME, K-ROW.
- **Open.** OQ-13 (copies vs row abstraction), OQ-14, OQ-38.
- **Obligation.** *Mechanical:* N-1 to N-4, each a structural induction. The step most likely to
  be non-mechanical is N-5/N-6's literal-position invariant: it must be stated as a predicate on
  `Expr` preserved by `Step1`, or names must become a syntactic sort of `Expr` (a kernel syntax
  change with a SPEC entry). Either is one induction over the step relation; the first changes no
  definition.

---

## 9. Models

### K-MODEL: the form of a model of a signature

- **Form.** A model of `n:E` for a body answering `A`, its clauses performing `Σ`, at carrier
  `C`, is a pair `H = (h_ret, hs)` of values:

  ```
  Δ; Γr ⊢ h_ret : !U(A ⊸ C)                                              (retTy)
  Δ; Γc ⊢ hs : ⊗_{i ∈ I} clauseTy(op_i)                                  (clausesTy)
     clauseTy(op_i) = !U(A_i ⊸ C)                    if op_i abortive
                    = !U(A_i ⊗ K_{q_i}(B_i, C) ⊸ C)   otherwise
     K_lin(B, C) = U((B ⊸ C) & ⊤)
     K_aff(B, C) = U((B ⊸ C) & C_1)
     K_unr(B, C) = !U((B ⊸ C) & C_1)
  ───────────────────────────────────────────────────────────────
  Δ; Γr, Γc ⊢ H : Model(n:E ⇒ A; Σ; C)
  ```

  with `C = F_Σ R` and `C_1 = F_Σ 1` as built, and `C_1` the carrier's cancel answer in general.
  The clauses are `!` (Tang, Hillerström, Lindley & Morris, POPL 2024, `T-Handler`'s requirement
  that clauses be duplicable at an unrestricted operation [via #235, L2]). An abortive operation's
  clause receives no `κ` (the machine exercises weakening eagerly, `[unwind]`/`[finalise]`). The
  handler is deep: `κ`'s resume branch reinstalls `hnd (n, H)` (`kappa`,
  `Paper/S3_Dynamics/Definitions.lean:438-442`).

  **A model is a handler, and handling is its fold.** A handler of `E` is a model of `E`, and
  handling is the unique homomorphism out of the free model (Plotkin & Pretnar, LMCS 2013,
  abstract, §1, §4 [via #235, L2, marked P there]). The semantic counterpart, `IsModel_Σ Φ` and
  `ewp_handle` as initiality, is D-MODEL and T-MODEL (05). As built `ewp_handle`
  (`Core/EffRules.lean:615-628`) is the fold by induction on the inner least fixed point, with
  the clause obligations as hypotheses `hret`, `hop`; it is a case analysis, not yet stated as
  initiality.

  **Carriers.** Plotkin & Pretnar's handlers go into any computation type, and so do phase A's
  ("handlers into any computation type", #235 phase A summary, PR #237). As built the carrier is
  `F_Σ R` only: `retTy S A R = !U(A ⊸ F_Σ R)` (`Core/EffRules.lean:994`), `clauseTy`
  (`:984-987`), `kTy` (`:976-980`). A state-passing handler is written today with a state passed
  to each clause (decision 59, "a handler whose operations resume has a state … passed to each
  clause and at each resume"), or by a carrier `F_Σ (U(S ⊸ F_Σ R))` that allocates a closure per
  operation (decision 56 names this cost). A carrier `S ⊸ F_Σ R` or `C & D` is the general form.
  Whether `[handle]` takes every carrier is OQ-37; under its default the general form is
  specified and today's carrier is the named restriction R-RETCARRIER.

  **Answering handlers are borrows.** `experiments/HandlersAsBorrows` translates an answering
  handler of System Ξ into `withbor` form (2), the handler's state lent as `Mut 'x S`
  (`translate_typed`, `experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`), with
  effect safety from BoLo's fundamental property (`effect_safety`, `…/Safety.lean:55`), and places
  it in the shift schema (`handle_is_shift`, `…/Safety.lean:115`; `shiftTy`,
  `experiments/Shifts/Shifts.lean:17-20`). That handler is a comodel (§10), not a model; whether
  a control handler (a model) is a borrow the same way, opening a lifetime, is OQ-3.

- **Uses.** O-MODEL, O-SIG, O-KONT, O-QUAL, O-ROW.
- **Today.** `retTy`, `clauseTy`, `clausesTy`, `kTy` (`Core/EffRules.lean:976-994`),
  `hndTerm` (`:997`), `effHandle` (`Core/Fundamental.lean:367-372`), `handle_compatC`
  (`Core/EffRules.lean:1092`). Status **as built** at carrier `F_Σ R`.
- **Slices.** `[handle]` typing (03, K-HND); `κ`'s types (03, K-KONT); `[ret]`, `[op]`,
  `[unwind]` (04); `IsModel`, T-MODEL (05); L-HRET, L-HOP, L-HFWD, L-HUNIQ, L-HFUSE, L-HCORR
  (06); handler schemas and T-ELAB (08).
- **Depends on.** K-SIG, K-ROW, K-NAME.
- **Open.** OQ-37, OQ-3, OQ-16 (`unr`), OQ-17 (`rel`), OQ-25 (handler state), OQ-26 (shallow).
- **Obligation.** *Mechanical:* the form is `clausesTy`/`retTy` re-indexed by the grouped
  signature. *Unknown:* `ewp_handle` at a carrier other than `F_Σ R` (OQ-37): the clause
  obligation `KapRel Tout Qout` (`Core/EffRules.lean:619-621`) is stated at a returner's answer
  relation `Qout`.

---

## 10. Comodels

### K-COMODEL: the form of a comodel of a signature

- **Form.** A comodel of `n:E` on state `S` lent at `'l`, its co-operations performing `Σ'`:

  ```
  for each non-abortive op_i ∈ E:
    Δ; Γ_i ⊢ c_i : !U(S ⊗ A_i ⊸ F_{Σ'}(S ⊗ B_i))
  for each abortive op_i ∈ E:      (no co-operation at Σ' = ∅; see below)
  ─────────────────────────────────────────────────────────────
  Δ; Γ ⊢ c : Comodel(n:E; S @ 'l; Σ')
  ```

  The co-operation acts on the **payload** of the lent cell, not on the `Mut` view: it receives
  the state `s : S` and hands back the new state. The `Mut 'l S` view is held by the capability
  and supplied, at each call, by `withswap`, whose frame over the cell is `[TR]` 6.66 (D-COMODEL).
  This is the type K-CAP's `Cap_l(E, S)` holds (03 K-CAP).

  A **capability** is a comodel lent by a borrow; an operation of the capability is a call of
  `c_i` on the lent state through `withswap`. Its carrier is `withswap`,
  `Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B` (`axWithswapTy`, `Core/Types.lean:1905-1906`; rule
  `withswap`, `Core/Fundamental.lean:254-255`), whose callback is a pure value function
  `A ⊸ A ⊗ B`: so as built `Σ' = ∅` (R-PURESWAP, OQ-20). The elaborated clause is `h__op : mut 'l S × A → mut 'l S × B` run by
  `withswap` (SPEC §18, the answering table, `SPEC.md:2127`), and the handler is
  `withbor` form (2) of the state's cell (`SPEC.md:2128`). Today nothing checks a capability's
  operations against `opTable ⟦n:E⟧`; that is D-COMODEL and T-COMODEL (05), the same protocol
  for model and comodel (TR D4.6, listed new in `docs/effects-tr/12-sources.md` §12.3, item 3).

  **Every qualifier admits a comodel.** A co-operation answers exactly once, now. Each of `lin`,
  `aff`, `unr` contains one use (`live_iff_one_le`, `experiments/Grades/Grades/Algebra.lean:160`),
  so every non-abortive operation, at any qualifier, can be implemented by a comodel [I].

  **Abortive operations have no comodel at `Σ' = ∅` (PP08 in the kernel).** Plotkin & Power,
  MFPS 2008: a theory with a constant has only the empty comodel [via 12-sources, PP08: "Thm 4.4
  and the constant remark [via phase A]"]; the #235 report states the same for exceptions in Set
  [via #235, Answers §3, caveats]. In the kernel the statement is: a co-operation for an abortive
  operation at `Σ' = ∅` would have type `!U(S ⊗ A ⊸ F(S ⊗ 0))`, and `𝒞⟦F(T ⊗ 0)⟧`
  holds of no term at any resource, because `wpTS` is total correctness (`∃ k', ARun …`,
  `Core/EffDefs.lean:36`) and `𝒱⟦0⟧` is `False` (`Core/Relation.lean:123`). At `Σ' ≠ ∅` a
  co-operation may itself raise, a *fallible co-operation*; the effects TR places these exactly
  at weakenable operations, with the failure delivered to the lend (`docs/effects-tr/12-sources.md`
  §12.3, item 8; #245, "Draft TR: PR #248", decisions on phase A's open questions).

  **Which effects can be answering.** An effect can be implemented by a comodel at `Σ' = ∅`
  exactly when it has no abortive operation; with fallible co-operations, also when each abortive
  operation's co-operation raises in `Σ'`. Answering ⊆ algebraic, not equality (the #235 report:
  "the inclusion is answering ⊆ algebraic", Answers §3 [via #235, I]). `Fail` is a model only
  (#245, phase A summary: "constants have only the empty comodel, so Fail is a model only").

  **A comodel is linearly used state.** Møgelberg & Staton translate an effectful function to
  `!A ⊗ S ⊸ !B ⊗ S` over linearly used state `S`, and adding a theory is "necessary and
  sufficient to supply the chosen state type S with the structure of a comodel" (LMCS 2014, §1.1-1.2,
  §8 [via #235, L3b, marked P there]). The co-operation type above is that shape with `S` the
  lent cell. That a borrow with a lifetime is such a state is the #235 report's inference [via
  #235, Answers §3 caveats, I]; `experiments/HandlersAsBorrows` proves it for answering handlers
  of a Ξ fragment, with aliasing of one capability by two closures refused
  (`twoBlocks_refused`, `experiments/HandlersAsBorrows/HandlersAsBorrows/Sharing.lean:196`).

- **Uses.** O-COMODEL, O-SIG, O-TY (`Mut`), O-BOR.
- **Today.** Answering handlers are elaborated (SPEC §18); `withswap` (`Core/Types.lean:1905`,
  `Core/Fundamental.lean:254`); `op_tail`, `handle_fold` as run facts (`Core/Handlers.lean:76,
  211`). Status **new** as a kernel object (OQ-1, OQ-19).
- **Slices.** K-CAP, K-SWAP (03); D-COMODEL, T-COMODEL (05); L-STATE, L-TENSOR, L-INTER, L-TAIL
  (06); T-ELAB, T-LOWER (08).
- **Depends on.** K-SIG, K-INT; the borrow constants (O-BOR).
- **Open.** OQ-1 (default (b): both primitive, one protocol), OQ-19 (default (a): state-access
  semantics only), OQ-20 (R-PURESWAP; the form of a fallible co-operation), OQ-25, OQ-29.
- **Obligation.** *Mechanical:* the PP08 statement in the kernel (one frame satisfying `wpTS`'s
  premises and `𝒱⟦0⟧ = False`). *Unknown:* the type of a fallible co-operation for an abortive
  operation (does it return the state, and what does the lend receive?) and its compatibility at
  `W` (OQ-20 option (c)).

---

## 11. Sum and tensor, and threads

**Definitions** (Hyland, Plotkin & Power, TCS 2006, as restated by Ahman & Bauer, ESOP 2020,
§3.1 [via #235, L4, marked "P, via A–B"]):

- the **sum** `T₁ + T₂` adds no equations: operations interleave freely;
- the **tensor** `T₁ ⊗ T₂` adds commutation of every operation of `T₁` with every operation of
  `T₂`; with a 0-ary operation, commutation becomes absorption. Ahman & Bauer's signals are this
  for the kernel's **state** operations only: `getenv(λc. kill s) = kill s` and
  `setenv(c, kill s) = kill s` (arXiv 1910.11629 §3.1, eq. (1), read in 05 §10); an external
  operation `op ∈ Σ` is related to state by commutation, not absorption. A runner's own signal
  skips the rest of the user code and runs the finalisation clause `kill s ↦ N_s` (§3.2, the text
  after eq. (3); Thm 7, §5.3); only an enveloping runner's signal bypasses the inner finalisation.

Both definitions are confirmed against the primary source: Hyland, Plotkin & Power, *Combining
effects: sum and tensor* (TCS 2006, §1, the authors' copy, read): for the sum, "one has the
operations for each of the two theories, subject to the equations for each of the two theories,
but with no equations relating them"; the tensor "amounts to taking the operations of both
theories and demanding that they commute with each other, while retaining the equations of
both".

**Where each arises in this calculus.**

| combination | where | why |
|---|---|---|
| sum | rows: `Σ₁ ⊕ Σ₂` (K-ROW), the handler's `n:E ⊕ Σ` | distinct static names; forwarding preserves order (L-HFWD); the program's free theory |
| tensor | two comodels on states from disjoint borrows | BoLo separation of the lent cells: the frame rule plus "an answering clause is a direct call" (#245, review input, item 1, "tensor is the frame rule plus …"); the kernel statement is L-TENSOR's unary half (06) |
| a free-theory consequence; whether also a signal is OQ-66 | cancel against the cancelled region's remaining operations | a clause that cancels discards what the body would still perform, which is L-HOP followed by L-W in any free theory (06 L-SIGNAL). Ahman & Bauer's own-runner signal has the same shape (skip the rest, run finalisation); it differs in discarding kernel state and in running one finalisation clause per `run`, where ours runs `D_K`, one finaliser per frame. #235's reading of cancel as a signal (L5-K) is that report's inference [I] |
| sum or tensor, by handling | `Log` and `Fail` in both nesting orders | `Log` outside keeps the logs (`W* × (A + E)`, the sum's model), `Fail` outside validates the tensor equation at arity 0, `log(m; raise e) ≡ raise e` (`E + (A × W*)`, the tensor's model; HPP 2006 as restated by Ahman & Bauer §3 [via #235, L4]); exhibited by `logOutside`, `failOutside` (`Core/EffPrograms.lean:15, 165-173, 220`) |
| sum for borrowed, tensor-with-kill for owned | a capability under an abort | a borrowed capability survives the abort, an owned resource is finalised (#235, L4 [I]); the unwinding borrows realise the first (L-BOR) |

The tensor is therefore not a row operation: rows are sums, and commutation arises from
resource separation between comodels, which is BoLo's frame rule. EffModelRel proves the tensor
for capabilities whose co-operations answer in place (`tensor`, `PureCo`,
`experiments/EffModelRel/EffModelRel/Tensor.lean:27, 91`) on a sibling calculus (OQ-5). That the
product of comodels on separated states is a comodel of the tensor theory is an inference here
[I], not a cited law.

**Threads.** Threads are required eventually; nothing here may close that door (OQ-18). What
each choice above would mean for threads [I]:

- *Rows as sums* do not commit to an interleaving: a sum states that operations of distinct names
  have no equations between them. A scheduler written as a deep handler of a thread effect keeps
  its own continuations in its state, which is the negative recursion R-NONEGREC excludes; a
  scheduler over `Loop_Σ` codata does not (06 L-ASYNC, OQ-60).
- *Tensor between disjoint capabilities* is what licenses two threads holding disjoint `Mut`
  capabilities to run without interference: the same separation that makes the operations
  commute sequentially.
- *Uninterceptable cancel* is what cancelling a parked task would use: the cancelled task's
  finalisers run LIFO (L-W). Whether it is a signal in Ahman & Bauer's sense is OQ-66 (above).
- *Static names* resolve by nearest enclosing frame in one stack; two threads activating one site
  concurrently would have one name for two activations. Threads push towards generative
  instances or a per-thread name space (OQ-14).

**Grades and combination.** `g(Σ₁ ⊕ Σ₂) = g(Σ₁) ⊔ g(Σ₂)` (§3): the sum's grade is the join, so
graded algebraicity at a sum is checked at the worse of the two qualifiers.

---

## 12. Requirement on 08: one row function

The elaborator computes a row twice, with no lemma relating the two (audit §2.2,
`docs/effects-audit.md:144`): by effect name and instance (`rowV`, `rowC`,
`Frontend/Elab/Effects.lean:418, 454`), and by operation key `(n, i)` (`opsC`, `opsV`,
`Frontend/Sugar.lean:2530, 2545`, with `fnRowOf`, `:2478`). The requirement: one function from a
term to its row `Σ` (K-ROW), from which both the instance view and the key view are projections,
and whose output is checked against the kernel's row by `[sub]`. The frontend's `EffSig`
(`Frontend/Elab/Effects.lean:57`) becomes a presentation of K-SIG, and the answering/control kind
moves from the declaration to the implementation (model or comodel, audit §3.1,
`docs/effects-audit.md:183-189`).

---

## 13. Open questions raised by this section

Boxed in [99](99-open-questions.md): OQ-35 (are operation types closed in lifetimes; shared
with 03), OQ-36 (how the typing judgement identifies equal rows inside types), OQ-37 (handler
carriers at every computation type; default R-RETCARRIER), OQ-38 (is site freshness a premise of
`[handle]`), OQ-39 (qualifier subsumption in `[sub]`), OQ-61 (operation types that perform their
own effect; default R-NOSELFROW; shared with 03 and 06).

Carried (00 §8), each cited at the entry it bears on: OQ-1 (K-COMODEL, K-INT), OQ-12 (K-SIG),
OQ-13 (K-ROW, K-REN), OQ-14 (K-NAME), OQ-17 (§3), OQ-19 (K-COMODEL), OQ-22 (K-THEORY), OQ-29
(K-SIG, K-COMODEL), OQ-66 (§11).

---

## 14. Report lists (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed.** None of this section's objects rests on
a printed `[TR]` lemma directly. The interpretation reads `𝒱`, which at a resuming table depends
on 6.150, not lifted at resuming tables (00, T-FRAME); 6.64 and 6.65 at resuming tables live only in
GhostEnd (`ewpTS_M_frameR`, `ewpTS_I_frameR`, per 00 T-FRAME). The borrow constants that carry a
comodel (`withbor` form (2), `withswap`) are the printed constants of `[TR]`, typed as built.

**Printed hypotheses not spent.** None: this section states syntax and the interpretation, and
proves nothing.

**Uniqueness or functionality results not used.** `Row.find_of_mem`
(`Core/EffRules.lean:748`) is the uniqueness fact behind ROW-1 and is used there. Not used:
`ResU.CompS.functional` and the determinism of runs (`head_det_eff`, `Core/Steps.lean:596`);
K-REN's run-level lemma N-6 is stated per step and does not need determinism, but T-REN's
two-run corollaries would, by TwoRun's route (`freshRun_det`,
`experiments/TwoRun/TwoRun/Fresh.lean:255`).

**Claims not derived.** The configuration of §4 case 2, the PP08 statement in the kernel, ROW-1 to
ROW-4, N-1 to N-6 and the grade reading of `[let]` are read from the definitions cited and are not
built in Lean. I have not verified that any obstruction is real.
