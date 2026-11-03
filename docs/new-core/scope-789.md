# Scope: typing rules for suspension, spawn and join over the tree relation (#789)

Part of #771, row 6. SPEC §62; `structure.md` §6, §7, §11; `conditions.md`. This doc fixes the
rules, the headline statements, the slices and what not to do. No proof work lands until it is
reviewed. Nothing here is checked in Lean unless it cites an existing result by name; every new
name is marked **new**.

Kernel target: `fundamentalT : CDerivesS Δ Γ e j → SemJT Δ Γ e j` over `cerwpT` at the typed tree
world, every rule included, and `adequacyT` to `OrDiverges` for closed programs (§4).

## 1. The central hypothesis, tested

**The hypothesis** (`structure.md` §6, §11): continuation and task types carry lifetimes, and a
continuation or task holding borrows at `'a` is stored only somewhere scoped within `'a`; spawn
takes a scope and join ends it.

**What Core already does.** The storage half is a consequence of rules Core has:
- `U C` has no outlives rule (`VOutlivesR` has no `thunk` case). A κ, a task or a closure is a
  `U` value, so it cannot be boxed, and so cannot leave a lend's callback, whose result is
  `['x] B` (`axWithbor*Ty`, `cbUTy`).
- `[@d] A` outlives `@a` when `a ⊑ d` (`VOutlivesR.box`). BOXED-κ (`effHandleVB`, §28) gives a
  clause `κ : [@d] K` when the handled computation's context and every answer type outlive `@d`
  (`hΓd`, `hSd`). That box is the task's lifetime: `lib/async.bc`'s `Task[A]` is
  `box top U (ν…)`, and `spawn_in` boxes at the meet of the lifetimes in scope.
- A row is a type in `Δ`: each operation's `A`, `B` mention only lifetimes bound at the handle,
  and a callback's row is chosen outside its `∀'x`, so it never mentions `'x`.

So a stored κ or task outlives exactly the lifetimes its type says: none at `U`, those `⊒ d` at
`[@d]`, where BOXED-κ has checked every borrow it holds **from outside** the handled computation
against `@d`. The handler is inside every lend of `Δ`, so an unboxed κ never leaves any of them,
and a boxed one leaves only those below `@d`.
What row 6 adds is the inside: with T1 (§19) lifted, a stop happens under lends the handled computation
opened itself (lifetimes not in `Δ`). Those lends' records are owned by the stopped branch
(`O`, `oc`; capture keeps them, `contShareT`), so they do not constrain where κ goes. The
semantic reading of `U` and `[@d]` must say so: at the tree, `[@d] A` holds a resource whose
owned records, folded back, leave it in `Res_d` (the **stop lemma at the tree**, `stopLemmaT`,
**new**, not checked; today's `stop_lemma` assumes no lend open at a stop).

**The table.** Each field of `OpEntT` (`Core/TreeWpEff.lean`) and each open condition, and what
supplies it. "Signature" means the operation's declared `OpSig`, copied into the entry by
`OpSig.entT` (§2.1).

| Field / condition | Supplied by | Verdict |
|---|---|---|
| `q` | signature: `(o.entT δ).q = o.q` by definition | supplied, not by the hypothesis |
| `abort` | signature: `o.abort = (B = 0 ∧ q ≠ lin)` | supplied, not by the hypothesis |
| `PA` | `𝒱T⟦o.A⟧δ`, `[perform]`'s premise `V : o.A` | supplied for lifetimes named in `A`. **Not supplied** for a lend opened inside the handled computation: a payload of type `U C` can carry that lend's cells to the handler, which may then cancel κ (ending the lend) while holding them. Needs its own condition: `Row.Across`'s payload clause (§2.6) |
| `PBv` | `𝒱T⟦o.B⟧δ`; at an answer binder `∃β ⊏ δ(b). 𝒱T⟦o.B⟧δ[h↦β]` (§2.1) | supplied by the signature. The payload argument of `PBv` is never read by a typed entry; **remove** it, or keep it constant |
| `fin` | the cancel row `o.fin` read as `finObl` reads it today, at `capB o.q o.B` | supplied by the signature and `[then]`/`[let-dtor]`'s `hfin` (§27) |
| `fd` | none per operation. Types do not supply it (`not_fdFromLifetimeTypes`, `not_fdFromThunkTypesT`). It is the uniform `fdJoinT` (the frame holds nothing at the masks of the records the resumed run owns), discharged inside `[handle]`'s proof from what the frame learns at the stop (`twp_bind_fd`, branch `si-781d`, for a top-level scheduler only) | **not supplied by the hypothesis**; fixed to `fdJoinT` and **removed** as a per-entry field. Its discharge for every typed handler is the riskiest step (§6) |
| `oc` | `oc _ O := (o.q = unr → O = [])`. At an unrestricted stop nothing live: `[let]`'s `hU`, and `Row.Across`'s no-`unr` clause under a lend | needs its own condition (condition 1); it is the existing `hU` plus `Row.Across` |
| 1. no `unr` while a borrow or owned resource is live | `[let]`'s `hU : Σ.Unr → !Γ₂` (exists); `Row.Across` (new) under a lend; `contShareT`'s first clause | supplied by typing (`hU` + `Row.Across`) |
| 2. where κ resumes | `extFT` in `contShareT`; R4 (#781 slice (c)) | relation, not typing |
| 3. `PA ∈ Res_A`, `PB ∈ Res_{↓A}` / `Res_A` | `PA`: `Row.Across`'s payload clause gives `VOutlivesLe Δ bnd o.A`, so `vC_outlivesLe`'s strata. `PB`: the answer's lifetimes are `Δ`'s or an answer binder's, above the lend after the graft (`graft_mono`) | `PA` needs its own condition; `PB` expected from the graft, **not checked** |
| 4. `PA`/`PB` stable along `Ext` | `kmono` of `𝒱T` at `o.A`, `o.B` | a lemma (condition 11, #782), not a condition |
| 5. `withswap` with a suspending callback | none | **not supplied**; `withswap` keeps its pure callback (§2.6) |
| 7. `[handle]` without `hdv` needs `hE` | `contShareT`'s `unr` clause (the share empty) with `hU` | expected supplied, no premise; **not checked** |
| 9. the `Div` tick table | `tick : 1 ↠^lin 1`, an ordinary must-resume entry; `Row.Across` admits it | supplied by the signature |
| 11. `𝒱`/`𝒞` for every type | slice S2 (§6), needs #782 | gap |
| 16. store types at the codes | `KTy` has `unit sum imm mut box ref` only. `withbor2` at `A = U C` (a `mut` lend of a cell holding a task) needs a code for `U C`, read at the step index | gap; #782 must deliver it, or S2 does (§6) |
| 18. lifetime terms read as `max`/`min` on `ℕ`, `LifeCtx.Models` | every rule that reads `Δ.EntailsLt`/`EntailsLe` | gap: `LifeCtx.ModelsT` (**new**) at a cactus, in S2 |
| 20. the cactus invariant carries the proofs | `[handle]` and capture (S4) | relation |
| 23. the resume condition at every type | = `fd` above | as `fd` |
| Closing: entry qualifier = declared | `Row.tabT_q` (**new**, by definition) | supplied |
| Closing: rule across closeable points | `[let]`'s `hW`, `[let-dtor]`'s `hds`, the lend's finaliser `d` (§2.7) | supplied by existing premises |
| Closing: `lin`-paused branch strictly linear | `kTy … lin` ends in `⊤` (`kappa_lin_strict`); no rule eliminates `⊤`; a task built from it has no `close` component and no `HasDtor` case | supplied; the lemma for every value containing a `lin` κ is **new** (`strict_of_lin`) |

**Bottom line.** The hypothesis holds for what it claims, where κ and tasks may be stored, and
Core already enforces it; it needs no new type former. It does **not** supply `fd`, the payload
restriction under a lend, or the ban on unrestricted operations under a lend. The smallest
principled additions:
1. `fd` fixed to `fdJoinT` (removed from the entry), discharged in `[handle]`'s proof;
2. `Row.Across Δ bnd Σ` on the lend rules: non-abortive operations not `unr` at any depth, and
   payloads outlive `bnd`. It is the hypothesis applied to payloads: a value crossing to the
   handler is stored by the handler, outside the lend, so it must outlive the lend. κ is the one
   value exempt, because it owns the records of the lends it crosses;
3. answer binders on `OpSig`, for an answer lent by the handler after the stop (§2.1).

## 2. The rules

### 2.1 Operation signatures

`OpSig` today: `n i q A B fin rc`. Lifetimes may already occur in `A`, `B` (`CFree` reads them at
`.eff`); the refusal of a lifetime on a `ctl` operation is the surface checker's, not Core's.

- **Lifetimes of the handle's scope.** An operation's lifetimes are bound at the handler: surface
  `effect Pass { ctl pass<'b>(m: mut 'b i32) -> mut 'b i32 }` elaborates to the effect `Pass['b]`,
  instantiated where it is handled, so `pass : Mut 'b I32 ↠^cancel Mut 'b I32` with `'b ∈ Δ`.
  A lifetime chosen per perform is refused: with `'b` instantiated at a lend opened inside the
  handled computation, a clause could keep the payload `Mut 'c`, cancel κ (which ends `'c`) and
  then write through it (argued, not checked).
- **Answer binders** (**new** field `ab : Option (LifeVar × Life)`): `A ↠^q ∀'h ⊏ @b. B`, an
  answer at a lifetime the clause chooses when it resumes, below `@b`, `b ∈ dom Δ`. It types a
  handler that answers a borrow it opened after the stop.
- The qualifier is `o.q`, as today (`Qual`).

The entry (**new**, `Row.tabT S δ n i := (Row.find S n i).map (OpSig.entT δ)`):

    OpSig.entT δ o = { q := o.q, abort := o.abort,
      PA  := 𝒱T⟦o.A⟧δ,
      PBv := fun _ => (o.ab = none ⇒ 𝒱T⟦o.B⟧δ | o.ab = (h, b) ⇒ ∃β ⊏ δ b. 𝒱T⟦o.B⟧δ[h↦β]),
      fin := if capB o.q o.B then finObl o.fin δ (at the tree) else none,
      fd  := fun _ => fdJoinT,
      oc  := fun _ O => o.q = .unr → O = [] }

**How κ is resumed at an answer binder** is the one typing choice this doc leaves open. The κ's
first component takes the answer directly (no unit argument), so its type cannot be the explicit
`CTy.all` (whose `[]` is an application to `()`; `allE` would resume κ with `()`). Options:
(a) a Curry-style lifetime `∀` on computations, `CTy.allC x b C`, introduced and eliminated on the
same term (as `!E` and `[]E` are); (b) a dedicated rule for `(force κ).1` at an instance. (a) is a
new former and is general; (b) adds no former. Recommendation: (a). Not checked.

### 2.2 `[perform]` and `[perform-let]`

`[perform]` (`effPerform`) keeps its statement. At an answer binder the answer's lifetime scopes
over the rest, so perform and its `let` form one rule (**new** constructor `effPerformL`, on the
existing term `M to x. N`):

    Γ = Γ₁ ⋈ Γ₂   Σ(n.i) = A ↠^q ∀'h ⊏ @b. B   q, B non-abortive   Γ₁ ⊢ V : A
    Δ, 'h ⊏ @b; x : B, Γ₂ ⊢ N : F_Σ C     'h ∉ Δ, Γ₂, Σ, C
    Σ.Cancels → Γ₂ own-free      Σ.Unr → !Γ₂
    ───────────────────────────────────────────────────────────────
    Γ ⊢ perform n.i V to x. N : F_Σ C

```lean
| effPerformL {m Δ Γ Γ₁ Γ₂ V N} {S : Row} {o : OpSig} {h : LifeVar} {b : Lifetime.Life} {C : VTy}
    (hsi : m = .si) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hf : Row.find S o.n o.i = some o)
    (hab : o.ab = some (h, b)) (hna : o.abort = false) (hac : o.rc = false)
    (hx : Δ.find? h = none) (hC : ¬ VFree h C) (hΓ : ∀ s ∈ Γ₂, ¬ VFree h s.ty)
    (hSh : ∀ o' ∈ S, ¬ VFree h o'.A ∧ ¬ VFree h o'.B)
    (hW : S.Cancels → Γ₂.OwnFree) (hU : S.Unr → Ctx.Banged Γ₂)
    (hV : CDerivesM m Δ Γ₁ V (.val o.A))
    (hN : CDerivesM m (Δ.extend h b) (⟨o.B, true⟩ :: Γ₂) N (.comp (CTy.effOf S C))) :
    CDerivesM m Δ Γ (.app (.val (.lam N)) (BoCa.BoLo.performE (opArgE o.n o.i V)))
      (.comp (CTy.effOf S C))
```

### 2.3 `[handle]` without `hdv`

`effHandleV` and `effHandleVB` keep their statements except that `hdv` (the handled row has no
`Div`) is asked only of the total mode (§2.8); `effHandleT` and `effHandleL` have no `hdv`:
`(hdv : m = .tot → Row.divB (Row.ofEff n E 0 fs cs ++ S) = false)`. `kTy` and `clauseTy` read
`ab` (§2.1). No premise is added: what the relation needs of the clauses (where κ resumes, `fd`)
comes from `cerwpT` and the masks, not from the program (§1).

### 2.4 Continuation and task types

No new former. A continuation is `kTy S R q B F` (§19, §27), boxed at `@d` by BOXED-κ. A task is
codata over a κ, a library type (`Task[A]`, `lib/async.bc`). Their lifetimes are those of their
row, answer, result and box; §1 says why that is enough for storage. Their meaning at the tree is
`𝒱T` at `U` and `[@d]` with the stop lemma (§1).

### 2.5 Spawn and join (derived)

Spawn and join are library handlers and need no constructor, as `[let-dtor]` is `[then]`:
- **`[scope]`** opens a lifetime `'d` with no cell: `withbor1` on a fresh `alloc ()`, freed after.
  Its callback's result `['d] B` is what ends the scope.
- **`[spawn]`**, `with spawn_in 'd { M }`, is `effHandleVB` at the library's `spawn` handler, box
  `@d`: `Γ_M ⊐ @d`, the answers of `M`'s row `⊐ @d`, giving `Task_d A = [@d] U(ν…)`.
- **`[join]`** is not a rule. A `Task_d` does not outlive `'d` (`[@d] A ⊐ @d` needs `d ⊑ d` and its
  borrows `d ⊏ ·`; the scope's result needs `⊐ @d`), so every task is resumed to its end or
  cancelled before `'d`'s callback returns. A task paused at a `lin` point has no `close`
  component, so it is resumed or joined, not dropped.

Semantically a spawned task is a stored branch (`cactusT_spawn`, `cactusT_move` at capture); a
join is its resume to the end, and the lend's end after it is valid by R3
(`r3_joinEndNeedsFdEsc`, `fdEsc_at_join`).

### 2.6 Lend, reborrow and Anti-Frame across stops

The unwinding forms `withbor1U`, `withbor2U`, `withbor3U` (reborrow and Anti-Frame), `withloadU`,
`sliceBorrowMU`, `sliceBorrowIU` keep their terms, types and finaliser `d`. Their row premise
`hS : S.Unwind x` becomes:

    (hS : S.Across Δ Δ.meetOfDom) (hT : m = .tot → S.Unwind x)

```lean
/-- **new**: a row a lend may be live across. Every operation named; a non-abortive one not
unrestricted at any depth of its cancel rows; every payload outliving the lend's bound. -/
def Row.Across (Δ : LifeCtx) (bnd : Lifetime.Life) (S : Row) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ (o.abort = false → o.q ≠ .unr ∧ ¬ o.fin.FinUnr) ∧ VOutlivesLe Δ bnd o.A
```

`Row.Unwind x → Row.Across Δ bnd` (every operation abortive; `VOutlives → VOutlivesLe`), so each
existing constructor is an instance. The finaliser `d` stays pure, so no cancel row records it.
At a cancelling row a cancel of κ runs `d` on the source (§2.7). `withswap` keeps its pure
callback (condition 5). `withbor1`…`withload` (the pure-callback forms) are unchanged.

### 2.7 Closing a branch

- **The entry's qualifier is the declared one:** `Row.tabT_q : Row.tabT S δ n i = some en →
  ∃ o, Row.find S n i = some o ∧ en.q = o.q` (**new**, `rfl`-level).
- **Across a closeable point** (a row that `Row.Cancels`) every live value is persistent or has a
  destructor: `[let]`'s `hW`, `[let-dtor]`'s `hds`, `effPerformL`'s `hW`, and for a lend live
  across the point its finaliser `d : Ref A ⊸ 1` (or `Mut @a A ⊸ 1`), already a premise of every
  `…U` form. Unchanged.
- **A `lin`-paused branch is strictly linear:** `kappa_lin_strict` for κ; for any value holding one,
  `strict_of_lin` (**new**): a type with a `kTy … lin` component reachable outside a `!` has no
  `DropOk` and is not persistent. Typed programs therefore never close it.

### 2.8 The mode index

The total relation proves termination and cannot have the new rules (§62, `structure.md` §8). So
the judgment gets an index (**new**): `inductive Mode | tot | si`, `CDerivesM : Mode → …`, with
`abbrev CDerives := CDerivesM .tot` and `abbrev CDerivesS := CDerivesM .si`. A premise that only
the total relation needs is asked as `m = .tot → …`; a new rule asks `m = .si`. Every existing
statement keeps its text; each induction over `CDerives` (`CDerivesAt`, `CDerivesP`, `Tied`,
`PinDerives`, totality) gains the new cases, impossible at `.tot`. `CDerives.toS : CDerives Δ Γ e j
→ CDerivesS Δ Γ e j` (**new**). Not checked: that `abbrev` keeps dot-notation and `cases` working
on existing proofs.

## 3. What stays and what changes in Core

| Kind | Rules | How |
|---|---|---|
| Kept, statement unchanged | every value, CBPV, `!`, box, borrow-axiom, array, slice, integer, fold, `ν`, `μ`, `effSub`, `effPerform`, `effAwait`, `effRaise`, `effLet`, `effThen(Div)`, `letPoly` | each re-proved at `SemJT` (S3, S4) |
| Generalised | `effHandleV/VB` (`hdv` at `.tot` only); `withbor1U/2U/3U`, `withloadU`, `sliceBorrowMU/IU` (`Row.Across`, `Unwind` at `.tot`); `OpSig` (`ab`, default `none`); `kTy`, `clauseTy` (read `ab`) | at `.tot` and `ab = none` the old premises and types exactly |
| New | `effPerformL`; `CTy.allC` (if option (a)) | `.si` only |
| Replaced | none | |

Every existing theorem keeps its statement: `fundamentalC`, `adequacyC`, `adequacyD`,
`resourceSafety`, the totality results stay on the total relation at `.tot`.

**World-building sites that move from `TW` to the tree world** (the `TW` constructors Core's
compatibility proofs build, and their counterparts in `TWNT`):

| `TW` site | Files | Tree counterpart |
|---|---|---|
| `alloc`, `free`, `store` | `Wp`, `ArrayWp`, `Blocks` | `TWNT.alloc/free/store` (and `Core/TreeHeap`, branch `si-781d`) |
| `immFrame`, `immEnd`, `mutFold`, `mutUnfold` | `FrameRules`, `EffWp`, `Compatibility` | the same constructors of `TWNT` |
| `reb`, `rebDeep`, `rebEnd`, `rebEndDeep` | `Reborrow`, `Images` | `TWNT`'s, canonical images (`canonTc`, `canonDTc`), premises at one record (`RebRecLeT`, `RebEndRecT`, `RebCellLeT`) |
| `empty` (adequacy) | `Fundamental`, `Demonic`, `Totality`, `EffCancel`, `EffCancelRuns`, `DivRuntime`, `DivReify`, `DelayNaive`, `Stale` | `w₀`, `topAdequacyT` |
| readers `TW.inv`, `TW.valid`, `TW.linLife` | `RelationFacts`, `Invariant`, `Wp`, `Reborrow` | `twnt_invHolds`, `TWNT.mutOne`, `TWNT.noOwnUnder` |
| new: `reread` | none today | at every tree growth: graft, a fresh lend |

`TW` itself stays for the total relation (open question 1, §8).

## 4. Headline statements

Does not elaborate: the names marked new do not exist.

```lean
/-! Row 6 of #771: the fundamental theorem over the tree relation, and adequacy. -/

/-- **new**: `𝒞` at the tree. A computation at `F_Σ A`: at every index, world, list, owned records
and frame condition the context admits, the term at `cerwpT` at the row's table, its values at
`𝒱T⟦A⟧`. `⊸`, `&`, `⊤`, `∀`, `ν` as `cC` reads them. -/
def cT : CTy → Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → LSub → Expr →
    TRes w.K → Prop  -- defined in S2 (§6)

/-- **new**: `Δ; Γ ⊨ e : C` at the tree. -/
def SemCT (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ (n : Nat) (w : TWd) (δ : LSub) (γ : List Val) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (ρ : TRes w.K),
    Δ.ModelsT w.K δ → gDenT n w ls δ Γ γ ρ → cT C n w ls O δ (substAll γ e) ρ

abbrev SemVT (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy) : Prop := SemCT Δ Γ e (.ret A)

/-- **new** -/
def SemJT (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .val A => SemVT Δ Γ e A
  | .comp C => SemCT Δ Γ e C

/-- **new**: every rule, the new ones included, at the tree relation. -/
theorem fundamentalT {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesS Δ Γ e j) : SemJT Δ Γ e j

/-- **new**: a closed well-typed program is safe or diverges: every reachable configuration steps
or is a value, a value only at the empty memory, every `free` finds its cell. From
`fundamentalT` at the empty row (`Row.tabT [] δ = OpTabT.empty`) and `topAdequacyT`. -/
theorem adequacyT {e : Expr} (h : CDerivesS LifeCtx.empty [] e (.comp (.ret .unit))) :
    OrDiverges (ℍ := ℍ) e

/-- **new**: the same at a persistent answer, as `adequacyD_obs`. -/
theorem adequacyT_obs {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerivesS LifeCtx.empty [] e (.comp (.ret A))) : OrDiverges (ℍ := ℍ) e

/-- **new**: every derivation of today's judgment is one of the new judgment. -/
theorem CDerives.toS {Δ Γ e j} (h : CDerives Δ Γ e j) : CDerivesS Δ Γ e j
```

| Name | Status |
|---|---|
| `cerwpT`, `opTableT`, `OpTabT`, `OpEntT`, `contShareT`, `twp`, `TWd`, `TWNT`, `SRecT`, `FrameRecT`, `TRes`, `OrDiverges`, `topAdequacyT`, `CDerives`, `SemJ`, `fundamentalC`, `adequacyC`, `adequacyD_obs`, `kTy`, `OpSig`, `Row.Unwind`, `VOutlivesLe`, `kappa_lin_strict` | exist on main |
| `fdJoinT`, `SchedOKT`, `cerwpT_schedHandle`, `twp_bind_fd`, `Core/TreeHeap` | exist on `si-781d` only |
| `Mode`, `CDerivesM`, `CDerivesS`, `CDerives.toS`, `OpSig.ab`, `Row.Unwind.across`, `CTy.allC`, `effPerformL`, `Row.Across`, `OpSig.entT`, `Row.tabT`, `Row.tabT_q`, `vT`, `cT`, `gDenT`, `LifeCtx.ModelsT`, `SemCT`, `SemVT`, `SemJT`, `stopLemmaT`, `strict_of_lin`, `fundamentalT`, `adequacyT`, `adequacyT_obs` | new |

## 5. Worked checks (by hand)

Rule names as in §2; `Σ` rows written as sets. Each derivation is at `.si`.

### 5.1 A `mut` borrow handed between two suspended tasks (`pingpong-mut.bc`)

Effect `Pass['b] = { pass : Mut 'b I32 ↠^cancel Mut 'b I32 }`. `'b` is the lend `main` opens:
`withbor2U slot (Λ'b. λm. body)`, `Δ₁ = Δ, 'b ⊏ @⊓Δ`.

1. **`fill`**, under `Δ₁`: `pass m : F_{Pass['b]} (Mut 'b I32)` by `effPerform` (found, `B ≠ 0`,
   unmarked). The rest by `effLet`: `Pass` cancels, so `Γ₂` own-free; `Γ₂ = {n, i : I32}`. ✓
   `m` is linear: it is the payload, and the answer rebinds it. A relay that tried to hand `m` to
   both tasks fails at `Ctx.SplitP` (one slot, two uses). ✓
2. **`stepper`** (`effHandleV`, no `hdv`): the clause for `pass` gets `m : Mut 'b I32` and
   `κ : kTy S R cancel (Mut 'b I32) = U((Mut 'b I32 ⊸ F_S R) & F_S 1)` (`S` the handler's outer
   row), and answers `inl (m, thunk νin⟨λm₂. κ.1 m₂, κ.2⟩)`, a
   `Step['b, A] = U(ν X. (Mut 'b I32 ⊸ F_S((Mut 'b I32 ⊗ U X) + A)) & F_S 1)`. ✓
   The `& F 1` component is κ's cancel component; at `lin` it would be `⊤` and the clause would
   not type (`kappa_lin_strict`), so `pass` must be `cancel`.
3. **`relay`** and the callback: `Step['b, ·]` is a `U` type, so it never leaves `'b`'s callback;
   `relay` answers `I32`, which outlives `'b`, so the callback's result `['b] I32` is a `boxI`. ✓
   The callback's row is `{Exhausted (abortive), tick (lin)}`: `Row.Across` holds (no `unr`,
   payloads `1`/closed). Today `Row.Unwind` refuses `tick` (`Row.Unwind.divB`). ✓ at `.si`.

This program holds no lend across a stop: `'b` is opened outside the handler. So also:

**1b. A lend held across `pass`.** `fill` lends a scratch cell around each `pass`:
`withbor2U tmp (Λ'c. λt. … m ← pass m; … t …)`, `d = λr. free r`. The callback's row is
`Pass['b]`: `Row.Across Δ₁ (⊓Δ₁) {pass}` needs `pass` not `unr` (✓, `cancel`) and
`VOutlivesLe Δ₁ (⊓Δ₁) (Mut 'b I32)`, i.e. `⊓Δ₁ ⊑ 'b` (✓, `'b ∈ Δ₁`). `t : Mut 'c I32` is live
across `pass`, and `Mut` has a destructor (`HasDtor.mut`). The stored κ owns `'c`'s record; when
`relay` cancels `f`, κ's cancel runs `d` on `tmp` (`letDE_cancel_run` shape). ✓ at `.si`;
refused at `.tot` (`hT : S.Unwind x` fails: `pass` is not abortive).

Where the proof, not the typing, can still fail: `𝒱T` at `ν` (monotonicity open, condition 11),
and `fd` at `relay`'s resumes, which are not a top-level scheduler's (§6).

### 5.2 A handler that resumes a task inside its own borrow (`async-handler-lends.bc`)

Effect `Ask = { ask : 1 ↠^lin ∀'h ⊏ @⊓Δ. Imm 'h I32 }` (an answer binder, §2.1).

1. **`task`**, `mine : Imm 'a I32`, `'a ∈ Δ`: `ask () to theirs. copy mine + copy theirs` by
   `effPerformL`: `N` is typed under `Δ, 'h ⊏ @⊓Δ` with `theirs : Imm 'h I32`; `N : F_∅ I32`, and
   `I32` does not mention `'h`. ✓
2. **The clause**, in `Δ`: `c ← alloc 10; withbor1U c (Λ'h. λv. box (κ.1 v)); free c`. Inside the
   callback `Δ' = Δ, 'h ⊏ @⊓Δ`, and resuming at `'h` needs `Δ' ⊨ 'h ⊏ @⊓Δ` (✓, by `Δ'`), through
   `CTy.allC`'s elimination (option (a)). κ's result `I32` is boxed at `'h` (✓). The callback's
   row is the handler's outer row `∅`: `Row.Across` ✓.
3. **The run.** The task stopped at `ask` under no lend of its own; the clause opens `'h`, a child
   of the handle point, and resumes κ inside it: a graft (`graft_mono`), the share re-read at the
   grown tree (`contShareT_resume`). The resumer's frame holds `c`'s cell in `'h`'s escrow; κ owns
   no records, so `fdJoinT` asks nothing (`recMask [] = ∅`). ✓

The original program reborrows the handler's `mut` state `imm`, which Core has no rule for (SPEC
§62, earlier gaps); the variant above uses a cell of the clause's own. Without answer binders
(open choice, §2.1) only the variant with the lend opened at the handler's installation types.

### 5.3 Refusals

1. **A task stored past its lifetime.**
   `t ← withbor1U r (Λ'a. λv. box (spawn_in 'd { await (); copy v }))`; `resume t`.
   `spawn_in 'd` needs `v : Imm 'a I32 ⊐ @d`, i.e. `d ⊏ 'a`. The callback's result `['a] Task_d`
   needs `[@d] … ⊐ @a`, i.e. `'a ⊑ d`. Both hold only if `Δ` has no model; the `boxI` premise
   `CtxOutlives Δ' Γ 'a` fails. With the unboxed `spawn` (`effHandleV`), the task is `U(…)`, and
   `VOutlivesR` has no `thunk` case. **Refused** at `boxI`.
2. **An unrestricted operation under a lend.** `withbor2U r (Λ'x. λm. choose (); …)` with
   `choose : 1 ↠^unr Bool`: `Row.Across` fails at `o.q ≠ .unr`. **Refused** at `hS`.
3. **A payload that carries the lend out.** Under `withbor2U r (Λ'x. λm. …)`, `send (thunk (modify m))`
   with `send : U(F 1) ↠^cancel 1`: `VOutlivesLe Δ (⊓Δ) (U (F 1))` has no derivation (no `thunk`
   case). **Refused** at `hS`. Boxing the payload at an outer lifetime, `send : [@b] U(F 1) ↠ 1`
   with `b ∈ Δ`, types only a thunk that holds nothing of `'x`.

## 6. Slices

Each leaves main green; none is replaced later; none has an assumed-fact hypothesis.

| Slice | Lands | Done when | Size |
|---|---|---|---|
| **S1 Typing** | `Mode`, `CDerivesM` with the `abbrev`s, the generalised constructors, `OpSig.ab` (default `none`), `Row.Across` and `Row.Unwind.across`, `effPerformL`, `CTy.allC` (if (a)), `Row.tabT_q`, `strict_of_lin`, `CDerives.toS`; every induction over `CDerives` extended | every existing theorem builds with its statement unchanged; the §5 derivations as Lean terms; the §5.3 refusals as theorems (`¬ CDerivesS …` where feasible, else the failing premise refuted) | 1.5–3k |
| **S2 Semantic types** | `vT`, `cT`, `gDenT`, `OpSig.entT`, `Row.tabT`, `LifeCtx.ModelsT` (condition 18), monotonicity at every type, codes for every `VTy` incl. `U C` at the step index | each defined; downward closed and monotone along the tree at every type | 3–6k, on top of #782 |
| **S3 Plain rules at the tree** | compatibility of every rule with no stop: CBPV, `!`, box, borrow axioms, arrays, slices, folds, `ν`, `μ`; the `TW` sites of §3 at `TWNT` | each kept constructor's lemma at `SemJT` | 15–25k (Core's `fundamentalC` closure is 56 files, 35k lines) |
| **S4 Effects at the tree** | `cerwpT` with abortive stops and forwarding (`structure.md` §3, items 1 and 4); `[perform]`, `[perform-let]`, `[raise]`, `[await-c]`, `[let]`, `[then]`; `[handle]` at every typed handler (clauses that store κ, lend, resume inside a lend, forward), `fd` by masks; `stopLemmaT` for BOXED-κ | each effect constructor's lemma at `SemJT` | 6–10k |
| **S5 Lends across stops** | `…U` forms at `Row.Across`, as instances of capture (condition 20); Anti-Frame (`withbor3U`) | each lemma at `SemJT` | 3–5k |
| **S6 Headlines** | `fundamentalT`, `adequacyT`, `adequacyT_obs`; the §5 programs through `adequacyT`; SPEC §62 and `conditions.md` updated | §4 proved, axioms ⊆ the three | 1–2k |

S3 and S4 split further by rule family if needed; S5 needs S4's capture. S1 can land first:
it only types, and claims nothing for `.si` until S6 (the checker must not target `.si` before).

**The riskiest step: `[handle]` at `cerwpT` for every typed handler (S4).** `si-781d` proves it for
a top-level scheduler whose clauses meet `SchedOKT` semantically and hold no lends. A typed clause
is arbitrary code: it may store κ in data, resume κ inside a lend it opens (5.2), resume a κ that
another clause stored (5.1's `relay`), or forward. For each, `fdJoinT` must follow from the masks
the frame learns at the stop (`twp_bind_fd`), across a clause whose own run opens and ends lends.
If the masks cannot be carried through arbitrary clause code, `fd` needs the cactus invariant as
a resource of the handler's state, and `twp`/`EndT` change (scope-781 §5): every rule of
`Core/TreeWp*.lean` would be re-proved. Second in risk: codes for `U C` at the step index (S2),
which the typed tree world does not have and which every `mut` lend of a cell holding a closure
needs. Third: abortive stops at `cerwpT` (S4), which change the relation slice (b) proved rules
for.

## 7. Not doing; tempting shortcuts → stop and report

- A condition added to make one program pass. `Row.Across`'s clauses each trace to §1's table;
  a new one needs a row there.
- A second relation for the new rules, or a second typing judgment. The mode index records which
  of two properties (termination, safety) is claimed, as `structure.md` §8 allows; the rules are
  one inductive.
- A hypothesis standing in for an open item: `fd` discharged per program, `SchedOKT`-style
  semantic premises on a typed handler, the stop lemma or monotonicity as a premise of
  `fundamentalT`.
- A per-entry `fd` or `PBv` chosen by a program.
- A done-when counted in corpus programs. The §5 programs illustrate; a variation of each must
  pass too.
- Restricting programs (no lends across stops, segmentation) to dodge S4.
- `withswap` across stops, per-perform lifetime polymorphism, multi-shot continuations over
  borrows: out of scope, refused by the rules above.
- Connectors and their laws, the binary relation, session types, one codata former (#771's scope
  line).

## 8. Unsettled (for review)

1. **`TW`'s replacement.** #771 records the tree world as a staged replacement of `TW`. The total
   relation must keep `adequacyC`'s termination, which the step-indexed relation does not give. So
   either `TW` stays as the total relation's world, or the total relation is re-based on `TWNT`,
   whose codes would then need the total relation's interpretation (`TWNT` parametrised by its
   code interpretation). This doc keeps `TW`; replacing it is a slice after S6, not sized.
2. **Answer binders:** option (a) `CTy.allC` or (b) a κ-specific rule (§2.1).
3. **The mode index** against an alternative: new constructors only, with the total results taking
   a predicate "uses no new rule". The index keeps every statement's text; the predicate does not.
4. **Payloads under a lend:** `Row.Across` asks `VOutlivesLe` of every operation of the row,
   including those no stop under this lend reaches. A per-stop reading would be finer and is not
   needed by any §5 program.
