# Scope — #804: resource safety for every source program with exceptions

*History: a spike for #804 on the chain world. The current design is `chain-interpretation.md` and SPEC §62. The text below is kept as the record.*

Spike on the chain world (main). Question, yes or no: does every program of a small typed source
fragment with exceptions, in which owned values may be in scope at a raise, translate to a
`CDerives` derivation, so that `resourceSafety` (`Core/ResourceSafety.lean`) holds of every such
program?

**Kernel target.** `resourceSafety` extended to every program of the source fragment, by a
typing-preservation theorem for the consume-glue translation into `CDerives`. No new kernel rule,
and `CDerives` is not changed.

Prior art: Congard, Munch-Maccagnoni & Douence, ESOP 2026 (arXiv 2510.23517), §4.1–4.3. Their
source is resource CBPV, where every positive type has a chosen disposal map (their `drop_A`). Their translation is
**error-passing**: `P⁻ = P⁺ ⊕ E`, a raise unwinds the context (`unwind_Γ`, their `drop` per variable,
with `swap` moving the exception past each one) and injects `ι₂`, and `try` is a `case` on the sum.
Prop 3 says the translation preserves typing into the linear fragment. Thm 4.1 says resource safety
follows from the linear calculus. Their payload `E` is purely positive and resource-free, because
the `swap` needs `E` central (Prop 4). Our contexts have exchange, so that reason does not carry
over. They have no borrows.

**The decision this doc cannot make (§0).** After the coordinator's correction, raised payloads
may hold owned cells. `CDerives.effRaise` does not admit them. §0 states the conflict, gives the
Lean check and lists the routes. §1–§7 are written for route **K** (the kernel's own `[raise]`,
`[then]`, unwinding borrows and `[handle]`, which is what #804 asks about) and say at each point
what changes under the other routes.

---

## 0. Owned payloads and `[raise]`

The correction (#804, 2026-11-04) says the only payload restriction is `Row.Unwind`: the payload
type is not mentioning the lend's lifetime and outlives every lifetime. That excludes borrows and admits
owned cells. `Row.Unwind` does admit `Ref I32`. Checked:
`Row.Unwind [exnOp 7 (.ref (.int .w32))] x`.

But `CDerives.effRaise` (`Core/Fundamental.lean:520`) has a second premise, `hd : o.A.OwnFree`.
`VTy.OwnFree` (`Core/EffRules.lean:1086`) admits data, borrows, `!`, `Unk` and the host opaques,
and **not** `Ref`. Checked: `¬ VTy.OwnFree (.ref (.int .w32))`, by `cases`. SPEC §19 *Unwinding*
gives the reason: "If a finaliser raises during an ordinary unwind, the new unwind supersedes the
pending one: the pending `raise (m, v)` is in the finaliser's continuation and is abandoned … So
an operation that raises must have an argument that consumes with nothing owned." Lint records the
same site (SPEC §12: "`abandon` … at a superseded raise payload (`effRaise`'s `hd`)").

So under route K, a source raise of an owned payload has no `[raise]` derivation through
`effRaise`. Whether some other `CDerives` route types such a raise is **not derived, and the
obstruction is not verified**. `Inversions.der_raiseJ` says every derivation of a raise is
`effRaise` followed by the same-term rules, but its `RaiseBase` omits `hd`, so it does not settle
the question. The claim is stated as an elaborating `def`, `OwnedRaiseTypable : Prop`, in
`~/repos/scratch-archive/804/Checks.lean`. It is neither proved nor refuted.

The routes, for the user to decide:

| route | what it is | payload | uses `[then]`/`withborU`? | kernel change |
|---|---|---|---|---|
| **K** | the kernel's own exceptions: `raise` to `[raise]`, `try` to `[handle]`, glue to `[then]` and `withborU` | `OwnFree ∧ Row.Unwind`: data, `!`, ints, host opaques | yes, the question #804 asks | none |
| **K+cell** | K, where an owned payload is stored into a cell the `try` lends (`Mut` through the body), and the raise carries `()`. After the `[handle]` and the end of the lend, the `try` reads the cell and runs the exception arm on the owned value. | anything `Row.Unwind` admits | yes | none, but every computation under a `try` with an owned payload gets the lend's `Mut` threaded or reborrowed (`withbor3U`) around each head that may raise |
| **E** | their route: error-passing into sums. `F_Σ A` becomes `F (A ⊕ P)`, a raise becomes "consume the rest, `return (inr v)`", a `let` becomes a `case`, `try` becomes a `case`, and a borrow callback answers `['x](B ⊕ P)` through the *pure* `withbor` | anything `Row.Unwind` admits (the box `['x]` needs exactly its two conditions) | no: the glue is §12's ordinary consumes in the `inr` arms | none |
| **K′** | relax `effRaise.hd`, e.g. only where no enclosing finaliser's row raises | owned | yes | yes: a NOT-do here, and a re-proof of `then_compatC` |

Trade-offs:
- **K** answers #804 as filed. The fragment then excludes owned payloads, against the correction.
- **K+cell** keeps the kernel's machinery and admits owned payloads. The translation is much
  larger, since every head that may raise is wrapped in a reborrow of the cell's `Mut`. The risk is
  R1b (§5).
- **E** is the shortest route to "resource safety of every source program, owned payloads
  included", and it is the prior art's own translation. It tests none of the kernel's exception
  rules. SPEC §18 decides that errors are a control-flow effect at the surface; E is a translation,
  not a surface feature, but it does take the kernel's `[raise]` out of the theorem. Under the
  effect-erasure decision, "abort = branch" is what the IR does anyway.
- **K′** is outside this spike.

**Decided (user, 2026-11-04): route K.** The source typing's payload condition excludes owned
payloads: `ExnRow` asks `o.A.OwnFree` of every exception operation, which `ownFreeB` decides
(fallback condition C1, here a premise). Relaxing `effRaise.hd` is a separate kernel question,
for later. Its reason is SPEC §19 *Unwinding*: a finaliser that raises during an ordinary unwind
supersedes the pending raise, whose payload is then abandoned, so a raised payload must hold
nothing owned. A relaxation would have to rule out that supersession, for example by excluding
abortive operations from the row of every finaliser between the raise and its handler, and would
re-prove `then_compatC`. §8 records what was built.

---

## 1. The source fragment

### Types

The source uses the kernel's `VTy`/`CTy` directly, under a predicate, so that typing preservation
keeps `Γ` and the judgment unchanged. The fragment:

- **values** `A ::= 1 | I32 | A ⊗ A | A ⊕ A | Ref A | Imm 'a A | Mut 'a A | !A`;
- **computations** `F_Σ A`, where `Σ` is an **exception row**;
- an **exception operation** is `exnOp n P = ⟨n, 0, cancel, P, 0, F 1, false⟩`: name `n ≠ 0`,
  index 0, qualifier `cancel` (never `unr`: `EffCtx.NoUnrExn`, and `[then]`'s `UnrD` stays false),
  answer `0` (so `OpSig.abort = true`), empty cancel row, unmarked;
- **`ExnRow Σ`**: every operation is an `exnOp`, the names are distinct (`Row.Uniq`), and every
  payload `P` is closed: mentioning no lifetime variable and outliving every lifetime. This is
  `Row.Unwind`'s condition at every `'x`, which is what lets a raise leave any borrow. Under K,
  `P.OwnFree` as well (§0).
- thunks appear only as a borrow block's callback, which is syntax, never a variable.
- excluded: `0` as a value type (no `absurd`), `⊤`, `&`, `μ`, `ν`, arrays, closures as values,
  `Div`, the cancellable and unrestricted qualifiers' resuming operations, and `Tok`/declared
  types. Every type that is in the fragment is `Consumable` (`Consumable.ref`, `.imm`, `.mut`,
  `.bang`, `.tensor`, `.sum`, `.int`, `.unit`), so the translation never meets group 3 (§12).

The hardest case stays in: `Ref` content is any fragment type, owned values may be live in the
callback and outside it, and borrows are `Imm` lends of an owned `Ref`.

### Where owned values may sit at a raise

Anywhere in the context. At a `raise` and across a `let` whose head may raise, every live slot the
abort abandons is at a fragment type. The fragment's types are all `Consumable`, so the source rule
needs no separate premise, and the premise is recorded as `Ctx.ConsumableLive Γ₂` (every live slot
`Consumable`) for when the fragment grows. Normal paths are linear: the source writes its own
consumes there. §12's end-of-path insertion is already proved (`consumeSlot_derives`) and is not
part of this spike.

### `raise` and `try`

The existing abortive effect plus its handler: `raise n V` is the kernel's `[raise]` at `exnOp n P`,
and `try_n M with (x. N_ret) (e. N_exn)` is `[handle]` (`effHandleV`) at `E = [(cancel, P, 0)]`.
Why: `resourceSafety` is stated at `F A` with an empty row, so every source program ends in handled
exceptions, and the kernel's handler is the rule that removes a name from a row. There is no kernel
`try` to target, and a new one would be a new rule.

`[handle]` asks its handler value to be a value form over a context whose live slots are
persistent (`effHandleV.hd : Ctx.DeadP Γ₁`). So `N_ret` and `N_exn` see only their binder and
persistent slots, and the source rule asks the same. Under E, `try` is a `case`, and both arms may
use the linear context additively.

### Borrows

One borrow block: `borrow V as m in M`, where `V : Ref A`, `m : Imm 'x A`, `M : F_Σ (['x] B)`, and
`'x` is fresh. Under K it translates to `withbor1U` at `d = consumeE (Ref A)`. `Mut` lends
(`withbor2U`, `withbor3U`) have the same clause shape and are left out to keep the fragment small.
They add no case the `Imm` lend does not have.

### Typing rules (Lean sketch)

The source syntax is Church-style: binders carry their types, and each `let` and `raise` carries
the mask of the slots its abandoned part owns, as the checker's `TExpr` nodes carry `Masks`. The
translation is then a function of the term, and the derivation only justifies it.

```lean
/-- Source terms: de Bruijn, Church-annotated. `u` is the mask of the slots the rest owns. -/
inductive STm where
  | var (i : Nat) | unit | lit (c : IntLit) | pair (a b : STm) | inl (a : STm) | inr (a : STm)
  | ret (V : STm)
  | letv (A : VTy) (u : List Bool) (M N : STm)        -- x : A ← M; N        (glue site)
  | letp (V M : STm) | seq (V M : STm) | case (V M₁ M₂ : STm)
  | alloc (V : STm) | free (V : STm)                   -- kernel constants, applied
  | box (V : STm)                                       -- [@a]I, for a callback's answer
  | raise (n : UInt32) (u : List Bool) (V : STm)        -- consume the u-slots, then raise
  | try (n : UInt32) (P A R : VTy) (M Nret Nexn : STm)
  | borrowI (A B : VTy) (x : LifeVar) (V M : STm)

/-- A context's live slots are consumable. -/
def Ctx.ConsumableLive (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → Consumable s.ty

-- The source judgment. Same indices as `CDerives`; rows are `ExnRow`s.
inductive SDerivesX : LifeCtx → Ctx VTy → STm → Jdg → Prop where
  -- values and pure computations: CDerives's rules, one source constructor each
  | var  (h : Ctx.SoloP Γ i A) : SDerivesX Δ Γ (.var i) (.val A)
  | pair (hs : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SDerivesX Δ Γ₁ a (.val A))
         (h₂ : SDerivesX Δ Γ₂ b (.val B)) : SDerivesX Δ Γ (.pair a b) (.val (.tensor A B))
  | ret  (h : SDerivesX Δ Γ V (.val A)) : SDerivesX Δ Γ (.ret V) (.comp (CTy.effOf S A))
  | letp | seq | case | alloc | free | box | sub   -- as CDerives (tensorE, unitE, sumE, …, effSub)
  /-- `x ← M; N`. No `hW`: the abandoned `Γ₂` may hold owned cells. -/
  | letv (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hu : u = Γ₂.map (·.live)) (hS : ExnRow S)
      (hMS : RowLe SM S) (hC : Ctx.ConsumableLive Γ₂)
      (hM : SDerivesX Δ Γ₁ M (.comp (CTy.effOf SM A)))
      (hN : SDerivesX Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
      SDerivesX Δ Γ (.letv A u M N) (.comp (CTy.effOf S B))
  /-- `raise n V` with the rest `Γᵣ` abandoned (consumed by the translation). -/
  | raise (hs : Ctx.SplitP Γ Γv Γr) (hu : u = Γr.map (·.live)) (hS : ExnRow S)
      (hf : Row.find S n 0 = some (exnOp n P)) (hC : Ctx.ConsumableLive Γr)
      (hV : SDerivesX Δ Γv V (.val P)) :
      SDerivesX Δ Γ (.raise n u V) (.comp (CTy.effOf S B))
  /-- `try_n M with (x. Nret) (e. Nexn)`: the arms see persistent slots only. -/
  | try (hs : Ctx.SplitP Γ Γh Γb) (hd : Ctx.DeadP Γh) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
      (hS : ExnRow (exnOp n P :: S))
      (hM : SDerivesX Δ Γb M (.comp (CTy.effOf (exnOp n P :: S) A)))
      (hr : SDerivesX Δ (⟨A, true⟩ :: Γh) Nret (.comp (CTy.effOf S R)))
      (he : SDerivesX Δ (⟨P, true⟩ :: Γh) Nexn (.comp (CTy.effOf S R))) :
      SDerivesX Δ Γ (.try n P A R M Nret Nexn) (.comp (CTy.effOf S R))
  /-- `borrow V as m in M`, `m : Imm 'x A`, the callback at `Σ`, its answer boxed at `'x`. -/
  | borrowI (hs : Ctx.SplitP Γ Γv Γc) (hx : Δ.find? x = none) (hsc : VScoped Δ A)
      (hfA : ¬ VFree x A) (hfB : ¬ VFree x B) (hS : ExnRow S) (hU : S.Unwind x)
      (hΓx : ∀ s ∈ Γc, s.live = true → ¬ VFree x s.ty)
      (hV : SDerivesX Δ Γv V (.val (.ref A)))
      (hM : SDerivesX (Δ.extend x Δ.meetOfDom) (⟨.imm (.var x) A, true⟩ :: ⟨.unit, false⟩ :: Γc)
              M (.comp (CTy.effOf S (.box (.var x) B)))) :
      SDerivesX Δ Γ (.borrowI A B x V M) (.comp (CTy.effOf S (.tensor (.ref A) B)))
```

**The name is a placeholder.** `scripts/check-judgments.sh` freezes every `inductive …Derives…`,
and `scripts/judgments.allow` says not to add lines. A source fragment's typing is a typing
judgment, so it needs either an allowlist line (precedent: `experiments/HandlersAsBorrows/…/Source.lean`
has `VDerives` and `XDerives`) or the user's other ruling. Renaming it to dodge the grep would be
dodging the rule, so that is not an option. This is decision **D1** in the report.

The spike's Lean goes in `experiments/ExnGlue/` (a `lean_lib`, not a default target), importing
`Core`. Nothing in `Core/` changes.

---

## 2. The translation (route K)

`tr : STm → Expr` is a function on syntax. Write `cs T u e` for the consumes of the slots `u` marks,
over `e`: `consumeSlotE T_i i (… e)`, innermost slot first, with `T_i` read from a context of types
`T : List VTy`, which is a second argument of `tr` (the checker's `finalOf` has the same shape). The
slot types are the same in `Γ`, `Γ₁` and `Γ₂`, because `Ctx.SplitP` only changes liveness.

| source | target | kernel rule |
|---|---|---|
| values, `ret`, `letp`, `seq`, `case`, `alloc`, `free`, `box` | the same term | the same rule (`tensorI`, `ret`, `tensorE`, `unitE`, `sumE`, `alloc`/`free` + `lolliE`, `boxI`) |
| `letv A u M N`, `SM = []` | `(λx. ⟦N⟧) ⟦M⟧` | `bind` (head at `F A`, so no `hW`; `bind`'s `N` may be at `F_Σ`) |
| `letv A u M N`, `SM ≠ []` | `thenE ⟦N⟧ (cs T u' (ret ())) ⟦M⟧`, where `u'` is `u` under `[then]`'s dead binder | `effSub` on `M` up to `Σ`, then `effThenA` |
| `raise n u V` | `cs T u (raiseE (opArgE n 0 ⟦V⟧))` | `consumeSlot_derives` per slot, then `effRaise` |
| `try n P A R M Nr Ne` | `hndExpr n [cancel] (⟨!λx.⟦Nr⟧, (!λe.⟦Ne⟧, ())⟩) ⟦M⟧` | `bangThunkV`, `tensorI`, `effHandleV` at `E = [(cancel, P, 0)]`, `fs = finsNil`, `cs = rcsNil` |
| `borrowI A B x V M` | `r ← ⟦V⟧; f ← thunk (Λ. λm. ⟦M⟧); w ← withborUE (consumeE (Ref A)); w r f` | `bind`×3, `withbor1U` at `d = consumeE (Ref A)`, `thunkV`/`allI`/`lam`, `app`/`force` (the pattern of `DeclLend.d_declAcrossBody`) |

**Where `[then]` goes.** At every `let` whose head's row is non-empty (it may raise), with the
consumes of every live slot of the rest as the finaliser, at the pure row (`effThenA`: `Σ_D = ∅`,
`ThenLe.nil`, `hSD` by `rfl`). A head at the pure row uses `bind`, not `effLet`, because `effLet`'s
`hW` reads the *outer* row `Σ`, and that row is non-empty whenever an exception is in scope.

**Where consumes go.** In `[then]`'s finaliser for the rest's context. Before a `raise`, for every
live slot the payload does not use. In `withbor1U`'s `d`, for the lent source. No consume is moved
across an effect: at a raise they run immediately before it, as §12 places them before a path's
terminal computation.

**The borrow callback's unwind form.** Always the unwinding form `withbor1U`, at the callback's row
`Σ`. At `Σ = []`, `Row.Unwind [] x` holds vacuously, and `withborUE`'s `[then]` never fires. The
alternative (the pure `withbor1` at `Σ = []`, as the checker does) is decision **D4**. It adds a
second clause and changes nothing in the proof's hard case.

**How the context at each possible abort becomes `Ctx.OwnFree`.** It never has to. The kernel asks
for `Ctx.OwnFree` only at `effLet.hW`, and the translation emits no `effLet`. At every possible
abort, the owned part of the context has already been consumed by the time control leaves:

- at a `raise`, the `cs` before it leave a context `DeadP` apart from the payload's part, and
  `effRaise` reads only `hd` (the payload type);
- at a `let` with a head that may raise, `[then]` holds `Γ₂` in `N` and `D` additively. `D`
  consumes it, so the abort abandons only the continuation `K` up to the `ubind` frame, which holds
  nothing (`ewp_end`'s `NoOwn` share);
- in a borrow callback, the same two cases apply inside the callback's own context. At the
  callback's boundary `withborUE`'s `[then]` runs `d r` on the returned source, and the call site's
  own `[then]` (it is a `let` whose head may raise) consumes the outer context.

**Under K+cell** the `raise` row changes to "store `v` through the lend's `Mut`, then raise `()`",
and every `letv` with a head that may raise wraps the head in `withbor3U` on the cell's `Mut`.
**Under E** every row is `[]`, `F_Σ A` becomes `F(A ⊕ P₁ ⊕ …)`, `letv` becomes `bind` + `sumE`
whose `inr` arm is `cs T u (ret (inr e))`, and `borrowI` uses `withbor1` with the callback answering
`['x](B ⊕ P)`.

---

## 3. The theorem statements

```lean
/-- **Typing preservation** (Prop 3's shape): every source derivation is a `CDerives` derivation
of the translation, at the same lifetime context, context and judgment. -/
theorem tr_derives {Δ : LifeCtx} {Γ : Ctx VTy} {t : STm} {j : Jdg}
    (h : SDerivesX Δ Γ t j) : CDerives Δ Γ (tr (Γ.map (·.ty)) t) j

/-- **Source-level resource safety** (Thm 4.1's shape): `resourceSafety` ∘ `tr_derives`. Every run
of a closed source program's translation from the empty memory continues to a value at the empty
memory, and every `free` it reaches finds its cell. -/
theorem sourceResourceSafety {t : STm} {A : VTy} (hA : A.Persistent)
    (h : SDerivesX LifeCtx.empty [] t (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (tr [] t) μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety hA (tr_derives h) hs
```

`CTy.effOf [] A = .ret A` holds by `rfl`, so a closed program at the empty row is at `F A`.

Hypotheses, classified:

| statement | hypothesis | kind |
|---|---|---|
| `tr_derives` | `h : SDerivesX Δ Γ t j` | the situation |
| `sourceResourceSafety` | `hA : A.Persistent` | the situation (as `resourceSafety`'s) |
| | `h : SDerivesX .empty [] t (.comp (.ret A))` | the situation |
| | `hs : Steps … (tr [] t) μ₁ e₁` | the situation |
| `SDerivesX.letv` | `hu`, `hC`, `hS`, `hMS` | side conditions the source typing carries. A checker decides each (`consumableB`, `Row.uniqB`, `rowLeB`), and the mask is the split's own |
| `SDerivesX.raise` | `hu`, `hC`, `hf`, `hS` | side conditions, as above |
| `SDerivesX.try` | `hd`, `hn0`, `hnS`, `hS` | side conditions; `hd` mirrors `[handle]`'s `Ctx.DeadP Γ₁` |
| `SDerivesX.borrowI` | `hx`, `hsc`, `hfA`, `hfB`, `hU`, `hΓx`, `hS` | side conditions. `withbor1U`'s, `allI`'s `hΓx`, and `Row.Unwind` |

No hypothesis stands in for an unproved fact. In particular there is no premise that "the glue
exists" or that "the translation is typed". The source rules carry only what a checker reads off
the program.

Library lemmas the proof needs (each proved in the spike, none assumed):
- **`consumeAll_derives`**: if `Ctx.ConsumableLive Γ₂` holds, then
  `CDerives Δ (⟨1, false⟩ :: Γ₂) (cs T u (ret ())) (.comp (.ret .unit))` at `u = Γ₂.map live`. By
  induction on `Γ₂`, with `consumeSlot_derives` per live slot and `unitI` at the end, where the
  context is `Dead`. This builds §12's chain of consumes as one lemma; nothing in `Core` states it
  for a whole context today.
- **`raiseRest_derives`**: the same chain over `Γᵣ` in front of `effRaise`, using `Ctx.SplitP Γ Γv Γr`.
- **the borrow clause**: `bind`, `withbor1U`, `thunkV`/`allI`/`lam` and the `app`s, with
  `consume_wf` and `consumeE_closed` for `d` (as `DeclLend.d_declAcrossBody` does for one program).
- **the handler clause**: `effHandleV` with `H.ValFormIn Γh` and `Ctx.DeadP Γh`, `retTy` and
  `clausesTy` by `bangThunkV`. Every arm's context is persistent (`Ctx.Banged`), from `hd` plus the
  binder. The binder is linear, so `bangThunkV`'s `Ctx.Banged` needs care: see R4.

---

## 4. The hardest case, by hand (route K)

The program. `o` is owned outside the borrow, `i` is owned inside the callback, and the callback
raises. With K's payload restriction the payload is data (`I32`). The owned-payload version follows.

```
try_7 (                                   -- Σ₀ = [exnOp 7 P]
  o ← alloc 1;                            -- o : Ref I32, outside
  r ← alloc 2;                            -- r : Ref I32, the lender's source
  (r', b) ← borrow r as m in (            -- m : Imm 'x I32
      i ← alloc 3;                        -- i : Ref I32, inside
      _ ← raise_7 5;                      -- the abort abandons i and m
      free i; release m; ret (box ()));   -- the normal path consumes them itself
  free r'; free o; ret ())
with (x. ret x) (e. ret ())
```

The translation, outside in, with the rule each step meets:

1. **`try`** becomes `hndExpr 7 [cancel] H ⟦body⟧`, by `effHandleV` at `E = [(cancel, I32, 0)]`,
   `S = []`. Premises: `hd`, since `Γh = []`, which is `DeadP`. `hH`: `H` is a pair of λ-values, a
   value form. `hc`: `retTy [] 1 1` and `clausesTy [] 1 E` by `bangThunkV` over a `Banged` empty
   context. `hn0`: `7 ≠ 0`. `hnS`: vacuous. `hlen`. `hdv`: no `Div`, by `decide`. `he`: the body at
   `Row.ofEff 7 E 0 ++ [] = [exnOp 7 I32]`, which is `rfl` at `finsNil`/`rcsNil`.
2. **`o ← alloc 1; …`** has a pure head, so it is `bind` with no row condition. Same for `r ← alloc 2`.
3. **`(r', b) ← borrow …; free r'; free o`** has a head at `Σ₀ ≠ []`, so it is `[then]`
   (`effThenA`):
   - `hNZ`, `hUq` hold at `Σ₀` (checked, §5);
   - `hU : Σ₀.UnrD → …` is vacuous (checked: `¬ Row.UnrD [exnOp 7 P]`);
   - `D = consumeSlotE (Ref I32) (o's index + 1) (ret ())`. Its derivation is `consumeSlot_derives`
     with `Consumable.ref .int` (checked, §5). `D` runs in the same `Γ₂ = {o}` as `N`, and `N`
     frees `o` on the normal path.
4. **The borrow** becomes `bind`s of `⟦r⟧`, the callback thunk and `withborUE d`, at
   `d = consumeE (Ref I32)`, then `w r f`. By `withbor1U` at `x`:
   - `hΓ`: the constant's context is `DeadP`;
   - `hx`: `x` is fresh;
   - `hsc₁`: `VScoped Δ I32`;
   - `hfree₁`, `hfree₂` hold by `simp [VFree]`;
   - `hS : Σ₀.Unwind x` (checked at the payload `I32`, and also at `Ref I32`);
   - `hdc`: `consumeE_closed`;
   - `hd`: `consume_wf (.ref .int)` at a dead context.

   The callback is `thunkV`/`allI`/`lam`, with `allI.hΓx` from the source's `hΓx`: `o` is
   `Ref I32`, not mentioning `x`.
5. **Inside the callback**, `i ← alloc 3` is `bind`. Then `_ ← raise …; ret (box ())` is a `let`
   whose head is at `Σ₀`, so it is `[then]` again, with `D = consume i; consume m`
   (`Γ₂ = {i, m}`; `m`'s consume is `releaseImm`, `Consumable.imm`). `N` frees `i` and releases `m`
   on the normal path. The head `raise_7 5` has an empty `Γᵣ`, so
   `cs = id`, and it is `effRaise`: `hf` by `Row.find`, `ha`/`hrc` by `decide`, `hd : (int).OwnFree`.
   Checked: a consume of an owned slot followed by `effRaise` at `exnOp 7 I32` elaborates (§5,
   check 6).
6. **The run.** The raise stops at the inner `ubind` frame, which runs `D = consume i; consume m`
   (frees `i` and releases `m`), then raises again. It reaches `withborUE`'s `ubind`, which runs
   `d r` (frees `r`: the lend ended, and the source went back to its lender and was consumed by the
   lender's finaliser), then raises again. It reaches the outer `[then]`, which frees `o`, then
   raises again. It reaches the handler, which runs `ret ()`. The memory is empty: `resourceSafety`'s
   conclusion, with no theorem beyond `tr_derives`.

**The owned-payload version** (the correction): `raise_7 p` with `p ← alloc 5 : Ref I32` allocated
inside the callback, and the handler `(e. free e; ret ())`.

- **K:** step 5's `effRaise` needs `hd : (Ref I32).OwnFree`, which is false (checked: `cases`).
  This is the one step that fails. Every other step is unchanged, `Row.Unwind` admits `Ref I32`, and
  the handler's clause `!λe. free e; ret ()` is typed by `bangThunkV` (the clause binds `e`; its
  outer context is empty). So `effHandleV`'s side accepts an owned payload, and only `[raise]`
  refuses it.
- **K+cell:** the `try` becomes `c ← alloc (inl ()); (c', a) ← borrow_mut c as k in
  (hndExpr 7 … ⟦body⟧[k]); case (take c') { inl () → Nret a | inr p → free p; ret () }`, and
  the raise becomes `k′ ← reborrow; swap k′ (inr p) → consume old (inl ()); raise_7 ()`. The
  payload rides in `c`. `free p` is the handler consuming it after the lend ends. The inner borrow
  needs `k` reborrowed into the callback (`withbor3U` on `k`, whose `d` is the release of a `Mut`). Each step meets
  `withbor2U`/`withbor3U`/`swap`/`effRaise` at payload `1`, all of which exist. Not checked in Lean.
- **E:** the raise is `cs (ret (inr p))`, and the callback answers `['x](B ⊕ Ref I32)`. `boxI` asks
  `CtxOutlives Δ Γ 'x` of `p`'s context, and `p : Ref I32` outlives `'x` (`VOutlivesR.ref .int`). At
  the borrow's call site a `sumE`'s `inr` arm frees `r'` and `o`, then `ret (inr p)`. The `try` is a
  `sumE` whose `inr` arm runs `free p; ret ()`. Each step is a pure rule. Not checked in Lean.

---

## 5. Risks, ranked

The checks are in `~/repos/scratch-archive/804/Checks.lean`, run with `lake env lean` on
`spike-804` against a targeted build of `Core.ResourceSafety`, `Core.Inversions` and
`Core.EffBorrow`. All elaborate, with no `sorry`. Their numbering:
1. `¬ VTy.OwnFree (Ref I32)`.
2. `Row.Unwind [exnOp 7 (Ref I32)] x`.
3. `Row.NZ`, `Row.Uniq`, `¬ Row.UnrD` and `Row.Cancels` at exception rows.
4. `def OwnedRaiseTypable : Prop`, stated only.
5. A finaliser consuming an owned slot under `[then]`'s dead binder, at `F 1`.
6. A consume of an owned slot, then `effRaise` at `exnOp 7 I32`.

Plus `#check`s of every rule and lemma the translation names.

| # | risk | check run | status |
|---|---|---|---|
| R1 | **Owned payloads at `[raise]`** (K): `effRaise.hd : o.A.OwnFree` refuses `Ref`. | `example : ¬ VTy.OwnFree (.ref (.int .w32))` by `cases`; `Row.Unwind [exnOp 7 (Ref I32)] x` holds. Stated, not proved: `def OwnedRaiseTypable : Prop` | **real for `effRaise`**; for all of `CDerives`, not derived and the obstruction not verified (`der_raiseJ`'s `RaiseBase` omits `hd`) |
| R1b | **K+cell's threading.** Every head that may raise needs the cell's `Mut`. Sequential heads need reborrows (`withbor3U`), each with its own `'x` and its own `Row.Unwind`. A raise in a callback nested *n* deep needs *n* reborrows, and the payload stored through `Mut 'x (1 ⊕ P)` must outlive every `'x` (closed `P` does). | not checked | the largest unknown of K+cell |
| R1c | **A handler receiving an owned payload.** `clauseTy` at an abortive operation is `!U(P ⊸ F_Σ R)`: the clause binds the payload linearly and may consume it, but its outer context is `Ctx.DeadP`. A source handler that consumes the payload *with* an owned value from outside the `try` is not typable by `effHandleV`. Under E and K+cell the exception arm runs after the handler, where it may use the linear context. | `clauseTy` read; `bangThunkV` needs `Ctx.Banged` of the clause's context, and the payload binder is inside the λ, not in that context | K: the arms are restricted as `[handle]` is; K+cell and E: no restriction |
| R2 | **`[then]`'s row premises.** `S.NZ`, `S.Uniq`, `S.UnrD → Banged Γ₂`. | `Row.NZ`, `Row.Uniq`, `¬ Row.UnrD`, `Row.Cancels` at exception rows, all by `simp`/`decide` (checks 3) | met by `ExnRow`; `Uniq` is a source premise, not derivable from `Row.Unwind` |
| R3 | **`Row.Unwind`'s closed-data argument** at every callback: `∀ Δ a, VOutlives Δ a P` and `¬ VFree x P`. | `Row.Unwind [exnOp 7 (Ref I32)] x` (check 2) | met by `ExnRow`'s closed payloads; a payload holding a borrow is excluded, as intended |
| R4 | **Handler arms with a linear binder.** `retTy`/`clauseTy` are `!U(A ⊸ …)`, built by `bangThunkV` over a `Banged` context. The λ's own binder is inside the thunk (`lam`), so a linear `x`/`e` is fine; the arms may not capture linear slots. | not checked | low |
| R5 | **`Div` in finalisers.** `effThenA` puts `D` at `F 1`. The consumes are `consume_wf` at `T ⊸ F 1` (pure), and the fragment has no codata, whose `close` is the only consume that runs code. | `#check @consume_wf` | not a risk in this fragment |
| R6 | **The consume-all lemma.** The masks must agree with the split. `consumeSlot_derives` takes one slot with an explicit `SplitP` and `SoloP`, and the chain needs the induction to build both from `u = Γ₂.map live`. | single slot under the dead binder (check 5) | mechanical |
| R7 | **`[handle]`'s `Row.ofEff` shape.** `Row.ofEff 7 [(cancel, P, 0)] 0 finsNil rcsNil ++ S` must be `exnOp 7 P :: S`, so `UInt32.ofNat 0 = 0` and `fs 0 = .ret .unit` reduce. | not checked; `d_toResultG` uses the same shape at `Ef` | low |
| R8 | **The borrow clause's term shape.** The application `w r f` goes through `bind` + `app` + `force` with de Bruijn shifts, as in `DeclLend`. `CDerives.insert_dead` (`Core/InsertDead.lean`) may be needed to put the callback's dead `Λ` slot under the source's context. | not checked | mechanical, error-prone |
| R9 | **The judgment freeze** (D1). | `scripts/check-judgments.sh` read | needs a ruling |

**Size estimate (route K, owned payloads excluded):** the source syntax and judgment, ~250 lines;
`tr`, ~100; `consumeAll_derives` and `raiseRest_derives`, ~120; `tr_derives`, ~700–1000 (about
fifteen cases, with the borrow and handler cases ~150 each); `sourceResourceSafety`, ~15; tests
(the §4 program through `tr`, and a negative test), ~100. **~1300–1600 lines.** K+cell adds a
threaded translation and roughly doubles it. E is ~900–1200, since every case is a pure rule plus
`sumE`.

---

## 6. NOT-do list and tempting shortcuts → STOP

- **Changing `CDerives`**, including relaxing `effRaise.hd` (route K′), adding a `try` rule, or
  adding a coordinate. STOP and report instead.
- **Proving it for the checker's output on example programs**, or for `Frontend/Check`'s glue. The
  translation is the spike's own `tr`, quantified over every `SDerivesX` derivation.
- **A translation that refuses the hard case**: one that rejects a raise under a borrow with owned
  values on both sides, or that "solves" owned payloads by excluding them without the user choosing
  route K (§0).
- **Restating `resourceSafety`**: `sourceResourceSafety` is the composition, and its proof is one
  line.
- **A hypothesis standing in for a fact**: no "`hglue : ∃ D, CDerives …`" premise, and no
  `Ctx.OwnFree Γ₂` premise on the source `let`, since that would assume the glue away.
- **Hiding the source judgment from the freeze** by naming it outside `…Derives…`.
- **Splitting cases the source does not split**: one `letv` clause; the `SM = []` versus
  `SM ≠ []` choice is the translation's, read off the row, and the source rule is one rule.
- **Editing `~/repos/borrow-core`** or `vercheck/`, or merging anything: the spike lives on
  `spike-804`.

---

## 7. Kill criterion, and the fallback

**"Yes"** means `tr_derives` and `sourceResourceSafety` are proved for the chosen route's
fragment, with the hard case in it, with no hypothesis beyond §3's table, and with `#print axioms`
⊆ `[propext, Classical.choice, Quot.sound]`.

**"No"** means a closed `SDerivesX` derivation in Lean, every hypothesis discharged, together with
two proofs: that no `CDerives` derivation types its translation `tr [] t`, and that no translation
in §2's class (glue only: consumes, `[then]`, `withbor1U`'s `d`) types it.
- Under route K, the candidate is the owned-payload program of §4. Its kernel half is the negation
  of `OwnedRaiseTypable`, which needs `der_raiseJ` strengthened to keep `hd`. That is an inversion
  proof, not a stand-in.
- Under routes K+cell and E, the candidate is a case of `tr_derives` whose kernel premises are
  refuted in Lean for some source derivation.

A proof that stalls is not a "no". It is reported as "not derived; obstruction not verified".

**The fallback is not "no"** (the user, 2026-11-04: "resource safety, except under these well
defined conditions" is acceptable). If part of the fragment cannot be covered, the result is the
theorem with the excluded class as an explicit hypothesis:

- the hypothesis is a condition on types or rules, never a list of programs;
- it is decidable on the typed source term, so the checker can compute it per program and warn
  where it fails;
- it is proved non-vacuous: the §4 program (data payload) satisfies it, by `decide`, and has a
  derivation;
- its scope is pinned: a program it excludes is exhibited, by `decide` on the decider.

```lean
/-- The program is in the covered class. A `Bool` on the Church-annotated term. -/
def coveredB : List VTy → STm → Bool          -- the conjunction of the deciders below, per node

theorem coveredB_sound : coveredB T t = true → Covered T t      -- Covered: the Prop conjunction

theorem sourceResourceSafety_cov {t : STm} {A : VTy} (hA : A.Persistent)
    (h : SDerivesX LifeCtx.empty [] t (.comp (.ret A))) (hcov : coveredB [] t = true)
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (tr [] t) μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u)
```

`hcov` restricts which programs are covered. It is not a lemma's statement assumed, because
`tr_derives` is still proved, for every derivation of a covered term, with no other premise. To
make the conditions decidable, the source terms carry the types they read: `raise` carries its
payload type `P`, and `try` already does.

The conditions expected, most likely first. Each gives (a) the decider, (b) its soundness lemma,
(c) what the warning names, and what it excludes.

| # | condition | (a) decider | (b) soundness | (c) the warning names | excludes |
|---|---|---|---|---|---|
| C1 | **Raised payloads hold no owned cell** (route K: `effRaise.hd`) | `ownFreeB P` at every `raise`/`try` node (`Frontend/Check/Decide.lean:824`) | `ownFreeB_sound : ownFreeB A = true → A.OwnFree` (exists) | the `raise` site and its payload type: "this raise carries `T`, which owns a cell: resource safety is not guaranteed for it" | owned payloads (`Ref`, an owned tuple). Under K+cell or E: not needed |
| C2 | **Handler arms capture only persistent slots** (`effHandleV.hd`) | `Γh.all (fun s => !s.live ‖ decide s.ty.Persistent)` at each `try`, `Γh` from the arm's mask | `Ctx.DeadP Γh`, by induction on `Γh` (`Ctx.DeadP.weaken`/`.cons`) | the `try` and the slot an arm uses: "the handler of `n` uses `x : T`, which is linear" | arms that use the linear outer context (route K). Under E: not needed |
| C3 | **Every slot live across an abort is consumable** | `consumableB` on each live slot of a `letv`'s rest (head row non-empty) and of a `raise`'s rest | `consumableB_sound` (`Frontend/Check/Steps.lean:303`) | the slot, its type and the abort site, as `finalOf`'s message today | group-3 values across an abort: thunks, `Tok`/`must_close` declared types, type variables. Vacuous in §1's fragment; needed as it grows |
| C4 | **Each borrow callback's row is `Row.Unwind`** | `Row.unwindB S x` at each `borrowI` | `Row.unwindB_sound` (`Decide.lean:913`) | the borrow and the operation: "a raise of `T` leaves the borrow of `'x`, and `T` mentions `'x` or does not outlive every lifetime" | payloads holding a borrow; a resuming operation in a callback |
| C5 | **Exception rows are unique and abortive at `cancel`** | `Row.uniqB S && Row.nzB S && S.all (·.q == .cancel)` at each row annotation | `Row.uniqB_sound`, `Row.nzB_sound` (exist), plus a one-line `List.all` lemma for `q` | the row: "two operations share a key" / "an unrestricted abort" | duplicate keys and unrestricted aborts (`EffCtx.NoUnrExn` already rejects these in checked programs) |

C4 and C5 are `SDerivesX`'s own premises. They move to `coveredB` only if the fallback is preferred
to rejecting the program. C1 and C2 are the two conditions on which the routes differ:
- under K, the fallback reads "resource safety for every program whose raised payloads own no
  cell and whose handler arms are persistent";
- under K+cell and E, neither condition is expected.

The only conditions allowed are ones with a `Bool` decider and a soundness lemma, like those above.
A semantic condition with no decider (for example, "no finaliser raises during this unwind") is not
an acceptable fallback, and the doc lists none.

---

## 8. As built (route K)

The library is `experiments/ExnGlue/` (`lake build ExnGlue`, not a default target). It imports
`Core` and changes nothing there. It adds one line to `scripts/judgments.allow`, for the source
judgment `SDerives`.

| result | file:line | statement |
|---|---|---|
| `SDerives` | `ExnGlue/Source.lean:61` | the source judgment `Δ; Γ ⊢ t : F_Σ A` |
| `tr` | `ExnGlue/Translate.lean:39` | the translation with its glue |
| `consAll_derives` | `ExnGlue/Translate.lean:91` | the consumes of a part `Γb` of `Γ = Γa, Γb` are typed in front of a term typed at `Γa` |
| `tr_derives` | `ExnGlue/Translate.lean:144` | `SDerives Δ Γ t S A → CDerives Δ Γ (tr t) (.comp (CTy.effOf S A))` |
| `sourceResourceSafety` | `ExnGlue/Translate.lean:188` | `resourceSafety hA (tr_derives h) hs` |
| `hard_derives` | `ExnGlue/Example.lean:115` | the §4 program's source derivation, every premise discharged |
| `hard_safe` | `ExnGlue/Example.lean:121` | `sourceResourceSafety` at it |
| `not_exnRow_ref` | `ExnGlue/Source.lean:105` | a `try` at an owned payload `Ref A` is outside `ExnRow` |

Every result's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.

Changes from §1–§2, each to fit what the kernel's rules read:
- **Every `let` is `[then]`**, at every row (`effThenA`; at `Σ = []` its premises hold vacuously).
  So `letv` asks its rest's context to be consumable at every row, not only where the head may
  raise. No `bind` clause is needed.
- **Values are kernel value derivations** (`CDerives … (.val A)`). `alloc`, `free`, literals and
  `[]I` are therefore not source constructors, and nothing is translated inside a value.
- **The borrow's source is a slot** (`borrowI A i M`, `Ctx.SoloP Γv i (Ref A)`), so the translation
  needs no shift: `bindE cb (bindE (withborUE d) ((w r) f))`, as `DeclLend.declAcrossBody`.
- **Handler arms see a `!` context** (`Ctx.Banged Γh`): `retTy` and `clauseTy` are built by
  `bangThunkV`, which reads `Ctx.Banged`, not persistence.
- **`allI`'s side conditions** come from `Δ.Ok` and `x`'s freshness, as `allI_fresh` derives them,
  with the captured context's slots not mentioning `x` (`hΓx`).

Hypotheses of `tr_derives`: only `h : SDerives …` (the situation). Hypotheses of
`sourceResourceSafety`: `hA : A.Persistent`, `h`, and the run `hs` (the situation, as
`resourceSafety`'s). The source rules' premises are side conditions read off the program (§3's
table), each decidable: `ownFreeB`, `consumableB`, `Row.nzB`, `Row.uniqB`, `Row.unwindB`, and
`decide` on `Persistent`/`Banged`. None stands in for a fact.
