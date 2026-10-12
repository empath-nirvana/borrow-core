# ProbeD1: the bridge hypothesis — one lifetime-carrying former for suspensions

**The hypothesis tested.** A suspension is a value that carries lifetimes. One new type former, added
conservatively to Core, covers every program we cannot run today because a suspension must outlive a
call while a borrow is open. It has two halves:
- **External lifetimes, bounded.** `U@'a C` is a thunk that may be forced only while `'a` is live. It
  has no elimination to plain `U`, and it is resumed or cancelled before `'a` ends.
- **Internal lifetimes, bound.** The freeze binder hides the suspension's own lends at the stop, and
  resume or placement instantiates them.

The claim is that the two halves are one former, or one former plus one binder. The former is
introduced exactly at the cut, where `κ` is captured inside an open lend. Its hard step, resuming
after a re-lend at a different concrete lifetime, is supposed to be the cut-based `∀` that tier 2
already solved.

**Status words.**
- *Proved*: a Lean theorem, cited by name.
- *Machine-checked here*: proved in this unit's probe, `ProbeD1/BridgeProbe.lean`.
- *Inspection*: read off a rule or a definition, with file and line, and no proof.
- *Not derived*: neither proved nor refuted, and no obstruction verified.
- *Corpus*: a program in `~/repos/borrow-core/corpus` that the toolchain accepts or rejects with
  that message.

**Worlds** (BRIEF §10):
- **Core σ=[]**: the kernel relation `vC`/`cC`.
- **GE**: GhostEnd's own relations.
- **W**: ProbeD1's draft relation `vRLM`/`cRLM`.

GhostEnd's `Relend`, `withbor_spans_yields_cC` and `withborR_compat` are predicates and theorems over
Core's `wpG`/`ewpTS`, so their results are at Core σ=[].

**The probe.** `ProbeD1/BridgeProbe.lean` elaborates with `lake env lean`. It has no `sorry`, `axiom`,
`native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`. Axioms per theorem:
- `thunk_not_outlives`: none.
- `ctxOutlives_not_of_live_thunk`: none.
- `not_coreThawTop`: `[propext, Classical.choice, Quot.sound]`.

The file is not added to `ProbeD1.lean`'s imports, so `lake build ProbeD1` does not build it.

---

## 0. The verdict on one page

**The hypothesis does not hold as stated.** It fails in three independent places, and each failure
is a positive finding.

1. **The external half already exists.** It is BoLo's own `U C`, so no new former is needed.
   - `U C` has no outlives rule, so it cannot leave a borrow. Machine-checked here:
     `thunk_not_outlives`.
   - A context holding a live `U` slot is never `CtxOutlives`, so `[]I` boxes nothing typed in it.
     Machine-checked here: `ctxOutlives_not_of_live_thunk`.
   - `[@c] U C` is Rust's `+ 'c`, the boxed capture bound.
   - A borrow callback's `['x] B` exit is "consumed before `'x` ends".
   - The kernel already accepts suspensions that hold an external borrow:
     - `corpus/for-data-div.bc`'s `tens<'a>` and `corpus/gen-borrowed.bc` are accepted;
     - `corpus/reject/gen-escape.bc` is the refused escape.
   - "No elimination to plain `U`" adds nothing. A continuation is never in a box, so `[]E` never
     applies to it.
2. **The internal half is not a type former at the cut.**
   - At `[handle]`, `κ : U((B_i ⊸ F_Σ R) & F_Σ 1)` is built from `B_i`, `Σ` and `R`, all typed in
     the handler's `Δ` (SPEC §19 *Typing*; inspection). A lifetime opened inside the handled region is
     never in that `Δ`, so no type at the cut can mention it.
   - **Every T1 refusal in the six programs involves only internal lends.** The lend is opened
     inside the region that `κ` captures. This is also the prior-art reading of T1:
     `docs/prior-art-suspension-borrows.md` §0 calls it "self-referential suspended state".
   - So the binder lives in the **continuation's semantic share at a stop**, not in a type that
     `κ` carries. Where a type-level binder does appear, it is on the **callback** that suspends
     inside a lend: a re-lendable `∀♮` (§1.3). It does not appear on `κ`.
3. **The hard step is not the already-solved cut-based `∀`.** What tier 2 proved holds in two
   places only:
   - at W, where **every** `U` clause quantifies over instantiations (`RelendJ`). That is the
     non-conservative change this unit is told not to repeat;
   - in `TyEq`, which does not read the room between lifetimes (`tyEqInst`, `tyEqRoomBlind`).

   **Core's relation does not survive an internal re-instantiation at every configuration.**
   - The unrestricted thaw is false. Machine-checked here: `not_coreThawTop`, from tier 2's
     `coreAllNotNatural`.
   - Whether a residual of a typed program can reach that witness is unchecked. So the thaw would
     have to be restricted by something Core's relation does not see: the residual's typing.

**What does bridge conservatively.** The smallest set is below.
- **(S0) Nothing**, for external lifetimes: programs 5 and 6, and 1 and 2 in their handler-inside
  forms.
- **(S1) Liveness-based lend splitting in the elaborator.** A lend open at a resumable stop is ended
  before the statement that may suspend and re-lent after it.
  - It applies when only the lend's views (and paths into them) and `'x`-free values are live across
    that statement.
  - Core and `CDerives` are unchanged.
  - Program 4 needs both of its programs, and they need only this.
  - It is the prior-art recommendation (`prior-art-suspension-borrows.md` §0 item 4).
  - The re-lend is erased at run time.
- **(S2) One conservative kernel binder `∀♮`**, the re-lendable lifetime binder. It is needed only
  where the suspending code is not visible to the elaborator:
  - inside a kernel constant's term (`foldImm`'s per-node `withload`, program 5);
  - in a stored callback's body (program 1, handler outside the lend).

  Its semantic clause is GhostEnd's `Relend`, a least fixed point over Core's `wpG`. Its fundamental
  case is proved for straight-line bodies at Core σ=[]:
  - `relend_chainΓ`, `withbor_spans_yields_cC`, `imm_spans_yield`;
  - `withborR_compat`, which also covers the affine cancel path.

**What does not bridge without a non-conservative change.** These are suspensions where a value
**derived** from an internal borrow is live at the stop: an iterator, a closure or an object over
the view. Examples:
- `gen-adapters-io`'s `bytes(&mut c)`;
- program 2 with `Log`'s handler outside the counter's lend.

Such a value is a Core `U` value at a type that mentions the internal lifetime. Re-lending moves that
lifetime, and Core's `U` is not invariant under the move in general (`not_coreThawTop`). Two routes
are known, and neither is conservative and proved:
- tier 2's W, which changes every `U`;
- GhostEnd's GFPA, a generalised fundamental lemma at its own relations, OPEN.

The other route keeps the lend open and does not move it. It hits `↭`, whose `mut` clause forbids a
run from ending a borrow cell it started with (proved: LoopBorrow's `not_upd_of_ended_mut`,
`not_upd_of_new_mut`). That changes every run that consumes a frozen `κ`.

**Programs 3 and 6 are not blocked by lifetimes at all** (§3).
- Program 3 (`gen-digits`, `gen-lazy`, `gen-lines`) is blocked by an owned capability with no
  destructor across an affine operation: a cancel cannot hand back a residual (K3, SPEC §19
  *Finalisers*). The borrowed variant of each is S0 (inspection, not run).
- Program 6's confinement is S0 plus a handler that opens a lifetime. Its remaining obstacles are the
  machine's name supply and the decided algebra's "static per-site names", which only the user can
  reopen.

---

## 1. The former(s), stated

### 1.1 The external half: `U@'a C` is `U C`

The hypothesis asks for four rules. Each already holds in Core.

| asked of `U@'a C` | what Core has | evidence |
|---|---|---|
| captures borrows at `'a` | `U C` captures anything: the `U` clause is `∀ ls', Ext ls ls' ρ → cC C ls' δ (force v) ρ`, with no lifetime condition on `ρ` | `Core/Relation.lean`, `vCE` at `.thunk` (inspection) |
| no escape past `'a` | `VOutlivesR` has no `thunk` rule, so no value containing an unboxed `U` outlives anything | **machine-checked here**: `thunk_not_outlives` |
| no elimination to plain `U` | unnecessary: `[]I`'s premise `CtxOutlives Δ Γ a` fails on any context with a live `U` slot, so a value typed with `κ` in scope is never boxed, and `[]E` never applies to it | **machine-checked here**: `ctxOutlives_not_of_live_thunk`; `CDerives.boxI` (`Core/Fundamental.lean:139`) |
| resumed or cancelled before `'a` ends | a borrow callback answers `['x] B`, and `U` is not boxable, so a `κ` holding an `'x` borrow is consumed (resume or `cancel`) inside the callback; an affine `κ` is consumed by exactly one entry (decided algebra) | SPEC §19 *Kinds of operation*; `corpus/reject/gen-escape.bc` |
| bounded captures for storage (`dyn FnMut + 'a`) | `[@c] U C` by `[]I` from a context outliving `c` | R6 rule 2 (`docs/effect-polymorphism.md` §5.6); `box_lolli_outlives_iff` |

The one thing `[@c] U C` cannot do is confine. It is a lower bound on captures, not an upper bound on
use. SPEC §19 *Names* reads the box as the confinement ("not enough, since `[]E` removes it"), but the
confinement is the **absence** of an outlives rule for `U`, together with the box at a lend's exit.
§3.6 uses this.

### 1.2 Why the internal half is not a type at the cut

- **`[handle]`'s premises type the body and the clauses in one `Δ`** (SPEC §19 *Typing*):
  `Δ; Γ₂ ⊢ e : F_{Σ, n:E} A` and `Δ; Γ₁ ⊢ H : …K_i…`.
  - A lend opened inside `e` binds `'x` in a sub-derivation of `e`: `withbor`'s callback
    `∀'x ⊏ ⊓Δ. …`.
  - So `'x ∉ Δ`, and `K_i = U((B_i ⊸ F_Σ R) & F_Σ 1)` cannot mention it. That holds whether or not
    `B_i` is closed in lifetimes (BRIEF §3.8 notes the as-built rules do not enforce closure; this
    argument does not need it).
- **So there is nothing for `U@'a` to name.** At the cut, the handler sees a `κ` whose internal lend
  is not in any type. The lifetime that would bound `κ` from outside is the internal lend's
  **source**. When the source is a reborrow of an external `Mut 'a T`, `κ` captures that borrow and
  is confined by §1.1 already. When the source is owned inside the region, `κ` is self-contained and
  may go anywhere: a stored generator with a self-borrow.
- **The cut-introduction rule** "κ captured inside an open lend gets type `U@'a C`" therefore has no
  `'a` to write. The obligation it was meant to discharge is in the **semantics**: at a stop with an
  open internal lend, `wpG`'s stop condition refuses. There are two conjuncts (BRIEF §3.1):
  - T1, conjunct 40: frames unchanged;
  - `↭`, conjunct 37: no new `mut` cell.

### 1.3 The binder that is needed, and where it goes: `∀♮`

The internal half is discharged in one of two ways:
- by the elaborator (S1), with no kernel change;
- where the elaborator cannot see the suspending code, by a **re-lendable lifetime binder on the
  callback** that suspends inside the lend.

**Syntax.** One computation-type former beside `∀`:

    C ::= … | ∀♮'x ⊏ @b. L ⊸ F_Σ(['x] B)        (L a lend type: Mut 'x T or Imm 'x T)

**Introduction (`∀♮I`).**

    Δ, 'x ⊏ @b; m : L, Γ' ⊢seg N : F_Σ(['x] B)     Γ' ⊢ 'x-free, Γ' ⊐ 'x
    ───────────────────────────────────────────────────────────── [∀♮I]
    Δ; Γ' ⊢ Λ♮'x. λm. N : ∀♮'x ⊏ @b. L ⊸ F_Σ(['x] B)

- `⊢seg` is `⊢` with one extra condition: at every subterm that may stop at a resuming operation of
  `Σ`, the live variables are `m`, paths into `m`, and slots of `Γ'`.
- `relend_chainΓ`'s hypotheses are this condition at a straight-line chain:
  - `hΓx`: `Γ'` is `'x`-free;
  - `hΓo`: `Γ'` outlives `'x`;
  - the residual `N_f` is typed in `m :: Γ'`.
- `Σ` may hold resuming operations. Its operation types are closed in lifetimes, as GhostEnd's
  theorems take them.

**Elimination: the resuming borrow constants.** One per printed constant, in the pattern of the
existing `*U` unwinding forms (`Core/EffBorrow.lean`):

    withbor♮ d : U(src ⊸ U(∀♮'x ⊏ ⊓Δ. L ⊸ F_Σ(['x] B)) ⊸ F_Σ(src ⊗ B))

- The term is GhostEnd's `withborUV d`, the same term as `withborU`. Only the callback's type
  differs.
- `d : src ⊸ F 1` is the source's destructor, which runs at a cancel.
- At `Imm`, `RelendI` and `ewpTS_I_frameR` play the same role.

**The binder's instantiation.**
- At each resumption the frame lends the source again, at a lifetime fresh for the resumer's list.
  These are `ewpTS_M_frameR` and `ewpTS_I_frameR`: `relendG`'s `fresh fun α => ptoMutS l α ls … ─⋆ wpG …`.
- The re-lend does not instantiate a frozen residual. It **re-derives** the next segment from its
  typing at the new lifetime: `relend_fin`, `fundamentalC` at `Δ.extend x b`.
- That is why `⊢seg` restricts what is live at a stop. It is GhostEnd's "the borrower re-lendable,
  its last segment re-derived from its typing at each new lifetime" (`GhostEnd/Program.lean`
  docstring).
- No relation is transported across an instantiation. Only the views are rebuilt, by the re-lend
  itself, and the `'x`-free frame values are carried (`gDenC_local`, `frame_outlives`).

**Outlives and lend end.**
- `∀♮` is a computation type, so it occurs in value types only under `U`, which has no outlives rule.
- A `∀♮` callback is stored, as in R6, as `[@c] U(∀♮'l. …)`, boxed by `[]I` from a context outliving
  `c` (rule 2).
- At the lend's end, the borrow's `['x] B` exit is unchanged.
- At a cancel, `withborR_compat`'s `ewp_then_owner` hands the owner to `d`. The lend is not re-opened
  (`GhostEnd/Drop.lean` docstring).

**The semantic clause added to Core's relation (sketch).** One new clause of `cC`. No existing clause
changes.

    cC (∀♮'x ⊏ c. Mut 'x T ⊸ F_Σ(['x] B)) ls δ e ≜ fun ρ =>
      ∀ l, Relend (opTableO (Row.tab Σ δ) l T δ) l T δ (finPost l T B δ) ls
             (.app (.app e (.val .unit)) (.val (.loc l))) ρ
    (and RelendI at Imm)

- `Relend` (`GhostEnd/Relend.lean:57`) is the least fixed point of `relendF`, written in `Prop` as
  `ewpTS` is.
- In one unfolding, the callback is lent at a fresh `α` below the bound and runs under `wpG`, to a
  value or to a stop admitted by the table. At either, its share is in `[α]` and hands the owner back.
- At a stop, the continuation is owed the owner and the next unfolding.
- `withborR_compat` is exactly `withbor♮`'s compatibility lemma given this clause.

**What `∀♮` does not cover.** Only `m` (and paths into it) may be live with an `'x` type at a stop. A
closure, iterator or object over `m` that is live at a stop is excluded by `⊢seg`. That is the
general case, §1.4.

### 1.4 The general case: the `Frz` former, and where it stops

The full freeze binder on `κ` would be a value former. It is stated here so that its cost is on
record.

    A ::= … | Frz C          κ : Frz((B_i ⊸ F_Σ R) & F_Σ 1)   at a new handler rule [handle♮]

- **Clause, in AllPosJ's shape (GAP.md §3.2 (B)).** `𝒱⟦Frz C⟧ ls δ v` holds when:
  - the resource splits into the ghost-ended internal lends (owners) and a retained part;
  - for every instantiation `ι` at the frozen stack's cut, with the views handed back at `ι`, the
    body is in `cC C` at the instantiated reading.
- **Agreement with Core at an empty frozen stack** is `allPosJNil`'s argument: `InstAt [] ι` forces
  the identity.
- **Its fundamental case at `[handle♮]` needs the thaw.** At a stop, the residual `K[·]` is a
  semantic object established at `α_x`: the bind lemmas discharged `K`'s obligation at the run's
  lifetime, not from a typing derivation. The clause asks for it at every `ι(α_x)`.
  - Unrestricted, that is `CoreThawTop`, and it is false (`not_coreThawTop`, machine-checked here).
    The witness is GAP.md §3c's `Λ. return ℓ₀ : ∀'0 ⊏ ⊤. F (Mut '0 1)` over a `mut` cell adjacent to
    `⊤`. Its world is a `TW` world (`tw_single_mut_empty`). The value is not claimed derivable, so
    this refutes the unrestricted statement, not a thaw restricted to typed residuals.
  - Restricted to residuals of typed programs, it is not stated and not derived. It needs either:
    - the residual's typing at the stop: a typed evaluation context, which is subject reduction for
      `κ`, and Core has no such invariant; or
    - a relation whose every `U` quantifies over instantiations: W's `RelendJ`, which diverges from
      Core on borrow-only programs (LEDGER §8, D1–D12).
  - `Restrat.Open.WpNatural`, the naturality of `wp` itself, is open. Its stated stopping point is
    `wp`'s `∀ρ_f` (`frame_outside_image`).
- **Not taken.** `Frz` is recorded for completeness. It is not part of the proposed set.

**The keep-open alternative, also not taken.** Here the lend stays open at its original `α_x` and is
never re-instantiated.
- A run that consumes `κ` would start with `κ`'s `mut` cell in its flattening and end without it.
  `not_upd_of_ended_mut` (proved, `experiments/LoopBorrow/LoopBorrow/Obstruction.lean`) says `↭`
  forbids that.
- `↭` is printed ([TR] p. 6 `wp`). Changing it for every run that may force a `κ` is a change to
  Core's `wpTS`/`wpG`, not a conservative extension.
- A typing discipline that keeps `κ` from being captured into a later lend's callback would make the
  identity instantiation always available **dynamically**. But `wpTS` quantifies over every `TW`
  frame, including frames with a newer lend below `α_x`, so the relation would still ask for the
  other instantiations. Not derived; no obstruction verified beyond that observation.

---

## 2. Conservativity

| piece | what changes | why Core's relation and theorems are unchanged on programs that do not use it |
|---|---|---|
| S0 (external) | nothing | no definition changes |
| S1 (lend splitting) | the elaborator only | the emitted terms use the existing borrow constants and `hnd`; `CDerives`, `cC`, `wpG` and every theorem are untouched; the checker certifies the split program as it certifies any other (a `CDerives` derivation) |
| S2 (`∀♮`, `withbor♮`) | one `CTy` former; one `cC` clause; one `CDerives` constructor per borrow constant | `vCE`/`cC` recurse on the type, so the new clause is read only at `∀♮` types. Every existing clause, and so `vC`/`cC` at every `∀♮`-free type, is the same definition by structural recursion. `fundamentalC` gains one case per new constructor and keeps its statement; the precedent is the six `*U` constants (`withbor1U` … `sliceBorrowIU`), added the same way with every existing statement kept (SPEC §19 *Baseline*). Functions over `CTy` (`subst`, `instT`, `VOutlives` through `U`, `TyEq`'s `CTyEq`) need a case each. `CTyEq` at `∀♮` should mirror its `∀` clause; `tyEqInst` would need re-running, which is not attempted |
| `Frz` (not proposed) | a `VTy` former and a handler rule | conservative as a definition, but its fundamental case needs the thaw (§1.4); W's route to the thaw is not conservative (LEDGER §8) |

**Why S2 is not tier 2 again.** ProbeD1 put the lend stack into every `U` clause (`RelendJ`), into
`∀`'s own-lend conjunct, and into the guard. The ledger's D1–D12 are what that cost on borrow-only
programs. `∀♮` adds a clause read only at `∀♮` types, and it transports no relation: it re-derives the
segment from typing. The `TW` world, `wpTS`, `wpG`'s stop conditions T1 and `↭`, and `Ext` are
untouched. At each stop of a `∀♮` callback the lend has already been ended by the frame, with
6.65's exit handing the owner back into the stop's share, so the stop condition sees no open lend.

---

## 3. The six programs

Each entry says whether the hypothesis types the program, what does, and what remains.

### 3.1 A stored effectful callback that captures a borrow (R6, `effect-polymorphism.md` §5.6)

- **Capturing a borrow is already allowed by R6.** Rule 1 says a one-use callback captures anything.
  Rule 2 boxes it at `@c` below every captured borrow (`[@c] U(…)`, `boxI`). This is S0.
- **R6 rule 3** forbids capturing a *stateful capability* (`not_sharedCapture`). That is a sharing
  and linearity restriction, not a lifetime one. No lifetime former touches it. The hypothesis does
  not type such a program, and neither does anything here.
- **If the handler of its control operation is inside the lend** that the call runs in, the program
  is S0.
- **If the handler is outside that lend**, the lend is internal to `κ`, and the stop is inside the
  **callee's** body. The elaborator cannot split it.
  - It types with S2 when the stored type is `[@c] U(∀♮'l. Mut 'l S ⊗ A ⊸ F_p(Mut 'l S ⊗ B))`, the
    R6 type with `∀♮`, and the body is `⊢seg`.
  - The body's stops must be in the body itself. **A `∀♮` callback calling another `∀♮` function with
    `m` is not derived.** The nested frames must be re-lent coherently at one instantiation, which
    is GhostEnd's stacked relation `vRLs` and GFPA (BRIEF §4, OPEN).
  - **Remains:** compositional `∀♮`. Ranked in §4.

### 3.2 An effectful object over a lent capability (`effect-model.md` §3.2)

The program: a reader with `next : F_{Log}(A ⊕ 1)` and `close : F_{Fail} 1`, over a lent counter. It
is typed and run in SIB (EffModelRel), not in Core.

- **`Log` answering:** S0. It is a call inside the lend (SPEC §19 acceptance 2, `logInBorrow`).
- **`Log` a control operation with its handler inside the counter's lend:** S0, and the object is a
  `U(ν…)` value confined to the lend. This is `corpus/gen-borrowed.bc`'s shape.
- **`Log` a control operation with its handler outside the lend:** the object, a `U` value over the
  counter view, is live at the stop.
  - That is the general case (§1.4). Neither S1 nor S2 types it, because the object is a derived
    value.
  - **The hypothesis's `U@'a` does not help.** The lend is internal to the `Log` handler's region,
    so there is no `'a` at the cut.
  - **Remains:** the restricted thaw. Not derived.

### 3.3 Generators holding a capability across `yield` (`gen-digits`, `gen-lazy`, `gen-lines`, `gen-adapters-io`)

- **Their stated blocker is not a borrow.** Each pending header says the same thing: an **owned**
  capability (`ref input`/`ref output`, no destructor, decision 31) is live across an affine
  `yield`. A cancel answers `()`, so the capability cannot come back. The fix named in every header
  is one of:
  - a continuation whose cancel hands back a residual: K3, SPEC §19 *Finalisers*, §14's `close`
    residual;
  - a capability with a destructor;
  - a `linear ctl` `yield` (no `break`).

  None of these is about lifetimes. The hypothesis does not type these programs.
- **The borrowed variants are S0** (inspection, not run). For example,
  `fn digits<'a>(c: mut 'a In) -> 1 with Yield[i32]` with `main` lending `stdin` around the `for`.
  - The `for`'s handler is then inside the lend, so `κ` holds an external borrow, as `tens<'a>`
    (`corpus/for-data-div.bc`) does today.
  - That `bytes` takes a `mut 'a In` is read off `gen-adapters-io.bc`'s `bytes(&mut c)`.
- **`gen-adapters-io` has a second, internal part.**
  - `line(c)` owns `c` and lends it to `bytes(&mut c)` across `yield`.
  - The iterator `U(iter …)` over that lend is a derived value live at the stop, so it is the
    general case (§1.4).
  - If `line` instead took `c: mut 'a In`, the lend would be external and it would be S0.

### 3.4 `corpus/reject/gen-self-borrow.bc` and `corpus/reject/for-lend-resumes.bc`

- **`gen-self-borrow`** (`borrow imm c { 'x, b -> yield(*b); () }`, with the handler in `main`) is
  an internal `Imm` lend. Only the view `b` is live at the stop, and the operand `*b` is evaluated
  before it. The hypothesis does not type it (no `'a` at the cut, §1.2).
  - **S1:** split at the `yield`, as `let v = borrow imm c { b -> *b }; yield(v); borrow imm c { b -> () }`.
    `c : Ref i32` is live across the `yield` and has a destructor, so the drop glue covers the cancel
    (SPEC §19 *Typing*).
  - **Semantically the unsplit form is also proved at Core σ=[]:** `imm_spans_yield` (6.64 at a
    resuming table, `ewpTS_I_frameR`, every hypothesis discharged).
- **`for-lend-resumes`** (`for x in &a { yield(*x) }`, `a` owned in the generator) is an internal
  lend of the whole array across the loop.
  - **S1:** a per-turn borrow, `for i in 0..len { let x = borrow &a { copy a[i] }; yield(x) }`.
    This is the form `bumped(a: array i32)` in `corpus/for-data-div.bc` already compiles to ("each
    element copied out under a borrow of one turn").
  - If `x` were used after the `yield`, the path `a[i]` would be re-derived after the re-lend.
  - The unsplit form, a block lend across a stop, is D12's territory (LEDGER §11.7) and is not
    needed.

### 3.5 `corpus/pending/async-borrow.bc`

- **Its own header already says the kernel covers a task holding a borrow within the borrow's
  scope.** The task's `imm 'a List` is external to the scheduler, which runs inside
  `borrow imm l`: S0. The blockers it names are not lifetime formers:
  - the surface (`async fn`, `spawn`, `.await`);
  - the runtime and the scheduler;
  - `corpus/pending/borrow-across-loop.bc`: a scheduler loop inside one borrow body, the
    divergence × borrow question;
  - a queue of tasks from different scopes. That needs no `∃'a` while the queue lives inside every
    scope it holds tasks from: `[@c] U(Loop …)` at the meet `c`, R6 rule 2. An `∃'a` would be
    needed only for a queue that outlives some task's scope, and then the task could not be run.
- **What is internal:** `yield_now()` inside `fold_imm`'s algebra.
  - `foldImm` lends each node by `withload` inside its own term (`Core/FoldImm.lean` docstring), so
    the stop is inside a kernel constant's internal lend. The elaborator cannot split it.
  - The algebra's live set at the stop is the node view `b` and data `s`, which is `⊢seg`'s shape.
  - So it needs `foldImm`'s compatibility at a resuming table with each node re-lent: S2's technique
    inside `foldImm_compatX` (by induction on the witness size, `withload_sized`). Not derived.
  - It also needs effectful folds at all (K4, #161: `foldImm`'s algebra is `F R`, not `F_Σ R`), which
    is independent of lifetimes.

### 3.6 Generative handler labels (SPEC §19 *Names*)

- **The confinement SPEC asks for** ("a scope-indexed thunk with no elimination to plain `U`") is
  S0 plus one rule.
  - The handler opens a lifetime `'h` and answers `['h] R`: HandlersAsBorrows' "an answering handler
    opens a fresh lifetime", applied to a control handler.
  - The label is a cell lent at `'h` around the `hnd` frame, so the `hnd` frame and `κ` hold a borrow
    at `'h`. That lend is **external** to the handled region, so it is Core today.
  - `κ : U C` is never boxable (`ctxOutlives_not_of_live_thunk`), so it cannot be returned through
    `['h] R`. Semantically, `κ`'s share holds the `'h` cell and is not in `Res_h`.
  - So a stale `κ` cannot meet a reused label. No T2 former is needed, and the box/`[]E` concern does
    not arise (§1.1).
  - **Inspection, not built.**
- **The semantic core of handling at a run-time name is already proved:** `handleAt_compatC`,
  `fresh_exists` (`experiments/SecondClass`, `docs/second-class-and-system-c.md` §2.1).
- **What remains** is SecondClass §2.2:
  - (a) a machine step that supplies fresh names (a cell whose location is the name suits linear and
    affine `κ`);
  - (b) name variables in rows, read through a map in the relation.
- **Generative names change a decided choice.** The decided algebra lists "Static per-site names
  (SPEC §19, *Names*): an operation reaches the handler site it names" (`decisions.md` on
  `tier1-effects`). Adopting generative labels is the user's call: a hard-stop item 1 for any unit.

### Summary table

| # | program | the hypothesis types it? | what types it | remains |
|---|---|---|---|---|
| 1 | stored callback capturing a borrow | no new former needed (R6 rule 2) | S0; with the handler outside the lend, S2 (`∀♮` in the stored type) | R6 rule 3 is not a lifetime matter; compositional `∀♮` |
| 2 | reader object over a lent counter | no (no `'a` at the cut) | S0 for an answering `Log` or a handler inside the lend | handler outside: the restricted thaw (open) |
| 3 | generators holding a capability | no (blocker is the residual on cancel) | the borrowed variants: S0 | K3 residual / destructor; `gen-adapters-io`'s internal iterator: thaw |
| 4 | `gen-self-borrow`, `for-lend-resumes` | no (no `'a` at the cut) | S1 (split, per-turn borrow); `imm_spans_yield` proves the unsplit self-borrow | elaborator liveness split |
| 5 | `async-borrow` | no new former needed (header: kernel covers it) | S0 for the tasks; S2 inside `foldImm` | surface, runtime, scheduler, borrow-across-loop, effectful folds; `foldImm` at resuming tables |
| 6 | generative labels | no former needed | S0 + a lifetime-opening control handler | name supply, name variables in rows; a decided choice to reopen |

---

## 4. Tier-2 results reusable for the fundamental case, and new obligations by risk

### 4.1 What is reused

At Core σ=[], the S2 fundamental case:

| result | file | use |
|---|---|---|
| `ewpTS_M_frameR`, `ewpTS_I_frameR` | `GhostEnd/Relend.lean:117`, `ImmLend.lean:175` | 6.65 and 6.64 at a resuming table: the binder's instantiation at each resumption |
| `relend_chainΓ`, `relend_chain`, `relend_fin` | `GhostEnd/Chain.lean:176, :201` | `∀♮I`'s case for a straight-line `⊢seg` body: segments re-derived by `fundamentalC` at the new lifetime, `'x`-free values carried (`gDenC_local`, `frame_outlives`) |
| `withborR_compat`, `ewp_then_owner`, `cancel_then` | `GhostEnd/Drop.lean:108` | `withbor♮ d`'s compatibility, the affine cancel path with the owner's destructor |
| `withbor_spans_yields_cC`, `imm_spans_yield`, `spans_two_affine_yields`, `withborR_spans_yields_cC` | `GhostEnd/Program.lean:188`, `ImmLend.lean:252`, `Drop.lean:318` | closed instances: the acceptance tests for S2 |
| `handleR_spans_yields`, `withborR_spans_yields_sem` | `GhostEnd/Drop.lean:284, :230` | the handled form (`handle_compatC` around `withborU` at a resuming row), as `gen-self-borrow` needs |
| `Restrat.Emb.models_mapN_iff` | `Restrat/Injection.lean:189` | `⟦Δ⟧` invariant under re-stratification, if a later unit moves lifetimes instead of re-deriving |
| `tyEqInst`, `tyEqRoomBlind` | `ProbeD1/GapCover.lean:355, :414` | `TyEq` is room-blind: an `Imm` leaf's coherence (`CohE`) survives an instantiation. S2 does not need it (no transport); `Frz` would |
| `instRealisesCut`, `allPosJTransport`, `allPosJNil` | `ProbeD1/GapPos.lean:43, :136, :98` | the cut-based `∀` (reading B) and its agreement with Core at σ=[]: the shape of `Frz`'s clause and its conservativity at an empty frozen stack (§1.4) |
| `coreAllAdjacent`, `coreAllNotNatural`, `not_coreAllImpCutAll` | `ProbeD1/GapWitness.lean:127, :150` | the warning: Core's `∀` reads the room between lifetimes; `not_coreThawTop` is their corollary |
| `not_upd_of_new_mut`, `not_upd_of_ended_mut` | `LoopBorrow/Obstruction.lean:49` | why the keep-open route is not conservative |

**Not reusable for a conservative extension.** W's relations (`vRLM`, `cRLM`, `RelendJ`, the guard
`PlaceViewsL`, `CohS`, `RetainedPay`) and everything stated at them. They are the lend stack in every
`U`.

### 4.2 New obligations, ranked by risk

1. **HIGH — the restricted thaw, for derived values live at a stop** (§1.4; programs 2 and 3's
   `gen-adapters-io` in their internal forms).
   - The unrestricted form is false (`not_coreThawTop`).
   - A form restricted to residuals of typed programs needs a statement that the relation can carry.
     Two candidates:
     - typed evaluation contexts at stops: subject reduction for `κ`;
     - GFPA (GhostEnd's arising-guarded generalised fundamental lemma; the `lam` and `allI` rows are
       proved, the rest is OPEN, and it lives at GE).
   - `WpNatural` is open, and `mut_not_natural`'s arising check is open (BINDER §4).
   - Not derived; no obstruction verified for the restricted form.
2. **MEDIUM — compositional `∀♮`** (program 1 with nested callees; any `∀♮` body calling a `∀♮`
   function with its view).
   - Nested frames re-lent at one instantiation is the stacked relation's problem (GhostEnd `vRLs`,
     #282–#283).
   - The risk is that it pulls a lend stack back into the clause. Mitigation: state `∀♮`'s
     compositionality as a lemma about `Relend` at two locations before building anything.
3. **MEDIUM — `⊢seg` beyond chains.**
   - `relend_chainΓ` covers `yield y₁; …; yield yₙ; N_f` with closed payloads answering `()` at a
     linear entry (`hq`, `hPB`); `withborR_spans_yields_cC` covers the affine one.
   - A segment with arbitrary typed code between stops, an operation answering a non-unit value, and
     stops inside `case` branches all need `relend_chainΓ`'s induction generalised to the shape of the
     typing derivation. This is GFP's statement restricted to `⊢seg`.
   - GFP unrestricted is refuted as we stated it (`not_gfp`), with a witness that does not arise
     (`wpG_below_not_arises`). So the restriction must be visible in the statement.
4. **MEDIUM — `foldImm` at resuming tables** (program 5).
   - `foldImm_compatX`'s induction on witness size, re-run with `ewpTS_I_frameR` at each node's
     `withload`.
   - Also needs effectful algebras (K4, #161), which is independent.
5. **LOW — S1 in the elaborator.**
   - A liveness computation at resumable points, re-derivation of paths after a re-lend, and the
     per-turn borrow for `for` over a lent array.
   - No proof obligation: the kernel is unchanged and the checker certifies the result.
   - Risk: what the user sees when a split is refused. The message must name the derived value that
     is live, as `gen-adapters-io`'s does today.
6. **ORTHOGONAL — the residual on cancel** (K3) for program 3, and the name supply plus name
   variables in rows for program 6.

---

## 5. Lowering (BRIEF §1a)

- **S0.**
  - A suspension holding an external borrow is a state-machine state holding the borrow as a word,
    the address (Representation: borrows are locations).
  - This is today's behaviour for `tens<'a>` and `gen-borrowed`, at today's counts.
- **S1.**
  - The split's re-lend is erased. `withbor`'s term is `λr. λf. f [] r` plus a pair; the view is the
    owner's own location, and lifetimes are ghost.
  - After closure conversion the split adds no allocation and no dispatched call [inspection; not
    measured]. `bcc-counts` would confirm it on a split `gen-self-borrow`.
  - The place that spans the suspension stays a real cell: one allocation, the known cost (BRIEF §1a,
    "a place that spans a suspension stays a real cell today"). That is `gen-cell`'s cost today, the
    hand-written workaround.
  - **Pin does not arise.** The view is re-derived from the place at each resume, so the address is
    read afresh after the re-lend. If inline placement in the frame (P13) lands, a state that moves
    still gets a correct view, because nothing holds the old address across the stop. This is the
    freeze binder's location half for free, but only for views.
- **S2.**
  - `withbor♮ d` is `withborU`'s term, so it lowers as today's unwinding borrows. Its `ubind` is a
    finaliser frame in the state (SPEC §19 *Lowering*: "borrows' unwinding forms are finaliser
    frames, so their lends end here"), and a cancel runs `d` on the owner.
  - The re-lend at each resume is erased as in S1. No runtime cost beyond `withborU`'s, which is a
    finaliser variant in the state [inspection].
- **`Frz`, the general case (not proposed).**
  - A derived value over an internal view (an iterator over a buffer the state owns) holds an address
    into the state's own place.
  - With places as cells (today), the address is stable and the state may move.
  - With inline placement, the state becomes self-referential, which is Rust's `Pin` case. Either
    the state is fixed after its first resume, or the derived value is re-derived, which in general it
    cannot be.
  - So the general case also has a lowering constraint that S0–S2 do not have.

---

## 6. Verdict

**One former does not bridge.**
- The external half is already BoLo's unboxed `U` (machine-checked here). So the hypothesis's former
  would be redundant where it would be easy.
- The internal half cannot be a type at the cut: the internal lifetimes are not in the handler's `Δ`.
- The hard semantic step is **not** the solved cut-based `∀`. Tier 2 solved it at W, by changing every
  `U` clause, and in `TyEq`. Core's relation is not invariant under internal re-instantiation in
  general (machine-checked here, from `coreAllNotNatural`).

**The smallest conservative set** is:
- **S0**: nothing;
- **S1**: liveness-based lend splitting in the elaborator;
- **S2**: one binder, `∀♮` on suspending callbacks, with resuming borrow constants. Its clause is
  GhostEnd's `Relend` over Core's `wpG`. Its fundamental case is proved at Core σ=[] for
  straight-line bodies, including the affine cancel.

| programs | covered by |
|---|---|
| 4 | S1 |
| 5 | S0 for the tasks, S2 inside `foldImm` |
| 6 | S0, plus name machinery and a decided choice the user would have to reopen |
| 1 | S0, and S2 (non-compositional) with the handler outside the lend |
| 2 | S0 in its handler-inside forms |
| 3 | the borrowed variants: S0 |

**The program class that breaks the idea is a derived value of an internal borrow live at a stop.**
- Examples: `gen-adapters-io`'s `bytes(&mut c)` iterator in a generator that owns `c`; program 2's
  reader object with `Log` handled outside the counter's lend.
- Such a value is a Core `U` value at a type mentioning the internal lifetime. Resuming must move
  that lifetime (a re-lend under a younger resumer's lends; D-ORD), and Core's `U` is not invariant
  under the move in general.
- Keeping the lend open instead is refused by the printed `↭` (`not_upd_of_ended_mut`).
- Both known routes change Core for every program:
  - the stack in every `U` (tier 2);
  - a relaxed `↭` at runs that force `κ`.

**Status of the remaining routes.**
- A restricted thaw, through typed residuals or GFPA, is not derived, and no obstruction is verified.
- It is the one place where "a principled `Pin`" would have to be built rather than reused.
- Rust rejects these programs too (E0626 without `Pin`). The prior-art survey's recommendation, to
  adopt the slice and split by liveness, stands, with S2 as the banked second tier it describes.

---

## § Segment-shift check

**The hypothesis.** At a stop, everything the suspended region opened since its handler was
installed is the top segment of the lifetime stack above the handler's frame. A stop packs that
segment into `κ`, and a resume pushes it back on top of a possibly different stack. The move shifts
the whole segment together, so no gap opens inside the segment, only between the segment and what
lies below it.

**Orientation.** `Life = ℕᵒᵈ`.
- `⊤ = 0` is the longest lifetime.
- A younger lend is a larger natural, so it is lower in the order. The top of the lend stack is the
  bottom of `Life`.
- `Restrat.Emb c` (`experiments/Restrat/Restrat/Injection.lean:31`) fixes every lifetime `⊒ c`.
- `Emb.shift c k` (`:94`) sends every `x ⊏ c` to the lifetime `k` younger:
  - it fixes the cut and everything older;
  - it translates the segment strictly younger than `c` uniformly;
  - its `k` unhit lifetimes lie between `c` and the moved segment.

So **`shift c k` is exactly the hypothesis's move**. `k` is the number of lends the resumer has
open above the cut at the resume. Those lends must be older than the pushed segment, because `κ`
runs inside their callbacks.

**Probe.** `ProbeD1/SegShift.lean` elaborates with `lake env lean`.
- It contains no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or
  `implemented_by`.
- `not_segShiftInv`, `segShiftFailsAtEveryCut` and `segShiftFailsWithRoom` each depend on
  `[propext, Classical.choice, Quot.sound]`.
- It is not in `ProbeD1.lean`'s imports.

### Check 1: is Core's relation invariant under a whole-segment shift?

**Statement.** `SegShiftInv` (`SegShift.lean:46`):

    ∀ c k C ls δ e ρ, cC C ls δ e ρ →
      cC C (ls.map (srecRestrat (shift c k))) (LSub.mapN (shift c k).toNat δ) e ((shift c k).relRU ρ)

The reading, the records and the resource are moved together.

**Result: REFUTED (machine-checked).** Three results, each stronger than the last.

1. **`not_segShiftInv` (`:56`).**
   - GapWitness's `adjθ` is literally `segθ ⊤ 1`, by `rfl` (`adjθ_eq_segθ`, `:53`).
   - So `coreAllNotNatural` is an instance of a **whole-segment shift**. The segment is every
     lifetime below `⊤`, here the one cell at `1`.
   - The gap `{1}` opens **between the cut and the segment**, which is the kind of gap the
     hypothesis allows. It does not open inside the segment.
2. **`segShiftFailsAtEveryCut` (`:156`, `:163`).** `⊤` is not special.
   - For every cut `c = m` and every `k > 0`, take `∀'0 ⊏ 'c. F (Mut '0 1)` with `'c ↦ m` and
     `Λ. return ℓ₀`.
   - The clause holds at a `mut` cell at `m+1`, adjacent to the cut (`cut_holds`, `:76`).
   - It fails at the cell's image `m+1+k` (`cut_fails`, `:92`).
   - The reading is fixed, because `m` is at the cut (`mapN_cutδ`). Only the segment moves.
3. **`segShiftFailsWithRoom` (`:260`, `:270`).** A segment that already has room below the cut is
   not safe either.
   - Take `∀'0 ⊏ 'c. ∀'2 ⊏ '0. F (Mut '2 1)` and `Λ. Λ. return ℓ₀`.
   - The clause holds at a cell at `m+2`, one free lifetime below the cut (`cut2_holds`, `:182`).
   - It fails at the cell's image `m+2+k` (`cut2_fails`, `:210`).
   - Nested `∀`s read distance from the cut. That `d` nested `∀`s read distance `d` is by
     inspection; `d ≤ 2` is machine-checked.

**Side conditions.**

| side condition | status | evidence |
|---|---|---|
| "no gap inside the segment" (the hypothesis's own) | **insufficient** | (1) and (2): the failing gap is the one between the cut and the segment |
| "the segment is not adjacent to the cut" | **insufficient** | (3) |
| "no `∀` type in play" | **insufficient at the printed `vDen`** | `Restrat.MutCounterexample.mut_not_natural` (`Restrat/MutCounterexample.lean:148`), at the same `shift ⊤ 1`; see below |
| the moved part has **no running state**: internal `mut` cells ghost-ended at the stop (D14.4 `Freeze`), and the segment's code **re-derived** from its typing at the shifted `δ` | **holds** | `Restrat.Segment.restrat_segment` (`Restrat/Segment.lean:73`): `SemC` at `δ` gives `cC` at `mapN (shift c p) δ`, outer variables fixed. `Restrat.Fixed.relRU_of_inStratum` (`Fixed.lean:83`): every cell in `Res_c` is unmoved |
| the configuration **arises** from a typed program | **not derived; no obstruction verified** | see below |

- **The "no `∀` type in play" row.** At the printed `vDen`, `𝒱⟦Mut 'a (Imm 'b 1)⟧` fails under
  `shift ⊤ 1`. The cause is `ptoMut`'s stored-predicate **equality**. The image of `𝒱⟦S⟧_δ` misses
  resources with cells in the gap, and `𝒱⟦S⟧_{e∘δ}` holds there.
  - Core's `ptoMutS` has the same equality (`ofS Q = P ls₀`, `Core/Relation.lean:46`).
  - The port to Core's `vC` is **not done**. Its `Imm` version needs records, because `Coh` at an
    empty record list is false. A `Mut`-of-`Mut` version is the cheap route.
- **The "no running state" row.** This is S2/`∀♮`'s route (§1.3). It does not transport a
  relation, so it is not the hypothesis's move.
- **The "arises" row.** Neither witness is claimed derivable.
  - The adjacency witness needs a value at `∀'x ⊏ 'e. F (Mut 'x T)`, with `'e` at or above the
    cut, that returns a segment cell. Typing would have to derive `'x ⊑ 'y` from `'x ⊏ 'e` for a
    `'y ⊏ ⊓Δ_h ⊑ 'e`. That is not derivable in `⟦Δ⟧`'s models, which include room.
  - So typed residuals plausibly never read the room. Stating that needs the residual's typing at
    the stop, which is subject reduction for `κ`, and Core has none.
  - Or it needs naturality of `wpTS`. `Restrat.Open.WpNatural` is open, and its proof method stops
    at `frame_outside_image` (`Restrat/Open.lean:37, :43`).

**Is any side condition met at stops?**
- The two "insufficient" rows are not met in general anyway:
  - the region's lend lifetimes range over **every** `α ⊏ @bnd`, including `↓c` (`cC .all`,
    `Core/Relation.lean:161`, which has no freshness conjunct);
  - live values at a stop may have `∀` types.
- The "no running state" condition is met only if the stop ghost-ends the segment's lends and
  re-derives the residual. That is S2, not packing.

### Check 2: are the region's lends exactly a top segment above the handler's frame?

All of this is inspection unless marked otherwise. `Core/…`, `Paper/…`, `SPEC.md` and `lib/` cite
`~/repos/borrow-core` at `main` (4b267fc).

**Core today: vacuously yes.** Every borrow constant's effectful form is unwind-only.
- `Row.Unwind` (`Core/EffBorrow.lean:133`; SPEC §19 *Borrows*) means every operation is abortive.
- So no resuming stop happens inside an open lend, and the region's open-lend set at every
  resuming stop is empty. The tier1-effects §25 capture cell is an `own` cell with no lifetime, so
  it changes nothing here (`~/repos/borrow-core-tier1/SPEC.md` §25, read only).

**Under the extension the hypothesis needs** (borrow callbacks that may stop at a resuming
operation), it depends on what the stack is measured against.

| kind of lend | in the top segment? | why |
|---|---|---|
| a lend opened by the region (`withbor`1/2, `withload`, slice borrows) | **yes, with respect to the handler's named lifetimes** | `[handle]` types the body in the handler's `Δ_h` (SPEC §19 *Typing*). Each lend binds `'x ⊏ ⊓Δ'` with `Δ' ⊇ Δ_h` (`CDerives` at `Δ.meetOfDom`, `Core/Fundamental.lean:241–250`; `axWithbor*Ty`, `Core/Types.lean:1885–1897`). So every internal lifetime variable is below every variable of `Δ_h` |
| a reborrow of an external borrow (`withbor`3, `Mut @a A ⊸ (∀'x ⊏ @bnd. …)`) | the reborrow's lifetime **yes**; the source cell **no**, and it stays fixed | the source cell is at `⊒ @a ⊒ c`. At the TW level a reborrow's `β` is youngest (`TW.reb`'s `StratumLe W β`, `Core/World.lean:127`; `rebDeep`'s `W.InStratum β`, `:134`) |
| "mixed": a place owned outside, lent inside | **does not exist in Core** | `[handle]` splits `Γ` into `Γ₁` (clauses) and `Γ₂` (body), and `Ref A` is linear. A place lent inside the region has been **moved into** it, so this is the internal case with the `own` cell travelling in `κ`. Alternatively the elaborator lends it **around** the handler and passes the view in, which is external (S0). The surface `&mut c` at a non-borrow parameter is take-and-hand-back, not a lend (SPEC.md:970–972) |
| lends of the **caller's** frames that are not named in `Δ_h` | **interleave** | the relation instantiates the region's lends at every `α ⊏ @(⊓Δ_h)δ` (`Core/Relation.lean:161`). `TW.mutFold`/`immFrame` put no order premise on the new cell's lifetime (`Core/World.lean:115, :135`). So an internal `α` may be older than a caller's live lend `'y ⊏ @(⊓Δ_h)δ`, and `shift c k` would then move `'y`'s records (`srecRestrat` on `ls`) too. Choosing the cut as the youngest live lifetime does not help, because the `∀` still ranges over `α` above it |
| a handler clause's own lends before it resumes | **not in the segment; they are the gap** | the clause is typed in `Δ_h`, so its lend `'h ⊏ ⊓Δ_h`. Pushed on top, `κ`'s segment must be younger than `'h`. These lends are the `k` in `shift c k`, exactly where Check 1's witnesses fail. Lends `κ` opens after the resume are bounded only by its own static `Δ'`, which does not contain `'h`, so typing does not keep them below `'h` either |
| nested handlers | **yes, nested segments** | an inner handler's `Δ_i ⊇ Δ_h ∪` the outer region's lends open at its install, so its segment is a sub-segment |

**Nested handlers in more detail.**
- An inner clause holding a packed `κ_inner` and performing an outer operation contributes
  `κ_inner`'s packed lifetimes and its own lends to the outer segment.
- Their relative order is unconstrained by typing. They move together under the outer shift.

**Deep reinstall.**
- `kappa` reinstalls `hnd H K[y]` (`Paper/S3_Dynamics/Definitions.lean:438`). A handler frame
  carries no lifetime (`hndVal`, `:352`).
- So after a resume, the cut of later stops is the resumer's position, not the original `c`.

**Summary.** The top-segment picture holds for the region's lifetime **variables** relative to
`Δ_h`. It does not hold relative to **all live lifetimes**, because unnamed caller lends interleave
in the relation's quantifier. Clause lends always sit in the gap between the cut and the pushed
segment.

### Check 3: classification of the breaking programs

| program | borrow | class | does the hypothesis cover it? |
|---|---|---|---|
| `corpus/pending/gen-adapters-io.bc` `bytes(&mut c)` | **none** | **owned, not a borrow** | not needed. See the correction below |
| reader object, `Log` handled outside the counter's lend (`effect-model.md` §3.2; `pReader`, `EffModel/Programs.lean:163`, with `withCounter` (`:31`) inside the `Log` handler) | counter lent as `x : Mut 'l Ctr`; the reader is `U(F_Log int & F_Fail …)` over `x` | **internal**: the counter is allocated, or moved, inside the region. In the surface "mixed" form (counter made outside, lent inside), Core moves it in, which is still internal | **not derived**. Packing moves `'l` and the reader with it. The reader's type has no `∀` and `'l` is not in it, so neither machine-checked witness applies to its type. Its obligation is `wpTS` naturality along the shift (`WpNatural`), which is open. The payload `int` mentions no moved lifetime, so `mut_not_natural`'s mechanism does not apply either |
| `corpus/reject/gen-self-borrow.bc` | `borrow imm c {'x, b -> yield(*b); ()}`, `c` allocated in `selfref` | **internal** `Imm` lend. No derived value is live at the stop (`*b` is read before it) | **not derived** by transport, since the frozen residual is untyped. Covered **without** the hypothesis by re-lending: `imm_spans_yield` (GhostEnd `ImmLend.lean:252`, Core σ=[]) and S1 |
| `corpus/reject/for-lend-resumes.bc` | `for x in &a { yield(*x) }`, `a` from `array_new` in `elems_of` | **internal** slice lend of the whole array around the loop (SPEC.md:1799, :1883). Live at the stop: the view family, at a type mentioning `'x` | **not derived** by transport. The view family is `⊢seg`'s shape (the lend's own view), so S2 applies in principle and S1's per-turn borrow certainly does |

**No program in the set is external-only, and none is mixed at the Core level.** The hypothesis's
proposed typing, which types only mixed loans by the owner's scope, therefore has nothing to type
in these programs. Its whole load is the transport of the internal segment, which is Check 1.

**Correction to §3.3, §0 and §6 of this file, about `gen-adapters-io`.**
- `bytes : In => U (iter u8 In In)` (`lib/io.bc:114`). The parameter is not a borrow type.
- So `&mut c` elaborates to take-and-hand-back: "the call takes the place and hands it back"
  (SPEC.md:970–972).
- The corpus message's type, `U (iter u8 (ref input) (ref input))`, has **no lifetime**. The
  iterator **owns** `c`.
- So `gen-adapters-io` contains **no internal borrow**. It is not an instance of "a derived value
  of an internal borrow live at a stop". Its only blocker is the one its header names: an owned
  capability with no destructor across an affine `yield` (K3).
- The derived-value class that defeats S1/S2 is represented in this set only by the reader object
  with `Log` outside the lend.

### Verdict

**The packing hypothesis does not survive as stated.**
- Shifting a whole top segment is exactly `Restrat.Emb.shift c k`. Core's relation is not
  invariant under it, at every cut and every `k > 0` (machine-checked).
- The gap that breaks it is the one the hypothesis permits, between the cut and the segment, and it
  is filled by the resumer's lends.
- Room already present does not help (machine-checked at depth 2).
- What is known to work is to re-derive the segment, not to transport it: `restrat_segment` with a
  ghost end, which is S2.
- Transport restricted to configurations that typed programs reach is **not derived; no
  obstruction verified**. It needs subject reduction for `κ` or `WpNatural`.

**Unspent and untranscribed items.**
- `WpNatural` (open).
- A Core port of `mut_not_natural` (not done).
- Residual typing at stops (not in Core).
- The arising status of every witness here (unchecked).
