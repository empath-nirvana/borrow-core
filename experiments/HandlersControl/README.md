# Handlers control: state behind control, reentry, capture, and the closure outlives rule

**Scope.** Issue #170, follow-up to `experiments/HandlersAsBorrows` (#184). Theory index T20,
with T1 (#172), T2 (#173) and T15 (#182).

**Build.** `lake build HandlersControl`. The library is non-default, imports `HandlersAsBorrows`
(and through it the paper layer), and nothing imports it.

- **Not used.** No CBPV, arrays, `count_try` or frontend code.
- **Hygiene.** No `sorry`, `axiom` or `native_decide`. Every `#print axioms` is within
  `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Tac.lean` | `dead`, a tactic for `Ctx.Dead` goals |
| `Behind.lean` | §1: frame-owned state, operations as requests; `d_progU`, `progU_runs`, `progP_eval`; `no_uniform_comp` |
| `Reentry.lean` | §2: `memo`; `d_memoProg`, `memoProg_runs`, `memoPair_eval`; `no_shared_app`, `spanFwd_refused`, `BorrowSpansForward`, `not_borrowSpansForward` |
| `Capture.lean` | §3: `lam_bang_persistent`, `multiShot_ref_refused`, `multiShot_imm_refused`, `forget_not_lolli`; the programs `twoShot`, `abortProg` and `laterProg`/`laterU`, each typed, safe and run |
| `Outlives.lean` | §4: `box_lolli_outlives_iff`; `crossProg`, typed, safe and run |

---

## 0. Answers

1. **State behind control.** There is a construction, in BoLo + `!`, with two limits.
   - **The construction.**
     - The handler's frame owns the state as a `Ref S`.
     - An operation is a *request* `inj₂ (a, k)` that carries the rest of the computation as an
       owned closure `k : B ⊸ R`.
     - The handler updates the state and resumes `k`.
     - The capability carries no resource, so it is shareable.
   - **The acceptance test.** Two blocks performing operations of one stateful handler is typed,
     safe by the FP, and run (`progP_eval`: the second block sees the first's update).
   - **Limit (a): bounded depth.** The computation type must be unrolled by the number of
     operations. A single capability type used at unboundedly many sites needs
     `X = R ⊕ (A ⊗ (B ⊸ X))`, which no BoLo type solves (`no_uniform_comp`). That needs `μX` with
     `X` under `⊸` (T15, #182), or a native capture construct (§5, K-a).
   - **Limit (b): the program is written with explicit continuations.** Direct style needs K-a.
   - **In direct style, no shareable token can carry state:**
     - an `Imm` token lends a cell that comes back unchanged (`[TR]` 6.64, `wp_I_frame`);
     - a `!` token holds the empty resource (`vX`'s `!` clause, SPEC §2).
2. **Reentry.**
   - **The rule needs no new typing rule.** Once `resume` and `forward` take the state token, the
     rule is BoLo's linearity of that token: `withbor σ` consumes `σ` for the scope of its
     callback.
   - **`memo` is accepted** with separate `get`/`insert` borrows around a re-entrant forward:
     typed, safe, and run, with the second call hitting the cache (`memoPair_eval`).
   - **One borrow spanning the forward is refused** at every `Δ`, context and type
     (`spanFwd_refused`).
3. **Capture.** Each mode of `k` has the paper's rule behind it:

   | mode | example | BoLo + `!` rule |
   |---|---|---|
   | borrowed, used in place | — | no reification needed (`HandlersAsBorrows`) |
   | linear, dropped | `abortProg` | `forget` has no typing at `⊸` (`forget_not_lolli`); abort resumes into the continuation's own finalizer |
   | owned, resumed later | `laterProg` | the closure is stored in a `Ref` and resumed later |
   | `!`, copied | `twoShot` | promotion needs `!Γ` (`lam_bang_persistent`), so a `!` continuation captures only persistent values (`multiShot_ref_refused`) |
4. **T2.** The capture-bounded closure is the box `[@c](T₁ ⊸ T₂)`.
   - It outlives `@a` iff `@c ⊐ @a` (`box_lolli_outlives_iff`).
   - `crossProg` carries a continuation that captures a borrow out of an inner scope and resumes
     it.
   - Control needs T1/K1 only when a continuation that captures a borrow is resumed after control
     has left that borrow's scope (§4).

## 1. State behind control (`Behind.lean`)

    op   = λp. inj₂ p                                     -- (argument, continuation)
    f    = !λp. op p         g = !λp. op p                -- two blocks performing flip
    body = f ((), λa. g ((), λb. (a, b)))
    hS n = λ(c, σ). case c { r ⇒ (r, σ) | (u, k) ⇒ u; let (σ, b) = flip σ; n (k b, σ) }
    prog = let σ = alloc (inj₁ ()); let (r, σ) = hS (hS id) (body, σ); drop (free σ); r

- **The state lives only in the handler's frame.** `σ : Ref B`, and `flip` swaps it.
- **Exclusivity comes from sequential control.** The handler runs between requests, which is
  System C's and Ξ's reason. No borrow of the state is ever handed to the body, so nothing
  prevents two blocks from both "holding" the capability.
- **The computation type is unrolled:** `C₀ = R`, `Cₙ₊₁ = R ⊕ (1 ⊗ (B ⊸ Cₙ))`. The two blocks
  are the same code typed at two types (`d_blk`).
- **Why a single capability type is impossible:** `no_uniform_comp` shows no `X : Ty` satisfies
  `X = R ⊕ (A ⊗ (B ⊸ X))`.
  - This is the free model of one operation.
  - `CoeffectsStrict` prints handlers as its fold, and notes that general arity needs `X` under
    `U`/`⊸`, which `FShape` excludes (T15).

**Direct style (no request data, the operation returns to its caller).**

- The state must change during the call, so the call must hold `Mut`/`Ref` access.
- A shareable token is `Imm` or `!`:
  - `[TR]` Theorem 6.64 (`Fig16.LogRel.wp_I_frame`) returns an `Imm`-lent cell with the value it
    had;
  - `vX b (!T) … ρ` requires `ρ = ∅` (SPEC §2).
- So the only way to mutate on behalf of a shared token is to transfer control to the owner of
  the state. That is K-a, or the request encoding above.
- I have not derived a general non-existence theorem over all direct-style encodings, and have
  not verified that one holds beyond these two facts.

## 2. The reentry rule (`Reentry.lean`)

**As a typing rule.** It is admissible, and needs no new rule. In the frame encoding a clause
has the state token `σ : St` (here `Ref S`). `resume` and `forward` are functions whose domain
includes `St`:

    resume  : B ⊗ St ⊸ R          forward : St ⊸ St ⊗ B

A borrow of the state is `withbor σ (Λ'y. λm. M) : St ⊗ T`. Its callback's context cannot
contain `σ`, which `withbor` consumed. So:

    Γ ⊢ withbor σ (Λ'y. λm. M)  ⟹  σ ∉ live(Γ_M)       (⊸E's split at withbor σ cb)

`M` therefore cannot call `resume`/`forward` on `σ`, and outside the callback the borrow `m` no
longer exists. This is statically what `RefCell` checks dynamically.

**`memo`.**

    memo fwd (σ, ()) = let (σ, c) = get σ;                       -- borrow 1
                       case c { none ⇒ let (σ, b) = fwd σ;       -- forward (may re-enter)
                                        let (b₁, b₂) = dup b;
                                        let σ = insert (σ, b₁);   -- borrow 2
                                        (σ, b₂)
                              | some v ⇒ (σ, v) }
    memo₀ = memo base      rec₁ σ = let (σ, b) = memo₀ (σ, ()); (σ, not b)      memo₁ = memo rec₁

- **Accepted and safe:** `d_memoProg`, `memoProg_runs`.
- **Re-entry.** `memo₁`'s forward re-enters `memo` on the same state while `memo₁`'s clause is
  live.
- **Run:** `memoPair_eval` gives `(inj₂ (), inj₂ ())`. Without the cache hit, the second call
  would recompute and answer `inj₁ ()`.
- **Refused:** `spanFwd fwd rest = withbor σ (Λ. λm. let (σ′, b) = fwd σ; rest)`.
  - `spanFwd_refused` shows it has no derivation at any `Δ`, context, type, `fwd` or `rest`. The
    failing step is `no_shared_app`: `σ` would be live in both halves of `⊸E`'s split.
  - `BorrowSpansForward : Prop` is the elaborated obstruction, and `not_borrowSpansForward`
    refutes it.

**BoLo is less strict than the proposed rule in one place.** A clause may *lend* its borrow `m`
into a forward that takes `∀'z. Mut 'z S ⊸ …` (`withbor` form 3, a reborrow). While the forward
runs, the clause does not hold `m`, so this is sound. The proposed rule ("any borrow must end
before the call") forbids it. Not built here.

## 3. The capture rule, and control-flow linearity (`Capture.lean`)

**The results:**

- `lam_bang_persistent`: `DerivesWf Δ Γ (λb) T` with `T` a `!` type under boxes implies
  `Ctx.Persistent Γ`. This is by inversion of every `DerivesWf` rule.
- `multiShot_ref_refused` and `multiShot_imm_refused`: a continuation over a live `Ref` or `Imm`
  slot has no `!` type.
- `twoShot`: `choose` resumed twice, with a continuation that captures a `!` function. Typed,
  safe and run: the result is `(inj₂ (), inj₁ ())`.
- `forget_not_lolli`: `forget` has no type `(T₁ ⊸ T₂) ⊸ 1`. This is by inversion
  (`forget_types`, `unit_dead`).
- `abortProg`: the continuation takes `B ⊕ 1`, and the handler resumes it with `inj₂ ()` (abort).
  The continuation's abort branch frees the cell it captured. Typed and safe: memory ends empty.
- `laterProg`: the handler stores `k` in a `Ref`, takes it back and resumes it. Typed, safe and
  run.

**Comparison with Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity* (POPL 2024;
read: §§1–3, 6).** Their calculus is F°eff.

| | F°eff | BoLo + `!` (continuations explicit) |
|---|---|---|
| what is tracked | *control-flow linearity* of each operation `ℓ : A ↠^Y B`, lifted to row kinds `Row^Y` | the type of each continuation: `B ⊸ R` (linear) or `!(B ⊸ R)` |
| the side condition | T-Seq `let^Y x ← M in N`: `Y = •` needs `Δ ⊢ Γ₂ : •` (the continuation captures no linear variable); T-Handler gives `r` the value linearity `Y` | `!I` needs `!Γ` (`lam_bang_persistent`) |
| granularity | per operation. §6 names the limitation: `hesitantClose` cannot give its two `Choose`s different linearities | per continuation, so `hesitantClose`'s two continuations get different modes. The price is that continuations are written explicitly (§1), or a native capture rule (K-a) infers them |
| discard | a linear continuation cannot be dropped (Thm 3.6, linearity-aware semantics) | the same (`forget_not_lolli`); abort is resuming into a finalizer |
| borrows | none | a `!` continuation cannot capture an `Imm` borrow, although `Imm` is duplicable (`multiShot_imm_refused`). That is stricter than needed; widening promotion is T6 (#9) |
| soundness | syntactic, plus a linear-safety theorem over a tagged semantics (Thm 3.6) | the semantic FP with leak freedom (adequacy at empty memory) |

**Comparison with van Rooij & Krebbers, *Affect* (POPL 2025; read: §1–2.1).**

- Affect makes one-shot continuations affine functions, and stores continuations in `Cell`-style
  references that are "moved out" by replacement. That is what `laterProg` does with `Ref`.
- Its capturing condition ("when calling a multi-shot effect, the remaining computation does not
  capture one-shot continuations") is the `!Γ` premise.
- Its continuations are affine, so dropping is allowed. In BoLo they are linear, and dropping
  needs a finalizer (`abortProg`) or destructors (SPEC §12, `Core`).
- Its soundness is semantic, in Iris, over Hazel/Maze's effectful weakest precondition. §5 K-a
  proposes the same shape for BoLo.

## 4. The closure outlives rule, T2 (`Outlives.lean`)

- **At the paper level, T2's rule is the box.**
  - `[TR]` p. 2 prints no outlives rule at `⊸` (`lolli_not_outlives`).
  - `[@c](T₁ ⊸ T₂)` is introduced by `[]I` (row 2.13), which asks every captured live slot to
    outlive `@c`.
  - It outlives `@a` iff `@c ⊐ @a` (`box_lolli_outlives_iff`, row 2.35).
  - Its semantics is `[TR]` 6.62/6.60 at the box, already inside the FP.
  - For an owned continuation that captures borrows at `'a`, the rule must say: **the
    continuation is bounded by a lifetime `@c ⊏ 'a`, and may cross any scope `@x ⊏ @c`.**
    `crossProg` does this: `k : ['c](1 ⊸ 1)` captures `y : Imm 'a 1` and leaves the scope `'x`.
- **An unindexed rule `U C ⊐ @a` is not what is needed.** The type does not determine the
  captured resource: decision 3, `envShape_unlinked`. The index is the capture bound, and the box
  already is that index. What remains for T2 at CBPV (#173) is to use `[@c] U C` where CBPV
  needs it (derived forms, inference), not a new semantic clause. I have not derived the CBPV
  statement and have not verified any obstruction.
- **T1/K1 is separate.** Control needs it exactly when a continuation that captures a borrow is
  suspended across the end of that borrow's lending scope, and resumed on the other side. Two
  cases:
  - a handler outside a `withbor` whose callback performed the operation, resuming later;
  - a generator lending its own state across a `yield`.

  When the lend encloses both the capture and the resumption, the box suffices (`crossProg`).
  K1's obstruction is `experiments/LoopBorrow`'s (`refoldKripke_false`,
  `not_markerInstallable`), not the missing outlives rule.

## 5. What needs a kernel extension

Nothing below is built. Each item gives the rule, the semantic clause, the obligations and what
they reduce to.

**K-a. Native capture (a delimiter and an operation), with modes.**

- **Syntax:** `handle e with {x, k. h}` and `do v`.
- **Typing** adds an effect annotation `! ε`, with `ε = op : A ↠^m B / R` (one operation, mode
  `m ∈ {1, !}`, answer type `R`):

      Δ; Γ ⊢ v : A                                   Δ; Γ₁ ⊢ e₁ : T₁ ! ε    Δ; Γ₂, x : T₁ ⊢ e₂ : T₂ ! ε    (m = ! ⇒ !Γ₂)
      ─────────────────────── [do]                   ───────────────────────────────────────────────────── [let]
      Δ; Γ ⊢ do v : B ! ε                            Δ; Γ₁, Γ₂ ⊢ let x = e₁; e₂ : T₂ ! ε

      Δ; Γ₁ ⊢ e : R ! (op : A ↠^m B / R)     Δ; Γ₂, x : A, k : K_m ⊢ h : R           K₁ = B ⊸ R,  K_! = !(B ⊸ R)
      ─────────────────────────────────────────────────────────────────────────── [handle]
      Δ; Γ₁, Γ₂ ⊢ handle e with {x, k. h} : R

  **Scope side condition.** A `withbor` callback's effect annotation must be pure unless the
  handler lies inside the callback. Otherwise the continuation spans a lend (T1/K1).
- **Operational:** `(μ, handle K[do v] with {x,k.h}) ↦ (μ, h[v/x, (λy. handle K[y] with {x,k.h})/k])`,
  where `K` contains no `handle`. And `handle v with … ↦ v`.
- **Semantic clause.** An effectful weakest precondition `ewpTS ls e Ψ Q`, where `Ψ` is a
  protocol: the resource at `do v` is split into what the handler receives and a continuation
  resource `ρ_k`. This follows de Vilhena & Pottier as Affect uses them.
  - `wpTS = ewpTS ⊥`.
  - At mode `!`, the continuation's resource must be `∅` (the `!` clause).
- **Obligations:**
  1. compatibility of `do`, `let` (the `ewp` bind) and `handle`;
  2. every existing `*_compatX` at `ewpTS`;
  3. the frames 6.64–6.66 over `ewpTS` with an empty protocol inside the frame, as the scope
     side condition ensures;
  4. adequacy at a pure program.
- **What they reduce to.**
  - (2) and (3) reduce to the existing lemmas through `wpTS = ewpTS ⊥`.
  - The `!` mode reduces to `gSepX_persistent` (`!Γ` holds `∅`).
  - A continuation stored across a scope reduces to 6.60/6.62 at the box.
  - The new obligations are (1) and the `ewp` bind with `Ext`-stability of protocols (§12.70's
    `hQ` form).

**K-b. `μX` with `X` under `⊸` (T15, #182).** This is the uniform request encoding: one
capability type at unboundedly many sites (`no_uniform_comp`). `experiments/CBPVMu` and
`CoeffectsStrict` record it as open.

**K-c. Destructors for continuations.** Needed only if abort must *drop* a continuation rather
than resume it into a finalizer. `Core` has destructors (SPEC §12), but `U C` has none
(Affine). The finalizer encoding (`abortProg`) needs no extension.

## 6. InvalML (Gao & Parreaux, OOPSLA 2025; read: §1, §2.5, §3 (Theorem 3.2), §5.2–5.3)

**Its mechanism** avoids linearity and ownership:

- regions and scopes are rigid type variables, and escaping extrudes them to `⊤` (a leaked
  handler becomes `Exc[_, ⊤]`, unusable);
- temporary invalidation is Boolean-algebraic effects with negation bounds, e.g. `iter`'s
  `E ≤ ¬R`, or `push`'s bound, which forbids a second push on the same stack while a frame is
  pushed.

**The same guarantees, by other means:**

| InvalML | BoLo |
|---|---|
| permanent invalidation, by extrusion | the fresh lifetime and the `['x]` check (`escape_refused` in `HandlersAsBorrows`). BoLo *refuses* where InvalML extrudes; the extruded, unusable `Exc[_, ⊤]` plays the role of `Unk` |
| temporary invalidation, `E ≤ ¬R` | `withbor` consuming the owner: disjointness by linearity. §2's reentry rule is InvalML's `push` bound, stated by ownership |

**Its limits:**

- no linear resources;
- handlers shown for exceptions only (`throw`/`handle`, §5.2);
- soundness (Thm 3.2) by a paper proof over a fuel-indexed evaluator.

**The synthesis:** BoLo borrows for owned state, plus an InvalML-style "in use" effect for
shared capability tokens.

- **As a surface discipline, it plausibly composes.**
  - A clause that holds the state carries the effect "state in use"; `resume`/`forward` require
    its absence.
  - When that check passes, an elaborator can thread the state token linearly as in §§1–2. That
    is the core's discipline, so the FP applies unchanged.
  - I have not derived this elaboration and have not verified that any obstruction is real.
- **As a semantic reading of the core, it conflicts.** It would let a shared token *mutate*
  state guarded only by effect disjointness. In BoLo's model a shared (`imm`) cell is frozen
  (6.64, 6.115), so this needs a new cell kind: interior mutability (route (b) of #184). The
  global invariant would have to be restated.

## 7. Hypotheses and scope

- **No hypothesis is added to any BoLo statement.** Every program is closed at `Δ = ∅`, and its
  safety is `Fig16.LogRel.Typed.adequacy`.
- **The programs are bounded instances:**
  - one handler;
  - first-order data;
  - a fixed number of operations;
  - `memo` with a one-slot cache.
- **Stated for arbitrary configurations:** the refusals (`spanFwd_refused`,
  `multiShot_*_refused`, `forget_not_lolli`) and the inversion lemmas hold at every `Δ`, context
  and type.
- **Paper-level adequacy is angelic** (some run), as in #184.
- **Untranscribed run-up:** `[TR]` Lemma 6.40, as in #184. It is inherited through the FP.
