# Handlers as borrows: lexically scoped answering handlers in BoLo + `!`

Issue #170. Theory index T20.

**Question.** Is a lexically scoped effect handler (Effekt's System Ξ; Brachthäuser, Schuster
& Ostermann, *Effects as Capabilities*, OOPSLA 2020, extended TR) an instance of borrowing in
BoLo (`[CONF]`/`[TR]`, Wagner et al., OOPSLA 2025)?

**Answer.** For answering handlers, yes, and it is proved:

- **(a) Embedding.** A Ξ fragment translates into BoLo + `!` with typing preserved:
  - `handle` becomes `withbor` form (2), lending the handler's state as `Mut 'x S`;
  - the clause becomes `!` code;
  - an operation becomes `withswap` on the borrowed state.
- **(b) Effect safety.** Effect safety is BoLo's Fundamental Property applied to the embedding.
  No new semantic argument is needed.
- **(c) A separating program.** A capability returned from a function and stored in a heap
  cell is typed, safe and runs. This separates BoLo + `!` from Ξ, **not** from System C.
  System C's boxes already store capability-capturing blocks at a type that bounds them.
- **Aliasing is not covered.** A stateful capability captured by two closures at once is
  refused (`twoBlocks_refused`). System C accepts it.

**Build.** `lake build HandlersAsBorrows`. The library is non-default and nothing imports it.

- **Imports.** It imports only the paper-faithful layer (`Paper/`, `Support/`), which carries
  SPEC §2's `!` rules, plus `experiments/Shifts` for one `rfl` lemma.
- **Not used.** No CBPV (`Core`, Entry 2), arrays, `count_try` or frontend code.
- **Hygiene.** No `sorry`, `axiom` or `native_decide`. Every `#print axioms` is within
  `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Weaken.lean` | `DWk` and `DerivesWf.dwk`: a derivation survives retyping consumed slots and appending consumed slots |
| `Source.lean` | the fragment: `VTy`, `VExp`, `Entry`, `Stmt`, `VDerives`, `XDerives` |
| `Env.lean` | `EnvTy`, the environment's type; `Good n K Δ`; scoping; the environment outlives a fresh handler lifetime (`Good.outlives`) |
| `Combinators.lean` | closed code for operation and block calls: `opHere`, `blockHere`, `atSucc`, `d_opAt`, `d_blockAt` |
| `Translate.lean` | `tr`, and **(a)** `translate_typed` |
| `Safety.lean` | **(b)** `effect_safety`, `effect_safety_open`; the escape check: `capability_not_outlives`, `object_not_outlives`, `escape_refused`, `lolli_not_outlives`; `handle_is_shift` |
| `Sharing.lean` | aliasing: `liveAt_of_occ`, `no_shared_pair`, `twoBlocks_refused`, `SharedCapture`, `not_sharedCapture` |
| `Examples.lean` | two blocks using one stateful capability, typed in the fragment, safe by (b), run: `x_sharedUnit`, `sharedUnit_safe`, `sharedUnit_eval`, `sharedPair_eval` |
| `Separating.lean` | **(c)** `d_sepProg`, `sepProg_runs`, `sepProg_eval` |

`refs/` holds the Effekt TR PDF; it is git-ignored.

---

## 1. The source fragment

Ξ's syntax and rules (TR §4, Figs. 3–4) are restricted as follows. Each restriction is
recorded in `Source.lean`.

| Ξ | fragment | why |
|---|---|---|
| value types `Int`, `Bool`, … | first-order data `1`, `A ⊗ B`, `A ⊕ B` | BoLo's data. `split`, `case` and `drop` are added to eliminate it |
| value variables used freely | **used linearly** | BoLo is linear. Data admits a definable copy and drop, but the bookkeeping is not built. This is a restriction on the fragment, not a claim about expressiveness |
| blocks `{(x̄ : τ̄, f̄ : σ̄) ⇒ s}` | one value parameter, **no block parameter**, **captures no value variable**; may use every capability and block in scope | block parameters: §6 |
| `[Handle]` with clause `(x, k) ⇒ s′` | **answering**: the clause resumes exactly once, in tail position, with a value computed from the argument and the handler's state `S`; it is **pure** (no capability, no value variable of the context) | the scope of the issue. At `S = 1` this is Ξ's own `handle`. General `S` is a parameterized handler, which Ξ cannot write (TR §7.2.1, "Functional State"), and which Effekt writes with local state (TR §6.2.2) |
| no multi-shot, no abort | none | control effects are out of scope: §6 |

**Judgment.** `XDerives K Γ s C` is Ξ's `Γ Δ ⊢ s : τ`, with Ξ's block environment `Δ` as an
**environment** `K : List Entry`, innermost first. Its entries are:

- `cap S A B`: a handler with state `S` and operation `A → B`;
- `blk A B`: a block.

An operation `op j e` or a call `call j e` names entry `j`, de Bruijn style. Ξ's
`[BlockVar]`/`[Call]` look block variables up the same way.

**Padding `[encoding]`.** Source contexts carry consumed slots wherever the translation binds a
variable that the source does not see. These are the threaded environment and the `Λ` of a
borrow callback. Padding slots are never live, so they change no typing. They make source and
target de Bruijn indices coincide, and `DWk` makes their types irrelevant.

## 2. The translation

The environment is **one threaded value** (`Env.lean`):

- `EnvTy n [] = 1`;
- `EnvTy n (cap S A B :: K) = (Mut 'x S ⊗ !(S ⊗ A ⊸ S ⊗ B)) ⊗ EnvTy n K`, with
  `'x = '(n + ncaps K)`;
- `EnvTy n (blk A B :: K) = !(A ⊗ EnvTy n K ⊸ B ⊗ EnvTy n K) ⊗ EnvTy n K`.

**A capability is an object.** It is the handler's state, borrowed mutably at the handler's
lifetime, beside the clause as `!` code. A block is `!` code that takes the environment of its
definition. A statement translates to a term open in the environment slot, at type
`C ⊗ EnvTy n K` (`Translate.lean`):

    ⟦e⟧                    = (⟦e⟧ᵥ, env)
    ⟦val x = s₀; s₁⟧       = let (x, env) = ⟦s₀⟧; ⟦s₁⟧
    ⟦F_j(e)⟧               = opAt j (⟦e⟧ᵥ, env)
    ⟦f_j(e)⟧               = blockAt j (⟦e⟧ᵥ, env)
    ⟦def f = {x ⇒ b}; s⟧   = let (y, env′) = (λenv′. ⟦s⟧) (!λp. let (x, env) = p; ⟦b⟧, env);
                             let (f, env) = env′; forget f; (y, env)
    ⟦handle_S {F ⇒ s} with e₀, cl⟧ =
        let (c, r) = withbor (alloc ⟦e₀⟧ᵥ) (Λ. λm.
                       let (y, env′) = (λenv′. ⟦s⟧) ((m, !cl), env);
                       let (ent, env) = env′; let (m, cl) = ent; forget m; forget cl; □(y, env));
        drop_S (free c); r

**The operation at the head** (`opHere`) performs `withswap m (λs. c (s, a))`. `withswap` hands
the borrowed state to the clause and stores what the clause returns: the clause resumes once, in
tail position, with no continuation reified.

**Lexical scoping is `atSucc`.** A call at index `j` peels `j` entries and runs the entry
against the environment *it was defined in*. A block therefore never sees a capability bound
after its definition, which is Ξ's lexical scoping. This is how the translation avoids
accidental handling.

**Relation to the library's handlers.** `Core/Handlers.lean` (SPEC §18) elaborates an operation
to the same `withswap ℓ (λs. g (s, v))`, over `CDerives` (CBPV). This spike states the
embedding at the paper's `DerivesWf`.

## 3. The theorems

**(a) Typing preservation**: `translate_typed`.

    XDerives K Γ s C → ∀ n Δ, Good n K Δ →
      DerivesWf Δ (⟨EnvTy n K, true⟩ :: emb Γ) (tr s) (C ⊗ EnvTy n K)

- `Good n K Δ` says `Δ` binds exactly the variables below `n + ncaps K`.
- At a closed program it is `Good 0 [] ∅`, so `d_prog : XDerives [] [] s 1 → DerivesWf ∅ []
  (prog s) 1`.

**(b) Effect safety.** Ξ's effect safety (TR Thms 4–5 and §5.2) says a closed well-typed program
is never stuck on an *undelimited label*: a capability applied outside its handler's delimiter.

In the translation:

- applying a capability is `withswap` on the handler's borrowed state cell;
- the delimiter is the `withbor` that lent `'x`;
- after the delimiter the cell is taken back and **freed**.

Effect safety therefore becomes **no use of a borrow after its lifetime**. Three statements
carry it:

- **`effect_safety`**:
  `XDerives [] [] s 1 → Steps ∅ (prog s) ∅ ()`.
  - It is `Fig16.LogRel.Typed.adequacy` (`[CONF]` Lemma 3.1 with Corollary 3.3, at `SemX`)
    composed with (a).
  - The run reaches `()`. On it, every operation found its handler's cell allocated, and every
    handler's cell (and every other cell) was freed.
- **`effect_safety_open`**: an open statement is in the logical relation, that is
  `SemX Δ (⟨EnvTy n K, true⟩ :: emb Γ) (tr s) (C ⊗ EnvTy n K)`.
  - It is `Fig16.LogRel.Typed.fundamentalProperty` (`[TR]` 6.151 at `SemX`) composed with (a).
  - It holds in every world where the environment's capabilities are live `Mut` borrows at
    their lifetimes: the statement runs safely and hands them back.
- **The escape check** is where Ξ's second-class restriction is replaced:
  - `capability_not_outlives`: `Mut 'x S ⊐ 'x` fails at every satisfiable `Δ`.
  - `object_not_outlives`: the same for the object `Mut 'x S ⊗ !code`.
  - `escape_refused`: `[]I`'s premise (`[TR]` p. 2, row 2.13) fails for any context that still
    holds the capability live.
  - So the handled statement's result `['x] (C ⊗ E)` cannot carry the handler's own capability.

**Consistency with `experiments/CoeffectsStrict`.** CoeffectsStrict says scope (owned vs.
borrowed) "meets [the equational axes] only through the Fundamental Property". This result is an
instance of that: nothing about effect safety comes from an algebraic law. It is the FP on the
image of a typing translation. `CoeffectsStrict/Handler.lean` proves the *equational* side (a
deep handler is a fold). This spike proves the *safety* side, and here safety is scope.

**Scope of (b).** At the paper level adequacy is angelic: *some* run reaches `()`, because
`alloc↦` may choose any free location. The every-run version (SPEC §13, `adequacyD`) exists only
over `CDerives`, which is out of bounds here. The machine is otherwise deterministic, so the
difference is only in which free location `alloc` picks.

**(c) The separating program** (`Separating.lean`). It runs inside a `flip` handler with state
`1 ⊕ 1`:

    let (c, w) = withbor (alloc (inj₁ ())) (Λ. λm.
      let obj = pack m;                                  -- pack = λm. (m, flip): returns the capability
      let r = alloc obj;                                 -- stores it in a heap cell
      let (m′, f) = free r;  let (f₁, f₂) = copy f;
      let (m″, b) = withswap m′ (λs. f₁ (s, ()));        -- the operation, through the stored object
      forget m″; forget f₂; b; □());
    w; case (free c) {x ⇒ x | y ⇒ y}

- **Typed**: `d_sepProg`, with `r : Ref (Mut 'x B ⊗ !(B ⊗ 1 ⊸ B ⊗ B))`.
- **Safe** by the FP: `sepProg_runs`.
- **Run** by the interpreter with no cell left: `sepProg_eval`.
- **Ξ cannot express it.** Blocks and capabilities "can neither be returned nor stored in data
  structures" (TR §1.6), and Ξ's value types have no block component (Fig. 3).
- **Bounded by `'x`.** The cell holding the capability must be freed inside the handler.
  `object_not_outlives` refuses any context or result that still holds it at `['x]`, and
  `Ref (Mut 'x S ⊗ …) ⊐ 'x` fails for the same reason.
- **A second separation, already inside (a).** The translated handler returns the *outer*
  environment, holding the outer handlers' `Mut` capabilities, as a value through the inner
  handler's `['x]` box (`Good.outlives`: `'x ⊏ ⊓Δ`). In Ξ the outer capabilities are only
  lexically visible, never values.

The separation is **against Ξ only**; see §5.

## 4. Ξ → BoLo correspondence

**Row numbers.** "Row N.M" is `Paper/INDEX.md`'s definition-row numbering of `[TR]`: row 2.x is
`[TR]` p. 2 (typing rules) or p. 3 (axiom table), as `Paper/S2_Statics/Definitions.lean`
records. `!` rules are SPEC §2.

| Ξ (TR Fig. 4) | fragment | BoLo + `!` | rule / axiom |
|---|---|---|---|
| value type `τ` | `VTy` | `1`, `⊗`, `⊕` | `Ty.unit/tensor/sum` |
| `[Expr]` `e` | `ret` | `(⟦e⟧ᵥ, env)` | ⊗I, row 2.5 |
| `[Val]` `val x = s₀; s₁` | `val` | `let (x, env) = ⟦s₀⟧; ⟦s₁⟧` | ⊗E, row 2.6 |
| block env `Δ` | `K : List Entry` | the threaded `EnvTy n K` | ⊗I/⊗E |
| capability `F : τ₁ → τ₀` | `cap S A B` | object `Mut 'x S ⊗ !(S ⊗ A ⊸ S ⊗ B)` | `Mut`, row 1.38; `!T`, SPEC §2 |
| `[Handle]` | `handle` | `withbor (alloc e₀) (Λ. λm. …)`, then `free` | `withbor` form (2), row 2.45 (`DerivesWf.withbor2Ax`); ∀I row 2.11; ⊸I row 2.9; alloc/free rows 2.15, 2.16 |
| fresh label `l` (TR §4.3 `(handle)`) | — | fresh lifetime `'x ⊏ ⊓Δ` | ∀I's freshness premise (§12.44) |
| delimiter `#l {…}` | — | the scope of `withbor`'s callback, ended by `['x]` | `[]I`, row 2.13, with `Δ ⊢ Mut 'x S ⊐ 'x` failing (row 2.37; `capability_not_outlives`) |
| `(ret)` `#l {v} ↦ v` | — | `□(y, env)` then `withbor` returns the cell | `[]I` row 2.13; `[]E` row 2.14 |
| answering clause | `cl` | `!λp. …` over the state | `bangLamI`, SPEC §2 |
| `[Call]` at a capability, `(cap)` | `op j e` | `withswap m (λs. c (s, a))` through `atSucc^j` | `withswap`, row 2.48; `copy` at `!`, `copyBangAx`; `bangE` |
| `[Def]` + `[Block]` | `defn` | `!` code over the definition environment | `bangLamI`; `forget` at `!`, `forgetBangAx` |
| `[BlockVar]` + `[Call]` at a block | `call j e` | `blockAt j` | ⊸E row 2.10; `copyBangAx`, `bangE` |
| second-class restriction | — | the escape check at `['x]` | `[]I` row 2.13 + outlives rows 2.30–2.37 |
| effect safety (Thms 4–5) | — | FP + adequacy | `[TR]` 6.151 at `SemX`; `[CONF]` 3.1/3.3 |
| the labelled-shift reading | — | `withbor` (2) is `shiftTy (Ref S) (Mut · S) true` | `handle_is_shift` (`experiments/Shifts`) |

## 5. Comparison with System C

Sources: Brachthäuser, Schuster, Lee & Boruch-Gruszecki, *Effects, Capabilities, and Boxes*,
OOPSLA 2022, extended TR. Read: §1–§4.5, §5.2 (Mutable State), §5.4, §6.5–§6.8.

**Its mechanism.**

- Blocks are second class, but `box b : σ at C` makes one first class. It is typed at the
  capture set `C` of the capabilities it closes over (rule BoxIntro).
- `unbox e` is allowed only where `C` is in scope (BoxElim).
- `try` marks `f` tracked, and the answer type may not mention it, so "`try { (f : σ) ⇒ return
  box {f} f }` … does not type check" (§4.3.3).
- Effect safety (Cor. 9) is progress and preservation, mechanised in Coq.

**So (c) is not new against System C.** Storing a capability-capturing block in data within its
handler, and returning it from a function there, is exactly what boxes do. The type `σ at {f}`
bounds it by `f`'s scope, as `'x` bounds `Ref (Mut 'x S ⊗ …)` here.

**What differs.** The two systems are incomparable, and neither subsumes the other:

| | System C | BoLo + `!` (this spike) |
|---|---|---|
| capability | a label; holders never touch handler state | the handler's state itself, `Mut 'x S`: a unique borrow |
| aliasing a stateful capability | yes: several blocks capture `f`, boxes are duplicable | **no**: `twoBlocks_refused` (below) |
| handler state | in the handler's frame / a region (§5.2, `Ref[τ]`, unrestricted) | an owned heap cell, lent and taken back; **leak freedom** (`Steps ∅ e ∅ ()`) |
| scope bound | capture set `C`, a set of names | lifetime `'x`, ordered by `⊏` |
| control effects | yes (multi-shot, capture of `k`) | no |
| soundness | syntactic, Coq | semantic: the FP of a separation-logic model |

**Why System C can alias.** In System C and Ξ, "Calling a capability captures the stack segment
up to the next dynamically enclosing delimiter … and binds it to `k`" (Effekt TR §4.3). A
capability holder never touches the state. The operation transfers control to the handler,
which owns the state in its frame, so exclusivity comes from sequential control, not uniqueness.
System C §5.2's `Ref[τ]` cells in a `region` are reached only through the region capability, in
the same way.

**What this spike covers.**

1. **Stateless or read-only handlers.** The capability could be `!` code alone, or an `Imm`
   borrow, which `copy` shares. This is not built here, and the fragment's handlers all carry a
   `Mut` state.
2. **Stateful handlers with one non-aliased capability**, threaded linearly. This is (a) and
   (b). Several *blocks* may still use one capability (`Examples.lean`: `sharedUnit_safe`,
   `sharedPair_eval`), because a block receives the environment at each call instead of
   capturing it. The second block sees the state the first one left.

**What it does not cover: aliased stateful capabilities.**

- `twoBlocks` is System C's
  `try { f ⇒ (box {f} {() ⇒ f(())}, box {f} {() ⇒ f(())}) } with …` through the encoding: two
  closures each performing the operation on the same capability.
- `twoBlocks_refused` shows it has no `DerivesWf` derivation at any `Δ`, context or type.
- The failing step: a variable free in both components of a pair is live in both halves of a
  `Ctx.Split` (`liveAt_of_occ`, `Ctx.Split.not_both`, `no_shared_pair`).
- `SharedCapture : Prop` is the elaborated obstruction, and `not_sharedCapture` refutes it.

**Two routes a follow-up could take.** Neither is added here.

- **(a) State behind control.** An operation is a shift into the handler's frame, and the
  capability is a shareable token. This needs control (T1/K1 territory).
- **(b) Interior mutability** (SPEC: open; `experiments/InteriorMutability`).

**The user's candidate correspondence, row by row.** CBPV's thunk `U C` is not in BoLo. Its
BoLo analogue is a `⊸`/`∀` closure.

| System C | borrowing | status here |
|---|---|---|
| value type | value type | **proved** as a row of (a): `VTy` ↦ data |
| block type | computation type | **by analogy**. Blocks become `!` code taking their environment explicitly (`EnvTy`), not closures, so no computation type is involved |
| block parameter (second class) | borrowed thunk in the context | **not in the fragment**. Precondition (1) below |
| `box b : T at C` | owned thunk whose type records what it borrows | **not built**. Precondition (2) below. (c) uses the *object* `Mut 'x S ⊗ !code`, whose type does record the borrow, but it is not a closure |
| `unbox` | force while `C`'s lenders are live | as the `box` row |
| subcapturing | outlives | an **abstraction, not an iso**. Precondition (3) below |

**The three preconditions.**

1. **Block parameters.** A block that captures a `Mut` capability and is called many times is
   an FnMut-style closure, which `!` does not cover:
   - `!` cannot capture a `Mut` (promotion needs `!Γ`);
   - a `⊸` closure capturing it is one-shot;
   - SPEC §2's `FnMut` row exposes the environment's type, `(env, !code)` behind `Mut`, which a
     callee cannot abstract over without type polymorphism.

   This is a gap `!` does not cover. It is not "BorrowedClosures stage 2", which `!T`
   superseded (decision 3, `envShape_unlinked`). The fragment side-steps it: blocks do not
   capture capabilities, they are passed the environment. That is why the fragment has no block
   parameters. I have not derived a translation of block parameters and have not verified that
   any obstruction is real.
2. **`box` / `unbox`.** A closure that captures borrows and crosses a scope needs an outlives
   rule for closures. `[TR]` p. 2 has none at `⊸` (`lolli_not_outlives`). At CBPV it is T2
   ([#173]), the `U C` rule. It is **not** the spanning-lend obstruction T1/K1 ([#172]), which
   `experiments/LoopBorrow` places in the Kripke order and `↭`. The object form of (c) avoids
   T2 because its type is data (`⊗` of `Mut` and `!`), which does have outlives rules.
3. **Subcapturing vs. outlives.** `C ↦ ⊓{lifetime(f) | f ∈ C}` is monotone: `C ⊆ C′` implies
   `⊓C′ ⊑ ⊓C`, so a value bounded at `C` is bounded at `C′`. It forgets *which* capabilities
   were captured, and System C uses that as effect information (a box at `{console}` vs.
   `{time}`), so it is not an isomorphism. This reading is exactly right as a statement about
   the two orders; no Lean was built for it.

## 6. Where the embedding stops

- **Control effects** (abort, suspension, multi-shot) are out of scope. BoLo has no control
  operator, and the embedding covers exactly the handlers whose continuation is never reified.
  The follow-up is T1/K1 and the control-flow-linearity route named in #170.
- **Block parameters** are covered by precondition (1) above.
- **Effectful clauses.** A clause that uses an outer capability would need `!` code over a
  heterogeneous environment. The encoding would pass the outer environment to the clause as
  blocks receive theirs. It is not built.
- **Clauses and blocks capturing value variables** would need linear one-shot closures, or
  duplicable data. Neither is built.
- **Unrestricted value variables** would need definable copy and drop at data, inserted at every
  split. They are not built.

## 7. Hypotheses and encoding choices

No printed definition or statement was edited. `DerivesWf`, the FP and adequacy are used exactly
as the library states them.

- **`Good n K Δ`**, a hypothesis of (a). `Δ` binds exactly the variables below `n + ncaps K`.
  - Scope: it is the translation's lifetime bookkeeping.
  - Non-vacuous: `good_empty` discharges it at every closed program.
  - It is re-established at each handler by `Good.handle`, and for the clause by `Good.clause`.
- **`Δ.Ok`**, a hypothesis of `effect_safety_open`. It is the FP's own hypothesis, unchanged.
- **Padding slots** in source contexts `[encoding]` (§1).
- **The source fragment's restrictions** (§1): these are choices of the fragment, not hypotheses
  on BoLo.
- **`Stmt.handle` carries the state type `S`**, so that the final state can be dropped
  (`dropD`).

## 8. Prior internal work, and what this adds

- **`docs/ideas-handlers-and-borrows.md`**: "a stateful handler is a borrow presented through an
  interface" (row 1 of its table), untested there. This spike states that row precisely for
  Ξ's answering handlers and proves it at the paper's judgment. The slogan holds for a unique,
  non-aliased capability; §5 shows where it stops.
- **`experiments/Coeffects`**: "a borrow block is a handler with no operations that resumes
  once". This spike adds the operations (`withswap` through the stored clause), several handlers,
  blocks, lexical scoping (`atSucc`), and a typing *translation* with effect safety as a
  corollary. Coeffects worked over `CDerives` (CBPV); this spike works over the paper's
  `DerivesWf`.
- **`experiments/CoeffectsStrict`**: see §3. Safety is the FP, consistent with "meets them only
  through the Fundamental Property".
- **`experiments/Shifts`**: `handle` is `withbor` form (2), an instance of the labelled-shift
  schema with the source returned (`handle_is_shift`).

## 9. What did not go through

Nothing that was attempted failed. The items not attempted are in §5 (precondition 1, `box`)
and §6. For each, I have not derived it and have not verified that any obstruction is real.
The one machine-checked obstruction is `not_sharedCapture` (§5), which concerns the encoding
and not a printed result.

**Untranscribed rows.** The run-up the FP rests on includes `[TR]` Lemma 6.40, the one
`untranscribed` row of `Paper/INDEX.md`. This spike does not use it directly; it inherits the FP
as the library proves it.
