# §9 The factoring, T1, and step-indexing

[← §8 Two decisions](08-decisions.md) · [index](README.md) · next: [§10 Findings](10-findings.md)

---

## 9.1 Did the factoring hold?

The brief: borrows carry global constraints over the heap; control effects are local to their
dynamic extent; so write the calculus as BoLo's resource world plus a local control discipline,
meeting at exactly three points. The verdict, point by point.

**It held for safety.** The unary relation (§5) is BoLo's `wp` plus protocols. Its only
heap-specific definitions are the three meeting points (D4.3–D4.5), and every heap obligation of
a capture is discharged by independence (C5.3). Instances never appear in a resource.

**It held for the laws, with one exception.** The binary relation (§6) mentions no resource, and
every law of §7 but one is proved through it. Agreement (T6.6) uses the unary relation's safety
in one direction only, to know that the trees describe the machine.

**Where it strained.**

1. **ν/op at a non-contractible qualifier (O1).** The law needs the binary relation to know that a
   continuation is forced at most once. That is a fact about resources (a one-shot continuation is
   an owned cell) that the binary relation, defined over names alone, cannot see. A proof needs
   pending names owned by continuation values: meeting point 2 reaching into the instance supply.
   This is the one place where control was not local enough to be separated from resources.
2. **The resource handle had to become an instance.** Phase A's `resD` was a value on the
   resource side; a continuation could carry it past its frame (§10.2). Making it an instance of
   `Res` (D1.3) confines it by rows, the control side's scoping discipline, while its ownership
   stays a resource of the `fin` frame (L5.16). So "resources with destructors" sit at the
   boundary: owned on the resource side, *named* on the control side.
3. **The lend had to own.** Phase A's lend left the capability with its owner while the body ran
   (a place-based borrow). That form is unsound once the place has been moved (§10.1). The owning
   form (BoLo's `withbor` shape) keeps the capability with the `run` frame, which travels with any
   continuation that captures it. With it, meeting point 1 needs only `own` cells.
4. **The borrow half of BoLo is not exercised.** Because of 3, this calculus uses only BoLo's
   `own` fragment (L4.1): no `imm` or `mut` cell, no lifetime, no `↭` beyond the trivial. The
   factoring's hardest point, a continuation that holds a *borrow*, does not arise in this
   calculus; it arises at the kernel lift, and that is where T1 lives (§9.3). The definitions are
   written on the full carrier so the lift does not change them, but their proofs use L4.1 in
   places, which the lift must redo (each such step is marked).

**What each meeting point needed.**

| meeting point | definition | used in | needed independence at |
|---|---|---|---|
| 1. capabilities are resources | `Cap(ℓ, s)` (D4.3) | L5.15, L5.17 | the `run` frame: `lin` only ([lend]) |
| 2. continuations are values | `V⟦U_m⟧` at `κ¹`, `κ*` (D4.4) | L5.14 | every capture point (D2.6); the handler's own frame ([handle], §10.3) |
| 3. cancellation is finalisation | `Cancel(S₁)` (D4.5) | L5.6, L5.14, L5.15, L5.16 | the `fin` frame: not under `C` ([using]) |

## 9.2 Where the brief's rules went

| brief | here |
|---|---|
| independence governs what a multi-shot continuation may hold | L5.4, L5.6: a continuation at a `C` qualifier holds only `Pers`; T5.2 |
| T1 governs resuming while holding a lend | §9.3: not needed in this calculus (T9.1); needed for a borrowed source in the kernel lift (T9.2) |
| cancellation runs destructors | D4.5, L5.14 case 2, T5.2.3 |
| instances, handlers and the laws stay local | §6, §7 over names alone, except O1 |
| capability store and destructor frames become BoLo's resource world | `Cap`, `rsrc` cells, `fin` frames own them (§4.2) |
| only the instance supply is new | D4.7 (phase B) and D4.8 |

## 9.3 T1

**Theorem T9.1 (T1 is not needed in this calculus).** The Fundamental Property (T5.1) holds for
§2's rules, whose [lend] has no T1 premise. The harm T1 prevents in phase A, an operation on a
lent capability after its owner consumed it, does not occur in any run of a typed program
(T5.2.2). Phase A's T1 counterexample `t1Harm` is rejected by grades.

*Proof.* T5.1 and T5.2. For `t1Harm` (`experiments/EffModel/EffModel/Refusals.lean`): with the
owning lend, phase A's `lend c as x in M` is `lend c as x in M to z. split z as (c, r). …`, which
rebinds `c` *inside* the handler. `t1Harm`'s `getcap c` is outside the handler, so it is a second
use of the outer `c`: `gradeOK(lin, [2,2])` fails at `c`'s binder. ∎

*Why.* A suspended continuation that holds a `run` frame holds the capability (L5.15), so nothing
else can consume it while the lend is suspended; and the continuation is linear (`lin`
qualifiers only), so it is resumed. T1 protected a capability that phase A's lend left with its
owner; the owning lend leaves it with the frame.

T1 is needed when the thing a continuation holds is a **borrow** of a place whose owner keeps
running: a `Mut` or `Imm` borrow at a lifetime `α`, as in the kernel's `withbor` callbacks (SPEC
§19: "a stored κ would hold a lend across a suspension"). There the owner regains the place
when `α` ends, which is when the callback returns; a continuation suspended past that point
holds a borrow of a lifetime that has ended.

**Definition D9.1 (in-place and abortive tables).** A protocol table (in the sense of SPEC §19,
over BoLo's full `Res`) is *in place or abortive* when each of its instances is either bound by
a runner, or bound by a handler whose bound has `susp = false` (D2.8), or has only abortive
operations.

**Lemma L9.2 (tail resumption).** Let `N` be a clause with `tail_k(N)`, run on an elimination
stack `S_e` (no handling frame) in an environment with `k ↦ κ`, and suppose every operation `N`
performs is on an instance whose protocol is in place. Then, in the run of `N`:

1. `κ` is forced at most once on each path, and nothing is evaluated after it on that path:
   when `κ` is forced, the stack is `κ`'s eliminations followed by a suffix of `S_e`;
2. in particular, every frame `N` pushed (`bind`, `hnd`, `run`, `fin`) has been popped when `κ` is
   forced: every handler, lend and `using` frame of the clause has ended, and with them every
   lifetime the clause opened.

*Proof.* By induction on the derivation of `tail_k(N)` (D2.7), and within it on the run.

- `k ∉ fv(N)`: `κ` is never forced; nothing to show.
- `M to x. N'` with `k ∉ fv(M)`: the run of `M` pushes `bind(γ, x.N')` and forces nothing named
  `k`. A stop of `M` on an in-place instance is resumed in place, so the stack after its
  resumption is the stack at the stop (apply this lemma to the outer handler's clause, by
  induction on the depth of nesting of in-place clauses, which is bounded by the run's length).
  When `M` returns, the `bind` frame is popped and `N'` runs on `S_e`: the induction hypothesis.
- `if`, `case`, `split`: no frame is pushed; the branch's induction hypothesis.
- `λx. M`: pops an `arg` of `S_e`, so `M` runs on a suffix of `S_e`; the induction hypothesis.
- A tail call `(prj₁ (force k)) W⃗` or `(force k) W⃗` or `prj₂ (force k)`: the arguments `W⃗` do not
  mention `k`; evaluating the application pushes `arg` frames and `prj` frames, which are `κ`'s
  eliminations, and then forces `κ`.

Every other form of `N` has `k ∉ fv(N)` (D2.7's last clause), which is the first case. (2) is (1):
the only frames above the suffix of `S_e` are `κ`'s eliminations. ∎

**Theorem T9.2 (T1 for a borrowed source).** *Setting:* the kernel lift, where a lend's source is
a borrow (`withbor`, `withload`, [TR] §2's constants, or SPEC §19's unwinding forms) and its
callback runs at a row `Σ`. If the callback's table is in place or abortive (D9.1), then [TR]'s
frame theorems 6.64 (Imm Frame), 6.65 (Mut Frame) and 6.66 (Anti Frame) hold with `ewp` at that
table in place of `wp`.

*Proof.*

- **Abortive tables.** borrow-core proves these in Lean: `ewpTS_I_frameU`, `ewpTS_M_frameU`,
  `ewpTS_M_antiFrameU` (`Core/EffWp.lean`; SPEC §19 *Theorems* 3, "the LIFO frame lemmas"). At a
  stop on an abortive instance the continuation is abandoned, holding at most borrows at the
  frame's lifetime and below, as `wp`'s left-over `ρ⁺`; the frame ends as at a return.
- **In-place tables.** At a stop on an in-place instance, the handler's clause runs with the
  callback's share in the *frame* of its `wpG` (D5.2's `∀ r_f`): the clause can neither read nor
  write the share, and `↭` preserves every `mut` and `imm` cell of it ([TR] 6.48: frames preserve
  `↭`). By L9.2 the clause ends every frame it pushed, and so every lifetime it opened, before it
  resumes the callback, and it resumes it exactly at the stack it captured. So from the frame
  theorem's point of view the stop is a call: a `wpG` segment with the share framed, after which
  the callback's run continues with its share unchanged and its lifetime `α` still the most
  recently opened one. [TR] 6.65's proof then goes through with `ewp` in place of `wp`: it applies
  6.112 (`Nf`) once, at the frame's start, to choose `α` below every lifetime of the resource; it
  runs the callback under `wp-mono` and the frame; and it ends `α` with 6.104 (`[]⋆`) and the
  `mut` cell's preservation under `↭` (6.27, 6.28). None of these steps is affected by a framed
  segment in the middle whose lifetimes are all closed. 6.64 and 6.66 alike. ∎

**Status.** The abortive half is mechanised (borrow-core). The in-place half is proved here at
the level of the argument above: L9.2 is proved in full; the transcription of 6.65's `↭`
bookkeeping across the framed segment (the step "none of these steps is affected") is stated, not
written out line by line. That write-up is **open problem O2**.

**Lemma L9.3 (T1 is necessary for a place-based lend).** Phase A's `t1Harm`, a lend whose body
performs an operation of a suspending handler that returns the continuation in a stream, is typed
when T1 is not checked, and its run reaches "a lent capability used after its owner consumed it".

*Proof.* Machine-checked by phase A: `acceptsWithoutT1 sigs t1Harm` is `true` and the refusal is
recorded with T1 as its only rule (`Refusals.lean`, `docs/effect-model.md` §3.3, "Without T1,
`t1Harm` *types*, so T1 is the only rule that refuses it"). ∎

**Open problem O3 (an owning lend of a borrowed source under a suspending table).** Does [TR]
6.65 lift to `ewp` at a table with a suspending instance when the lend owns its source, so that a
continuation holding the callback also holds the frame? *The step not derived:* [TR] 6.65's proof
chooses `α` below every lifetime of the resource at the frame's start (6.112) and ends it after the
callback; if the callback is suspended, code outside the frame runs in between and may open and
close lifetimes of its own, and 6.65's proof does not order those relative to `α`. I have not
derived the lifted lemma and have not verified that any obstruction is real. A lifetime-based
replacement for T1 (a continuation whose type mentions `α` cannot be resumed after `α`, phase A's
open problem 4) needs an outlives rule for thunks, which the kernel does not have (T2, #173; SPEC
§19 *Names*).

## 9.4 Step-indexing: what would force it, and why nothing here does

**Theorem T9.4 (no step-indexing).** No definition of §§3–6 is step-indexed or fuelled. Every
recursive definition is one of:

| definition | recursion | well-founded on |
|---|---|---|
| `⟦M⟧` (D3.13) | structural | the term; `bfix_n` by `n` |
| `Tree`, `Strm` (D3.9) | inductive types | — |
| `V⟦·⟧`, `E⟦·⟧`, `Elim` (D5.4, D5.5) | by types | the type, with `strm` by a least fixed point |
| `ewp` (D5.3) | least fixed point in `Prop` | — (Knaster–Tarski) |
| `TreeRel` (D6.2) | inductive relation | — |
| `StrmRel` (D6.3) | least fixed point in `Prop` | — |
| `VR`, `CRU` (D6.4) | by types | the type |

and every typed program terminates (T5.2.1).

*Proof.* Inspection of each definition. Termination: T5.2's `wpG` asserts a finite run. ∎

**What would force step-indexing.** Each item says what it would take, and where this calculus
stands.

1. **General recursion.** A `fix` whose unrollings are unbounded makes some computations diverge.
   Then `wpG` (total correctness) is false of them, and a partial-correctness relation needs an
   index or a guarded fixed point. Phase A has `fix`; this calculus has `bfix_n`, SPEC §20's
   `bounded_fix`, whose proof is "the induction on the budget" (L5.17). Divergence stays §14's
   `ν` codata (SPEC §19 *Divergence*), observed one finite step at a time.
2. **A recursive type with a negative occurrence.** `μX. U(X ⇒ F A)` encodes divergence without
   `fix`. The relation at such a type is defined by recursion on itself in a contravariant
   position, which has no least fixed point in general: the classic reason for step-indexing.
   This is T15 (a), "`X` under a `U`-codomain", #182. The one recursive type here, `strm`, has `X`
   only to the right of `F` (D1.6), so its relations are least fixed points of monotone operators
   (D5.4, D6.3), and its elements are finite (every stream is produced by a finite computation).
3. **Higher-order state.** A cell that can hold a thunk allows Landin's knot (a thunk stored in a
   cell that it reads and calls). Capability states here are ground (D1.2). For the **unary**
   relation, BoLo's own method would suffice: a `mut` cell carries a predicate at a strictly later
   lifetime, `Mut_α ≜ {(β ⊐ α, v, ρ, P̂ : Val → SProp_β)}` ([TR] §5), which stratifies the
   impredicativity by lifetime instead of by step, and linear ownership prevents the knot from
   being tied. For the **binary** relation no such stratification has been defined (O4, §9.5).
4. **Continuations as stored data.** A one-shot continuation is a heap cell, but its content is a
   stack of frames, *code*, and its relation is the thunk relation at its type (D4.4), defined by
   recursion on the type. No predicate is stored in the heap, so no knot arises. A continuation can
   be stored in a stream (positive, item 2) but not in a capability's state (ground, item 3).
5. **Multi-shot continuations.** A copyable continuation is a thunk value at an unrestricted mode;
   copying it is copying a value. No new recursion.

*Source.* Biernacki, Piróg, Polesiuk & Sieczkowski's relations for handlers (*Handle with care*,
PACMPL 2 (POPL 2018), DOI 10.1145/3158096; *Abstracting algebraic effects*, POPL 2019, DOI
10.1145/3290319; *Binders by day, labels by night*, PACMPL 4 (POPL 2020), DOI 10.1145/3371116 —
titles, venues and authors verified via Crossref) are step-indexed [their construction is
recalled, not re-read here], because their calculi have general recursion. This calculus avoids it
by giving up general recursion (item 1), as BoLo does ([TR]'s calculus has no recursion and its
`wp` is total correctness), not by a different technique for the same calculus. That is a
difference in setting.

## 9.5 Lifting the ground restriction

Operation arguments and answers, and capability states, are ground (D1.2).

- **Operation arguments and answers.** *Unary*: SPEC §19's protocol already carries argument and
  answer relations (`𝒱⟦A_i⟧ ⋆ …`, `𝒱⟦B_i⟧ ─⋆ Φ`), and D4.6 lifts by putting the argument's resource
  in the stop's resource and the answer's in the resumption, as there. *Binary*: `TreeRel.op`
  would relate `op i E o v k d` with `op i' E o v' k' d'` at `VR(A_o)`-related arguments and with
  `k`, `k'` related at `VR(B_o)`-related answers, in place of equality; the folds' lemmas
  (L6.3) gain the corresponding premises. This is routine and not done here.
- **Capability states.** **Open problem O4**: a binary relation for capability states of
  higher type, whose worlds relate the two sides' cells by a relation stratified as BoLo's `mut`
  cells are. I have not defined it.
