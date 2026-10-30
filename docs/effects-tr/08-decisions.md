# §8 Phase A's two open questions, decided

[← §7 The laws](07-laws.md) · [index](README.md) · next: [§9 The factoring, T1, step-indexing](09-factoring.md)

Phase A left two questions open (`docs/effect-model.md` §5, items 1 and 3). This section decides
each, says what the decision changes in phase A's model, and gives the reasons. Every claim here
rests on a numbered result of this document, on phase B's Lean, or on a cited paper.

---

## 8.1 Where a dropped continuation is destroyed: statically

**The question.** Phase A destroys a dropped cancellable continuation *dynamically*: when a resuming
clause ends, the machine checks by reachability whether the clause's result mentions `κ`, and
cancels `κ` if not (`clauseEnd`, `Val.mentions`). Congard, Munch-Maccagnoni & Douence place the
destructor call at the weakening point of the typing derivation, *statically*. Which does the
calculus use?

**Decision.** Static. A continuation whose qualifier admits weakening has type
`K(q, B, ρ', C) = U_m^∅((B ⇒^{ρ'} C) & F 1)` (D1.8), a **linear** thunk when `C ∉ q`: the clause
must take exactly one of `resume` and `cancel`. A clause that drops `κ` calls `cancel k`, which the
elaborator inserts at the weakening point, as it inserts every other drop glue (SPEC §19:
"the elaborator inserts a `[then]` finaliser for every owned local in scope at a possible
weakening point… The kernel checks it; the elaborator establishes it").

**Reasons.**

1. **The proof needs it.** The Fundamental Property's handler case (L5.14) uses the continuation
   value's relation, `V⟦K(q, B, ρ', C)⟧`, which is a statement about the clause's *type*. A
   dynamic rule makes the obligation "if the clause's result does not mention `κ`, cancel `κ`",
   a property of a run, not of a type, and it is not preserved by putting `κ` in a data
   structure the program later drops (phase A's own open problem 1: "a droppable thunk holding a
   continuation leaks when dropped"). With the static rule, exactly-once finalisation is
   linearity (T5.2.4): the one-shot continuation is a heap cell that its one use frees, and a
   cell left over violates `wp`'s `ρ⁺|own = ∅`.
2. **Phase B already does it.** Phase B's denotation types the continuation with `ktyB`, the pair
   `⟨resume, cancel⟩` at mode `lin` (or `unr`), and its Fundamental Property covers it (`mkK_rel`,
   `dtorsT_rel`). The static rule is what phase B proved sound.
3. **The kernel already does it.** SPEC §19's `κ = ⟨resume, cancel⟩ : U((B ⊸ F_Σ R) & F_Σ 1)` and
   its drop glue are the static rule.
4. **It is the source's construction.** Congard et al. make weakening an effect performed at the
   weakening points, which is what restores the strength `T(− ⊕ E)` needs in a linear setting, and
   with it T7.3. The `A & 1` encoding is Munch-Maccagnoni's, who reads it as an affine type in
   his system (*Resource Polymorphism*, arXiv 1803.02796, 2018) [recalled].
5. **It costs nothing at run time.** The reachability check was a model artefact (phase A §6:
   "`clauseEnd` reachability, leak tracking: model artifacts; with static weakening …, a dropped
   `κ` is a static destructor call").

**What changes in phase A's model.**

- The `clauseEnd` frame goes, and the machine's cancel happens only at `prj₂ (force κ)`, an
  abortive operation, or a co-operation's failure (D3.6).
- A clause that drops `κ` must say `cancel k`. Phase A's `hTake`, `hTimeout` and `hStream`
  (the drop branch of a stream) each gain one. The observable order is phase A's when the
  elaborator places the cancel at the end of the clause's scope, as Rust places drops; phase A
  cancelled at the clause's end, after the clause's other actions. The kernel accepts either
  placement; it is the elaborator's choice, and a different placement can reorder a `free` with an
  `emit` in the same clause.
- Phase A's stream had to be linear with an explicit `drop` because it had no static weakening
  points (`docs/effect-model.md` §3.2: "if streams had a derived drop, an implicit drop would have to run the destructor").
  With static weakening the same holds for every value holding a one-shot continuation: it is
  linear, and its destructor is called where the elaborator drops it. This calculus gives a
  destructor to continuations (`cancel`) and to streams (`drop`) only. A general destructor per
  type (Congard et al.'s `δ : A → TI` for every type) is not added; that is the elaborator's drop
  glue over these two.

## 8.2 Co-operations that can raise: they fail to the lend, at fallible operations

**The question.** Phase A's co-operations are pure state access, `A × S → F (B × S)`. A failing
capability (an I/O error) needs a co-operation that can fail. What does failure do, and where is
it handled?

**Options.**

| | failure | handled | the runner stays a comodel of `E`? | the runner stays a direct call? |
|---|---|---|---|---|
| (a) | none (phase A) | — | yes | yes |
| (b) | answers `inr (e, s')` | at the `lend`, which answers `(cap, inr e)`; the client's continuation is cancelled | yes: the error leaves through the runner's boundary, not through `E` | yes: a branch to the lend's landing pad |
| (c) | raises an abortive operation of the client's row | by the client's handler | no: `E` would need an operation answered by a constant | yes |
| (d) | performs any operation of the context | by the context's handlers | no | no: the co-operation captures a continuation |

**Decision.** (b), and only at a **fallible** operation, one whose qualifier admits weakening
(`W ∈ q_o`, D1.3). A co-operation answers `(B_o ⊗ S) ⊕ (E_o ⊗ S)` with `E_o = int` at a fallible
operation and `E_o = 0` otherwise (D1.9). On failure the machine writes the state, cancels the
client's continuation up to the `run` frame (its `fin` frames' destructors, innermost first), and
the lend answers the capability with `inr e` (D3.6).

**Reasons.**

1. **A comodel cannot answer by a constant.** Plotkin & Power (*Tensors of comodels and models*,
   MFPS 2008) [as read for phase A, `docs/effect-model.md` §2]: a theory with a constant has only
   the empty comodel in `Set`. So the failure cannot be an operation of `E` answered by the
   runner, which excludes (c) as a runner of `E`. It leaves through the runner's own boundary, the
   lend, which is where Ahman & Bauer's runners deliver an exception or a signal: to the
   `finally` of the run (*Runners in action*, ESOP 2020, §3 [via phase A and the literature report
   on #235]).
2. **Fallible exactly when weakenable is independence.** A failure discards the client's
   continuation between the operation and the lend, as an abortive operation discards it up to
   its handler. Independence requires everything that continuation holds to be droppable or to
   have a destructor, which is `W ∈ q_o` at the capture points (L5.15.2 uses the protocol's cancel
   conjunct, present exactly when `W ∈ q_o`). So the runner bound `rbnd(E)` contains `cancel`
   exactly when `E` has a fallible operation, and the frames across a fallible operation are checked
   as frames across a `raise`. No new rule is needed.
3. **Phase B implemented it.** Phase B's `coRes`, `coK`, `coStep` and the failure branch of
   `runL_rel` are (b), at every operation; its Fundamental Property covers it. Restricting to
   fallible operations is a special case (`E_o = 0` makes the branch empty), and it is what the
   unary relation needs (L5.15.2).
4. **The lowering survives.** The runner still answers in place: a co-operation is a direct call,
   and its failure is a branch, as an abort is (phase A §6).

**What stays open.**

- **(d)** would let a co-operation perform control operations of the context (a capability whose
  implementation logs, or suspends). Its continuation would then be captured inside the runner, and
  the runner would no longer be in place. That is the dual of T1 (§9.3), and it is not taken up.
- **The error type** is `int` here (phase B's choice). A ground error type per operation is the
  same proof; a non-ground one needs §9.5's lifting.
- **The state on failure** is the co-operation's `s'`. Ahman & Bauer's signals, which discard the
  state (tensor with `kill`), are not modelled; with (b) the lender always regains its capability
  with a state, which is the sum (T7.10's `lent_state_survives`).
- **Failing finalisers** (phase A open problem 8, SPEC §19 K3): destructors here only free. A
  finaliser that raises is outside this calculus.
