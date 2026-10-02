# Handlers around divergent computations (parked)

A design spike for the gap of SPEC §21 *Open* and decision 59: no handler can wrap a div
computation (`with to_result { f(x) }`, `f` looping and raising; `corpus/reject/rec-loop.bc`).
**Parked** by the user before any Lean or probe was written: handlers around loops are not a
priority, since the operator's shape (a generator pipeline with a handler per iteration) already
works. These are the findings so far, for whoever reopens it.

**How claims are marked.** **[inspection]**: read off the rules, the library or the
elaborator, with no proof. **[hypothesis]**: not checked. Nothing here is **[Lean]** or
**[checker]**.

## 1. The general form

`handle_loop` installs a handler per observation, with the handler's state in the loop's
state, as SPEC §19 *Divergence* says. With the inner loop `L = U(Loop_{n:E, Σ} A B)` and the
handler's state `P`, it is `unfold` at `Loop_Σ R B'` with state `P ⊗ L` and step

    step (p, l) = ⟨ a ← hnd_n (hrN, hcN) (next l);  kN (p, a),
                    a ← hnd_n (hrC, hcC) (close l); kC (p, a) ⟩

    hrN : retTy Σ (A ⊕ L) AnsN      hcN : clausesTy Σ AnsN E      kN : !U(P ⊗ AnsN ⊸ F_Σ(R ⊕ P ⊗ L))
    hrC : retTy Σ B AnsC            hcC : clausesTy Σ AnsC E      kC : !U(P ⊗ AnsC ⊸ F_Σ B')

- **It uses only existing rules [inspection].** It needs `unfoldN`, `nuOut`, `proj₁`/`proj₂`,
  `effHandle` and `effLet`. `effLet`'s side conditions fall on `P`, which is live across the
  site: it drops if `Σ` has weakening, and is persistent if `Σ` is unrestricted. The probe was
  to be a derived rule `d_handleLoop`, on the model of `d_handleAbortCapture`
  (`experiments/SecondClass/SecondClass/AbortClause.lean`), with the step a closed `!` value.
- **Abortive operations [inspection].** Take `P` to be the clauses' captures and
  `AnsN = (A ⊕ L) ⊕ E`. Its clauses and return are §21's `inl`/`inr` injections, at the
  observation's type. `kN` is the `case` that §21 runs after the site:
  - `inl (inr l')` continues;
  - `inl (inl a)` finishes with the return clause's answer;
  - `inr e` finishes with the clause's answer.

  A `raise` in observation `k` therefore ends the whole loop with the handler's answer. The
  residual is `B' = B ⊕ E`, since closing may raise.
- **Resuming operations [inspection].** Use §21's state-passing answer,
  `AnsN = U(P ⊸ F_Σ(R ⊕ P ⊗ L))`, with `kN (p, g) = force g p`. `κ` is captured inside
  `hnd_n` around one observation's code, so it never holds frames of another observation. The
  state persists because it is a component of the loop's state.
- **Instantiating user clauses [inspection].** The user's clauses are written against the
  answer `R`. Reading them at the observation's answer is mechanical when every `k` is in tail
  position or absent: a clause's `return r` becomes "finish with `r`", and `k(v)` passes its
  answer through unchanged. A clause with work after `k(v)` (`r <- k(v); M[r]`) would run `M`
  after the rest of the loop. That needs pending frames across observations: a first-order
  buffer, as `deep` keeps, or a stored continuation (§5). Such clauses would be rejected with
  that reason.

## 2. Composition [inspection]

The result is again a `Loop_Σ`, so `handle_loop h₁ (handle_loop h₂ M)` types. Each outer
observation runs exactly one inner observation: the step calls `next` once on every path. So
the observation structure stays one-to-one. After fusion, the state is `P₁ ⊗ P₂ ⊗ (M's state)`
and one step is `hnd_{n₁}(hnd_{n₂}(M's step))`.

## 3. Where it should live [hypothesis]

**Not in the effects pass.** That pass emits the site before divergence is inferred, which is
the #232 failure. It runs first (`Frontend/Sugar.lean`, `elaborateS`: `Effects.elaborate`, then
`elabDivs`). It should emit the site exactly as today, as the `hndCtl` sugar node.

The principled point is the div body's state machine (SPEC §14 *One state machine per body*).
A handler site whose body has a resumption point is a scope of the machine, as a loop around a
point is. Each state under the site holds the handler's state as well. Each observation in such
a state runs inside `hnd_n`, reinstalled per observation with its clauses read at the step's
answer type. This needs no effect names and no prediction: the machine already knows the
step's type. `handle_loop` is that construct's meaning, stated once.

## 4. What it would close [hypothesis]

- control handlers around loops;
- a loop inside a recursion (`Exhausted` reaches the handler);
- layers over div recursions;
- the reconciler chain;
- the I/O-driven loops of #188 stage 4.

Effects under `deep` would need the same site scope over `deep`'s machine.

## 5. Lowering and open problems

- **Lowering [hypothesis].** The handler fuses into the machine: per observation, a site of
  known clauses, with no closure per observation. A tail-resumptive clause is a direct call.
  The exception is a stateful handler, which still dispatches at each resume until a native
  handler parameter exists (§19/§21 *Open*).
- **Open problems [inspection].** The design does not lean on any open problem. A continuation
  spanning observations would have to be stored in `P ⊗ L`, but `κ`'s type mentions `AnsN`,
  which mentions the state. That makes the state recursive under `U` (`X` under `⊸`, T15;
  compare `no_uniform_comp` in `experiments/HandlersControl`).
