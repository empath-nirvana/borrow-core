# 04 · Dynamics and the erased lowering

This section fixes the machine of the effect calculus: its configurations, evaluation contexts,
head steps, cancellation, runs under every allocator, and determinism, including determinism up
to renaming. It says which code of a captured context runs on each path a continuation can take:
resumed, cancelled, abandoned at an abortive operation, dropped, or resumed somewhere else. It
states the erasure obligations, resume once = call, abort = branch, suspend = state machine, as
theorems that relate this machine to the `Backend/` lowering.

It uses the objects of [00-structure.md](00-structure.md) §1 verbatim. It owns K-CTX, K-STEP,
K-CANCEL and K-RUN and the notation of O-FIN (`D_K`, the cancel state). It says nothing about the
relation. Where the model depends on the dynamics (D-STOP, D-OWED, D-DTOR, T-LEAK, T-FIN), this
section gives the run-level facts that model consumes and cites the model id. Open questions are
cited by id; every question is boxed in [99](99-open-questions.md). This section raises OQ-41 to
OQ-43 (§9).

Marks follow 00 §0.1: **[Lean]** a declaration cited `file:line`; **[read]** a reading of code or
documents; **as built / changed / new** the status against the kernel today.

---

## 0. The machine under every open option

The machine is the one already in the kernel, `Head` with the context rule
(`Paper/S3_Dynamics/Definitions.lean:445-551`) and allocator runs (`Core/Alloc.lean:70-92`). The
re-indexing of the model does not change it.

- **The world `W = (ρ, ls, σ)` is ghost.** Lifetimes, lends, records and the open-frame stack `σ`
  have no run-time representation. BoLo's terms carry no lifetime values, and a borrow constant
  is an ordinary λ-term (`withborUE`, `Core/EffBorrow.lean:186-188`). Making `σ` a component of
  the world (D-W) and relativising the stop (D-STOP) change predicates over runs, not the runs.
- **Every option of OQ-8, OQ-9 and OQ-10 leaves K-STEP unchanged.** Option (a) of OQ-9 (`share`
  and `owed` carry the open frames) and option (c) (R-T1) are statements about runs of the same
  machine. Option (b), capture rebasing, is stated by its source as "the machine changes nothing:
  freeze and resume remain D3.6's capture and force" (`docs/effects-tr/14-stored-continuations.md`
  §14.3) [read].
- **Options that would change the machine**, each stated with its question:

| question | option | machine change |
|---|---|---|
| OQ-14 | (b) generative instances | a step that allocates a fresh instance label, and `HasHnd`/`Catches` compare labels instead of static names |
| OQ-26 | (b) shallow handlers | a head step `hnd_n H K[perform_n v] ↦ h_op(v, λy. K[y])` without reinstalling `hnd_n` |
| OQ-12 | (b) scoped operations | none: `scope_{n,j}(V; M) ≜ perform (n, (j, (V, M)))`, `[op]` unchanged; the clause type and the handling of the scope are 03 §9.1's K-SCOPE, the latter OQ-59 |
| OQ-15 | (b) div as a row | one step, `fix g ↦ g (thunk (fix g))` (03 §9.2) |
| OQ-20 | (b) `withtake` | no step; a new constant, an ordinary λ-term over `load`/`store` |
| OQ-24 | (b) owned abortive payload | no step; `[finalise]` already runs `D_K` before the payload reaches the clause |
| OQ-41 | (b) a region-keyed `ccatch` | `[cancel]`/`[cancel-raise]` match the region's names |

Under the defaults of these questions the machine is exactly as built.

---

## 1. Configurations and runtime forms

**Configurations.** `⟨μ, e⟩` with `μ : Heap = Loc → Option Val`
(`Paper/S3_Dynamics/Definitions.lean:159`) and `e : Expr` closed. Values `v, w` are the `IsVal`
expressions. The machine is parametric in the host `ℍ` (`{ℍ : Host} [HostIs ℍ]`, throughout).

**The effect primitives** (SPEC §19 *Terms and machine*), all applications of a `Prim`, with no
new `Expr` constructor:

```
perform_{n,i} v         ≜  perform (n, (i, v))            performE ∘ opPayload   Definitions.lean:343, 349
raise_{n,i} v           ≜  raise (n, (i, v))              raiseE ∘ opPayload     :346, 349
hnd_n H e             ≜  hnd (n, (h_ret, hs)) e         hndE ∘ hndVal          :331, 352
M then x. N unwind D  ≜  ubind (λx.N, λ_.D) M           ubindE; thenE          :334; Core/EffRules.lean:923
ccatch e                                                ccatchE                :337
cfin s e                                                cfinE                  :340
```

- `hs` is a right-nested tuple of clauses; `clauseAt hs i` selects the `i`-th
  (`Definitions.lean:356-360`).
- **The cancel state** (O-FIN) is `s = (N, err)` with `N : List Nm`, `err : Option Val`, carried as
  the payload of a `raise` of the reserved name `⊥ = 0`:
  `⊥(N, err) ≜ raise (cancelVal N err) = raise (0, (0, (namesVal N, errVal err)))`
  (`Definitions.lean:362-375`).
- **The error policy** is `errNext N err m j w`: keep `err` if set; else none if `m ∈ N`; else
  `(m, (j, w))` (`Definitions.lean:378-382`). It is OQ-21's option (a).

**Runtime-only forms.** `ccatch`, `cfin` and the continuation `κ` (K-KONT, below) have no typing
rule: `CDerives` has rules for `perform`, `raise`, `[let]`, `[then]` and `[handle]`
(`Core/Fundamental.lean:340-372`) and none for `ccatch` or `cfin`. They arise only from the
`[op]` step and the cancel steps. Every statement below about "reachable configurations" means
configurations reachable by `→` from `⟨μ₀, e⟩` with `e` closed and typed by `CDerives`.

---

## 2. Evaluation contexts

### K-CTX: evaluation contexts and their predicates
- Form:
  ```
  K ::= □ | (K, e) | (v, K) | let (x,y) = K in e | case K {…} | e K | K v | K; e | inj₁ K | inj₂ K
  ```
  Evaluation is argument-first: `e K` evaluates the argument, `K v` then the function. So
  `hnd_n H e` runs `e` under the frame `hnd_n H □ = (hnd (n,H)) □`, and `ubind`, `ccatch`, `cfin`
  likewise. Plugging `K[e]` and composition `K ∘ K'` with `(K ∘ K')[e] = K[K'[e]]`.

  The **catcher frames** are `hnd_m H □`, `ubind (N,D) □`, `ccatch □` and `cfin s □`. On a
  context, by structural recursion:

  ```
  HasHnd n K    ⟺  K has a frame hnd_n _ □                       (K is "free of n" when ¬HasHnd n K)
  Catches n K   ⟺  K has a frame hnd_n _ □, or ubind _ □, or cfin _ □, or (n = ⊥ and) ccatch □
  hndNames K    =  the names of K's handler frames, outermost first
  Plain K       ⟺  K has no catcher frame and its innermost frame is not □ v
  ```

  **The destructor** (O-FIN). For `K` with ubind frames `ubind (N₁,D₁) □ … ubind (N_k,D_k) □`
  listed innermost first, `D_K` is the ordered list `[D₁, …, D_k]` run nested: `K°` is `K` with
  its plain frames deleted, and `D_K⟨e⟩ ≜ K°[e]`. Each `Dⱼ ()` runs under the frames outside
  frame `j`, so a raise from `Dⱼ ()` supersedes and is finalised by those frames (§3, *Notes on
  the steps*). This LIFO reading of `D_K⟨e⟩ = K°[e]` holds **only when `e` is a raise or a cancel**:
  then each frame's `[finalise]` or `[finalise-cancel]` fires and runs `Dⱼ ()`. When `e` returns a
  value `w`, `ubind (Nⱼ, Dⱼ) w ↦ Nⱼ w` by `[then]`, so `K°[e]` runs the frames' continuations, not
  their finalisers. For an `e` that may return, the **sequential form** `D_K ▷ e` runs
  `D₁ (), …, D_k ()` LIFO, each under the frames outside it (a finaliser's raise superseding and
  finalised outward), and then `e` outside all of them; when every finaliser answers `()` it is
  `D₁ (); …; D_k (); e`. `D_K` names the code a cancel or an abortive unwind runs out of `K`. D-DTOR (05) is
  the predicate that code discharges.

  **The region of a capture.** For `[op]` at `hnd_n H` around `K`, the region's names are
  `N(n, K) ≜ n :: hndNames K`.
- Uses: O-FIN, O-NAME.
- Today: `Kont` (`Paper/S3_Dynamics/Definitions.lean:93-104`), `plug` (`:135-145`), `comp` and
  `plug_comp` (`Support/Dynamics/Machine.lean:226-240`), `HasHnd` (`Definitions.lean:386-394`),
  `Catches` (`:397-407`), `hndNames` (`:410-417`), `shift` (`:420-431`); the composition lemmas
  `hasHnd_comp`, `catches_comp`, `hndNames_comp` (`Core/EffDefs.lean:77-98`); `Plain`
  (`Core/Steps.lean:649-660`). `D_K` is not a Lean definition. Status: as built; `D_K` new as a
  named function.
- Slices: typing of the frames 03 (K-THEN, K-HND); D-DTOR 05; L-ALG0, L-W 06; T-FIN 07; the
  lowering's `Frame` (`Backend/Clos/Capture.lean:651-658`) 08.
- Depends on: none.
- Open: OQ-41 (contexts that contain `ccatch`/`cfin`).
- Obligation: `D_K` as a Lean function on `Kont`, with `D_{K ∘ K'} = D_{K'} ++ D_K` (innermost
  first): **mechanical**, by the same induction as `catches_comp`.

**Static names, dynamic resolution.** The machine resolves `perform_n` to the *nearest* enclosing
`hnd_n` at run time (`HasHnd`, the side condition of `[op]`). The resolution is lexical only
because elaboration gives each `handle` site its own name (SPEC §19 *Names*). When a site is
re-entered (`memo` under itself), the nearest instance wins dynamically. This is the one place
where the machine's resolution and the lexical reading differ, and it is OQ-14's subject.

---

## 3. Head steps

Judgement forms:

```
⟨μ, a⟩ ↦ ⟨μ', a'⟩                       head step                         Head μ a μ' a'
⟨μ, e⟩ → ⟨μ', e'⟩                        step                              Step1
⟨μ, e⟩ →ₐ ⟨μ', e'⟩  (count k ↦ k')       step under allocator A            AStep1 A k μ e k' μ' e'
⟨μ, e⟩ →*ₐ ⟨μ', e'⟩                      run under A                       ARun A k μ e k' μ' e'
```

### K-STEP: the head steps
- Form. The context rule:

  ```
        ⟨μ, a⟩ ↦ ⟨μ', a'⟩
  ──────────────────────────────  [ctx]
   ⟨μ, K[a]⟩ → ⟨μ', K[a']⟩
  ```

  **The pure and memory steps**, BoLo's `↦` box ([TR] p. 4) with the host, array, loop and
  fixed-point steps: `beta`, `alloc`, `free`, `load`, `store`, `seq`, `letpair`, `case₁`, `case₂`,
  `host`, `tab`, `idx`, `split`, `drop`, `count`, `countTry`, and

  ```
  ⟨μ, bounded_fix (s, (k, a))⟩ ↦ ⟨μ, s (self_k, a)⟩                         [boundedFix]
      self_0 = inj₁ (),   self_{k+1} = inj₂ (λx. bounded_fix (s, (k, x)))
  ```

  The machine counts the budget down, so every run of `bounded_fix` is finite at every host
  (`boundedFixNext`, `fixSelf`, `Support/Dynamics/Arrays.lean:90-99`).

  **The capture steps** (SPEC §19). Side conditions are over K-CTX. `n ≠ ⊥` is a typing premise
  (`hn0`, `Core/Fundamental.lean:370`), not a side condition of the step.

  ```
  ⟨μ, hnd_n H w⟩ ↦ ⟨μ, h_ret w⟩                                                       [ret]

     clauseAt hs i = c      ¬HasHnd n K
  ─────────────────────────────────────────────────────────────────────────────────  [op]
   ⟨μ, hnd_n H K[perform_{n,i} v]⟩ ↦ ⟨μ, c (v, κ_n(H, K))⟩

     clauseAt hs i = c      ¬Catches n K
  ─────────────────────────────────────────────────────────────────────────────────  [unwind]
   ⟨μ, hnd_n H K[raise_{n,i} v]⟩ ↦ ⟨μ, c v⟩

  ⟨μ, ubind (N, D) w⟩ ↦ ⟨μ, N w⟩                                                      [then]

     m ≠ ⊥      ¬Catches m K
  ─────────────────────────────────────────────────────────────────────────────────  [finalise]
   ⟨μ, ubind (N, D) K[raise_{m,j} v]⟩ ↦ ⟨μ, D (); raise_{m,j} v⟩

     ¬Catches ⊥ K
  ─────────────────────────────────────────────────────────────────────────────────  [finalise-cancel]
   ⟨μ, ubind (N', D) K[⊥(N, err)]⟩ ↦ ⟨μ, cfin (N, err) (D ())⟩

  ⟨μ, cfin s w⟩ ↦ ⟨μ, raise s⟩                                                        [cfin-ret]

     ¬Catches m K
  ─────────────────────────────────────────────────────────────────────────────────  [cfin-raise]
   ⟨μ, cfin (N, err) K[raise_{m,j} w]⟩ ↦ ⟨μ, ⊥(N, errNext N err m j w)⟩

     ¬Catches ⊥ K
  ─────────────────────────────────────────────────────────────────────────────────  [cancel]
   ⟨μ, ccatch K[⊥(N, none)]⟩ ↦ ⟨μ, ()⟩

     ¬Catches ⊥ K
  ─────────────────────────────────────────────────────────────────────────────────  [cancel-raise]
   ⟨μ, ccatch K[⊥(N, some E)]⟩ ↦ ⟨μ, raise E⟩
  ```

  **The continuation** (K-KONT's term). `κ_n(H, K)` is the `&` pair of its entries, encoded as
  a function of a selector:

  ```
  κ_n(H, K) ≜ λs. case s { inj₁ u. u; λy. hnd_n H K[y]
                          | inj₂ u. u; ccatch (hnd_n H K[⊥(N(n,K), none)]) }

  resume κ w ≜ (κ (inj₁ ())) w   →⁴  hnd_n H K[w]                        beta, case₁, seq, beta
  cancel κ   ≜  κ (inj₂ ())      →³  ccatch (hnd_n H K[⊥(N(n,K), none)])  beta, case₂, seq
  ```

  `Kont.shift` makes the substitutions in these steps give back `K` exactly.

  **No capture step allocates.** `κ` is a term, not a heap cell. This differs from the TR's
  machine, where a one-shot continuation is a heap cell freed by its use
  (`docs/effects-tr/03-dynamics.md` D3.2) [read]. Here "resumed twice" is not a use after free at
  the machine level. Linearity of `κ` is a property of typed runs (T-LIN, 07), not of the machine.
- Uses: K-CTX, O-NAME, O-FIN, O-KONT.
- Today: `Head` (`Paper/S3_Dynamics/Definitions.lean:445-546`): `beta` `:446`, …, `boundedFix`
  `:495`, `hret` `:499`, `hop` `:502`, `hunwind` `:508`, `uthen` `:513`, `ufin` `:517`, `ufinC`
  `:523`, `cfret` `:528`, `cferr` `:532`, `cancel` `:538`, `creraise` `:542`; `Step1` (`:549`);
  `kappa` (`:438-443`); the run lemmas `ewp_kappa_resume` (`Core/EffRules.lean:493`, four steps)
  and `ewp_kappa_cancel` (`:529`, three steps). The executable counterpart is `catchOp` and
  `effApp?` (`Support/Dynamics/Interpreter.lean:175-221`). No Lean statement relates it to `Head`
  (§6.0). Status: as built.
- Slices: typing 03 (K-OP, K-RAISE, K-THEN, K-HND, K-KONT); the stop tables `opTable`,
  `cancelTab` 05 (D-OPTAB, D-CANCELTAB); the reduction halves of L-HRET, L-HOP, L-HFWD, L-ALG0,
  L-W, L-TAIL (§5 here); compatibility 07; lowering 08.
- Depends on: K-CTX.
- Open: OQ-14, OQ-26 (steps that would be added); OQ-21 (`errNext`); OQ-24 (`[finalise]`'s
  payload); OQ-41.
- Obligation: none new for the steps (as built). The SPEC text of `[unwind]` reads "`K` free of
  `n`, unwind-clear" (SPEC.md §19 *Terms and machine*). The Lean step reads `K.Catches n = false`
  (`Definitions.lean:511`), which also excludes `cfin` frames and, at `n = ⊥`, `ccatch` frames.
  Lean governs, and the SPEC text is to be aligned in 08: **mechanical**.

**Notes on the steps.**

- **Abortive operations unwind eagerly, innermost first.** A `raise_m` meets the nearest catcher
  frame. At a `ubind`, `[finalise]` runs that frame's `D` and raises again from the frame's
  position. At `hnd_m`, `[unwind]` passes the argument to the clause. Every other frame of `K`
  is discarded with no step: plain frames, and handler frames of other names, whose clauses are
  `!` at `∅`.
- **A finaliser's raise supersedes.** Under `[finalise]`, the pending `raise_m` is in the
  continuation of `D ()`. If `D ()` raises `q`, the pending raise is abandoned and `q` unwinds
  from there.
- **`ufin` excludes the name `⊥`, not the payload shape.** `[finalise]` needs `m ≠ 0`
  (`Definitions.lean:517`). `[finalise-cancel]` needs the payload to be `cancelVal N err`
  (`:523-526`). A `raise (0, p)` with any other payload is stuck at a `ubind`. Typed programs never
  raise it: `Row.NZ` (`Core/EffRules.lean:702`) and `hn0`.
- **Cancel is uninterceptable only by typing.** `Catches ⊥ (hnd_m H □)` holds iff `m = 0`
  (`Definitions.lean:400-406`). The machine would let a handler named `0` catch a cancel. `[handle]`'s
  premise `hn0 : n ≠ 0` (`Core/Fundamental.lean:370`) is what makes cancel uninterceptable
  (L-SIGNAL).

### K-CANCEL: cancellation
- Form. The reserved name `⊥ = 0`; the cancel state `s = (N, err)` carried as `⊥(N, err)` (§1);
  the delimiter `ccatch □`; the frame `cfin s □` under which a finaliser runs during a cancel; the
  steps `[finalise-cancel]`, `[cfin-ret]`, `[cfin-raise]`, `[cancel]`, `[cancel-raise]` of K-STEP;
  the cancel entry of `κ`:

  ```
  cancel κ  →³  ccatch (hnd_n H K[⊥(N(n,K), none)])
  ```

  and the error policy `errNext` (§1; OQ-21's option (a)). A cancel runs exactly the destructor
  `D_K` of the captured context and answers `()` or re-raises the kept error (P-CANCEL, §7.1). It
  is uninterceptable by typing: a handler frame catches `⊥` only if its name is `0`, which
  `[handle]`'s premise `n ≠ ⊥` excludes (§3, *Notes on the steps*).
- Uses: K-CTX, K-STEP, K-KONT, O-FIN, O-NAME.
- Today: `ccatchE`, `cfinE` (`Paper/S3_Dynamics/Definitions.lean:337, 340`); `cancelVal`,
  `namesVal` (`:362-375`); `errNext` (`:378-382`); the steps `ufinC`, `cfret`, `cferr`, `cancel`,
  `creraise` (`:523, 528, 532, 538, 542`); the closed runs `prog_run`, `prog₃_run`
  (`Core/EffCancel.lean:103, 113`). Status: as built.
- Slices: D-CANCELTAB, D-OWED 05; L-W, L-SIGNAL 06; T-FIN 07; the lowering's cancel arm 08.
- Depends on: K-CTX, K-STEP.
- Open: OQ-21 (what a finaliser may perform; the error policy), OQ-41 (a continuation captured
  inside a cancel run), OQ-9 (frames handed to a continuation that is then cancelled), OQ-18
  (uninterceptable cancel under threads).
- Obligation: P-CANCEL as a general run lemma: **mechanical** given OQ-41's default (§7.1).

---

## 4. The operational reading of every construct of 03

Each construct of 03 runs by the steps below. Nothing in the machine recognises a construct by
name.

| construct | runs by | notes |
|---|---|---|
| K-OP `perform_{n,i} v` | none on its own: `K[perform_{n,i} v]`, `¬HasHnd n K`, is final (§5) until `[op]` at the nearest `hnd_n` | `perform` is `Prim.Inert` (`Core/Steps.lean:169-170`) |
| K-RAISE `raise_{n,i} v` | `[finalise]` at each `ubind` passed, then `[unwind]` | errors are this (#168) |
| K-LET `M to x. N` | `beta` on `(λx.N) M` after `M` reaches a value | `effLet` (`Core/Fundamental.lean:353`); its graded side condition (K-GRADE) has no run-time content |
| K-THEN | `[then]` on a value; `[finalise]` / `[finalise-cancel]` on an unwind | |
| K-HND | `[ret]`, `[op]`, `[unwind]`; deep: `κ` reinstalls `hnd_n H` | forwarding is the absence of a step at `hnd_n` for a name `m ≠ n` (§5, L-HFWD) |
| K-KONT `κ` | `resume κ` (4 steps), `cancel κ` (3 steps, then K-CANCEL) | an `unr` `κ` is a `!` value: `copy` duplicates the term, `forget` discards it |
| K-CAP a capability call | pure steps: `withswap ℓ (λs. g (s, v))` | `op_tail` (`Core/Handlers.lean:76`): the call reduces to the clause run with no change to memory, in any `K` |
| K-SWAP `withswap` | `beta`, `load`, `letpair`, `store` | `Definitions.lean:587-590`; the cell is restored only on return (§7.4) |
| K-BOR pure form | `beta` and the constant's body | lends are ghost: no step begins or ends one |
| K-BOR unwinding form | `ubind (λb.(r,b), λ_. d r) (f [] r)` | `withborUE` (`Core/EffBorrow.lean:186-188`); `d` is the source's destructor: `forget` for a `Mut`/`Imm` source, `free` plus the content's destructor for an owned `Ref A` (`:13-14`) |
| K-FIX | `[boundedFix]` | recursive groups as fixed points of generators run as `bounded_fix` of the generator (SPEC §21) |
| K-NU, effectful observations | `unfold` is a closed λ-term; each observation is an ordinary run that stops or returns | `Backend/README.md`: `nu_in`/`nu_out` erase |
| K-DIV | as K-NU: `Loop_Σ A B = νX. F_Σ(A ⊕ U X) & F_Σ B`, one observation at a time | OQ-15 |
| K-HOST | `host`: `ℍ.call op v = some r` | externs are outside the proofs |
| K-GRADE | none | the qualifier decides which entry of `κ` exists, not a step |

**Effects inside closures, generators and recursion.** A `perform` inside a λ body is resolved
when the body runs, against the context of the call. A stored closure that performs `n` therefore
reaches the nearest `hnd_n` around its *call site*. A generator's `yield` handled by a `for` is
`[op]` at the `for`'s handler with `κ` the rest of the generator. `take(k)` is `cancel κ` after `k`
resumes. A recursion that performs runs `[boundedFix]` unfoldings with `perform` in each body; the
captured `K` holds the pending unfoldings' frames.

---

## 5. Final configurations, the stop, and the reduction halves of the laws

### 5.1 Final, stuck, and the stop condition

```
Final(e) ⟺  e = v
          ∨ e = K[perform_{n,i} v]  with ¬HasHnd n K               (a control stop)
          ∨ e = K[raise_{n,i} v]    with ¬Catches n K, n ≠ ⊥        (an abortive stop)
          ∨ e = K[⊥(N, err)]      with ¬Catches ⊥ K               (the stop of a cancel run)

Stuck(μ, e) ⟺ ¬Final(e) ∧ ¬∃ μ' e'. ⟨μ, e⟩ → ⟨μ', e'⟩
```

The fourth form is the only stop `cancelTab` admits (`Core/EffDefs.lean:131-134`).

**The current stop condition.** `wpG ls e Q` (`Core/EffDefs.lean:27-40`) asks, at every allocator
`A`, for a run `∃ k', ARun A k μ e k' μ' v` (`:36`) to a term `v` that `Q` accepts. `wpG` itself
does not require `v` to be `Final`; the post-condition does. `ewpStep` accepts a value or a stop the
table allows (`:68-70`), and `opTable`'s two disjuncts are exactly the control and the abortive
stops (`:157-167`). At every such final term, `wpG` also asks `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x,
x ∈ ls' ↔ x ∈ ls)` (`:40`): every 6.64 frame and record opened during the run is closed again
by the time the run reaches the term. At a value this is the printed `wp`. At a stop it is the
**lexical** stop condition: no lend opened in this run is still open across the suspension. This
is the single source of T1 (00 D-STOP; audit C1).

**The relativised stop** is D-STOP (05). From the machine's side:

- the set `Final` is unchanged;
- the run that reaches the stop is unchanged;
- only the post-condition at a control stop changes: frames still open (`ps ⊊ ps'`) are handed to
  the table (OQ-10).

What the dynamics owes D-STOP is §7: which code of the captured `K` runs on each path the
continuation takes. Those paths are where handed-on frames must close (OQ-9).

### 5.2 The reduction halves of the laws

Each law of 06 that has a reduction shape has a half that is a statement about `→`, with no
relation. These are owned here as facts of K-RUN; the laws are owned by 06.

1. **L-HRET.** `⟨μ, hnd_n H w⟩ → ⟨μ, h_ret w⟩`. One step. **As built** (`hret`).
2. **L-HOP.** For `¬HasHnd n K`:
   `⟨μ, hnd_n H K[perform_{n,i} v]⟩ → ⟨μ, c_i (v, κ)⟩`, and for every `w`,
   `⟨μ', K'[resume κ w]⟩ →⁴ ⟨μ', K'[hnd_n H K[w]]⟩` at every context `K'` and memory `μ'`.
   **As built** (`hop`; the four steps as in `ewp_kappa_resume`). The `→⁴` statement at an
   arbitrary `K'` is not stated as a `Steps` lemma: **mechanical**.
3. **L-HFWD.** For `m ≠ n`, `hnd_n H K₂[perform_{m,j} v]` with `¬HasHnd m K₂` has no head step at
   `hnd_n`. Under an enclosing `hnd_m H'` with `¬HasHnd m K₁`:
   ```
   ⟨μ, hnd_m H' K₁[hnd_n H K₂[perform_{m,j} v]]⟩ → ⟨μ, c'_j (v, κ_m(H', K₁ ∘ hnd_n H □ ∘ K₂))⟩
   ```
   and resuming reinstalls `hnd_n H` in place. The same holds at every arity. At an abortive
   `raise_m`, `hnd_n H` is not a catcher of `m` and is discarded. **As built**, by
   `hasHnd_comp`. Not stated as a lemma: **mechanical**.
4. **L-ALG0, destructor form.** For `¬HasHnd n K`, `n ≠ ⊥`, `K` with no `ccatch`/`cfin` frame,
   and `D_K = [D₁, …, D_k]`, every run of `hnd_n H K[raise_{n,i} v]` takes exactly the path below.
   `Kᵢ` is the part of `K` outside the `i`-th ubind frame.
   ```
   hnd_n H K[raise_{n,i} v]
     → hnd_n H K₁[D₁ (); raise_{n,i} v]        [finalise] at frame 1
     →* …                                     if D₁ () returns, raise_{n,i} v continues from frame 1
     →* hnd_n H K_k[D_k (); raise_{n,i} v]
     →* hnd_n H K_k'[raise_{n,i} v]  → c_i v    [unwind]
   ```
   If some `Dⱼ ()` raises `q`, `q` supersedes from frame `j` (§3). This is P-ABORT (§7.2). **Not
   built** as a lemma: **mechanical**, by induction on the number of ubind frames.
5. **L-W.** `cancel κ` runs `D_K` and answers `()` or `raise E`. This is P-CANCEL (§7.1).
6. **L-TAIL.** The reduction half of the tail-resumptive law is §6.2's (T-LOWER.tail).

---

## 6. The erasure obligations

The user's position: effect handling is erased at run time. A resume-once clause in tail
position is a call, an abort is a branch, a later resume is a state machine, and the compiler is
never stale. The backend realises this in `Backend/Clos/Capture.lean` and
`Backend/Clos/Unwind.lean` (SPEC §19 *Lowering*). This section states each class as a theorem
relating this machine to that lowering. T-LOWER (08) owns the results. Whether they are proved
theorems or per-class laws plus counts is OQ-23. The statements are fixed here either way.

### 6.0 The two sides of every erasure statement

- **Source side.** `→` of K-STEP under an allocator (K-RUN). The backend compares every stage
  with `runSource` (`Backend/Source.lean:28-37`), which runs `BoCa.step`
  (`Support/Dynamics/Interpreter.lean:239`), an executable interpreter marked `[about ours]`
  (`:9-11`). No Lean statement relates `step` to `Head`: the interpreter's header says nothing in
  the `wp` development depends on it (`:66`).
- **Target side.** The closure IR and its interpreter, `Backend/Clos/Interp.lean`, which checks
  the ownership discipline as it runs: a used variable is consumed, and every call must end with
  its frame consumed (`:9-15`). The flat IR and Wasm follow.
- **Obligation E0 (first).** `step` implements `AStep1` at the allocator that picks `Mem`'s next
  location:
  `step ℍ μ e = .next μ' e' → AStep1 A_next k ⌊μ⌋ e k' ⌊μ'⌋ e'`; `step ℍ μ e = .value v → e = v`;
  and `step ℍ μ e = .op r K p → Final(K[op_r p])`. Without E0 every erasure theorem below is about
  the interpreter, not the calculus. **Mechanical**: case analysis over `step` against `Head`.
  The non-mechanical step: `Mem.alloc`'s choice against `Alloc.fresh` (`Core/Alloc.lean:36-38`)
  needs `Mem`'s domain to be finite and its `next` above it.

**Observation.** For a closed program `e : F 1` (or a host program, OQ-30), `Obs(e)` is the final
value's observable form (`pvOfExpr`, `Backend/Source.lean:16-25`), the number of cells left, and
the I/O trace. Each erasure theorem says the stage's `Obs` equals the source's.

### 6.1 Abort = branch (T-LOWER.branch)

**Statement.** Let `e` be closed and typed, and let `Unwind` assign each code its raise set. For
every allocator run of `e` to a value or to an abortive stop, the closure IR's run of
`Unwind(e)` reaches the corresponding outcome:

- a value `v` maps to `inl v` at a raising code and to `v` at a non-raising code;
- a stop `K[raise_{n,i} v]` maps to `inr (n, i, v)` at every frame between, each discarding its live
  variables;
- a `ubind` frame on the path runs its finaliser and raises again (§5.2 item 4).

Raise sets are sound: if a run of a code's body reaches `K[raise_{n,i} v]` uncaught in the code,
then `(n, i)` is in the code's set.

- **Law that justifies it:** L-ALG0 in its destructor form. **Source half:** §5.2 item 4.
- **Lowering:** `Backend/Clos/Unwind.lean:5-33` (the convention and the rewrite).
- **Obligation:** **unknown** at one step only: the soundness of the raise sets, which rests on
  the 0-CFA (`Backend/Clos/Flow.lean`) over-approximating the codes a call reaches. The
  simulation itself is **mechanical**.

### 6.2 Resume once in tail position = a direct call (T-LOWER.tail)

**Statement (source half, the reduction half of L-TAIL).** Let the clause be
`c = λp. let (w, k) = p in B`, where `B` uses `k` once, as `(k (inj₁ ())) r` in tail position, and
`r` is computed from `w` without `k`. This is the shape `tailClause?` accepts
(`Backend/Clos/Capture.lean:542-551`). Let `c° = λw. B°`, where `B°` is `B` with the resume removed:
it ends by answering `r`. Then for every `μ`, `K₀` and `¬HasHnd n K`:

```
⟨μ, K₀[hnd_n H K[perform_{n,i} v]]⟩ →*ₐ ⟨μ', V⟩   ⟺   ⟨μ, K₀[hnd_n H K[c° v]]⟩ →*ₐ ⟨μ', V⟩
```

at every allocator `A`, with the same allocation counts, for every value `V`. The left run is the
right run with one `[op]` step and the four steps of `resume κ` inserted. This is a
↦*-joinability statement, not an equation over a relation.

**Statement (lowering half).** `tailResumptive` (`Backend/Clos/Capture.lean:631-648`) selects an
operation when, at every handler site whose body may perform it, the clause is one closed code that
passes `tailClause?`, does not suspend, and does not raise. `directCalls` (`:611`) then replaces
`perform` by a call of `c°`. The theorem: on such a program, the closure IR's run of the rewritten
program has the source's `Obs`.

- **Law:** L-TAIL (06), whose kernel run fact today is `op_tail`/`op_answer` for the answering
  class (`Core/Handlers.lean:76, 133`). For a `[handle]` clause, the source half above is not built.
- **Literature.** Xie, Brachthäuser, Hillerström, Schuster and Leijen, *Effect Handlers,
  Evidently*, ICFP 2020: "we can execute tail-resumptive operations *in place* (without needing
  to capture the evaluation context)" (abstract, read from the Microsoft Research publication
  page for this section).
- **Obligation.** The source half: **mechanical** (one `[op]`, then `ewp_kappa_resume`'s steps
  as a run). The lowering half: **unknown** at one step: the specialisation premise. The machine
  resolves `perform_n` to the *dynamically* nearest `hnd_n` (§2). The lowering's premise is that
  every site that may be nearest has the same clause. That is a fact about the 0-CFA's sites for
  `n`, and it must cover re-entry of a site (OQ-14).

### 6.3 Resume later = a state machine (T-LOWER.machine)

**Simulation relation.** A closure-IR outcome `inr (p, k)` of a code relates to the source
configuration stopped at `K[perform_{n,i} v]` when:

- `p` is `(n, i, v)`'s variant;
- `k` is a closure of the code's resume code over a state whose variant is the resumption point of
  this `perform`;
- the state holds the variables live in `K`'s frames that lie inside the code, the finalisers of
  its `ubind` frames among them, and, at a call point, the callee's `k`, related to the inner part
  of `K` by the same relation (nesting).

**Statement.** If `k ~ K`, then:

1. **Resume.** Running `k (inl y)` relates to `K[y]` at every `y`: both run to related outcomes.
   This is the lowering's `resumeArm` (`Capture.lean:861`) against `resume κ`.
2. **Cancel.** Running `k (inr mask)`, with `mask ⊇ N(n, K)`'s names, relates to the cancel run
   of `K` (P-CANCEL, §7.1). It runs the callee's `k`'s cancel first, then the finalisers of the
   point's `fin` frames innermost first, drops every other variable, and answers `inl ()` or
   `inr E` with `E` given by `errNext` at `N`. This is `cancelArm` (`Capture.lean:893`) and
   `errNext` (`:875`) against `[finalise-cancel]`, `[cfin-raise]`, `[cancel]` and
   `[cancel-raise]`.
3. **Drive.** `drive` (`drvBody`, `Capture.lean:207`) relates to `hnd_n H`:
   - `inl v` relates to `[ret]`;
   - `inr` of an operation of `n` relates to `[op]`, with `κ` (`kapBody`, `:233`) related to
     `κ_n(H, K)`;
   - `inr` of another name relates to L-HFWD (§5.2 item 3).

- **The cancel mask against the machine's region.** The machine's `N(n, K)` is computed from
  the captured `K` at run time (`kappa`, `Definitions.lean:438-443`). The lowering's mask is
  static: the names of the handler sites reachable from the handler's body. It equals the
  region's names exactly when no site is reached again from its own body, and the lowering
  checks this only when a finaliser may raise (`masks`, `Capture.lean:984-996`; SPEC §19
  *Lowering*). Item 2 therefore holds with `mask = N(n, K)` up to that check. The rejected cases
  are OQ-42.
- **Obligation.** **Unknown**: this is the largest of the erasure statements, a forward
  simulation of the capture steps by `Capture`'s machines with nesting through calls. The step
  most likely to be non-mechanical is the nesting clause at a call point, `k_caller ~ K_outer`
  holding `k_callee ~ K_inner`, against `K = K_outer ∘ K_inner`, together with the tail-call
  convention that passes a callee's outcome on (`SFacts.passes`, `Capture.lean:705`).

### 6.4 Multi-shot = copy (T-LOWER.copy)

**Statement.** At an `unr` operation `κ` is `!`. `copy κ` gives two equal terms, and each resume
runs from `hnd_n H K[w]` independently. In the closure IR the copy duplicates the state (SPEC §19
*Lowering*, "multi-shot"). The machine half: for every `w₁, w₂`, the runs of
`K'[(resume κ w₁, resume κ w₂)]` and of `K'[(hnd_n H K[w₁], hnd_n H K[w₂])]` are joinable.
**Mechanical.** That the copy duplicates no resource is L-P (the captures are persistent,
`lam_bang_persistent`), a typed fact, not a machine fact. Whether `unr` is kept is OQ-16.

### 6.5 Cost parity

Cost parity with the hand-written program is a criterion on counts (`corpus/kernel-counts.expected`
against `corpus/capture-*-hand.bc`, SPEC §19 *Lowering*), not a theorem of the semantics. It is
recorded in 08 with T-LOWER.

---

## 7. Paths of a captured continuation (the machine half of OQ-9)

OQ-9 asks whether 6.64 frames (and, under OQ-44, 6.65 lends) handed to a continuation still close on every path the
continuation takes. The lends are ghost, so the machine cannot close a frame. What it can do is
run code. This section states exactly which code of a captured `K` runs on each path. These are
the run facts D-STOP, D-OWED and D-DTOR (05) and T-LEAK and T-FIN (07) consume.

Throughout, `K` is a captured context: `[op]` fired at `hnd_n H` with `¬HasHnd n K`.

### 7.1 P-CANCEL: the cancel run runs exactly `D_K`

**Statement.** Let `K` contain no `ccatch` frame, no `cfin` frame and no handler frame named `⊥`.
Let `D_K = [D₁, …, D_k]`, innermost first, and `N = N(n, K)`. Write `K = K'_k ∘ … ∘ K'_1 ∘ K'_0`,
where the `j`-th ubind frame sits between `K'_j` and `K'_{j-1}`, and `K'_j` is the context *outside*
it. Then every maximal run from `⟨μ, K₀[ccatch (hnd_n H K[⊥(N, none)])]⟩` either diverges or gets
stuck inside some `Dⱼ ()`, or passes exactly through

```
K₀[ccatch (hnd_n H K'_k⋯K'_1[cfin (N, err₀) (D₁ ())])]            err₀ = none
  →* … K'_k⋯K'_2[cfin (N, err₁) (D₂ ())] …                          err₁ = err₀ if D₁ () returned,
                                                                       errNext N err₀ m j w if it raised (m,j,w)
  →* K₀[ccatch (hnd_n H K'_k[⊥(N, err_k)])]
  →  K₀[()]                    if err_k = none                       [cancel]
  →  K₀[raise E]               if err_k = some E                     [cancel-raise]
```

No step is taken in any frame of `K` other than these finalisers. `K`'s plain frames and handler
frames, and `hnd_n H` itself, are discarded with no step. Every handler frame of `K` is passed
because its name is in `N` and is not `⊥`.

- Today: two closed instances, `prog_run` and `prog₃_run` (`Core/EffCancel.lean:103, 113`). The
  model-level counterparts are `cancel_frame` (`Core/EffRules.lean:168`) and `ewp_ccatch`
  (`:580`). The general run statement is **not built**.
- Obligation: **mechanical**, by induction on `k`, using `catches_comp` and the steps
  `[finalise-cancel]`, `[cfin-ret]`, `[cfin-raise]`. The non-mechanical step is excluding `ccatch`
  and `cfin` frames from `K`: that is OQ-41.

### 7.2 P-ABORT: an abortive operation runs exactly `D_K`

**Statement.** As §5.2 item 4. The pending `raise` passes each ubind frame of `K` after that frame's
finaliser returns. If a finaliser raises, the new raise supersedes from that frame. Under `n ≠ ⊥`
and with `K` free of `ccatch`/`cfin`, no code of `K` other than `D_K` runs, and the clause receives
only the argument. `κ` is never built. **Mechanical.**

### 7.3 P-DROP: a dropped `unr` continuation runs nothing

An `unr` `κ` is a `!` value. `forget κ` and discarding it in a `[let]` frame take no step inside
`K`. The frames of `K` are never run: not `D_K`, not anything else. An affine or linear `κ` cannot
be dropped this way. It is a `U` of `(B ⊸ F_Σ R) & F_Σ 1` or `& ⊤` (`kTy`,
`Core/EffRules.lean:976-981`), consumed by forcing one entry. "A continuation cannot be dropped"
is answered by `cancel` (SPEC §19 *Kinds of operation*).

**Consequence.** On P-DROP the machine closes nothing, so an `unr` capture must own nothing that
needs a step to release. L-P's persistence condition is exactly what the dynamics needs here.

### 7.4 What these paths imply for frames handed to a continuation

These are machine facts that follow from §7.1 to §7.3. They are stated so that OQ-9's probe can be
built against them. They are not claims that any option of OQ-9 fails.

1. **On cancel and on abort, the only code of `K` that runs is `D_K`.** So if a lend is open in
   `K` at the stop and its release needs a step, that step can only be a finaliser in `K`.
2. **Unwinding form.** A borrow in K-BOR's unwinding form is `ubind (λb.(r,b), λ_. d r) (f [] r)`
   (`Core/EffBorrow.lean:186-188`). On cancel or abort, its frame contributes `d r` to `D_K`. That
   is `forget` at a `Mut`/`Imm` source and `free` plus the content's destructor at an owned
   `Ref A` source (`:13-14`). `withloadU` has no finaliser: the load consumed the source
   (`Core/Fundamental.lean:276-278`).
3. **Pure form.** A borrow in pure form leaves no catcher frame in `K`. A cancel through it takes
   no step at it. For a `Mut`/`Imm` source, whose destructor is `forget`, nothing at run time is
   lost. For an owned `Ref A` source, the `free` that its unwinding form would run is not run on
   this path.
4. **`withswap`.** Its frame `let (y, z) = □ in store x y; (x, z)` (`Definitions.lean:587-590`)
   stores the new contents back only when the callback returns. A cancel or abort through it runs
   no `store`, and the cell keeps the contents that were moved out to the callback. This is the
   run-time reason a co-operation's callee is pure today (R-PURESWAP) and why OQ-20's option (b)
   puts a placeholder in the cell while the payload is out.
5. **The first probe of OQ-9, from this side.** The probe is `[handle]` + cancel over a body that
   opens a 6.64 frame (`withbor1U`) and performs an affine operation under it (05 §12.1); OQ-44's
   probe is the same at a 6.65 frame (`withbor2U`, 05 §12.2). In the machine, the cancel run is
   P-CANCEL with `D_K` holding exactly the unwinding form's `d r` when the borrow is in unwinding
   form, and nothing when it is in pure form. Each probe's model statement (05) must close its
   frame on one of these two runs. The pure-form run takes no step at the frame.

### 7.5 P-RESUME and P-ESCAPE: where the captured frames run again

**P-RESUME.** `K'[resume κ w] →⁴ K'[hnd_n H K[w]]` at every `K'` (§5.2 item 2). The captured
frames run again inside whatever context `K'` the resume is called from.

**P-ESCAPE.** The frames *outside* `hnd_n H` at capture time are not in `κ`. Suppose a clause
returns or stores `κ` past an enclosing frame `F`, for instance a lender outside `hnd_n`, and `κ` is
resumed after `F` has returned. Then the frames of `K` run outside `F`, although they were inside
`F` when captured. The machine preserves the nesting of `K`'s frames relative to `hnd_n H` and to
each other. It does not preserve their nesting relative to frames outside `hnd_n H`.

- **A handler between two lenders.** Take `ubind₁ □` (outer lender) `∘ hnd_m H □ ∘ ubind₂ □`
  (inner lender) `∘ K_in`, and `perform_m` in `K_in`. `[op]` captures `ubind₂ ∘ K_in`, not `ubind₁`.
  The clause runs inside `ubind₁`.
  - Cancelling the captured `κ` runs `ubind₂`'s finaliser only (P-CANCEL), and `ubind₁` stays open.
  - Resuming reinstalls `ubind₂` inside the clause's context.
  - If the clause lets `κ` escape `ubind₁`, a later resume runs `ubind₂`'s frame outside
    `ubind₁`: the inner lend outlives the outer one in the run.

  The machine permits this run. Excluding it is a typing or model matter: OQ-3 (does a handler
  site open a lifetime), OQ-28 (how a stored continuation is bounded), and R-MID by default. The
  run is the configuration OQ-3's "What settles it" asks for, on the dynamics side.

### 7.6 Forwarding a cancel (the machine half of OQ-27)

Suppose a forwarding clause holds an inner continuation `k` across an outer operation, as in
`let r = op x in resume k r`, and the outer continuation is cancelled. Then `k` sits in a plain
`let` frame of the outer `K`, and P-CANCEL discards it with no step: `k`'s own `D_k` never runs.
For a cancel to forward, `k` must be in a ubind frame whose finaliser is `cancel k`:

```
(op x) then r. resume k r unwind cancel k
```

`cancel k` is a computation at `F_Σ 1`, `Σ` the inner handler's outer row (`kTy` at `aff`,
`Core/EffRules.lean:979`). A `[then]` finaliser is typed at `S.abortOnly`
(`Core/Fundamental.lean:364`). So this term is typed exactly when `Σ` has only abortive
operations, or under OQ-7's option (a). This locates OQ-27 in the machine: the forwarding term
exists. Its typing is OQ-7's question.

---

## 8. Runs, determinism, and determinism up to renaming

### K-RUN: allocator runs, unique decomposition, determinism
- Form.
  **Allocators and runs.** An allocator `A = (pick, fresh)`: at the `k`-th allocation from `μ`, a
  block of `n` cells at `pick k μ n`, free whenever `μ` has finite domain. `→ₐ` is `[ctx]` over
  `AHead`: a head step that does not allocate, or `alloc`/`tab` at `A`'s location. `→*ₐ` is its
  reflexive-transitive closure, counting allocations. `wpG` quantifies over every `A` and every
  start count (`Core/EffDefs.lean:29`). That covers every run of the machine (`Core/Demonic.lean`
  header).

  **Unique decomposition.**
  ```
  ∀ K K' a e μ μ' μ₂ μ₂' a' e'.  ⟨μ, a⟩ ↦ ⟨μ', a'⟩ → ⟨μ₂, e⟩ ↦ ⟨μ₂', e'⟩ → K[e] = K'[a]  →  e = a ∧ K' = K
  ```
  No redex holds another at an evaluation position. A redex that holds a non-value holds it at a
  catcher position. The `[op]` redex holds `perform`, which is inert, under frames free of `n`.

  **Determinism.**
  ```
  ∀ A k μ e. ⟨μ, e⟩ →ₐ^{k→k₁} ⟨μ₁, e₁⟩ → ⟨μ, e⟩ →ₐ^{k→k₂} ⟨μ₂, e₂⟩ → k₁ = k₂ ∧ μ₁ = μ₂ ∧ e₁ = e₂
  ```
  including the capture steps. Every step but `alloc`/`tab` is a function of the memory and the
  redex (the host is a function), and those two take `A`'s location.

  **Prefix.** A run under `A` is continued, under `A`, by every run under `A` that reaches a
  value. **Replay.** Every `Steps` run is an `ARun` under the allocator that replays its choices.

  **Determinism up to renaming of locations** (T-2RUN's machine half, owned by 07). A run is
  *fresh* when it takes no array step and allocates only locations its configuration does not
  name. Then:
  ```
  freshRun_det :  FreshRun μ e μ₁ v₁ → FreshRun μ e μ₂ v₂ → ∃ π : Perm Loc. μ₂ = π·μ₁ ∧ v₂ = π·v₁
  run_sim      :  FreshRun μB eB μB' vB → HeapRel g μB μA → Steps μA (g·eB) μA' vA →
                    ∃ g'. vA = g'·vB ∧ HeapRel g' μB' μA'
  ```
  **Renaming of handler names** (K-REN's machine half). For a bijection `π` of `Nm ⊎ {⊥}` with
  `π ⊥ = ⊥` (02 K-REN), extended to terms, contexts and payloads, every head step renames to a head step:
  `⟨μ, a⟩ ↦ ⟨μ', a'⟩ → ⟨μ, π·a⟩ ↦ ⟨μ', π·a'⟩`. The side conditions compare names only for equality
  (`HasHnd`, `Catches`) and membership (`errNext`'s `m ∈ N`), and `N(π n, π·K) = π·N(n, K)` by
  `hndNames`.
- Uses: K-STEP, K-CTX.
- Today: `Alloc` (`Core/Alloc.lean:36-38`), `AHead` (`:70-80`), `AStep1` (`:83-85`), `ARun`
  (`:88-92`), `Step1N` (`:96-98`); `plug_cmp` (`Core/Steps.lean:33`), `head_nested` (`:517`),
  `head_plug` (`:312`), `plug_decomp` (`:579`), `head_det_eff` (`:596`); `head_det`
  (`Core/Demonic.lean:46`), `AHead.deterministic` (`:111`), `AStep1.deterministic` (`:117`),
  `ARun.rest` (`:132`), `steps_replay` (`:164`), `Alloc.replay` (`:205`). Up to renaming:
  `head_rename` (`experiments/TwoRun/TwoRun/Rename.lean:359`), `steps_rename` (`:419`),
  `freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`), `run_sim`
  (`experiments/TwoRun/TwoRun/Sim.lean:253`), `fresh_run_image` (`:274`). Name renaming: not built.
  Status: as built (Core); experiment (TwoRun); new (name renaming).
- Slices: T-DET, T-2RUN, T-REN 07; L-REN 06; D-BIN and OQ-4's option (b) 05/06.
- Depends on: K-STEP, K-CTX.
- Open: OQ-43 (renaming at the effect and array steps); OQ-4 (whether laws go through TwoRun's
  route); OQ-14 (generative names would make name renaming a run-time permutation, as locations
  are).
- Obligation:
  - Determinism with capture: as built.
  - Name renaming: **mechanical**, one case per `Head` constructor. The non-mechanical step is
    `π ⊥ = ⊥` together with injectivity at `errNext`.
  - Location renaming at the effect steps: see OQ-43.

**TwoRun and the machine.** `head_rename` does case analysis over the pure, memory, host and
array steps of `Head` (`Rename.lean:359-394`). The capture steps, `count`, `countTry` and
`boundedFix` have no case in it. TwoRun is not a default build target (`lakefile.toml:2`), so
whether it elaborates against today's `Head` is not verified here. The
missing cases are expected to be mechanical: renaming commutes with `shift`, `subst` and `plug`
(`Rename.lean:156, 177, 281`), which is what `kappa` needs, and the capture steps compare only
names and literals. This is OQ-43's first half.

**Threads (OQ-18).** The machine is sequential: one term, one memory, `→` a function under an
allocator. Nothing in K-STEP depends on there being a single thread except determinism itself.
`N(n, K)` and the cancel state are local to one captured context, and handler resolution is by
the context of the running term. A threaded machine would add a scheduler over several
configurations sharing `μ`. Determinism would then hold up to schedule and renaming. Uninterceptable
cancel (L-SIGNAL), which runs the task's destructor, is what a scheduler cancelling a parked task
would use. No construct here
assumes otherwise.

**Totality and divergence.** `wpG`, and hence `ewp`, is total correctness: it exhibits a
terminating run at every allocator (`Core/EffDefs.lean:36`). The machine has no fuel. Divergence
is read through codata (K-NU, K-DIV). `wpTSD` gives the demonic reading: every run is safe, and a
run that reaches a value lands in the post-condition (`Core/Demonic.lean:223`). Div as a row with
a partial-correctness `ewp` (OQ-15 (b)) changes predicates over runs and adds one step, the
unbounded unfolding of `fix` (03 §9.2).

---

## 9. Open questions raised here

Boxed in [99](99-open-questions.md):

- **OQ-41**, a continuation captured inside a cancel run: P-CANCEL and P-ABORT (§7.1, §7.2)
  assume the captured `K` holds no `ccatch` or `cfin` frame, which holds under R-FINAB and is
  open under OQ-7 (a).
- **OQ-42**, the constructs the lowering rejects (a name with both control and abortive
  operations; a cancel whose finalisers may raise under a re-entered site; a handler name `≥ 64`).
  The calculus keeps each; T-LOWER.machine (§6.3) holds up to them.
- **OQ-43**, determinism up to renaming at every step of `Head` and at array steps.

**Carried from the register** and cited above: OQ-21 (the error policy `errNext`, §1, §7.1),
OQ-24 (the abortive payload at `[finalise]`, §0), OQ-27 (§7.6). Also cited: OQ-3, OQ-4, OQ-7,
OQ-9, OQ-10, OQ-12, OQ-14, OQ-15, OQ-16, OQ-18, OQ-20, OQ-23, OQ-26, OQ-28, OQ-30.

---

## 10. Run-up audit (00 §8)

**Printed lemmas in the run-up not transcribed.** This section rests on [TR] p. 4's `↦` box and
context rule, transcribed as `Head`'s first nine constructors (`Head.toWp`,
`Support/Dynamics/Machine.lean:207-217`). No printed lemma of [TR] concerns the effect steps:
they are ours (SPEC §19). None of the printed dynamics is untranscribed.

**Printed hypotheses not spent.** None: the section states no printed lemma.

**Uniqueness and functionality results not used.** `plug_decomp`, `head_det_eff`,
`AStep1.deterministic` and `ARun.rest` are used (K-RUN, §6.0). Not used: `Heap.rename_one` and
the `Equiv.Perm` group laws of TwoRun beyond `freshRun_det`; `Kont.Plain`'s inversion lemmas
(`step1_plug_inv`, `Core/Steps.lean:697`), which P-CANCEL's proof will need for runs inside
`D_j ()` under the plain part of `K`.

**Obligations, unknown first.**

| obligation | mark | where |
|---|---|---|
| T-LOWER.machine: forward simulation of the capture steps by `Capture`'s machines | unknown | §6.3 |
| OQ-41: captured contexts free of `ccatch`/`cfin` (or a machine change) | unknown | §9 |
| T-LOWER.tail lowering half: the specialisation premise against dynamic resolution | unknown | §6.2 |
| T-LOWER.branch: soundness of raise sets over the 0-CFA | unknown | §6.1 |
| OQ-43: `head_rename` at every constructor; block renaming | unknown at (b) | §9 |
| E0: `step` implements `AStep1` | mechanical (step: `Mem` freshness) | §6.0 |
| P-CANCEL, P-ABORT as general run lemmas | mechanical (given OQ-41's default) | §7 |
| reduction halves of L-HOP, L-HFWD, L-ALG0, L-TAIL source half, multi-shot copy | mechanical | §5.2, §6 |
| `D_K` as a function, with its composition law | mechanical | K-CTX |
| name renaming of head steps | mechanical (step: `π ⊥ = ⊥` at `errNext`) | K-RUN |
| SPEC §19 `[unwind]` text aligned with `Catches` | mechanical | K-STEP |
