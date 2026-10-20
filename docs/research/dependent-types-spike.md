# Dependent types for the law system: lift, usability, and worth (spike #625, for #624)

Research note, 2026-10-20. It records no decision. Part of #625, which is the spike for #624
(laws in the syntax, demanded properties, and `law P given I` for unsafe code).

The user's point on #625: "The thing is lean is already dependently typed." So the first option
studied, and the one studied most deeply, keeps our language non-dependent and makes Lean the
dependent layer. Laws written in our syntax elaborate to Lean propositions about the checked core
term's semantics, and their proofs and `given` invariants are Lean. The type-system options come
after it and are measured against it.

## 0. The answer in brief

**The yes/no question of #625.** Is there a form of dependent, refinement or indexed typing that
expresses #624's laws and invariants, keeps the corpus working with no new annotations, and is
worth its cost?

- **For laws, yes, and it needs no type-system change.** Lean is the dependent layer. A law
  about a function `bcc` checks can be stated over `bcc`'s own erasure and proved for every
  argument today, with nothing added to `Core/`. `experiments/DepSpike` does this for `max`:
  commutativity, a bound, associativity with a unit (the monoid law #620's parallel reduce
  needs), and the partition law of `split`.
- **Full dependent types are out.** QTT, Idris 2 and BendTT fail the kill criterion: they need a
  new borrow calculus. Linear dependent type theories in their general form fail it too, because
  their type checking is undecidable or evaluates open terms. What survives from LNL_D is its
  decidable restriction, and that restriction is DML.
- **Three typing options survive.** They are DML-style sizes (#72), Flux-style refinements
  layered over `CDerives`, and verifier-style specs. They add something the Lean layer does not:
  facts that the checker carries through a program. A bound known at a loop reaches the index
  inside it, and a validated field reaches its use. None of them is needed for the law system
  itself.

| option | (a) big lift? | (b) harder to use or understand? | (c) worth it? | kill criterion |
|---|---|---|---|---|
| **A. Lean as the dependent layer** | **No.** No kernel change. Frontend: law syntax and a statement generator. A Lean library of run lemmas, data representations and tactics | **No.** No corpus change. Easy laws close by automation; hard laws need Lean, in a sidecar | **Yes** | passes |
| B. Full dependent types with quantities (QTT, Idris 2, BendTT) | **Very large.** A new kernel and a new relation, and no prior theory with borrows | **Yes** | No | **killed**: (i), and (iii) unless a step budget |
| C. Linear dependent type theory (LNL_D, Fu–Kishida–Selinger) | **Very large** as printed | **Yes** | No | **killed** as printed: (iii), and (i). Its decidable core is option E |
| D. Refinement types (Liquid Haskell, Flux) | **Medium to large.** A second judgment layered on `CDerives`, its soundness through `fundamentalC`, and a solver in the frontend | **Mildly**, and opt-in | **Probably**, for targets 3 and 7, after A | passes if unannotated types default to `true` |
| E. DML-style indexed types (#72) | **Medium.** A size sort in `Δ` beside lifetimes; the relation gets a size substitution | **Mildly** (const generics) | **Yes** for arrays and matrices (targets 3, 6) | passes |
| F. Verifier-style specs (Verus, Prusti, Creusot) | **Small to medium** on top of A: `requires`/`ensures` and loop invariants compiled to Lean goals | **Mildly**, opt-in, but loops need invariants | **Yes**, as A's in-source surface | passes |

## 1. What exists today

Option A is mostly assembled from these pieces. Each one was read for this note.

| piece | where | what it gives the law system |
|---|---|---|
| `bcc_program% "file"` | `Frontend/Check/CrossCheck.lean` | A source file's AST as a Lean term. The parser runs at elaboration time; that the embedded AST is the parser's output holds by construction, not by theorem |
| `defErasure p k`, `mainOf p` | same | The checker run on a `def` or on `main`: its erasure, an `Expr`. `decide +kernel` evaluates the checker in the kernel (`library_erasures`, `sumProgExact_main`) |
| `derives_of_mainOf`, `checkProgram_sound` | `CrossCheck.lean`, `Frontend/Check/Program.lean` | An accepted `main` has a `CDerives` derivation (with `pins = []`). `checked_sem` applies `fundamentalC` |
| `fundamentalC`, `adequacyC` | `Core/Fundamental.lean` | Every derivation is in the relation; a closed `F 1` program runs to `()` at the empty memory |
| `adequacyD`, `adequacyD_obs`, `leakFree_closed` | `Core/Demonic.lean`, `Core/EffPrograms.lean` | The same at every run and every allocator, and at persistent answers |
| `fundamentalC_pin (hPin : PinLaw)` | `Core/PinFundamental.lean` | **A `given` already in the kernel.** The FP holds under a named hypothesis, and `bcc check` prints `assurance: PinLaw (…)` (SPEC §29) |
| `externs_every_run (hγ : ExternsMeet Γ γ)` | `Core/Stdio.lean` | **A `given` at the program level.** Adequacy at every implementation of the externs that meets their contracts |
| `runM`, `runM_val` | `Core/Run.lean` | Kernel-evaluated runs: a closed program's run is proved by `rfl` and read as a run of the machine. `runM` takes no host step, so integer programs are outside it |
| `Core/EffTier1Programs.lean` | — | Facts about specific closed programs, each a derivation plus a `runM_val` run |
| `Optics/Runs.lean`, `Optics/Shape.lean` | `experiments/Optics` | **Laws over every argument, about runs.** `over_id`, `over_fuse`, and `iterMut_shape` by induction over a list in the heap (`ListAt μ v ns`). Built against `Core` before `Kont.Plain` existed; it no longer builds at `main` (`steps_plug_inv` now takes `K.Plain`) |
| `TwoRun` | `experiments/TwoRun` | Allocation is the machine's only nondeterminism, and fresh runs are deterministic up to a permutation of locations (`freshRun_det`). The read footprint for typed programs is stated, not derived |
| `EffModelRel` | `experiments/EffModelRel` | A binary relation and contextual equivalence for the effect model's calculus. Not for `Core`'s machine |
| #79 | issue | `unsafe` as rows of the axiom table, with the proof possibly a hypothesis. Revision 2 adds `trust e`: the obligation is `e` in the every-allocator relation at its expected type. The open "bridge" is RefinedRust-style: shape-typed code whose memory operations meet their preconditions is in the relation |
| #7's ladder, `bcc trusted` | `Frontend/Check/Externs.lean` (`Assurance`, `trustedReport`) | Seven assurance levels, from assumed to proved; `bcc trusted` lists the externs and their levels |
| `Host.Conforms` | `Support/Dynamics/Host.lean` | A host that is `wasmHost` on the integer operations. Every machine theorem holds at every host; a law about arithmetic is stated at every conforming host |

**Three facts about the existing pieces matter below.**

- The checker is certifying: it returns a typed term whose erasure has the derivation (SPEC §3).
  A law about "the function `bcc` checked" is therefore a law about one `Expr` that Lean can
  name.
- The relation is unary. `fundamentalC` gives safety and the borrow guarantees at every type, and
  `wpTS` takes any postcondition. No binary relation for Core's machine exists, so an equational
  law is stated about runs (`Steps`) or through a postcondition, not as contextual equivalence.
- Facts about specific programs so far are closed instances (`rfl` by `runM`). Laws over every
  argument exist only in `experiments/Optics`, which is now stale, and in the new
  `experiments/DepSpike`.

## 2. Option A: Lean as the dependent layer

### 2.1 The shape

```
fn max(a: i32, b: i32) -> i32 = if a < b { b } else { a }

law max_comm:  forall (a: i32, b: i32). max(a, b) == max(b, a)
law max_assoc: forall (a: i32, b: i32, c: i32). max(max(a, b), c) == max(a, max(b, c))
law max_unit:  forall (a: i32). max(i32_min, a) == a
```

The language stays non-dependent: `law` is a declaration the type checker ignores apart from
checking that its two sides are well typed at a type with an equality. `bcc` elaborates each side
to a checked core term, and the law becomes a Lean proposition about those terms' runs:

```lean
-- generated: what `law max_comm` states
theorem max_comm (hℍ : ℍ.Conforms) (a b : UInt32) {μ μ' : Heap} {w : Val} :
    Steps μ (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) μ' w.1 ↔
      Steps μ (.app maxV.1 (Val.pair (.i32 b) (.i32 a)).1) μ' w.1
-- generated: `maxV` is what the checker produced
theorem max_erasure : defErasure lawsProg 0 = some maxV.1 := by decide +kernel
```

Both are in `experiments/DepSpike/DepSpike/Laws.lean` with proofs. The first is the law. The
second ties the law's subject to the checker's output, by kernel evaluation of the checker, as
`CrossCheck.lean` does for §13.1. Lean is the dependent type theory: a proposition about an
`Expr` is a type that depends on a term of our language.

### 2.2 The experiment: what was proved, and what it took

**Yes/no question.** Can a law about a function, as `bcc` checks it, be stated as a Lean
proposition about Core's machine and proved for every argument, with no new machinery in
`Core/`? **Yes**, at least for straight-line code at persistent types, at every conforming host.

`experiments/DepSpike` (`lake build DepSpike`; 420 lines; no `sorry` or axiom; `#print axioms`
of every result within `[propext, Classical.choice, Quot.sound]`):

| result | statement | lines | how |
|---|---|---|---|
| `max_erasure` | the checker accepts `max : !(i32 * i32 => i32)` from `laws.bc` and erases it to `maxV` | 2 | `decide +kernel` |
| `step1_host_inv`, `step1_case_inv`, `step1_seq_inv` | the only step of a host call, a `case` at a value, or `(); e` | ~70 | `Head`'s cases, as `Core.Steps`' `step1_beta_inv` |
| `maxCase_runs`, `max_first`, `max_runs` | **every run of `max (a, b)` to a value ends at `i32[smax a b]` at the memory it started from, and that run exists** | ~110 | peel each determined step (`steps_peel`); `Host.Conforms` fixes `lt_s` |
| `max_comm`, `max_ge_left` | `max(a, b) == max(b, a)` on runs; `max(a, b) >= a` | ~25 | `max_runs`, then `omega` through `BitVec.toInt` |
| `steps_plug_det`, `max_assoc`, `max_unit` | nested calls compose; `max` with `i32[0x80000000]` is a monoid on runs | ~50 | a determined subterm under a plain context; `omega` |
| `split_runs`, `split_whole`, `split_disjoint` | the machine's `split` answers two families whose leaves, in order, are the input's, and are distinct | ~60 | `Head.split`; `List.range_add` |

What it shows:

- **The chain from source to law is closed, apart from the parser.** `laws.bc` → `bcc_program%`
  → `defErasure` (the checker, run by the kernel) → `maxV` → `max_runs` → the laws.
- **The per-function cost is a run lemma, and each law is then short.** `max_runs` turns the
  function into a Lean function (`smax`); each law is then a fact about `smax` plus a rewrite.
  This is the pattern Creusot and RustHorn get by translation to a functional language. Here it
  is a theorem about the machine, so nothing in the translation is trusted.
- **The work is mechanical.** Every step of `max_runs` is "this redex has one step"; the proofs
  differ only in which `Head` case fires. That is what a tactic automates (§2.6).
- **Composition is free.** `max_assoc` needs only `steps_plug_det`: a subterm whose every run ends
  at `r` can be replaced by `r` under a plain context.

### 2.3 What a law states

| law's subject | Lean statement | status |
|---|---|---|
| a pure function at persistent types (`i32`, `bool`, sums and products of them) | same runs: `Steps μ lhs μ' w ↔ Steps μ rhs μ' w`, or a functional spec `Steps μ (f x) μ' w ↔ μ' = μ ∧ w = enc (φ x)` | **done** for `max` |
| a property of a result | every run that reaches a value reaches one with the property (`max_ge_left`) | **done** |
| a function over owned or borrowed data | the same, over a **representation predicate** that reads a Lean value out of the heap: `ListAt μ v ns` (`Optics/Shape.lean`), or generically a `Repr A μ v m` with `m : ⟦A⟧` | one instance exists (`ListAt`); the generic one is the main new library piece |
| a `mut` argument | pre- and post-heap of the same run: `Repr A μ ℓ m ∧ Repr A μ' ℓ m'`. No prophecy is needed, unlike Creusot, because the statement is about whole runs | — |
| an effectful function | at the empty row, as above. With `raise` or `yield`, about runs that end at `opE` (`Core.Steps`); with `div`, partial correctness on runs that reach a value, and termination from the totality theorems where the row allows it | — |
| allocation | runs agree up to a renaming of locations: `freshRun_det` and `fresh_run_image` (`TwoRun`) | — |
| `law P given I` | `I → P`, with `I` a named Lean hypothesis, as `PinLaw` and `ExternsMeet` are | precedent in the kernel |

Laws compare data, not functions, because `==` at a function type has no model. Bend draws the
same line (copying only at kind `Data`), and so does Creusot's `DeepModel`.

### 2.4 `given`, demanded properties, and unsafe code

- **The demanded floor costs nothing.** The borrow guarantee for every accepted function is
  `fundamentalC` applied to `checkProgram_sound`. Failing it is a type error that names the rule,
  and #79 Revision 2 sharpens that to the smallest failing subterm. No Lean is involved.
- **`trust e` is a law with a given.** #79's obligation for `trust e` is "`e` is in the
  every-allocator relation at the expected type": a `SemV`/`SemC` proposition, which is exactly
  what `bcc obligations` would emit. Discharging it with a proof that assumes `I` is
  `law borrow_safe given I`. `bcc trusted` lists `I`. The kernel already composes such hypotheses
  (`fundamentalC_pin`, `externs_every_run`).
- **An owning invariant needs one kernel piece, and it is RustBelt's.** #624's `Vec` example
  has `buf: RawPtr[T]` and the invariant "`buf` owns `cap` cells". A record of a raw pointer and
  two integers has a relation that owns nothing, because the relation is fixed per type. So
  `push`'s obligation cannot be stated as the relation at `Vec ⊸ …`. RustBelt's answer: "we had
  to first pick semantic interpretations for the abstract types exported by these libraries (e.g.,
  `Cell<T>`). We then proved that each publicly exported function from these libraries satisfies
  the semantic interpretation of its type" (RustBelt §6).
  - Here, that is a value-type former whose relation clause is supplied by a table of models:
    `VTy.opq` generalised from a closed enum with value-only models (`Opaque.Holds`) to models
    over resources.
  - Cost: one `VTy` former, about 100 match arms by the growth note. Every lemma by induction on
    types gets a case, and each model carries the facts those cases need: not persistent, its
    `Imm̲`, outlives, its shape.
  - No new `CDerives` rule is needed. The operations are rows of #79's table.
  - This is the bridge #79 leaves open. It is not needed while `Vec` is written over `array`
    (below), and it costs the same under every option.
- **A `Vec` over `array` needs no `given` at all.** `type Vec[T] { buf: array T, len: i32 }` is
  borrow-safe by the FP. `fits: 0 <= len <= length(buf)` is then a functional invariant, a law
  preserved by each operation, not a safety condition.

### 2.5 How `bcc` checks proofs

| route | what happens | cost | fit |
|---|---|---|---|
| **1. Lean at compile time** | `bcc check` with laws runs `lake build` on the generated statements and the proofs | Every law user needs the Lean toolchain and Mathlib (the repo's `.lake` is gigabytes), and checking waits for Lean | Poor as the default |
| **2. Certificates** | The certificate of a Lean proof is the `.olean` the kernel accepted, re-checkable by replaying it in the kernel. No checker smaller than Lean's kernel exists in this repository, and none was evaluated (unchecked) | Still Lean | Same as 1 for us |
| **3. Sidecar proofs in the gate** | `bcc check` never runs Lean. It reports each law as stated, proved or failed from a manifest. `bcc obligations` emits the statements; `proofs/` holds Lean files; the gate (`lake build`) checks them, and checks each statement against the regenerated one by `decide +kernel`, as `max_erasure` does | Lean in CI only | **Matches #79's simplification and the repo's practice:** `CrossCheck.lean` already re-checks `bcc` output in the gate |

Route 3 keeps the language independent of Lean: Lean is "the proof backend's implementation
detail" (#79, revision 1), and `bcc trusted` lists unproved laws beside `trust` sites and givens.
Bend's split is the same: the human writes `LAWS.bend`, and the gate proves `PROOF.bend`, with
`--verdict` re-checking it by a Lean-proved kernel.

### 2.6 Where automation closes laws

Measured on `smax` (scratch tests, not committed):

| tool | result | note |
|---|---|---|
| `decide` / `rfl` with `runM` | **closed instances only** (`EffTier1Programs`) | `runM` takes no host step: `look` has no `host` case. Adding it is a small `Core/Run.lean` change with a spec entry, and opens every closed integer program to `rfl` |
| `omega` after splitting the comparisons and moving to `BitVec.toInt` | **closes all four `max` laws** | the pattern the experiment uses: kernel-checked, three lines per law |
| `grind` | **fails** on `smax a b = smax b a` | it lacks the antisymmetry of `slt` on `BitVec 32`. Its failure lists the asserted facts, `a.slt b = true` and `b.slt a = true`: the missing fact is visible |
| `bv_omega` | **fails** | it works on unsigned `toNat`; signed comparison under `if` defeats it |
| `bv_decide` | **closes them, with native axioms** | its proofs depend on generated `…_native.bv_decide.ax_*` axioms (native evaluation), outside the hygiene list. Usable only if those axioms are accepted, which the repo does not do |
| SMT bridge | not evaluated (unchecked) | an SMT bridge into Lean must reconstruct kernel proofs to stay inside the hygiene list |

The tiers, from cheap to manual:

1. **Run-calculus tactic** (`bc_run`): rewrite with the step inversions and the substitution
   equations until the law is a statement about Lean functions. Mechanical; the experiment's
   `max_runs` is its output written by hand.
2. **Arithmetic tactic** (`bc_arith`): split comparisons, move to `toInt`, run `omega`.
   Decidable for linear integer arithmetic, and kernel-checked.
3. **`grind` and `simp`** for algebraic facts over data (lists, sums).
4. **Induction**, written by the user or an agent, for laws over recursive data: target 4.

The experiment's laws fall in tiers 1–2. Monoid laws for #620 over arithmetic are tier 1–2; over
lists they are tier 4.

### 2.7 Can "can't prove X" name what is missing?

Yes, in three layers.

1. **The checker's own errors** for the demanded floor. #79's smallest failing subterm, with
   the expected type and the reason.
2. **A counterexample, before any proof.** A false law has a witness, and the interpreter is
   the reference semantics. Running both sides on generated inputs (`plausible` is already in
   the dependency tree, untested here) reports "`max(a, b) == a` fails at `a = 0, b = 1`".
3. **The residual goal.** After tiers 1–2, what remains is a goal about the Lean model (`smax`)
   with named hypotheses: the law's `given`s and the context's facts. `grind`'s failure above
   lists exactly the facts it had. Mapping the residual back to source syntax is direct for the
   arithmetic fragment, since `smax` is the run lemma's reading of `max`.

The suggested fixes follow #79's addendum: an annotation, a `given`, or a hand proof.

### 2.8 (a), (b), (c) for option A

**(a) The lift is small.** No kernel change, and the FP and adequacy are untouched. In order:

1. **Law syntax and statement generation in the frontend.** Parse `law`, check its sides,
   elaborate them to checked terms, and emit the Lean statement with its `decide +kernel` link
   to the erasure.
2. **The run-calculus library.** Port `Optics/Runs.lean` (419 lines) to `Kont.Plain`, and add the
   experiment's inversions.
3. **Representation predicates** `Repr A μ v m` for data types: ⊗, ⊕, μ, `Ref`, arrays through
   `sepRange`. `ListAt` is one instance. This is the largest piece, an estimated hundreds to a
   few thousand lines (unchecked).
4. **The tactics `bc_run` and `bc_arith`.**
5. **The host step in `runM`**, for closed integer instances (a Core change, with a spec entry).
6. **`bcc obligations`, the law manifest, and `bcc trusted` rows.**
7. **Optionally**, the user semantic types of §2.4, for owning `unsafe` invariants. That is a
   kernel change, and it costs the same under every option.

**(b) It does not make the language harder.** No corpus program changes. A user who writes no
law sees nothing. A user who writes laws writes them in our syntax, and tiers 1–2 close the
arithmetic ones. Lean appears only for laws that need induction, and it lives in a sidecar where
an agent can write it. That is Bend's LAWS/PROOF split, with the proofs in a proved kernel.

**(c) It is worth it.** It delivers #624's laws, its givens, PinLaw and ParLaw as laws, and #620's
associativity premise, at a fraction of any type-system option's cost, on the semantics we
already prove things about.

### 2.9 What option A does not give

Laws are proved after the fact, about terms; they do not take part in typing. Three consequences
follow, and they are what the typing options add:

- **A fact does not flow.** `0 <= i < len(a)` known at a loop header does not reach the index
  inside it unless a law states and proves it there. Each use site is its own obligation.
- **A check cannot be removed by typing.** `slice_get_mut` and `array_get` answer `A ⊕ 1`.
  Dropping the `inr` branch needs a proof that it is dead. The backend can take a proved law as a
  licence ("compile from checked facts"), but that is a channel from Lean to the backend, not a
  type.
- **Errors arrive late.** A shape mismatch in a matrix product becomes an unproved law, not a type
  error.

**Static parameters are a partial exception.** Lean is the meta-language, so types computed from
compile-time constants are available to the elaborator. `Mat[3, 4]` can elaborate to a record or
block type and be checked by the ordinary checker, as const generics are. Dependence on run-time
values is what needs E or D.

## 3. The seven target programs

### 3.1 Under option A

| # | program | law and invariant in our syntax | Lean statement | difficulty | the user writes |
|---|---|---|---|---|---|
| 1 | `Vec[T]`, `len <= cap`, owning | over `array`: `type Vec[T] { buf: array T, len: i32 }` with `law push_fits: forall (v: Vec[T], x: T). fits(v) -> fits(push(v, x))`. Over raw memory: `invariant owns …; invariant fits …; law borrow_safe given owns, fits` | over `array`: the FP gives borrow safety; `fits` is `Repr`-level preservation per operation. Over raw memory: `SemV ∅ [] op (τ)` per operation, with `Vec` read through a user semantic type | over `array`: medium (one `Repr` per operation). Raw: hard, RustBelt-level per operation, plus §2.4's kernel piece. RustBelt did not do `Vec` ("supported – though we have not implemented it", fn. 12) | the invariants and laws; Lean for preservation proofs past `bc_run` |
| 2 | `split_at_mut` | `law split_whole: forall (s: mut 'a [T], i: i32). 0 <= i <= len(s) -> …halves are s…` | `split_runs`, `split_whole`, `split_disjoint` | **easy; done.** Disjointness is already typed: `famSplit_compatX` hands out two borrowed families, separated in the relation (`vP_fam_split`) | nothing beyond the law |
| 3 | indexing with `i < len` known | `fn get_unchecked(a: imm 'x [T], i: i32) -> imm 'x T requires 0 <= i < len(a)`; each call site an obligation | at each site, the `inr` branch of `idx` is unreachable on every run: `idxAns ℓ n i = inj₁ …` given the facts reaching the site | easy per site (`idxAns` is one `if`); the cost is that every site needs a proof that the fact reaches it | a `requires`, plus a site proof or a loop-invariant law |
| 4 | library `sum` equals the loop | `law sum_loop: forall (xs: imm 'x List[i32]). sum(xs) == loop_sum(xs)` | `∀ ns μ v, ListAt μ v ns → (Steps μ (sum v) μ' w ↔ Steps μ (loop v) μ' w)`, or both `↔ w = i32 (foldl (·+·) 0 ns)` | **medium to hard**, by induction over the fold's runs. Precedent: `iterMut_shape` (`Optics/Shape.lean`, 585 lines with its run lemmas) | Lean, or an agent's Lean |
| 5 | monoid law for parallel reduce (#620) | `law max_assoc …; law max_unit …` | `max_assoc`, `max_unit` | **easy; done** (tier 1–2) | nothing beyond the laws |
| 6 | sized matrix, shape-checked multiply | static sizes: `Mat[3, 4]` elaborated to a block type. Run-time sizes: `law mul_shape: forall (a, b). cols(a) == rows(b) -> rows(mul(a, b)) == rows(a)` and a `requires` per call | a `Repr`-level postcondition; a site obligation per call | easy laws; the cost is per-site obligations, and the mismatch is an unproved law, not a type error | the laws; site proofs |
| 7 | k8s `replicas >= 0` from decode to use | `type Replicas = abstract i32 invariant nonneg: self >= 0`; `law nonneg: forall (r: Replicas). to_i32(r) >= 0` | module-invariant induction: each operation that makes a `Replicas` establishes `nonneg` | easy proof, but it needs abstract types (data declarations are planned) so the invariant can be established at the module's operations | the invariant and the decode check |

### 3.2 Under the typing options

| # | B. full DT (QTT, Idris 2, BendTT) | D. refinements (Flux, Liquid Haskell) | E. DML sizes (#72) | F. verifier specs (Verus) |
|---|---|---|---|---|
| 1 | `Vec n A` with `n ≤ cap` as a type index. The owning part still needs a semantic model; Idris 2 builds linear arrays only through a continuation (`newArray`, §4.1) | Flux's `RVec<T>[n]` API (Fig. 3); the `unsafe` implementation is trusted (§3.3: "We treat vectors as a primitive") | `Block(n, A)` plus `Uninit` leaves for capacity (#72) | `requires`/`ensures` on each method; Verus' `PPtr`/`PermData` ghost permissions (§4.1) for raw memory |
| 2 | `Vec (n+m) ≅ Vec n ⊗ Vec m` by type | sketch: `split(s: [T][@n], i: i32{v: 0 <= v <= n}) -> [T][i] * [T][n - i]` | `Block(n+m) ≅ Block(n) ⊗ Block(m)` (#72) | `ensures` on the halves' lengths |
| 3 | `Fin n` index | `get(self: &RVec<T>[@n], idx: usize{v: v < n})` (Flux Fig. 3); the check is gone and the bound flows by inference | `Idx n` from `for i in 0..n` | `requires i < len`, proved by the solver from a loop invariant (Verus §3's `get_unchecked`) |
| 4 | a proof term over the inductive family | **not expressible**: Flux "restricts the specifications to those that can be expressed by … quantifier-free refinements" (§7) | not expressible | `ensures result == spec_sum(xs)` with a loop invariant; an inductive lemma in proof mode |
| 5 | a proof term | not expressible (it quantifies over all values) | not expressible | a `proof fn` lemma |
| 6 | `Mat m n → Mat n p → Mat m p` | `RMat` indexed by rows and columns (§5.1) | `Mat[m, n]` with `m, n` sizes | `requires` on shapes |
| 7 | `(r : Int ** r ≥ 0)` | `i32{v: v >= 0}` after the decode check; flows to the use | an index `r ≥ 0` on a singleton | `requires r >= 0` at each use, or a type invariant |

Laws 4 and 5 are about functions over every input, which refinements and indices do not express.
Only full dependent types and the Lean layer state them, and the Lean layer does so without a
new kernel. Targets 3, 6 and 7 are the ones where typing beats a law: the fact flows through the
program, and the check is removed by typing.

## 4. The typing options against our code

The numbers used below:

- `Core/`: 67,122 lines.
- `CDerives`: 96 constructors.
- `VTy`: 16 formers; `CTy`: 7.
- The relation and the lemmas proved by induction on types, the files any change of what a type
  is touches: `Relation`, `RelationFacts`, `Compatibility`, `Compat`, `Fundamental`, `Images`,
  `Invariant`, `Reborrow`, `ShapeMu`, `Types`, `Wp`, `World`, `Demonic`. Together, 14,443 lines.
- `Paper/` and `Support/`: 42,856 lines.
- `Frontend/`: 32,140 lines; `Backend/`: 10,993 lines.

### 4.1 Full dependent types with quantities: QTT, Idris 2, BendTT

**What the papers say.**
- QTT annotates each binder with a usage from a semiring such as {0, 1, ω}. Type formation
  happens in the 0-fragment, so "type formation requires no computational resources", and terms
  are checked at σ ∈ {0, 1} (Atkey §2.1.3, p.3).
- Conversion is judgemental equality (`Conv`, p.3).
- The semantics is realisability over linear combinatory algebras: assemblies, with no heap or
  mutable state (§4, pp.7–9). Atkey names "low-level imperative computation in the style of
  Ahmed et al." as future work (§6, p.10).
- Idris 2 calls multiplicity 1 "experimental" (§3.3, p.10). It has no quantity polymorphism
  (§4.2, p.12; §7, p.24). It reports that "linearity and exceptions do not mix well" (§4.3,
  p.16). It has no borrowing: a linear array is made through a continuation (§4.1, p.12).
- BendTT (from `bendtt.lean`, and the earlier Bend notes, read) is `Type : Type` with
  quantities `-`, plain and `+` and affine live code. Its checker "runs with a step budget, and
  it rejects a book when the budget runs out". It is pure: no heap, no mutation, no borrows.

**Lift against our code.**
- *Kernel.* `VTy`/`CTy` would contain terms. Every type-level lemma would gain term
  substitution into types and a conversion case. That is all 14.4k lines of the relation and its
  facts, and `CDerives` gains a conversion rule.
- *Theory.* The relation would need to interpret types that depend on terms over worlds with
  borrows, reborrow images and lifetimes. No paper read builds this. It is a new borrow calculus,
  so the FP and adequacy would be re-proved from scratch.
- *Elaborator and inference.* Unification with dependent types; implicit arguments (Idris §2.3.2).
- *Erasure and zero-cost.* Fine: QTT's 0 is the cleanest account of erasure (Idris §7: "the most
  valuable user-visible new feature enabled by QTT").
- *Decidability.* Conversion evaluates terms, and our language has `div`. So type-level terms
  must be restricted to a terminating fragment, or the checker needs a step budget, as BendTT's
  does.

**Kill criterion.** (i) fires: it needs a new borrow calculus and gives up the current FP until
one is built. (iii) fires unless a step budget is accepted. (ii) does not fire, since
non-dependent programs are a subset. **Killed.**

**(a)** The largest lift: a new kernel and an open research problem. **(b)** Yes, harder.
Brady: "Dependent and linear types are powerful concepts, and without care in library design,
can be hard to use" (§7, p.23). **(c)** No: the laws it would carry, A carries without the kernel
change.

### 4.2 Linear dependent type theory: LNL_D (Krishnaswami–Pradic–Benton), Fu–Kishida–Selinger

**What the papers say.**
- **KPB's types depend only on intuitionistic terms.** The linear/non-linear split means "we
  never have to form a type dependent on an open linear term" (§1, p.1). That matches our
  persistent/linear split (`VTy.Persistent`, `!A`).
- **KPB's imperative fragment is L3-style:** a type of locations, capabilities `e ↦ X`, a
  computation monad `T(A)`, and proof irrelevance `[A]` (§3, pp.4–5). That is the
  capability-passing reading BoLo starts from.
- **But KPB is extensional**, with equality reflection, and "the type system we present in this
  paper is (extremely) undecidable". The implementation is an intensional variant with explicit
  annotations (§5, p.13).
- **KPB covers total correctness only.** It needs "a termination metric on fixed point
  definitions" and rules out general recursion (§3.3 *Caveat*, p.8).
- **FKS's types depend on the *shape* of a linear term**, `Sh(N)`, which is duplicable (§1.3,
  p.3). Their `conv : !((x : List Qubit) ⊸ Vec Qubit (toNat x))` (§4.1) is target 6's
  list-to-vector conversion. Our shape relation (`vShape`, `ShapeMu.lean`) is the analogue.
- **FKS evaluates during type checking.** "The evaluation rules are also used during type
  checking", on open terms (§3.2, Def. 3.9). Their simple-type check "is undecidable in general"
  and is restricted to primitive recursive declarations (§4.3). Recursion is future work (§5).

**Lift.** A second kernel of the same size as B's, though the split keeps dependency off linear
terms, which suits our persistent fragment.

**Kill criterion.** (iii) fires for KPB as printed (undecidable) and for FKS (evaluation of open
terms). (i) fires: neither has borrows, and KPB needs termination everywhere. **Killed as
printed.**

**What survives** is the restriction that makes both decidable: types depend only on persistent,
first-order index data (sizes, shapes), in a decidable index language. That is option E.

**(a)** Very large as printed. **(b)** Yes. **(c)** No as printed; its useful core is E.

### 4.3 Refinement types: Liquid Haskell, Flux

**What the papers say.**
- **Flux layers refinements on Rust's types after borrow checking.** It works "as a plug-in to
  the Rust compiler", on programs that "satisfy Rust's borrowing rules, which our analysis relies
  on" (§4, p.14).
- **The ingredients.** Base types are indexed by refinement values (`i32[n]`). There are
  existentials `{v. B[v] | p}` and refinement parameters (§2.1). `&mut T` takes only weak updates,
  so the refinement is invariant through it. Strong references `&strg T` allow strong updates,
  with an `ensures` clause on the updated location (§2.2).
- **Soundness is a paper proof**, against a Stacked Borrows dynamic semantics: "well-borrowed
  evaluations of well-typed programs do not get stuck" (Thm 3.1, p.14; proofs in the supplement).
- **The refinement logic is decidable.** It is quantifier-free, and liquid inference solves Horn
  constraints, so loop invariants need no annotation (§4.2–4.3).
- **The evaluation.** Against Prusti on the benchmarks, specifications are about half the size,
  verification an order of magnitude faster, and loop annotations zero against 9% of code
  (Table 1, p.17).
- **The limit Flux states**: specifications are those "that can be expressed by the combination
  of type constructors and quantifier-free refinements"; functional correctness, such as
  sortedness, is out of reach (§7, p.21).
- **Liquid Haskell** (Vazou et al. 2014) shows the classic verification conditions are unsound
  under lazy evaluation and sound under eager evaluation, where "the domain of the closing
  substitutions [can] be restricted to values" (§2.4, p.4). Its fix is a stratification into
  terminating and diverging binders. Refinements stay in QF-EUFLIA, so checking is decidable.

**Lift against our code.**
- *Kernel.* None in `CDerives`; growth rule 19 forbids a new index. A refinement judgment
  `RDerives` is layered over `CDerives`, as Flux layers over rustc.
- *Soundness.* A refined relation `vP A … v ρ ∧ φ(v)` at persistent payloads (`i32`, `bool`,
  sizes, array lengths, which are the `n` of a family value `(ℓ, n)`). Its soundness is through
  `fundamentalC` and `wpTS_mono` with strengthened postconditions, one lemma per rule that touches
  refinements. The borrow FP is not re-proved.
- *Our evaluation order is the easy case.* We are call-by-value at the value/computation split,
  so Liquid Haskell's problem does not arise. Our `div` row already marks the binders that may
  diverge, which is the stratification Liquid Haskell had to build.
- *`Mut`.* Our `Mut` is invariant, so refinements through `Mut` are weak, exactly as Flux's
  `&mut`. Strong updates exist only on an owned `Ref`, through `swap`/`store`.
- *Elaborator and inference.* The frontend gains constraint generation and a Horn solver. The
  solver need not be trusted if its output is checked: `omega` decides the quantifier-free linear
  integer arithmetic, kernel-checked.
- *Erasure and zero-cost.* Refinements erase entirely, and they remove bounds checks, which is a
  zero-cost gain (#609).
- *Decidability.* Quantifier-free linear arithmetic is decidable.

**Kill criterion.** (i) no. (ii) no, if every unrefined type means `{v | true}` and only
signatures that want refinements carry them: Flux "does not modify the syntax of Rust programs"
(§4.1). (iii) no. **Passes.**

**(a)** Medium to large: a second judgment, its soundness lemma per touched rule (an estimated
thousands of lines; unchecked), constraint generation, a solver, and data-type measures
(`refined_by`) once data declarations exist. **(b)** Mild and opt-in. Errors are "cannot prove
`v < n` at …" with a counterexample from the solver. **(c)** Probably, after A, for targets 3 and
7, and partly 6. It does not do 4 or 5.

### 4.4 DML-style indexed types (#72)

The papers were not read for this note (unchecked); the design is #72's.
- **The design.** A size sort in `Δ` beside lifetimes, with linear arithmetic only, erased.
  `Size n` singletons give the run-time connection. `Block(n, A)` gives
  `Block(n+m) ≅ Block(n) ⊗ Block(m)`, and `Array A ≜ ∃n. Size n ⊗ Block(n, A)` is derivable.
- **Lift against our code.**
  - `Δ` already carries an index sort: lifetimes, with `∀'a ⊏ @b. C` (`CTy.all`) and the relation
    parameterised by a lifetime substitution `δ : LSub`. Sizes follow that template: `∀n`/`∃n`,
    and a size substitution beside `δ`.
  - Every lemma by induction on types gets the sized formers' cases.
  - No new index on `CDerives`, since `Δ` grows rather than a new index appearing (#72 cites growth
    rule 19).
- **Elaborator.** Index inference by unification plus linear constraints, decided by `omega`,
  kernel-checked.
- **Erasure.** Indices erase as lifetimes do (dream-properties C7).
- **Decidability.** Linear integer arithmetic is decidable.

**Kill criterion.** (i) no. (ii) no: `Array A` stays derivable, so the corpus is unchanged.
(iii) no. **Passes.**

**(a)** Medium: a carrier extension and the relation's case per sized former. **(b)** Mild: const
generics with run-time sizes. **(c)** Yes for arrays, slices and matrices (targets 2, 3 and 6).
Nothing beyond them.

### 4.5 Verifier-style specs: Verus, Prusti, Creusot

**What the paper says** (Verus; Prusti and Creusot were not read and are unchecked).
- **Three modes.** Specs, proofs and executable code are all Rust. Spec and proof code are
  ghost and erased; spec code is not linearity-checked, and proof and exec code are (Fig. 2,
  p.5).
- **The verification conditions go to Z3.** "Verus relies on the properties of borrowing in its
  SMT encoding", encoding `&T` and owned pointers as values (§2.1, p.6), and a `&mut` as a pair
  of pre- and post-values (§2.2, Fig. 3).
- **Unsafe code is out of reach.** Verus "cannot reason about traditional Rust unsafe code" and
  offers ghost-permission replacements instead (§9, p.17).
- **The formalisation covers less than the tool.** It omits "preconditions, postconditions, and
  verification condition generation, focusing instead on type safety and termination" (§10,
  p.18). The verification-condition generator is trusted.

**Lift against our code.**
- *Kernel.* None.
- *The work.* `requires`/`ensures`/loop invariants in our syntax, and a weakest-precondition
  generator from the checked term to Lean goals: the run calculus of A, run at verification-
  condition generation time.
- *Our advantage.* The semantics is in Lean, so that generator can be proved sound against
  `Steps`, which Verus' is not. Borrow information simplifies the conditions here as it does in
  Verus: `Imm` is a value, `Mut` a pre/post pair, and our relation's separation gives the framing.
- *Loops.* A `while` (a `div` loop) needs an invariant, which Flux's inference avoids (Table 1).

**Kill criterion.** Passes.

**(a)** Small to medium on top of A. **(b)** Mild. Loop invariants are the visible cost: Prusti's
are 9% of code in Flux's Table 1. **(c)** Yes, as A's in-source surface: `requires`/`ensures`
are laws with givens attached to a function.

## 5. The kill criterion

| option | (i) new borrow calculus, or loses FP, adequacy or a borrow guarantee | (ii) annotations on ordinary corpus programs | (iii) undecidable, or unbounded evaluation in the checker | verdict |
|---|---|---|---|---|
| A. Lean layer | no | no | no; the checker is unchanged, and proofs are checked outside it | **passes** |
| B. QTT, Idris 2, BendTT | **yes** | no | **yes** (conversion), unless a step budget, BendTT's choice | **killed** |
| C. LNL_D as printed | **yes** (no borrows; termination everywhere) | no | **yes** (KPB: "(extremely) undecidable"; FKS: open-term evaluation) | **killed**; its decidable core is E |
| D. Refinements | no (a layered judgment, soundness through `fundamentalC`) | no, if unrefined means `true` | no | **passes** |
| E. DML sizes | no (`Δ` gains a sort; the relation a size substitution, re-proved) | no | no | **passes** |
| F. Verifier specs | no | no | no | **passes** |

The criterion's own fallback, "no dependent types; laws go to Lean/automation", is option A. The
typing options that pass are additions to A, not alternatives to it.

## 6. Decision menu

| # | option | gives | costs | when |
|---|---|---|---|---|
| 1 | **A alone** | all of #624: laws in our syntax, givens, `trust` obligations as laws, PinLaw and ParLaw as laws, #620's associativity premise | frontend law syntax and generator; a Lean library (run calculus, representations, tactics); a host step in `runM`; gate integration | now |
| 2 | **A + E (DML sizes, #72)** | targets 2, 3 and 6 by typing: bounds without checks, typed splits, shape errors at compile time | `Δ` gains a size sort; the relation gains a size substitution; type-induction lemmas gain cases; the FP and adequacy re-proved | when bounds and shape are the most frequent `trust` and unproved-law reasons |
| 3 | **A + D (Flux-style refinements)** | targets 3 and 7 and part of 6: facts flow by typing, with inference | a second judgment and its soundness through `fundamentalC`; constraint generation and a solver; measures on data declarations | after data declarations; if the reasons are value predicates rather than sizes |
| 4 | **A + F (in-source `requires`/`ensures`)** | specs next to code; site obligations generated | a proved weakest-precondition generator over A's run calculus; loop invariants | together with A's surface syntax, or right after |
| 5 | **B or C** | — | a new kernel and an open problem | rejected by the kill criterion |

**Recommendation.**
- **Take 1 now**, with 4's surface (`requires` as a law with a given) designed alongside it, so
  that the law syntax has one form.
- **Choose between 2 and 3 from evidence**: #79's feedback loop, counting `trust` sites and
  unproved laws by reason. If sizes dominate, 2. #72 already scopes it, and it reuses the
  lifetime machinery of `Δ`. If value predicates dominate, 3. They are not exclusive: Flux
  indexes `RVec` by its length.
- **Reject 5.**
- **The one kernel item every path shares** is §2.4's user semantic types for owning `unsafe`
  invariants. It is #79's bridge, and it is needed only once code is written over raw memory.

## 7. Sources

**Read for this note**, with the Read tool (PDF pages) or as extracted text:

| paper | pages read | not read |
|---|---|---|
| Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018 | pp. 1–10 (all) | — |
| Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021 | pp. 1–16, 21–26 | pp. 17–20 (session types) |
| Lehmann, Geller, Vazou, Jhala, *Flux: Liquid Types for Rust*: arXiv 2207.04034v2, the PLDI 2023 paper's preprint. Its header carries an OOPSLA placeholder | pp. 1–23 (all) | the supplementary material |
| Krishnaswami, Pradic, Benton, *Integrating Dependent and Linear Types*, POPL 2015 | pp. 1–13 | p. 14 (references) |
| Vazou, Seidel, Jhala, Vytiniotis, Peyton Jones, *Refinement Types for Haskell*, ICFP 2014 | pp. 1–4; the evaluation and limitations by text search | pp. 5–15 in full |
| Lattuada et al., *Verus: Verifying Rust Programs using Linear Ghost Types*, OOPSLA 2023 (extended version, arXiv 2303.05491) | pp. 1–8; §7–§10 (implementation, user experience, limitations, formalisation intro) as text | §4.2–§6 and §10's rules |
| Jung, Jourdan, Krebbers, Dreyer, *RustBelt*, POPL 2018 | pp. 1–6; §4.1, §6, §7, §9 as text | §3, §5 |
| Fu, Kishida, Selinger, *Linear Dependent Type Theory for Quantum Programming Languages*, LMCS 2022 (extends LICS 2020) | pp. 1–4; §3.2 (Def. 3.9), §4.1–§4.3, §5 as text | §2's categorical structure |
| Bend 2: `bend2/bendtt.lean` (header, `Def.check`, `Book.check`, the claims preamble), `demos/pure_par_sort/LAWS.bend` | as listed | the BendTT paper itself was not re-read here; the BendTT claims come from the earlier Bend notes, which were read |

**Unchecked**, not read for this note:
- Xi and Pfenning on DML. §4.4 rests on #72's design.
- Prusti and Creusot. Their claims come from Flux §5, §6 and Verus §11.
- Liquid Haskell's later refinement reflection.
- Any proof-certificate checker smaller than Lean's kernel.
- SMT bridges into Lean.
- `plausible` as a counterexample finder for laws.

**Code read**: the pieces in §1's table. `experiments/DepSpike` was written for this note.
