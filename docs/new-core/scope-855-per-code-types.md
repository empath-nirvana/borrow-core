# #855: per-code closure and codata types, an erasing coercion to `dyn`, monomorphisation in Backend2

Kernel target: a design scope for per-code types, decided by the user on 2026-11-07 (#855):
- each closure and each `unfold` gets its own type, naming its code;
- an explicit erasing coercion goes to the shared `U C`/`νX. C` type (`dyn`);
- Backend2 monomorphises over the specific types, as Rust does.

This document picks how. It is a design only, with no Lean and no library change. Inputs:
- backend-foreman's answers (`scratch-archive/kernel/scope855/backend-answers.md`, cited as
  B1–B5);
- surface-foreman's answers (`…/surface-answers.md`, cited as S1–S5).

Read at `main` 82ed358e (worktree `borrow-core-scope855`, branch `scope-855`). `Const791` was
read at `origin/tier1-844`.

## 0. Summary

- **Recommendation: option (a), a new value-type former `VTy.code N E C`**, written
  `Code⟨N; E⟩ C`. It is a thunk of `C` whose code is `N` and whose captured environment has type
  `E`.
  - `N` is the closure's body with its free variables renumbered by rank (`capNorm`), so it is
    closed and stable under shifting.
  - `E` is the tensor of the captured variables' types in that order.
  - `(N, E)` is Rust's closure type (definition site plus generic arguments), transcribed to a
    kernel whose terms carry no types and whose polymorphism is substitution (`letPoly`,
    `Core/PolyLet.lean:4–9`).
- **The relation** reads `Code⟨N; E⟩ C` as a subset of `U C`'s values: the value is
  `λ(N[us])` for an environment `us` in `𝒱⟦E⟧`, and it is in `𝒱⟦U C⟧`.
  - The first conjunct is a fact about the value's syntax. The second is the existing `U` clause.
  - Every law of the relation follows from the `U` clause and from `E` being a structural
    subterm.
- **Five new `CDerives` rules**, each with one compatibility lemma. No new index and no new
  judgment.
  - `codeI` introduces the specific type at a thunk.
  - `erase` is the coercion to `U C`, a rule on the same term.
  - `force` is generalised to read `C` from either type.
  - `unfoldK` and `nuOutK` give `unfold`'s codata a specific type whose rest has that same type.
- **Arm counts (grep, §2.1).**
  - (a) adds about 150–160 match arms in `Core/`: 151 lines of `.opq` arms in 26 files and 161
    of `.thunk` arms in 32 files, the two closest formers.
  - (b), a code coordinate on `U` and on `ν`, rewrites every `.thunk` occurrence: 463 in 72
    files of `Core/`, 568 in `Frontend/` and `Backend2/`. A `ν` coordinate adds 265 `.nu`
    occurrences on top.
  - (c), abstract or nominal type constants, has no mechanism in the kernel to build on, and a
    type context would be a new `CDerives` index.
- **The hardest kernel case is `unfold`'s rest** (§4.1).
  - Every `for` loop in 119 corpus programs needs the rest's type to equal the codata's own type
    (S5). Without that, every loop state is erased to `dyn` after one step.
  - The case is tractable: `unfold`'s soundness proof already uses the per-code set as its
    coinduction candidate (`candN`, `Core/Nu.lean:358`, `candN_post` `:557`).
- **The hardest elaborator case is `alpha-nu-in`'s `wrap`**: a `nu_in` object whose rest is
  another code's rest (§4.2). It needs the object typed at the unrolled type with a specific rest,
  not at `ν`.
- **Backend2 loses its two flow analyses.**
  - `Backend2/Flow.lean` (177 lines, `UNPROVED` at `:119`) is deleted.
  - Layout's lambda-set walk (`UNPROVED` at `Layout.lean:398`) is deleted.
  - The `takesClos` per-use reconversion (`Convert.lean:3551`) is deleted.
  - Each is replaced by reading the code from the type, and the dyn classes from the `erase`
    nodes (B1, B4).
- **Units:** 6 kernel, 5 surface, 4 backend (§9). **Open choices for the user:** 4 (§10). The
  main one is whether a function type written in a signature means `impl` (specific, the
  default) or `dyn`. That choice decides whether the "no count rises" target can be met without
  rewriting the corpus.

## 1. What the kernel and the backend have today

- **`U C` is a leaf to the typed world.** `VTy.thunk (C : CTy)` (`Core/Types.lean:52`).
  `VTy.recV` treats it as a leaf (`:16–17`). Its relation clause reads `𝒞⟦C⟧` at the forced
  value and reads no type environment (`vNE`, `Core/Chain/Goal791N.lean:69–70`).
- **Terms carry no types, and closures carry no label.**
  - A thunk is the λ-value `.lam M`, typed by `thunkF` or `thunkV` (`Core/Fundamental.lean:211`,
    `:215`), or by their `!` forms.
  - The machine substitutes, so the runtime value is `.lam (M.psub γ)` (`thunkF_compatC`,
    `Core/Compat.lean:105`).
  - `Expr` is Paper's (`Paper/S1_Syntax/Definitions.lean:124`) and has no former to hold a node
    identity.
- **Polymorphism is substitution.** `CDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop`
  (`Fundamental.lean:200`) has no type context.
  - `letPoly` types each use of a closed λ-value on its own (`PolyLet.lean`).
  - The checker's `use` node checks a definition's body once per key, with its type arguments
    (`Frontend/Check/TExpr.lean:595`).
  - Monomorphisation is therefore already how the kernel types generic code. What is missing is a
    type that says which code a closure is.
- **Codata is a thunk of `ν`.**
  - `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` (`unfoldN`, `Fundamental.lean:510`).
  - `unfold step s` is `etaN C g s` (`Nu.lean:133`): the code `λo. self g s o` with captures
    `g, s`. Its rest is `etaN C g s′`, the same code with the same `g`.
  - `unfold`'s soundness is coinduction at the candidate `{etaN C g s | s ∈ 𝒱⟦S⟧}` with `g`
    fixed (`candN`, `Nu.lean:358`; `unfold_compatX`, `:576`).
- **Backend2 rebuilds the code sets** (B1). Three mechanisms do it:
  - `Flow.lean`, a 0-CFA on the LIR. A call is direct when its set is a singleton.
  - `Layout.lean`'s closure classes, a union-find over every move (`:398`). Data read out of a
    pair, sum, cell or array takes its class's whole set.
  - `convUse`, which converts again, at every use, a body that takes a closure (`takesClos`,
    `Convert.lean:2266`, `:3551`).
- **Measured, alpha-nu-in** (`corpus/counts-backend2.expected:98`, `corpus/counts.expected:105`):

  | | allocs | indirect |
  |---|---|---|
  | Backend2 | 5 | 3 |
  | old backend | 1 | 0 |

  The brief quoted "3/4". The 4 does not match the table at 82ed358e, which reads 5 allocations.

## 2. The kernel side: three options

### 2.1 Cost, measured

Counts are `grep` over `*.lean`. An "arm line" is a line starting `|` that names the former.
A new former needs about one arm per exhaustive match. A wildcard arm absorbs it, so these counts
are upper bounds. The closest formers are `.opq`, the most recent leaf, and `.thunk`, whose
children `code` shares.

| Option | What changes | `Core/` | `Frontend/` | `Backend2/` |
|---|---|---|---|---|
| (a) new `VTy.code N E C` | one new arm per exhaustive `VTy` match; `VTy.recV` gains a case | 151 (`.opq`, 26 files) – 161 (`.thunk`, 32 files) arm lines; 42 `VTy.recV` uses; 22–23 of the arm lines in `Core/Chain/` | 47 (`.opq`, 6 files) – 265 (`.thunk`, 26 files) | 20 (`.opq`, 6 files) – 42 (`.thunk`, 7 files) |
| (b) coordinate on `U` (and `ν`) | `thunk C k`, `k = dyn ∣ at N E`; every `.thunk` pattern and constructor gains a field; the semantic arms (relation, `[α]`, `VFree`, substitution) handle `at` | 463 `.thunk` occurrences in 72 files; with a `ν` coordinate, 265 `.nu` occurrences (140 arm lines) more | 568 `.thunk` occurrences in `Frontend/`+`Backend2/` (40 files); 189 `.nu` | (included) |
| (c) abstract/nominal type constants | a type context in `CDerives`; an environment in `cN` | not counted: needs a new index (§2.4) | | |

CLAUDE.md's "about 100 arms for a `VTy` former" undercounts today's `Core/` by about half: 151
`.opq` arm lines.

### 2.2 (a) A new former `VTy.code N E C` (recommended)

- **What a code is.**
  - `N = capNorm M` for the thunk's body `M`: `M` with its free variables renumbered
    `0, 1, …` by rank. `N` is closed relative to its captures.
  - `capNorm` is invariant under `shift`, because a shift preserves the order of the free
    variables. That invariance is what lets the type survive the checker's placement of a `use`
    body at another depth (`Frontend/Check/TShift.lean`). The invariance is a lemma, not proved
    yet.
  - `E` is the tensor of the captures' types in rank order, `1` if there are none.
- **Why `(N, E)` and not `N` alone.**
  - `wrap`'s object has the same body for every `o`. The code it calls on `o` is `o`'s, and only
    `E` says which.
  - `useKey` keys on type arguments (`Convert.lean:2284`), so `E` in the type is what makes two
    instances of `wrap` two keys (B2, B3).
  - This is Rust's closure type, which carries the parent's generic arguments.
- **Why not a label.**
  - A label `κ : Nat` needs a table that maps labels to codes. Inside `CDerives` that table is a
    new index ("No new index on `CDerives`"). Inside `Expr` it is a change to Paper's syntax.
  - The structural identity needs neither. Two nodes with the same `(N, E)` are the same code, and
    sharing them is correct.
- **The relation** (`vNE`, `Goal791N.lean:62`; Core's `vCE`, `Core/Relation.lean:121`):
  ```
  𝒱⟦Code⟨N; E⟩ C⟧ v ρ  ≜  (∃ us ρE ρR. v = λ(N[us]) ∧ ρE ⋆ ρR = ρ ∧ 𝒱⟦E⟧(tuple us) ρE)  ∧  𝒱⟦U C⟧ v ρ
  ```
  - The first conjunct is the code. It holds the environment in `𝒱⟦E⟧` at the same world and
    index.
  - `ρR` absorbs the resources of persistent slots the body does not use. Whether `ρR` is always
    empty is not derived.
  - In the observable view (`vOE`), `Code⟨N; E⟩ C` is `True`, as `U C` is (`Goal791N.lean:105`).
  - **A single code's semantic type is a subset of `U C`'s**: the second conjunct is the `U`
    clause itself.
- **The laws.**
  - The code conjunct is a statement about `v`'s syntax plus `𝒱⟦E⟧`, and `E` is a structural
    subterm. So each law (`cN_down`, `cN_congr`, `vN_extR`, `vN_local`, `vN_outlives`,
    `valRelOK_vN` at `Goal791N.lean:2485`) is its `U` proof plus the induction hypothesis at `E`.
  - **No `VOutlives` rule for `code`**, as there is none for `U` (`Types.lean:1867–1891`). So
    `vN_outlives` and the stratum laws are vacuous at `code`, and a code value never outlives a
    lifetime. This adds no borrow power (§5.4).
- **`[α]` and type equality.**
  - `VTy.alphaB` gets one arm: equal `N` (`Expr` has `DecidableEq`, `Core/LetCopy.lean:28`; the
    instance moves to `Types.lean`), `alphaB` at `E` and at `C`.
  - `Expr` holds no lifetimes and no names (it is de Bruijn), so lifetime renaming touches only
    `E` and `C`.
  - The `type equality` gate (`scripts/check-type-eq.sh`) is unaffected in kind: comparisons
    still go through `tyEqV`. One thing changes: Backend2's lookup of a code's node by type (§7)
    must go through `tyEqV`, or be allowlisted with its reason.
  - The `renaming` gate (`scripts/alpha-check.py`) is unaffected: binder names do not reach `N`.
- **Printing.** Types now contain bodies. `ppVT` and the checker's messages need a digest form,
  `{closure@span}` with `E`, or keys and errors grow with the program.

### 2.3 (b) A code coordinate on `U` and `ν`

This option is `thunk (C : CTy) (k : CodeIx)` with `CodeIx ::= dyn | at N E`, and `U C` as the
abbreviation `thunk C .dyn`.
- **It follows "Generalize by deleting"** literally: one general former, with the fixed one made
  an abbreviation.
- **What it costs.**
  - It changes the statement of every existing rule that names `.thunk`: `thunkF`, `thunkV`,
    `force`, the `!` forms, `unfoldN`, `retTy`, `clausesTy`. These are rules under #798's freeze.
  - It touches 463 occurrences in 72 `Core/` files for a coordinate that 9 rules in 10 ignore.
  - `CodeIx` holds a `VTy`, so it joins the `VTy`/`CTy` mutual block as a third type.
    Re-deriving `DecidableEq` for it is not verified.
- **The `ν` coordinate is not needed.**
  - A codata value is a `U (νX. C)` value. Its code is on the value type, and §4.1 handles the
    one recursive case with a rule, not a coordinate.
  - A coordinate on `νX. C` alone could not say what `wrap`'s object needs: its rest is a
    *different* code (§4.2).
- **What it buys.** Nothing semantically over (a): the relation clause is the same. (b) wins only
  if #867 also takes a coordinate (`fam L n`) and the two are wanted symmetric (§8.4).

### 2.4 (c) Abstract or nominal type constants

There is no mechanism for this to build on:
- **No type context.** `CDerives`'s context is `LifeCtx` (lifetimes) and `Ctx VTy`
  (`Fundamental.lean:200`). Type variables occur only under `μ`/`ν` binders (`VTy.tvar`,
  `Types.lean:66`).
- **No environment to interpret them.** The `U` clause of the relation reads no type environment
  (`Goal791N.lean:69`), so an abstract type inside a `C` would have no meaning there.
- **What it would take.** Constants in Δ would need a type context and a semantic environment
  threaded through `cN`. The context is a new `CDerives` index, which is excluded.
- **It answers the wrong question.** An existential hides the code, and the code is what the
  backend reads (B2).

**Rejected**, on these pointers.

### 2.5 (d) Not chosen: the code on the computation type

`CTy.code N E C`, with `U (code N E C)` as the specific type, would cost a `CTy` former. That is
cheaper by the growth rules.
- **The obstruction.** Every rule stated at an arbitrary `C` would then hold at `C = code …`:
  `bind`, `app`, `proj`, `allE`, `effSub`, `letPoly`. Their compatibility lemmas close `𝒞⟦C⟧`
  under head expansion (`cC_head`, `Core/Computation.lean:251`). A clause reading "the term is a
  closure of `N`" is not closed under head expansion.
- Not derived; obstruction not verified beyond that observation.

### 2.6 Recommendation

**(a).**
- It leaves every existing rule's statement unchanged.
- Its relation clause is the `U` clause plus a conjunct, so its laws delegate.
- Its arms are additive and mostly copies of the `.thunk` arm, with a recursive call at `E`.

(b) is the alternative if the user wants #855 and #867 symmetric as coordinates (§10, C4).

## 3. The rules

Each rule below is a new `CDerives` rule, mirrored into `CDerivesP`, `CDerivesAt` and
`TDerives*` by `scripts/gen-pin.py`. There is no new judgment, so the freeze is unaffected.

| Rule | Statement | Compatibility lemma |
|---|---|---|
| `codeI` | `Γ ⊢ .lam M : U C` ⟹ `Γ ⊢ .lam M : Code⟨capNorm M; Γ.capTy M⟩ C` | From the premise's lemma: the closed term is `.lam (M.psub 1 γ)` (`thunkF_compatC`), and a syntactic lemma `M.psub 1 γ = (capNorm M)[γ at M's free variables]` gives the code conjunct. `gDenC` gives the environment's resource. Not built. |
| `codeIB` | the same at `!U C` ⟹ `!Code⟨…⟩ C` | As `codeI`, under `!`'s empty resource. |
| `erase` | `Γ ⊢ e : Code⟨N; E⟩ C` ⟹ `Γ ⊢ e : U C` (and at `!`) | Forget the first conjunct (`wpTS_mono`). |
| `force` (restated) | `Ctx.SoloP Γ i T`, `T.forceTy = some C` ⟹ `forceE C (.var i) : C`, where `T` is `U C` or `Code⟨N; E⟩ C` | `force_compatC` (`Compat.lean:145`) reads the second conjunct. |
| `unfoldK` | `unfold` at a step of type `G` with `G.forceTy = S ⊸ C[S/X]`: `!G ⊸ !Code⟨hN; !G⟩ (S ⊸ Code⟨etaN; !G ⊗ S⟩ (νX. C))` | `unfold_compatX`'s proof, at the step's code. |
| `nuOutK` | `x : Code⟨etaN_C; E⟩ (νX. C)` ⟹ `force x : C[Code⟨etaN_C; E⟩ (νX. C)/X]` | `candN_post` (§4.1). |
| `eraseD` (later, K6) | `Code⟨N; E⟩ D` ⟹ `U C′` for `D ≤ C′`, covariant erasure inside `D` | `𝒞⟦·⟧` monotone in result positions under erasure. Not derived; obstruction not verified. |

About `force`:
- Restating it, rather than adding `forceK`, keeps one rule.
- The alternative `forceK` costs one more rule and keeps `force`'s statement.
- Neither can be avoided by `erase`: `force`'s premise is a context lookup (`SoloP`), not a
  derivation, so `erase` cannot be applied to the slot.

## 4. The hardest cases

### 4.1 `unfold`'s rest (the hardest kernel case)

- **The requirement.** `for` loops (119 programs, S5), generators and div bodies are `unfold`.
  Their loop state is the codata, and it must keep one type across steps (S4: "`U X` must equal
  itself"). If the rest is typed `U (νX. C)`, the first state is specific, every later state is
  `dyn`, and the elaborator must erase before the loop. Every step's call would then be indirect.
- **`nuOutK`** gives the rest the codata's own type.
- **Its soundness.**
  - By the code conjunct, `x` is `etaN C g s` with `g ∈ 𝒱⟦!G⟧`, `s ∈ 𝒱⟦S⟧`.
  - So `x` is in `candN C g S δ` once `g` is erased to the `!U` the candidate asks of it
    (`candN_post`'s `hg`, `Nu.lean:558`).
  - `candN_post` shows the candidate is post-fixed. Each rest is `etaN C g s′` with
    `s′ ∈ 𝒱⟦S⟧`: the same code with the same `g`, so it is in the code conjunct with
    environment `(g, s′)`.
  - The coinduction (`nuRel_coind`) gives the `U (νX. C)` conjunct of the rest.
  - In the chain's relation the same step goes through `cN`'s `ν` clause. Its rests are read at
    the candidate (`thunkRN R`, `Goal791N.lean:168`), and `unfoldN_compatN` uses `candNN`
    (`Core/Chain/NuKW835N.lean:21`).
- **Status.** Not built, and the step from `candN`'s membership to the code conjunct is not
  checked in Lean. No obstruction is known. The existing proof's candidate is exactly the
  per-code set.
- **What this needs from the relation.** The code conjunct must read the environment
  semantically (§2.2): `g ∈ 𝒱⟦!G⟧` is what `candN_post` consumes. A purely syntactic code clause
  would not prove `nuOutK`.

### 4.2 `wrap`'s η-object (alpha-nu-in; the hardest elaborator case)

- **The program.** `wrap` builds `nu_in ⟨read, close⟩`. Its `read` returns `o`'s rest, which is
  `unfold`'s, and not a rest of `wrap`'s object.
  - With `nu_in`, the object is at `νX. C`, its rest is `U X = U (νX. C)`, and the rest is
    erased.
  - `obs_close(rest)` is then indirect even when every other call is direct.
- **The fix.** Type the object at the unrolled type with the rest's synthesized type:
  `Code⟨N_w; E_w⟩ (C[T_u/X])`, where `T_u = Code⟨etaN; …⟩ (νX. C)` is `o`'s rest type.
  - No `ν` is needed: the object's rests are another code's, so it is not a fixed point of its
    own.
  - `obs_read`/`obs_close`, instantiated at `G = Code⟨N_w; …⟩ (C[T_u/X])`, observe it without
    `nu_out`. The elaborator inserts `nu_out` only when the forced type is a `ν`. That is sugar
    keyed on the type.
- **When the object must become `Obs<'c>`.** The rest's erasure is inside the computation type.
  That needs `eraseD` (K6). Without it, the elaborator writes the η-adapter in core terms (sugar
  over existing terms, at the cost of a closure). To confirm with surface which one is wanted
  first.

### 4.3 A recursive closure whose environment holds its own type

- **Not formable as a code type.** `E` would contain `Code⟨N; E⟩ C`, an infinite type, and `VTy`
  is an inductive. Rust refuses the same program (E0644) and asks for `Box<dyn …>`.
- **The fix.** The elaborator erases the capture to `U C`.
- **A μ-typed chain of the same code** is formable in the kernel: `roll` at the unrolling, with
  `E = (μX. Code⟨N; X ⊕ 1⟩ C) ⊕ 1`. That is because the code clause, unlike the `U` clause, reads
  `E` under `η`. The elaborator does not infer `μ`, so this is not used. Whether `roll`'s side
  conditions `NoMut 0` and `Cl 0` hold there is not derived.
- **Surface today.** A recursive closure is not expressible except through `unfold` state or
  `lib/rec.bc` groups (S4).

### 4.4 Polymorphic recursion at a growing specific type

- **The kernel.** Its recursion (`boundedFix`, the Z combinator, `unfold`) is at one type. So
  polymorphic recursion exists only in the elaborator's template instantiation (`makeInst`,
  `Frontend/Sugar.lean:5544`).
- **The guard.** A template whose instantiation reaches itself at a type argument containing the
  previous one is instantiated at the argument's erasure (`U C`) instead, with a note. This is
  decided at elaboration (B3), never in the backend.
- **To confirm with surface:** how `makeInst` handles a recursive template today. The answers do
  not say.

### 4.5 Codes under handlers (#542)

- **Clauses.** Handler clauses are a value form of variables typed `retTy`/`clausesTy` at `!U …`
  (`effHandleV`, `Fundamental.lean:583`; `clausesTy`, `Core/EffRules.lean:1212`).
  - With `erase` a rule on the same term, a clause variable at `!Code⟨…⟩` is typed in `hc`'s
    derivation by `tensorI(eraseB(var), …)`.
  - `effHandleV`'s statement is unchanged, so `HandlerLawN` (`handleV`, `handleVB`, `reify`) is
    unchanged.
  - At the handle node the backend reads each clause's code from its `erase` node's source. That
    is #542's "specialise per definition × handler site × closure code", read and not rebuilt.
- **Continuations** (`kappa`, `kappaC`) are built by the machine and keep their `kTy` type. They
  get no specific type in this scope. #542's per-kind lowering of continuations stays as it is.

## 5. The erasing coercion

- **5.1 Typing.**
  - `erase : Code⟨N; E⟩ C ≤ U C`, with an `!` form. It is an explicit `CDerives` rule on the same
    term, as `bangE` is, so the typed term has a node for it.
  - It is **not** subsumption: no other rule accepts a `code` where it asks for `U`. That is
    what B4 requires.
  - The checker inserts the node from `convVal` (`Frontend/Check/Conv.lean:30`), the way
    `convComp` inserts `rEffSub` (`Conv.lean:39–55`; S4).
  - The node is in the `TExpr` that Backend2 reads, so B4's "every entry into dyn is an explicit
    coercion node" holds by construction. A checker conversion that emits its own rule node is
    not implicit subsumption.
- **5.2 The compatibility lemma.** Forget the code conjunct. One line over `wpTS_mono`.
- **5.3 Erasure at run time.**
  - In the kernel's machine, `erase` is the identity: the same term.
  - In Backend2 it is a change of representation, decided by the backend:
    - a specific closure is its environment, laid out from `E`, so it needs no allocation and no
      tag;
    - `dyn` is a tag plus the widest environment of the codes erased into that `U C` (B4).
  - With the widest environment held in place, `erase` writes the tag and allocates nothing. If
    the backend chose a boxed `dyn` instead, `erase` would allocate. That is a backend choice and
    not a typing fact.
- **5.4 Qualifiers and borrows.**
  - **Persistence.** `Code⟨…⟩ C` is persistent exactly when `U C` is, which is never
    (`Core/Persistent.lean:47`). `!Code⟨…⟩ C` is persistent, like `!U C`.
  - **Consuming.** `consumeAt` at a code type is its `U` scheme, on the same term
    (`Core/Consume.lean:162–164`). The backend calls the consuming observation directly.
  - **Free lifetimes.**
    - `VFree x (Code⟨N; E⟩ C) ≜ VFree x E ∨ CFree x C`. So a closure that captures a borrow
      `Imm 'x A` has `'x` in its type, and lifetime substitution applies to `E`.
    - This is *stricter* than `U C`, whose type does not mention the capture.
    - At a lend's exit (`¬ VFree x B`, e.g. `withbor1`, `Fundamental.lean:407`), a code type that
      captured `'x` is refused, and `erase` to `U C` is today's typing.
    - The elaborator inserts that `erase` where the expected type is `U C`. This is the kernel's
      rule applied, not a workaround.
    - Whether to also insert it where no type is expected is §10's C2.
  - **Outlives.** No `VOutlives` rule for `code` (§2.2). A code value cannot be boxed at a
    lifetime, as a `U` value cannot.

## 6. The elaborator

Surface-foreman's answers (S1–S5) replace this section's assumptions, except where marked "to
confirm".

- **Where specific types arise.**
  - A closure is `thunkv (lam …)`, or `bangThunkv` for `!{…}` (S1, `Frontend/Parser.lean:1365`).
  - Codata has no surface literal. `unfold` is emitted by `for` (`Frontend/Sugar.lean:305`), div
    bodies (`:998`) and generators (`:5371–5430`).
  - The checker synthesizes the code type at each of these in `synV`: `capNorm` of the erased
    body, and the captures' types from the context.
- **Carrying the type.**
  - Inference is bidirectional, with first-order metavariables over value types (S2). A
    synthesized type already flows through `let`, pairs, `letpair` and functions returning
    closures from `if` arms (S2's probes p2, p4, p7). A code type flows the same way.
  - **Dependency: #849.** An unknown local is typed `1` today (`Frontend/Elab/Meta.lean:43`,
    `TCx.push`; `:69`, `tyV`). Carrying an inferred type the user never wrote is exactly the
    case #849 fixes, so S1–S2 below depend on #849 landing first.
- **Where `erase` is inserted** (S4):
  - at `convVal`, wherever the expected type is `U C` (parameters typed `U`, returns, data fields,
    arrays, `Ref` contents, handler arguments, handler state, `Frontend/Elab/Effects.lean:3355` per S4);
  - at a join of two different codes (`if`/`match` arms) with no expected type. Rust refuses that
    join, and the choice is §10's C3;
  - at a recursive template's growing argument (§4.4);
  - at a closure capture of its own type (§4.3).
- **Type parameters.**
  - `fn f[G](g: G)` exists (26 corpus files). It is instantiated by matching on arguments
    (`Frontend/Elab/Match.lean:16–37`) and monomorphised by `makeInst` (S3).
  - `specV` (`Sugar.lean:5986`) already specialises higher-order functions per callback type. It
    is the precedent for instantiating at a code type.
  - A closure's parameter holes are filled only from an expected `U(A ⊸ C)` (S1). So a generic
    parameter needs a bound giving `A ⊸ C`: `fn f[G: A => B](g: G)`, Rust's `impl Fn(A) -> B`.
    Syntax to confirm with surface.
- **The policy question** is §10's C1:
  - **specific by default:** a function type written in a parameter or return position is an
    `impl`, and the parameter becomes a template parameter;
  - **`dyn` by default:** the written type is `U C`, and specific types appear only through
    explicit generics.
- **The guard** for monomorphisation (B3) is the elaborator's: §4.4's growing-argument check, and
  any size bound, become `erase` at elaboration.
- **`nu_in`/`nu_out` at specific types** (§4.2).
  - `nu_out` is inserted only at a `ν`.
  - A `nu_in` whose body's rests are a specific type is typed at the unrolled type, unless the
    expected type is the `ν`.
  - `Clo` (`lib/clo.bc:20`, the library's type, not the elaborator's closures) has rest `U X`, so
    a per-code `Clo` must type its rest the same way (S1).

## 7. What Backend2 reads

| Backend need (B1–B5) | Kernel fact under (a) | Replaces |
|---|---|---|
| the type is the key (B2) | `Code⟨N; E⟩ C` in `use`'s type arguments and judgments; `useKey` unchanged in shape (`Convert.lean:2284`) | `takesClos` per-use reconversion (`Convert.lean:2266–2279`, `:3551`) |
| the code's node, from the type (B2) | a table from `(N, E, C)` to the `thunkF`/`thunkV`/`codeI` node, filled by one pass over the typed program after monomorphisation; equal keys are the same code | `Flow.lean`'s per-variable code sets |
| explicit coercion nodes (B4) | `erase`/`eraseB` nodes; the dyn class of `U C` = the codes of the `erase` nodes into it, plus closures built directly at `U C` | `Layout.lean`'s closure classes by union-find over moves (`:295–420`) |
| monomorphisation at the typed term (B3) | the existing `use` path: different code types give different keys | per-use `conv` of closure-taking bodies |
| the guard in the elaborator (B3) | §4.4 | — |
| handle and constant sites (#542, §4.5, §8.3) | the `erase` node's source type at a clause slot or callback argument | the 0-CFA's set at the clause's call |

**Deleted:**
- `Backend2/Flow.lean` (177 lines; its `UNPROVED` at `:119`);
- `Layout.lean`'s closure-class walk, `walk`/`places` (`:295–420`; its `UNPROVED` at `:398`);
- the class check in `Backend2/LayoutCheck.lean`, as far as it checks closure classes;
- `convUse`'s `takesClos` branch and `takesClos`/`takesClosK`.

**Kept:** `Layout.lean`'s other layouts (boxed fields, heap classes, `UNPROVED` at `:644`,
`:699`), which are not about codes.

The lookup of a node by type is a type comparison. It goes through `tyEqV`, or through a key that
is allowlisted in `scripts/type-eq.allow` with its reason (`ppVT` is `[α]`-invariant only if it
prints lifetime binders canonically: not verified).

## 8. Interactions

- **8.1 `HandlerLawN`** (`Core/Chain/HandlerLawN.lean:67`).
  - Unchanged. Clauses reach `effHandleV`/`effHandleVB` through `erase` nodes (§4.5).
  - `reify`'s `res` is a closed term at `resTy` (`Fundamental.lean:359`). It stays at `U`.
  - Continuations get no specific type.
  - `goal791N : HandlerLawN → Goal791N` keeps its statement. Its proof gains the new rules'
    cases (`FundamentalKW835N.lean`).
- **8.2 The per-lend world `KW`.** Unchanged.
  - The code clause reads the environment at the same world as the value. Its laws along
    `ExtR`/`KW.Owed` come from `E`'s, by induction.
  - A captured borrow is read by `Imm`/`Mut`'s existing clauses inside `𝒱⟦E⟧`.
- **8.3 `Const791` (#844).** Its constants' callbacks are `U …` arguments
  (`origin/tier1-844:Core/TreeGoal791.lean:135–161`).
  - They do **not** become generic in the kernel. The caller's `erase` node carries the
    callback's code, and the backend reads it at the constant's site (§7, last row).
  - `.poly 'y @b c` is untouched.
  - If a constant should instead return a specific type (e.g. a `Const791` that builds a
    closure), that is a separate rule, as `unfoldK` is for `unfold`. None is needed for #855's
    target.
- **8.4 #867 (sized arrays).**
  - **Shared plumbing:**
    - an index that is static and erased at run time;
    - an explicit coercion rule on the same term to the unindexed type;
    - insertion of that coercion at `convVal`;
    - `useKey` keyed by the indexed type;
    - the backend reading the index from the checked type.
  - **Separate sorts:** a code is compared for equality only, with an `Expr` and a `VTy`; a length
    is a natural, with arithmetic at `split` (B5).
  - With (a) here and a `fam` coordinate in #867, the two share rule shape and checker plumbing,
    not a former. With (b) here they are symmetric coordinates. That is C4.
- **8.5 #542.** Its specialisation key `definition × handler site × closure code` becomes:
  - the `use` key with code-type arguments;
  - the handle node;
  - the clause `erase` sources.

## 9. Units

Done-whens are theorems, checks or measured counts. Kernel units land with a SPEC entry first
(Spec first). Every kernel unit's axioms stay within `[propext, Classical.choice, Quot.sound]`.

**Kernel**

| Unit | Content | Done-when |
|---|---|---|
| K0 | SPEC entry: `Code⟨N; E⟩ C`, `capNorm`, the relation clause, the five rules, the erasure policy at lend exits; baseline theorems to preserve (`fundamentalC`, `adequacyC`, `goal791N`) | entry merged |
| K1 | the former across `Core/`: structural functions, `alphaB`, `VFree`, substitution, `VTy.recV`; `capNorm` and `capNorm_shift` | `lake build` clean; `capNorm_shift` and `alphaB` reflexivity at `code` proved; arm count recorded against §2.1's 151–161 |
| K2 | the relation: `vCE`, `vNE`, `vOE` clauses; every law | `valRelOK_vN` (`Goal791N.lean:2485`) and Core's `vC_*` laws at `code`, no new hypothesis |
| K3 | `codeI`, `codeIB`, `erase`, `eraseB`, restated `force`; pin regeneration | `fundamentalC` and `FundamentalKW835N` cover them; `goal791N`'s statement unchanged; `scripts/check-pins.sh`, judgment freeze pass |
| K4 | `unfoldK`, `nuOutK` | `nuOutK_compat` from `candN_post`; a kernel program whose `for` state keeps one code type across 3 steps, at `goal791N` |
| K5 | the lend-exit configuration | a lemma: a code type capturing `'x` fails `¬ VFree x`; its `erase` passes; corpus `rec-lifetimes` checks with the `erase` |
| K6 (later) | `eraseD`, covariant erasure inside `C` | `eraseD_compat` from `𝒞⟦·⟧` monotonicity in result positions; or the obstruction, in Lean |

**Surface**

| Unit | Content | Done-when |
|---|---|---|
| S0 | #849 landed | — |
| S1 | `synV` synthesizes `Code⟨…⟩` at closures and `unfold`; `convVal` inserts the `erase` node; `ppVT` digest | `make gate` passes with every corpus output unchanged; a census of `erase` nodes per program (expected nonzero in the 180 closure programs) |
| S2 | the inference policy (C1, C2, C3); bounds on generic parameters | every corpus golden unchanged (`make gate-full`); the breakage list of S5 checked one by one |
| S3 | the growing-instantiation guard | a negative program instantiated at `U C` with a note, and its golden |
| S4 | `nu_in`/`nu_out` at specific types (§4.2) | alpha-nu-in elaborates with `w` at a code type and `rest` at `unfold`'s code type |

**Backend**

| Unit | Content | Done-when |
|---|---|---|
| B1 | LIR type for `code`; node table by type; `useKey` over code types; `takesClos` deleted | `check-type-eq` passes; `takesClos` gone; corpus counts not above `counts-backend2.expected` |
| B2 | dyn classes from `erase` nodes; `Flow.lean` and the class walk deleted | `Flow.lean` deleted; `UNPROVED` at `Flow.lean:119` and `Layout.lean:398` gone; `make gate-full` passes |
| B3 | handle and constant sites read the `erase` sources | `counts-backend2.expected` rows of #542's 25 handler programs not above today's |
| B4 | the measured target | alpha-nu-in at ≤ 1 alloc and 0 indirect (old backend: 1/0; today: 5/3); no row of `counts-backend2.expected` rises (any change explained) |

Order: K0 → K1 → K2 → K3 ∥ S0. Then S1, B1, K4, S4, B2, B3, B4. K5 goes with S2. K6 only if C1's
answer needs `ν` objects erased with specific rests.

## 10. Choices for the user

- **C1. What a written function or codata type in a signature means.**
  - **Specific by default** (Rust's `impl` in argument and return position; `dyn` written to opt
    in): today's direct calls survive without rewriting, and the S5 breakages are worked through
    in S2.
  - **`dyn` by default** (the written `U C` is `dyn`; specific only through explicit generics):
    closer to the written types. But every program whose direct calls come today from `takesClos`
    or the 0-CFA rises until rewritten, so the "no count rises" target needs a corpus rewrite.
  - Recommendation: specific by default.
- **C2. Erasure where nothing expects a type.** Silently, at a lend's exit for a code type
  capturing `'x` (§5.4), or as an error asking for `dyn`. Recommendation: silently. The result is
  today's typing.
- **C3. A join of two codes with no expected type.** Erase to `dyn` silently, or refuse as Rust
  does. Recommendation: erase, with a count of such sites in S1's census.
- **C4. (a) or (b).** (a) is recommended (§2.6). (b) only if #855 and #867 are to be one kind of
  coordinate.

## 11. Risks and what is not verified

- **R1.** `capNorm_shift` and the `psub`/`capNorm` lemma behind `codeI` are standard, not proved.
- **R2.** Whether the environment's resource is the whole of the closure's resource (`ρR = ∅`)
  is not derived. The clause is stated with `ρR` so it does not need it.
- **R3.** `nuOutK` through `candN_post` is argued, not built. In particular, `g` is erased to the
  `!U` that `candN_post` asks for, and `E`'s order matches `etaN`'s captures.
- **R4.** `eraseD` (covariance of `𝒞⟦·⟧` under erasure) is not derived. The `eff` answers are
  contravariant, so the order is not covariance everywhere.
- **R5.** Types grow with bodies. Key and message size is handled by printing a digest. Memory
  is not measured.
- **R6.** §2.5's obstruction for a `CTy` former is an observation about `cC_head`, not a
  configuration.
- **R7.** The alpha-nu-in target (§9, B4) is a prediction, not a measurement. It also depends on
  S4 and C1.
