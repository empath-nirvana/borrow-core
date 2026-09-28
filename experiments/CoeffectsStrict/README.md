# Data/codata and effects/coeffects, defined strictly

**Question.** The first spike (`experiments/Coeffects/README.md`, branch `coeffects-spike`, PR
#100) found that data/codata is a real duality and effect/coeffect "only rhymes". It used
"effect" and "coeffect" loosely, and effects are built three ways in the core: capabilities,
computation types, and planned handlers. The hypothesis tested here is that the four notions
work together once each is defined in a strict algebraic sense. Andrew Wagner suggested
coeffects.

**Answer, in one paragraph.** They do work together, but as axes, not as a 2×2 of dualities.

- **Polarity: data or codata.** Data is `μ` on value types; codata is `ν` on computation types.
- **Direction: effects or coeffects, relative to one judgment `Γ ⊢ M : C`.** Effects are the
  output side: the monad `UF`, whose algebras are the computation types. Coeffects are the
  input side: comonads on value types, applied to `Γ`.
- **The effect and coeffect structures come from different adjunctions.** The comonad `FU` of
  Levy's adjunction is not a coeffect. Its coKleisli category is the thunk-typed fragment of
  the values: call-by-name, not context dependence.
- **Scope is a third axis.** Owned versus borrowed at `'a` is a resource algebra with a global
  store invariant. It is not an equational structure, and borrows are an instance of none of
  the four notions.
- **How they combine.** The equational axes combine by laws that are either canonical or absent
  for a stated reason. They meet the scope axis only through the Fundamental Property.

**Build.** `lake build CoeffectsStrict`. The library imports `Core` and nothing imports it.
`Core/`, `Frontend/`, `Backend/`, `SPEC.md` and `CDerives` are unchanged. No declaration uses
`sorry` or `axiom`, and every `#print axioms` is within `[propext, Classical.choice,
Quot.sound]`.

| file | contents |
|---|---|
| `Fold.lean` | initial-algebra laws of `foldOwn` on runs, at every `FShape`: β (`fold_beta`), the functor's action (`functor_leaf`/`_varX`/`_sum₁`/`_sum₂`/`_tensor`), uniqueness (`fold_unique`) |
| `Unfold.lean` | final-coalgebra laws of `unfold` at `Loop A B` on runs: β at both observations for **any** step (`unfold_next`, `unfold_close`), uniqueness on finite observation sequences for pure total steps (`unfold_unique`) |
| `Handler.lean` | a deep handler of `{write : I32 ⇝ 1}` is the fold of its free model `μX. A ⊕ (I32 ⊗ X)`: `handle_return`, `handle_write`, `handle_unique` |
| `Context.lean` | which context modalities are comonads: `Imm` is a comonoid (`copy_diag`, `copy_counit`); `!!A = !A` (`bang_idem`) and `[@a][@a]A = [@a]A` (`box_idem`) in the model; `[@a]`'s counit and shorter-index comultiplication (`d_box_counit`, `d_box_dig`); `U C` outlives nothing (`thunk_not_outlives`); `[]I` boxes data and codata alike (`d_box_data`, `d_box_codata`) |

## 1. Sources

Tags follow `docs/prior-art-sessions.md`:

- *(full)*: the whole text;
- *(sections)*: the named sections;
- *(abstract)*: the abstract only;
- *(secondhand)*: known only through another source.

All texts were read by this spike, from PDFs converted with `pdftotext`. Page numbers are those
of the PDF at the URL listed under Sources.

**Effects**
- **Plotkin, Power**, *Algebraic operations and generic effects*, ACS 2003 *(full, §§1–8)*.
  - Def. 1 (p.6): an algebraic operation on a strong monad `T` is a family
    `α_x : (Tx)^v → (Tx)^w` commuting with the parametrised lifting (bind).
  - p.6: "evaluation contexts E[−] commute with the computational effects induced by the
    operations."
  - Thm 2/3 (pp.18–19): algebraic operations correspond bijectively to generic effects
    `w → Tv`.
  - p.2: `handle` "is not algebraic … a deconstructor, whereas the other operations are
    constructors".
  - Cor. 2 (p.21): "The co-Kleisli category of the comonad on T-Alg induced by the monad T is
    used to model call-by-name languages with effects."
- **Plotkin, Power**, *Notions of computation determine monads*, FoSSaCS 2002 *(sections: §§1–3)*.
  - "computational effects determine monads but are not identified with monads."
  - An equational theory `(Σ, E)` gives `T = UF` for the free-model adjunction, and
    `(Σ,E)-Alg ≅ T-Alg`.
  - The seven equations of global state (p.7).
  - Monads are given by operations and equations iff they have bounded rank; continuations do
    not.
- **Plotkin, Pretnar**, *Handling algebraic effects*, LMCS 2013 *(sections: intro, §§1, 2.1–2.3,
  4, 5, conclusion)*.
  - Handlers are models, and handling is "the homomorphism induced by the universal property of
    the free model".
  - Def. 4.2: models and homomorphisms (`h ∘ op_M₁ = op_M₂ ∘ (id × h^β)`).
  - Prop. 4.3: the free-model adjunction.
  - §4.3: "computation types C by models … FA is interpreted by the free model."
  - `M to x. N ≃ M handled with {} to x. N`.
- **Levy**, *Call-by-push-value: decomposing call-by-value and call-by-name*, HOSC 2006
  *(sections: §§1–3, 6.1, 9, 10 opening, 11)*.
  - "a value type denotes an object of C whereas a computation type denotes a T-algebra."
  - §9 recovers the monad as `UF`, with `η = thunk return` and `μ` from `force x to y. force y`.
  - §11: the adjunction is "not investigated in this paper".
  - "comonad" does not occur.
  - Recursive types are excluded.
- **Møgelberg, Staton**, *Linear usage of state*, LMCS 2014 *(sections: §§1, 2.1, 3.2, 4, 5.1,
  Thm 8.1)*.
  - "computations cannot copy the state and save it for later, nor can they discard the state."
  - Thm 4.3: the state-passing translation `(σ ⇀ τ)^S = !σ^S ⊗ S ⊸ !τ^S ⊗ S` is fully complete.
  - §1.3: every monad is a linear-use state monad `S ⊸ !(−) ⊗ S`.
  - Thm 8.1: state access operations `B·S → A·S`, generic effects `B → T_S A` and algebraic
    operations are equivalent data.
- **Wu, Schrijvers, Hinze**, *Effect handlers in scope*, Haskell 2014 *(full, non-layout text)*.
  "fork is clearly a scoping construct"; scoping handlers both interpret and delimit, and "the
  two roles … can be fundamentally at odds".
- **Piróg, Schrijvers, Wu, Jaskelioff**, *Syntax and semantics for operations with scopes*,
  LICS 2018 *(sections: §§1–5, 8)*.
  - "an n-ary operation … is algebraic if … op(x₁,…,xₙ) >>= k = op(x₁ >>= k, …, xₙ >>= k)".
  - `once`/`catch` are not algebraic.
  - A scoped operation takes "a pair consisting of the computation in the scope (t) and a
    continuation (k)".
- **Katsumata**, *Parametric effect monads and semantics of effect systems*, POPL 2014 *(abstract
  only; the paper could not be retrieved)*. The definition of a graded monad used here is the
  one printed in Gaboardi et al. 2016, §5.1: "an E-graded monad on C is given by a lax monoidal
  functor of type E → ([C,C], Id, ∘)".

**Coeffects**
- **Petricek, Orchard, Mycroft**, *Coeffects: a calculus of context-dependent computation*, ICFP
  2014 *(sections: §§1–2, 3.1–3.5, 5.1–5.2)*.
  - Def. 1: the coeffect scalar.
  - Def. 17: an indexed comonad (`δ_{X,Y} : F_{X•Y} → F_X F_Y`, `ε_I : F_I → Id`).
  - §5.1: flat `D^⋆_r(⟦τ₁⟧ × … × ⟦τₙ⟧) → ⟦τ⟧` versus structural
    `D^n_R(⟦τ₁⟧, …, ⟦τₙ⟧) → ⟦τ⟧`.
  - §2.1: "This asymmetry explains why coeffect systems are not trivially dual to effect
    systems."
- **Brunel, Gaboardi, Mazza, Zdancewic**, *A core quantitative coeffect calculus*, ESOP 2014
  *(sections: §§1, 2, 4, 6)*.
  - `!_r` over a structural semiring.
  - Promotion scales the context: `r ⋆ [Γ] ⊢ !e : !_r B`.
  - p.13: when the semiring is trivial "an exponential action is just a comonad … a model of
    linear logic".
  - §6: Petricek's is "'global' comonadic information … ours is 'local', i.e., on each
    variable".
- **Uustalu, Vene**, *Comonadic notions of computation*, CMCS 2008 *(sections: §§1, 2.1,
  3.1–3.3, 4)*.
  - A comonad is "a comonoid in ([C, C], Id_C, ∗)".
  - CoKleisli maps `DA → B` are "context-dependent functions".
  - The product comonad `A × E` has `CoKl(D) ≅ Kl(E ⇒ −)`.
  - The costate comonad comes from `S × − ⊣ S ⇒ −`, "composition the other way around gives …
    the state monad".
  - §4: effects and context combine by "distributive laws of a comonad over a monad".
- **Benton**, *A mixed linear and non-linear logic*, CSL 1994, TR-352 *(sections: abstract,
  §§1.2–1.3, 2.1–2.3)*.
  - Def. 9: the LNL model, a symmetric monoidal adjunction `F ⊣ G` between a CCC and an SMCC.
  - §2.2: "the adjunction induces a comonad on L … Writing ! for FG".
  - Cor. 8/17: LNL models and linear categories correspond.
- **Torczon, Suárez Acevedo, Agrawal, Velez-Ginorio, Weirich**, *Effects and coeffects in
  call-by-push-value*, OOPSLA 2024 *(sections: §§1, 3, 4.1, 5, 6, 7)*.
  - "the combination U (F A) forms a monad and the combination F (U B) forms a comonad [Levy
    2003a]".
  - Coeffects grade context variables and the returner `F^q A`, which describes "the demands
    subsequent computation is allowed to make on the returned value". Effects grade `U^φ B`.
  - The CBN translation of `□_q τ` is `F^q (U ⟦τ⟧)`.
  - The combined system has no distributive law, "we have yet to determine what sorts of
    rearrangement are sound".
- **Gaboardi, Katsumata, Orchard, Breuvart, Uustalu**, *Combining effects and coeffects via
  grading*, ICFP 2016 *(sections: §§1, 2.3, 3.1, 5.1–5.3, 6–8)*.
  - "the graded monad and the graded comonad cannot interact, simply coexisting independently".
  - Def. 5: `σ_{r,e,A} : D_r(T_e A) → T_{κ(r,e)}(D_{ι(r,e)} A)` with four axioms, over a matched
    pair `(ι, κ)` (Def. 2).
  - Both worked examples have a law. The paper gives no example that lacks one.
- **Orchard, Liepelt, Eades**, *Granule*, ICFP 2019 *(sections: §§1, 4.2, 6 end, 9)*. Graded
  necessity and possibility coexist, and the distributive law is future work.

**Data, codata and their combinations**
- **Rutten**, *Universal coalgebra*, TCS 2000 *(sections: §§8, 9, 11, 13)*.
  - Final coalgebra (§9).
  - Lambek (Thm 9.1).
  - Coinduction proof principle (Thm 8.1(4)): "if f and g are homomorphisms then f = g".
  - Definition by coinduction (§11).
- **Meijer, Fokkinga, Paterson**, *Bananas, lenses, envelopes and barbed wire*, FPCA 1991
  *(sections: §4)*.
  - CataEval `⦇φ⦈ ∘ in = φ ∘ ⦇φ⦈L` and CataUP.
  - AnaEval `out ∘ 〚ψ〛 = 〚ψ〛L ∘ ψ` and AnaUP. These are in a CPO setting.
- **Hinze**, *Adjoint folds and unfolds*, SCP 2013 *(sections: §§3, 4.1, 7.1–7.2, 8)*.
  - `x = ⦇a⦈ ⟺ x · in = a · F x` and `x = [(c)] ⟺ out · x = F x · c`.
  - Computation (24) and reflection (25).
  - Type fusion (42): "`νF ≅ R(νG) ⇐ F∘R ≅ R∘G`" for `L ⊣ R`.
- **Backhouse, Bijsterveld, van Geldrop, van der Woude**, *Categorical fixed point calculus*,
  CTCS 1995 *(sections: §§3–3.2, 3.5)*. The rolling rule (Thm 4) is for initial algebras only.
- **Turi, Plotkin**, *Towards a mathematical operational semantics*, LICS 1997 *(sections: §§3,
  5–7)*.
  - A distributive law `λ : TD ⇒ DT` (§7.1).
  - Thm 7.1: laws ↔ liftings of `T` to `D`-coalgebras ↔ liftings of `D` to `T`-algebras.
  - Bialgebras, and initial and final bialgebras (Cor. 7.1–7.3).
- **Capretta**, *General recursion via coinductive types*, LMCS 2005 *(sections: §§1, 3, 8)*.
  The delay type `A^ν` is coinductive with `return`/`step`, and a strong monad on setoids
  (Thm 8.4).
- **Uustalu**, *Generalizing substitution*, ITA 2003 *(sections: abstract, §3)*. Final
  `T′(A, −)`-coalgebras of a parameterized monad carry a monad (Thm 3.9). No distributive law is
  assumed.
- **Piróg, Gibbons**, *The coinductive resumption monad*, MFPS 2014 *(sections: §§1, 3, 5)*.
  - `TA = νX. M(X + A)` is covered by Uustalu's construction.
  - `M(ΣM)^∞` needs a distributive law (Thm 3.8).
- **Ahman, Bauer**, *Runners in action*, ESOP 2020 *(sections: §§1–4.3)*; **Uustalu**, *Stateful
  runners of effectful computations*, MFPS 2015 *(sections: §§1–3, 5)*; **Katsumata, Rivas,
  Uustalu**, *Interaction laws of monads and comonads*, LICS 2020 *(sections: §§1, 2.1, 3.1–3.3,
  4.1–4.2)*. These are cited for the definition of comodels only (§2.4).
- **Power, Shkaravska**, *From comodels to coalgebras*, CMCS 2004: *(secondhand)*, via Behrisch,
  Kerkhoff, Power (ENTCS 2012) Def. 6.1 / Thm 6.2: "A comodel of a Lawvere theory L … is a model
  of L in C^op"; `Comod(L, C) ≃ G_L-Coalg`.
- **Not read:** Levy's CBPV book; Hyland–Plotkin–Power's overview; Klin's bialgebra
  introduction; Jacobs–Rutten's tutorial (its PDF has no text layer); de Vilhena–Pottier's
  Hazel.

## 2. Definitions

Each notion is fixed in a stated setting. `V` is a category of values (sets, or the
semantic value predicates of the typed world); `T` a strong monad on it.

| notion | setting | definition | the unique map and its laws |
|---|---|---|---|
| **data** | an endofunctor `F : V → V`, polynomial | the initial `F`-algebra `in : F(μF) → μF` | `fold a` is the unique algebra map to `a : FA → A`. **β**: `fold a ∘ in = a ∘ F(fold a)`. **η** (uniqueness): `h ∘ in = a ∘ F h ⟹ h = fold a` (Hinze (23)–(24); Meijer et al. CataEval/UP) |
| **codata** | an endofunctor `G` (here on computation types) | the final `G`-coalgebra `out : νG → G(νG)` | `unfold c` is the unique coalgebra map from `c : S → GS`. **β**: `out ∘ unfold c = G(unfold c) ∘ c`. **η**: `out ∘ h = G h ∘ c ⟹ h = unfold c` (Rutten §§9, 11; Thm 8.1(4)) |
| **effects** | an equational theory `(Σ, E)` (a Lawvere theory); its free-model adjunction `F ⊣ U` | the monad `T = UF` | an **algebraic operation** is a family `op_X : (TX)^n → TX` that commutes with bind, `op(x̄) >>= k = op(x̄ >>= k)` (Plotkin–Power Def. 1; Piróg et al. (1)); equivalently a generic effect `P → T(Ar)` (Thm 2). A **handler** is a model `M`; handling is the homomorphism `F A → M` induced by freeness (Plotkin–Pretnar Prop. 4.3). **Graded**: `E → ([V,V], Id, ∘)` lax monoidal (Katsumata, as printed in Gaboardi et al. §5.1) |
| **coeffects** | a comonad (or a graded comonad) `D` on `V`, applied to the context | a judgment `Γ ⊢ e : τ` denotes a coKleisli map `D⟦Γ⟧ → ⟦τ⟧` | counit `ε : D → Id`, comultiplication `δ : D → DD` (Uustalu–Vene §3.1). **Graded** (Petricek Def. 17): `δ_{r,s} : D_{r•s} → D_r D_s`, `ε : D_1 → Id`. **Structural** (Brunel et al.): one `!_r` per variable over a semiring, `+` for contraction, `0` for weakening, `⋆` for promotion |

**Which coeffect notion is "the" one.** It is the graded comonad on the context.

- **Structural**, per variable (Brunel et al.; Petricek's structural systems), when variables
  are linear. Its ungraded case is linear logic's `!`, which the core has.
- **Flat**, on the whole context (Uustalu–Vene; Petricek's flat systems), for modalities of the
  whole context.
- **Comodels and runners are not coeffects.**
  - A comodel of a theory is a model in `C^op` (Power–Shkaravska, secondhand).
  - A runner is a comodel, or equivalently a monad morphism `T → St_W` (Uustalu 2015 Prop.
    3.1).
  - In an interaction law the comonad is the machine that runs the effects (KRU §4), not the
    client's context.
  - They sit on the effect side, as interpreters of the operations. They are cited here only to
    place them. Linear state already provides what they provide (§2.4).

### 2.1 Placement in CBPV

Levy's adjunction `F ⊣ U : C → V` (values `V`, computation types `C`).

- **Effects.** `T = UF` is the monad on `V` (Levy §9: `η = thunk return`). A computation type
  denotes a `T`-algebra (Levy §3). So every computation type is closed under the operations:
  an algebraic operation is available at every `C`, not only at `F A`. Plotkin–Pretnar §4.3
  says the same for models of an effect theory.
- **The comonad `FU` on `C`.**
  - By the adjunction, a coKleisli map `FUB → B′` is the same as a value map `UB → UB′`.
  - So the coKleisli category of `FU` is the full subcategory of `V` on thunk types: a
    computation with one thunk in context.
  - Plotkin–Power Cor. 2 names it: the coKleisli category of the comonad on `T-Alg` models
    **call-by-name**.
  - It is an evaluation-order device, and carries no information about the context beyond the
    adjunction's.
- **Coeffects** are comonads on `V`, applied to `Γ`. In this core they come from structures
  other than `F ⊣ U`:
  - `!` is persistence. In the model it is idempotent (`bang_idem`: `!!A` and `!A` are one
    predicate): the coreflection onto the values held at the empty resource. Benton's LNL
    adjunction gives `! = FG` for a different adjunction, between a cartesian and a linear
    category (Benton §2.2). The usage grades `{0, 1, ω}` (`experiments/Grades`) are its
    structural grading.
  - `[@a]` is the lifetime necessity (§2.3).
  - `Imm 'a U ⊗ −` is a product comonad (§2.3).

**Petricek's comonad and CBPV's `FU` are different.**

- Petricek's comonad is on `V`, the category of contexts.
- `FU` is on `C`, and its coKleisli category adds nothing to `F ⊣ U`.
- Torczon et al. encode the graded `□_q` as `F^q U`, but the content is the grade `q` on the
  returner. That grade is a structural coeffect on the variable that `x ← M` binds. The
  ungraded `FU` is only the carrier.

So the hypothesis "effects and coeffects are two faces of one adjunction" fails, precisely: the
comonad of Levy's adjunction is not the coeffect comonad. The monad and the comonad that matter
come from two adjunctions: Levy's `F ⊣ U` for effects, and a persistent-to-linear adjunction
for `!`.

**Data and codata.**
- `μ` lives on `V`: SPEC §6's `μX. A`, a positive type built by construction.
- `ν` lives on `C`: SPEC §7's `νX. C`, a negative type defined by observation.
- `ν` is taken on the category of algebras, so codata is effectful by construction: every
  observation is an `F` computation.
- Transported to `V` it is the familiar effectful codata. Take Hinze (42) with `L ⊣ R = F ⊣ U`,
  `G X = F(A ⊕ UX) & F B` on `C`, and `F′ Y = T(A + Y) × T B` on `V`.
  - `F′ ∘ U ≅ U ∘ G`, because `U` preserves products (`U(C & D) ≅ UC × UD`).
  - Therefore `U(Loop A B) ≅ νY. T(A + Y) × T B`: the generalized resumption over the ambient
    monad (Goncharov–Schröder's `νX. M(X + A)`, per Piróg–Gibbons) with an early-close
    observation.
  - No distributive law enters: Piróg–Gibbons say Uustalu's parameterized-monad construction
    covers this shape.
  - This is a paper calculation from printed statements, not a Lean result: the unary relation
    has no isomorphisms.

### 2.2 The account: three axes

| axis | poles | where in `Γ ⊢ M : C` | structure | kind of law |
|---|---|---|---|---|
| **polarity** | data `μ` / codata `ν` | the types `A` in `F A`, and `C` itself | initial algebra on `V` / final coalgebra on `C` | equational, local: β and uniqueness |
| **direction** | effects / coeffects | output (`F`, `UF`) / input (`Γ`) | monad from `(Σ,E)` / (graded) comonad on `V` | equational, local: monad/comonad laws, algebraicity |
| **scope** | owned / borrowed at `'a` | resources of `Γ` and of values | a resource algebra (BoLo's cells composed by `○`, flattened into a heap) with a global store invariant (the typed world) | not equational: soundness is a global invariant over the store |

The equational axes are about composing programs. The scope axis is about the store: its
soundness is not closed under local composition. The mechanization is the evidence:

- the typed world;
- flattening;
- the update relation;
- `[TR]` 6.48's accounting through the immutable ancestor;
- the excluding property, which is historical, not pointwise, so that no local predicate is
  closed under composition.

The axes meet in one place, the **Fundamental Property**: each local typing rule is justified
semantically against the global invariant.

### 2.3 The core's context modalities, checked against the comonad laws

| modality | counit | comultiplication | contraction / weakening | verdict |
|---|---|---|---|---|
| `!A` | `bangE` | not a rule (promotion only at `λ`/`Λ`); holds in the model (`bang_idem`) | `copyBang`, `forgetBang` | a coeffect (Brunel's `!`, ungraded); syntactically without digging |
| `[@a]A` | `boxE` (`d_box_counit`) | `[@b]A ⊸ [@a][@b]A` for `a ⊏ b` (`d_box_dig`); same index holds in the model (`box_idem`), not a rule, since `VOutlives.box` is strict | — | a lifetime-indexed necessity: a flat coeffect in Fitch style (`[]I` filters the context, it does not scale it) |
| `Imm 'a U ⊗ −` | `forget` (`forget_steps`) | `copy`, the diagonal (`copy_diag`, `copy_counit`) | the same | the product (reader) comonad: the implicit-parameter coeffect |
| `Mut 'a U ⊗ −` | `forget` | `Mut ⊸ Mut ⊗ Mut` is not a rule; not derived, no obstruction verified. BoLo's `○` composes two `mut` cells at one location (`CellU.CompR.mutMut`), so the obstruction is not a disjointness of the resource algebra | — | **not a comonad in the core**. Sequential sharing is the reborrow, which hands the borrow back: state passing (§2.4) |

### 2.4 Capabilities: linear state, which is an effect

A `Mut` capability is threaded. `write_byte : !(∀'a. Mut 'a Output ⊗ I32 ⊸ F(Mut 'a Output))`
takes the state and gives it back. Two sequential uses are a reborrow (the first spike's
`d_seqD`). This is the linear-use state monad `S ⊸ !(−) ⊗ S` of Møgelberg–Staton.

- Their Thm 8.1 makes state access operations, generic effects and algebraic operations
  equivalent data.
- Their Thm 4.3 makes the state-passing translation fully complete.

So a `Mut` capability is the **effect** `write`, presented in state-passing form. The variable
sits in `Γ`, but the structure is the state monad, not a comonad. An `Imm` demand, by contrast,
is a genuine coeffect: the reader comonad.

## 3. Combinations

| pair | law needed | status here |
|---|---|---|
| **effects × codata** | none in CBPV: `ν` is taken on `C`, the algebras, so the functor is on algebras directly. On `V`: `U(Loop A B) ≅ νY. T(A + Y) × TB` by Hinze (42) | canonical. **`Loop` is exactly `νX. F(A ⊕ U X) & F B`** (`CTy.loop`, `Core/Types.lean`). The β law holds for any step, effects included (`unfold_next`, `unfold_close`) |
| **effects × data** | none: a free monad is data. `Tree_Σ A = μX. A + Σ_op P_op × X^{Ar_op}`; handlers are folds (Plotkin–Pretnar) | canonical for finite arities: `{write : I32 ⇝ 1}` is `μX. A ⊕ (I32 ⊗ X)` in `FShape` (`Handler.lean`). An operation with a non-finite arity (`read`) needs `X` under `U`/`⊸`, which `FShape` excludes (SPEC §6) |
| **coeffects × data** | the comonad commuting with `μ`: `!` over persistent `μ` (`VTy.persistent`); the borrowed view `Imm̲` substituting through `μ` (SPEC §6) | in the core: structural, per clause |
| **coeffects × codata** | the box on thunks: `[@d] U(νX. C)` | in the core: `[]I` at every value type (`d_box_codata`, the same rule as `d_box_data`). `U C` has no outlives rule (`thunk_not_outlives`), so the box is the only way a thunk crosses a scope. This is `docs/scope-recursion.md` §3.5's `IterMut<'a>` |
| **effects × coeffects** | a (graded) distributive law `D T → T D` (Gaboardi et al. Def. 5; Uustalu–Vene §4) | **absent for the ambient monad, and the core does not need one.** Promotion `!Γ ⊢ M : !A` at a computation `M` would need `!(T A) → T(!A)`. `alloc` refutes it: SPEC §2 says "`alloc ()` in an empty context must not have type `!(Ref 1)`". The core restricts promotion to `λ`/`Λ`, so a coeffect never crosses `F` |
| **data × codata** (bialgebras) | a distributive law of syntax over behaviour (Turi–Plotkin Thm 7.1) | not needed by the language. It would give congruence of bisimilarity for an operational semantics (Cor. 7.5), which a program-equivalence layer would want |

So every combination is expressible, and the laws compose axis by axis. The one missing law,
effects × coeffects, is excluded by design, and the exclusion is a rule of the core (promotion
at values only).

## 4. Classification of the core's constructs

| construct | structure | notes |
|---|---|---|
| machine effects: `alloc`, `free`, `load`, `store`, host steps | **algebraic operations of the ambient monad `T = UF`** (the heap monad) | every computation type is a `T`-algebra; `alloc` untracked in types (§13) |
| capabilities / stdio (`Mut 'a Output`, `write_byte`, `read_byte`) | **effect**: linear state (Møgelberg–Staton), equivalent to the algebraic operations `write`, `read` | a comodel/runner reading exists (§2) and is not needed |
| borrow block `withbor` | **none of the four; scope axis** | not algebraic: `(withbor c k) to x. N` cannot become `withbor c (k; N)`, since the scope's result must be `['x] T` and the cell comes back. It is a *scoped operation* (Piróg et al.), a delimiter. Its soundness is the typed world's (§2.2) |
| `Imm 'a U` demand | **coeffect**: reader comonad via the comonoid `copy`/`forget` | flat, one per borrow |
| `Mut 'a U` demand | **effect**: linear state | reborrow = sequential threading; not a comonad (§2.3) |
| `!A` | **coeffect**: the (ungraded) exponential | `{0,1,ω}` grades are its structural grading (`Grades`) |
| lifetime context `Δ`, `[@a]`, outlives | **coeffect** `[@a]` (lifetime-indexed necessity) plus the **scope axis** (`Δ`, `⊏`, `VOutlives`) | the box is equational; the lifetime order and its soundness are the store's |
| `fold_imm`/`fold_own`/`fold_reuse` | **data**: the unique algebra map (β and uniqueness: `Fold.lean`, for `fold_own`) | `fold_imm` traverses through `withload`: the fold is data × scope |
| `unfold`, `nu_in`/`nu_out` | **codata**: the unique coalgebra map (`Unfold.lean`) | — |
| div, `Loop` | **codata over the ambient effect**: `νX. F(A ⊕ U X) & F B`; `U(Loop) ≅ νY. T(A + Y) × TB`. Divergence is the effect whose monad is Capretta's delay, itself codata | `div_bind` is the delay monad's bind, written as an unfold |
| `Iter` | **codata** | an iterator's state may hold resources; one holding a borrow crosses scopes as `[@d] U(Iter …)` |
| `alloc` | algebraic operation of `T` | a capability version is the linear-state presentation of the same effect; the account needs neither |
| planned handlers (#18) | **effects**: handlers are folds of free-model data (finite arity now; general arity needs `X` under `U`) | tail-resumptive operations are capabilities already |
| planned async / generators (#52) | **codata** (`Loop`/`Iter`) whose state holds resources; borrows via `[@d] U(ν…)` | see §6 |

**Borrows are an instance of none of the four.**
- A borrow block is a scoped operation.
- A `Mut` demand is linear state.
- An `Imm` demand is a reader comonad, so its *typing* is a coeffect, but its *soundness* is the
  store's.
- Scope is its own axis.

## 5. Laws, on runs

The semantics is a unary logical relation with no program equivalence. So each law is stated as
reduction by pure steps (`PureSteps`, every heap to itself), and `Evals e v` is `e ↦* v`. An
equation `f = g` becomes "both reach one value". What cannot be stated is contextual equivalence
of two open terms, or of two effectful runs.

| law | statement | status |
|---|---|---|
| fold β, every `FShape` | `foldOwn g w ↦* (travO T (fold g) w) to r. g r` (`fold_beta`), and `travO T` is the functor's action (`functor_*`) | **proved** |
| fold uniqueness | any `h` with `T(h) w ↦* r ⟹ h w ↦* g r` reaches `fold g`'s value on every finite value without `Ref X` positions, for total `g` (`fold_unique`) | **proved** |
| fold laws at `Ref X`, and for `fold_imm` | the action frees a cell, or loads through `withload`: a heap step | not derived, no obstruction verified |
| unfold β at `Loop` | `next (unfold g s) ↦* x ← next (g s); map_{A⊕X} (unfold g) x`, and the same for `close`, for **every** step `g`, effectful or not (`unfold_next`, `unfold_close`) | **proved** |
| unfold uniqueness | two coalgebra maps from a pure, total step agree on every `n` observations (`unfold_unique`) | **proved** for pure steps. Effectful steps: not derived, no obstruction verified (it needs a relation between two runs) |
| handler = homomorphism | `handle (return a) ↦* g (inj₁ a)`; `handle k ↦* r ⟹ handle (write(n); k) ↦* g (inj₂ (n, r))`; uniqueness (`Handler.lean`) | **proved** |
| comonad laws of `Imm ⊗ −`, `[@a]`, `!` | table §2.3 | **proved** where the table says; digging at the same index holds only in the model |

## 6. Independence of the axes

**Test case 1: CBPV bakes `F` into computation types.**

Independence **holds for the laws**, and **cannot be abstracted** in the types.

- `unfold_next` and `unfold_close` hold for every step, whatever it does to the heap. The β law
  of codata does not depend on the effect.
- The effect of codata is a parameter only in the sense of a fixed ambient `T`. `U(Loop A B) ≅
  νY. T(A + Y) × TB` is `νX. T(F X)` at `T = UF`.
- A codata type over *another* monad `M` is expressible when `M` is itself written in the core:
  the delay monad, or a free monad as data.
- It cannot be quantified: "The core has no type ranging over computation types" (SPEC §14), and
  `F` is not graded.
- Divergence is where the two axes coincide by definition. Its monad, Capretta's delay, is
  codata, so marking a function div means switching its result to `Loop`, and SPEC §14
  specializes at callback types to avoid coloring.
- Strict independence would put a grade on `F` (Katsumata, Torczon's `U^φ`) and leave `Loop` as
  one implementation of it. That is a kernel change, and nothing here requires it.

**Test case 2: codata capturing borrows.**

Independence **holds**.

- The law is `[]I` at `U(νX. C)`: the same rule that boxes data (`d_box_codata`, `d_box_data`).
- It is covered by `fundamentalC`, since `[]I` is one rule at every value type.
- What makes it look special is that `U C` carries no outlives information
  (`thunk_not_outlives`), while `μ` is checked structurally (`mu_outlives`). The box supplies
  the capture bound. So "iteration at the borrow's lifetime" is codata × scope, solved once, as
  `docs/scope-recursion.md` §3.5 predicted.
- It is not yet written as a program (SPEC §7 Open).

**Test case 3: `fold_imm`'s termination by the witness size.**

This is the account's accepted interaction, and it is **not evidence against independence of the
laws**.

- `fold_imm`'s β and uniqueness would be statements about runs that step through `withload`. They
  are not derived here, and nothing in them mentions sizes.
- Its *soundness* (`foldImm_compatX`, via `withload_sized`) is a fact about the global
  invariant: a loaded view's witness is strictly smaller. Every construct's soundness goes that
  way.
- So the division is exact. Laws are local, per axis. Soundness is global, through the
  Fundamental Property. `fold_imm` is where data meets scope, and they meet only in the soundness
  proof.

**Suspended computations holding resources.** The claim is that three open problems are one:

- iterators holding borrows;
- async tasks suspended holding borrows;
- handlers holding continuations that own resources.

Each is codata whose state holds resources.

- **Owned resources:** the core already interprets them. The thunk clause of the relation
  (`vCE true (U C) v ρ = ∀ ls', Ext ls ls' ρ → 𝒞⟦C⟧ …`) holds a suspended computation at its
  resource `ρ`, and `bytes c` is an iterator that owns a capability.
- **Borrows within their scope:** the same clause covers them.
- **Crossing a scope:** the box supplies the bound (test case 2).
- **Continuations:** a handler's continuation of type `U C` is linear, hence one-shot by
  construction. The Hazel comparison is *(secondhand)*; Hazel was not read.

So the unification is right about the shape, and it sits exactly where the equational axes meet
the scope axis: at a value of `U C` whose resource includes borrows. What the core lacks is
expressiveness, not a new global invariant:

- a scheduler holding tasks whose borrows are at different lifetimes needs existential lifetimes
  or scoped spawning;
- multi-shot continuations are excluded by linearity.

Whether the frame end of `withbor` (6.64) needs any change for a boxed thunk that holds a
reborrowed view: not derived, no obstruction verified. `fundamentalC` covers every derivable
term, so the question is only what becomes derivable.

## 7. Verdict

**There is a coherent account.** Evidence strength:

- The definitions are strong: printed and read.
- The placement is strong for `FU` and its coKleisli category (one line from the adjunction,
  printed in Plotkin–Power Cor. 2). It is moderate for `U(Loop) ≅ νY. T(A+Y) × TB`, which is
  Hinze (42) applied on paper.
- The laws are machine-checked, at the reach stated in §5.

| | definition | place in CBPV | combines with |
|---|---|---|---|
| data | initial algebra `μF`, fold unique | `V` | effects: free monads are data, handlers are folds. Coeffects: the comonad through `μ`. Scope: `fold_imm`, sound by the global invariant |
| codata | final coalgebra `νG`, unfold unique | `C` (algebras of `T`) | effects: built in, `U(νG) ≅ ν(F′)` by type fusion. Coeffects and scope: `[@d] U(νG)` |
| effects | algebraic theory, monad `T = UF`, operations commute with bind, handlers are free-model homomorphisms | output side, `F`; `C` = `T`-algebras | coeffects: a distributive law `DT → TD`, absent for `alloc`, so promotion is value-only |
| coeffects | (graded) comonad on `V`, applied to `Γ` | input side, `Γ`; not `FU` | effects: as above |
| scope | resource algebra + global invariant | resources of `Γ` and values | everything, through the Fundamental Property only |

**Where the user's hypothesis holds.** Data/codata and effects/coeffects work together once
defined strictly, as orthogonal axes, with laws per axis.

**Where it fails.**
1. "Effects and coeffects are two faces of one adjunction" is false as stated. `FU` is not the
   coeffect comonad (§2.1).
2. The effect × coeffect combination has no canonical law for this core's monad. The core's rule
   (promotion only at values) is the correct response, not a gap.
3. Borrows are not one of the four. They are a third axis whose soundness is global.

## 8. Implications for the language

1. **Terminology.**
   - A `Mut` capability is an effect in state-passing form, not a coeffect.
   - `Imm` demands, `!` and `[@a]` are coeffects.
   - Borrow blocks are scope.
   - The first spike's `needs`/`provides` layer (`KDem`) is still a correct elaboration. What it
     elaborates is effect threading, so it belongs with effects in the surface.
2. **I/O stays capability-passing.** By Møgelberg–Staton that *is* the algebraic effect, so there
   is no second mechanism to add for tail-resumptive operations. User "handlers" of such an
   operation are values meeting the extern's contract (SPEC §11 "Handlers").
3. **#18 (handlers)**, re-planned. A handler is a fold of a free model, which is data. The kernel
   needs no handler construct:
   - finite-arity signatures work today, as `Handler.lean` shows;
   - general arity needs `X` under `U` in `FShape`, which is SPEC §6's open item and the one
     kernel extension on this path.
   - Handlers that resume later or never (generators) are codata observers, as SPEC §14 already
     does for div.
4. **#52 (async)**, re-planned. Codata (`Loop`) whose state holds resources, with borrows crossing
   scopes as `[@d] U(Loop …)`. Write `IterMut<'a>` first; it is the same construct. A scheduler
   over heterogeneous lifetimes is the open expressiveness question.
5. **`alloc`.** It is an operation of the ambient monad. Giving it a capability would move it
   into linear state. That is allowed and changes three constants, but the account does not ask
   for it. If allocation must be tracked in types, the account's place for that is a grade on `F`
   (the effect axis), not a context demand.
6. **Two optional rules the model already validates.**
   - Digging `!A ⊸ !!A` (`bang_idem`).
   - Same-index box comultiplication `[@a]A ⊸ [@a][@a]A` (`box_idem`).

   Each is one compatibility lemma if a program needs it.

### Surface, if it followed the account strictly

This is a sketch. None of the words are decided.

    data List a = nil | cons(a, List a)                -- polarity: built by constructors, consumed by `match`/`fold`
    codata Loop a b { next : a + Self, close : b }     -- polarity: built by `unfold`, consumed by observation

    effect Out { write : i32 -> () }                   -- direction, output side: operations
    fn greet() does Out = { write(72); write(105) }    -- elaborates to a threaded `mut 'a output`
    handle greet() { return x => …, write(n) => … }    -- a fold of the free model (finite arity)

    fn show(x: i32) needs cfg: Config = …              -- direction, input side: a reader demand (`imm`)
    borrow c as 'a { … }                               -- scope: a delimiter, not an operation

The account needs three surface families: one word pair per axis. The first spike's
`needs`/`provides` would split in two:

- `needs` would remain for the reader-like demands;
- threaded capabilities would move to the effect word (`does`);
- `borrow`/scope would stay its own form.

## Sources

- https://homepages.inf.ed.ac.uk/gdp/publications/alg_ops_gen_effects.pdf
- https://homepages.inf.ed.ac.uk/gdp/publications/Comp_Eff_Monads.pdf
- https://arxiv.org/pdf/1312.1399 (Plotkin, Pretnar)
- https://www.cs.bham.ac.uk/~pbl/papers/hosc05.pdf (Levy)
- https://arxiv.org/pdf/1403.1477 (Møgelberg, Staton)
- https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
- https://maciejpirog.github.io/papers/scopes.pdf
- https://tomasp.net/academic/papers/structural/coeffects-icfp.pdf
- https://www.cis.upenn.edu/~stevez/papers/BGMZ14.pdf
- https://cs.ioc.ee/~tarmo/papers/uustalu-vene-cmcs08-authorver.pdf
- https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-352.pdf (Benton)
- https://arxiv.org/pdf/2311.11795 (Torczon et al.)
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf
- https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- https://ir.cwi.nl/pub/48/0048D.pdf (Rutten)
- https://maartenfokkinga.github.io/utwente/mmf91m.pdf
- https://www.cs.ox.ac.uk/ralf.hinze/publications/SCP-78-11.pdf
- https://www.cs.nott.ac.uk/~psarb2/MPC/catfixpnt.ps.gz (Backhouse et al.)
- https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf (Turi, Plotkin)
- https://arxiv.org/pdf/cs/0505037 (Capretta)
- http://www.numdam.org/item/10.1051/ita:2003022.pdf (Uustalu 2003)
- https://www.cs.ox.ac.uk/files/6660/crm.pdf (Piróg, Gibbons)
- https://arxiv.org/pdf/1910.11629 (Ahman, Bauer)
- https://cs.ioc.ee/~tarmo/papers/uustalu-mfps15.pdf
- https://arxiv.org/pdf/1912.13477 (Katsumata, Rivas, Uustalu)
- https://purehost.bath.ac.uk/ws/files/9144807/2jul12.pdf (Behrisch, Kerkhoff, Power)
